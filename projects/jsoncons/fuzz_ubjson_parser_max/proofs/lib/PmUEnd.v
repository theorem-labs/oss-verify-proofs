(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit PmLayout PmLayoutU PmModel PmModelFacts PmStatics PmSpecs PmSpecsU PmStep PmKeep PmKitU PmFrame PmParSpecs PmParSpecsU PmParKit PmUEndP.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Ubsan.
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc. Local Ltac lia := L5FastLia.plia.
Module PMUEND.
Import PMU.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMU.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKU.klayout_U L LY.
Let SF := PMKU.sfoot_U L LY.
Theorem end_array_ok : PMU.end_array_spec L HI.
Proof.
unfold PMU.end_array_spec, PMSP.end_array_spec, PMSP.run_spec, PMSP.run_spec_r.
intros fx R M model K LBX cr sp r fb cat s str sm e HH MOK K0 ENT FOK ARGS RPRE INCS INV EC0 UNR CRED KONT.
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK). destruct FOK as (F1 & F2 & F3). cbn [pa_frame AD PmLayoutU.ADDR_U] in F2.
pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
destruct ARGS as ((A10 & A11 & A12) & HLEN). destruct RPRE as (PA & IA & VIS & VREF & BASE & ERR & TBOK).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12.
unfold PMSP.o_src, PMSP.o_p, PMSP.o_is, PMSP.o_ec, PMSP.o_v in *. cbn [pa_off_p pa_off_is pa_off_ec pa_off_v AD PmLayoutU.ADDR_U] in *.
change (PMSP.pm_scr 1) with 14336 in *.
assert (SC0 : 0 <= 14336) by lia.
set (LB := PM.parser_own s ++ LBX) in *.
assert (BR : PMFR.brange L LB) by (apply (PMFR.brange_of_heap L HI HIok LB LB cr M _ HH); apply incl_refl).
pose proof (L5C.stk_writable RSEGS _ M sp 14336 STK) as WR.
destruct s as [mo dn dp src tb tg vb vk stk].
cbn [PM.p_src PM.p_stk PM.p_depth PM.p_more PM.p_done PM.p_b PM.p_k PM.p_tb] in *.
assert (VIN : In (vb, 32 * 2 ^ vk) LB) by (unfold LB, PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
assert (SINC : incl (PM.vs_own str) LB) by (unfold LB; apply incl_appr; exact INCS).
destruct (BR _ _ VIN) as (V0 & V1 & V4). unfold hl_ceil in V4.
pose proof INV as (IM & ID & IDP & ISH & ITB). cbn [PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_tb PM.p_tg] in IM, ID, IDP, ISH, ITB.
pose proof ISH as (SH1 & SH2 & _). unfold PM.MAX_DEPTH in SH2.
assert (DPR : 1 <= dp <= 1024) by (clear - IDP SH2 HLEN; lia).
pose proof PA as (_ & PDEF & _ & _ & _ & P12 & P16 & P20 & _ & _ & _ & _ & _ & _ & PVEC & _).
cbn [PM.p_depth PM.p_b PM.p_k PM.p_stk] in P12, PVEC.
pose proof PVEC as (VC0 & VC8 & _ & Hk & Hlen & Hal & _ & _ & _ & _).
assert (AL5 : (fb + 40) mod 8 = 0) by (replace (fb + 40) with (fb + 8 * 5) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
assert (AL54 : (fb + 432) mod 8 = 0) by (replace (fb + 432) with (fb + 8 * 54) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
assert (AL35 : (32 * Z.of_nat (length stk)) mod 32 = 0) by (rewrite Z.mul_comm; apply Z.mod_mul; lia).
pose proof BASE as (IMG & _). cbn [pa_rw_lo AD PmLayoutU.ADDR_U] in IMG.
unfold PMSP.visitor_at in VIS. cbn [pa_vp_visitor AD PmLayoutU.ADDR_U] in VIS.
assert (WP : L5.writable RSEGS M (fb + 40) 384) by (apply (L5C.writable_of_defined RSEGS); [exact PDEF|lia|lia]).
unfold PMSP.cfg. cbn [pa_end_array AD PmLayoutU.ADDR_U].
cfeed P (PMUENDP.ueaA_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => dp | 34%nat => vb | 35%nat => 32 * Z.of_nat (length stk)
| 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8 | _ => 0 end)) ltac:(first [PMK.sc | unfold PMUENDP.aligned; first [exact A16 | exact AL5 | exact AL54 | exact AL35]
| (replace (fb + 40 + 368) with (fb + 40 + 360 + 8) by lia; exact VC8) | (replace (fb + 40 + 360) with (fb + 40 + 360) by lia; exact VC0)
| (clear - V0 V4 SLO STOP; unfold hl_ceil in *; lia) ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG1 & _ & FRZ1 & MS1 & KS1 & X10 & X11 & X12 & X13 & C368 & C8 & C12 & S16 & S8)); PMK.pvz_clrT.
set (P1 := fun a => (sp - 16 <= a < sp - 16 + 16) \/ (fb + 40 + 8 <= a < fb + 40 + 8 + 1) \/ (fb + 40 + 12 <= a < fb + 40 + 12 + 4) \/ (fb + 40 + 368 <= a < fb + 40 + 368 + 8)).
assert (FRZ1' : forall a, 0 <= a < 2 ^ 64 -> ~ P1 a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha N. apply FRZ1; [exact Ha| | | |]; intros X; apply N; unfold P1; [left| right; left| right; right; left| right; right; right]; exact X. }
apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x36a68 R1 0x36af4 M1 P1 K HH Mh Ml ltac:(lia) MS1 MG1 FRZ1').
{ intros a Pa. apply (PMK.cwr_stack L LB M sp 14336 a STK). unfold P1 in Pa. lia. }
{ intros a. repeat apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| |].
{ apply (PMK.ret_to RSEGS fx1 R1 M1 0x36af4 (ltac:(oW' 0x36af4%Z)) r (ltac:(oF' 0x36af4%Z)) eq_refl (ltac:(oD' 0x36af4%Z))); [rewrite (KS1 1%nat) by PMK.inl; exact Rra| lia| exact Hr2]. }
set (W1 := [(fb + 48, 1); (fb + 52, 4); (fb + 408, 8)] : list L5.range).
assert (WC1 : forall a, PMK.inW W1 a -> (fb + 48 <= a < fb + 49) \/ (fb + 52 <= a < fb + 56) \/ (fb + 408 <= a < fb + 416)).
{ intros a (r0 & Hin & Hr). unfold W1 in Hin. unfold L5.in_rng in Hr. destruct Hin as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hr; lia. }
assert (WHI1 : forall a, PMK.inW W1 a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply WC1 in I; left; lia).
assert (EK1 : PMK.ek L LB sp 14336 W1 M M1).
{ apply (PMK.ek_piece_in RSEGS L KL LB sp 14336 W1 M M1 P1 FRZ1' STK (PMFR.brange_hi L LB BR)).
intros a [Pa|[Pa|[Pa|Pa]]]; [left; lia| right; apply PMK.inW_here; lia| right; apply PMK.inW_next; apply PMK.inW_here; lia| right; do 2 apply PMK.inW_next; apply PMK.inW_here; lia]. }
assert (NW1 : forall a n, fb + 56 <= a -> a + n <= fb + 408 -> forall i, a <= i < a + n -> ~ PMK.inW W1 i) by (intros a n H1 H2 i Hi I; apply WC1 in I; lia).
assert (NW2 : forall a n, fb + 416 <= a -> a + n <= fb + 752 -> forall i, a <= i < a + n -> ~ PMK.inW W1 i) by (intros a n H1 H2 i Hi I; apply WC1 in I; lia).
assert (NW0 : forall a n, fb <= a -> a + n <= fb + 48 -> forall i, a <= i < a + n -> ~ PMK.inW W1 i) by (intros a n H1 H2 i Hi I; apply WC1 in I; lia).
assert (HLEN1 : (1 <= length stk)%nat) by lia.
apply (KONT fx1 R1 M1 model (PM.PST 1 dn (dp - 1) src tb tg vb vk (removelast stk)) sm e cr).
- apply PMK.preserved_by_index. intros k0 Hk0. apply KS1. revert k0 Hk0. apply (PMPK.sub_in PMUENDP.KS_ueaA). vm_compute. reflexivity.
- unfold PMSP.run_post, PMSP.run_pre, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.o_ec. cbn [pa_off_p pa_off_is pa_off_v pa_off_ec AD PmLayoutU.ADDR_U].
split; [|split; [unfold PMSP.src_step; cbn [PM.p_src]; split; [reflexivity|]; split; [reflexivity|]; split; [lia|]; split; [intros X; exact X| lia]|split; [intros X; exact X| right]]].
+ split.
{ apply (PMPK.parser_pop_upd RSEGS AD M M1 (fb + 40) (fb + 440) (PM.PST mo dn dp src tb tg vb vk stk) PA); cbn [PM.p_stk PM.p_depth PM.p_src PM.p_b PM.p_k PM.p_tb].
- lia.
- lia.
- exact HLEN1.
- intros i Hi. apply FRZ1'; [lia|]. unfold P1. lia.
- intros i Hi. apply FRZ1'; [lia|]. unfold P1. lia.
- intros i Hi. apply FRZ1'; [lia|]. unfold P1. lia.
- intros i Hi. apply FRZ1'; [lia|]. unfold P1. lia.
- apply PMPK.dkr_grows. exact MG1.
- apply PMPK.dkr_grows. exact MG1.
- apply PMPK.dkr_grows. exact MG1.
- exact C8.
- exact C12.
- lia.
- replace (vb + 32 * Z.of_nat (length stk) - 32) with (vb + 32 * Z.of_nat (length stk) - 32) by lia. exact C368.
- apply PMPK.dkr_grows. exact MG1.
- lia.
- clear - V4 STOP. unfold hl_ceil in *. lia.
- intros i Hi. apply FRZ1'; [clear - Hi V0 V4 STOP; unfold hl_ceil in *; lia|]. unfold P1. clear - Hi V4 SLO F1. unfold hl_ceil in *. lia.
- intros c0 n0 q0 _. apply PMPK.dkr_grows. exact MG1. }
split; [apply (PMFR.iss_keep RSEGS AD L KL LB sp 14336 W1 M M1 EK1 STK SC0 BR WHI1); [lia|lia| apply NW2; lia| exact SINC| exact IA]|].
split; [apply (PMFR.visitor_keep RSEGS AD L KL LB sp 14336 W1 M M1 EK1 STK SC0); [lia|lia| apply NW2; lia| exact VIS]|].
split; [apply (PMFR.u64_keep RSEGS L KL LB sp 14336 W1 M M1 EK1 STK SC0); [lia|lia| apply NW2; lia| exact VREF]|].
split; [apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 14336 W1 M M1 EK1); [| | | | exact BASE];
intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply WC1 in I; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutU.ADDR_U] in Ha;
clear - I Ha SLO STOP F1; lia|].
split; [apply (PMKP.err_ok_keep RSEGS AD L KL SF LB sp 14336 W1 M M1 EK1); [| | exact ERR];
intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply WC1 in I; cbn [pa_errcat_guard pa_atexit AD PmLayoutU.ADDR_U] in Ha;
clear - I Ha SLO STOP F1; lia| exact TBOK].
+ split; [apply (PMFR.ec_keep RSEGS L KL LB sp 14336 W1 M M1 EK1 STK SC0); [lia|lia| apply NW0; lia| exact EC0]|].
split.
* unfold PM.inv. cbn [PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_tb PM.p_tg].
split; [reflexivity|]. split; [exact ID|]. split; [rewrite (PMPK.removelast_len stk HLEN1); lia|].
split; [apply (PMPK.stack_shape_pop stk ISH HLEN)| exact ITB].
* unfold PMSP.prog_pop. cbn [PM.p_stk PM.p_src]. split; [|reflexivity].
exists (last stk PM.ps_root). apply app_removelast_last. intros E. rewrite E in HLEN. cbn in HLEN. lia.
- apply (PMK.hpres_of L LBX sp 14336 _ M M1).
+ apply (PMK.ek_weaken L LBX LB sp 14336 sp 14336 _ W1 M M1 EK1); [unfold LB; apply incl_appr; apply incl_refl| intros x Hx; exact Hx|].
intros a O r0 Hr0 Hin. unfold W1 in Hr0. unfold L5.in_rng in Hin.
unfold PMSP.W_run, PMSP.W_srcf, PMSP.err_W, PMSP.o_src, PMSP.o_p, PMSP.o_is, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec in O.
cbn [pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit AD PmLayoutU.ADDR_U app] in O.
destruct Hr0 as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hin.
* apply (O (fb + 40 + 8, 8)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
* apply (O (fb + 40 + 8, 8)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
* apply (O (fb + 40 + 360, 24)); [do 5 right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
+ apply (L5.defined_grows M M1 _ _ MG1). exact SDEF.
+ apply (PMK.dk_grows L LBX sp 14336 M M1 MG1).
- change (PM.pot_parser L (PM.PST 1 dn (dp - 1) src tb tg vb vk (removelast stk))) with (PM.pot_parser L (PM.PST mo dn dp src tb tg vb vk stk)).
unfold PMSP.credit_keep. lia.
- apply L5C.model_but_vm_refl.
- exact HH1.
Qed.
Theorem end_object_ok : PMU.end_object_spec L HI.
Proof.
unfold PMU.end_object_spec, PMSP.end_object_spec, PMSP.run_spec, PMSP.run_spec_r.
intros fx R M model K LBX cr sp r fb cat s str sm e HH MOK K0 ENT FOK ARGS RPRE INCS INV EC0 UNR CRED KONT.
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK). destruct FOK as (F1 & F2 & F3). cbn [pa_frame AD PmLayoutU.ADDR_U] in F2.
pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
destruct ARGS as ((A10 & A11 & A12) & HLEN). destruct RPRE as (PA & IA & VIS & VREF & BASE & ERR & TBOK).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12.
unfold PMSP.o_src, PMSP.o_p, PMSP.o_is, PMSP.o_ec, PMSP.o_v in *. cbn [pa_off_p pa_off_is pa_off_ec pa_off_v AD PmLayoutU.ADDR_U] in *.
change (PMSP.pm_scr 1) with 14336 in *.
assert (SC0 : 0 <= 14336) by lia.
set (LB := PM.parser_own s ++ LBX) in *.
assert (BR : PMFR.brange L LB) by (apply (PMFR.brange_of_heap L HI HIok LB LB cr M _ HH); apply incl_refl).
pose proof (L5C.stk_writable RSEGS _ M sp 14336 STK) as WR.
destruct s as [mo dn dp src tb tg vb vk stk].
cbn [PM.p_src PM.p_stk PM.p_depth PM.p_more PM.p_done PM.p_b PM.p_k PM.p_tb] in *.
assert (VIN : In (vb, 32 * 2 ^ vk) LB) by (unfold LB, PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
assert (SINC : incl (PM.vs_own str) LB) by (unfold LB; apply incl_appr; exact INCS).
destruct (BR _ _ VIN) as (V0 & V1 & V4). unfold hl_ceil in V4.
pose proof INV as (IM & ID & IDP & ISH & ITB). cbn [PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_tb PM.p_tg] in IM, ID, IDP, ISH, ITB.
pose proof ISH as (SH1 & SH2 & _). unfold PM.MAX_DEPTH in SH2.
assert (DPR : 1 <= dp <= 1024) by (clear - IDP SH2 HLEN; lia).
pose proof PA as (_ & PDEF & _ & _ & _ & P12 & P16 & P20 & _ & _ & _ & _ & _ & _ & PVEC & _).
cbn [PM.p_depth PM.p_b PM.p_k PM.p_stk] in P12, PVEC.
pose proof PVEC as (VC0 & VC8 & _ & Hk & Hlen & Hal & _ & _ & _ & _).
assert (AL5 : (fb + 40) mod 8 = 0) by (replace (fb + 40) with (fb + 8 * 5) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
assert (AL54 : (fb + 432) mod 8 = 0) by (replace (fb + 432) with (fb + 8 * 54) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
assert (AL35 : (32 * Z.of_nat (length stk)) mod 32 = 0) by (rewrite Z.mul_comm; apply Z.mod_mul; lia).
pose proof BASE as (IMG & _). cbn [pa_rw_lo AD PmLayoutU.ADDR_U] in IMG.
unfold PMSP.visitor_at in VIS. cbn [pa_vp_visitor AD PmLayoutU.ADDR_U] in VIS.
assert (WP : L5.writable RSEGS M (fb + 40) 384) by (apply (L5C.writable_of_defined RSEGS); [exact PDEF|lia|lia]).
unfold PMSP.cfg. cbn [pa_end_object AD PmLayoutU.ADDR_U].
cfeed P (PMUENDP.ueoA_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => dp | 34%nat => vb | 35%nat => 32 * Z.of_nat (length stk)
| 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8 | _ => 0 end)) ltac:(first [PMK.sc | unfold PMUENDP.aligned; first [exact A16 | exact AL5 | exact AL54 | exact AL35]
| (replace (fb + 40 + 368) with (fb + 40 + 360 + 8) by lia; exact VC8) | (replace (fb + 40 + 360) with (fb + 40 + 360) by lia; exact VC0)
| (clear - V0 V4 SLO STOP; unfold hl_ceil in *; lia) ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG1 & _ & FRZ1 & MS1 & KS1 & X10 & X11 & X12 & X13 & C368 & C8 & C12 & S16 & S8)); PMK.pvz_clrT.
set (P1 := fun a => (sp - 16 <= a < sp - 16 + 16) \/ (fb + 40 + 8 <= a < fb + 40 + 8 + 1) \/ (fb + 40 + 12 <= a < fb + 40 + 12 + 4) \/ (fb + 40 + 368 <= a < fb + 40 + 368 + 8)).
assert (FRZ1' : forall a, 0 <= a < 2 ^ 64 -> ~ P1 a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha N. apply FRZ1; [exact Ha| | | |]; intros X; apply N; unfold P1; [left| right; left| right; right; left| right; right; right]; exact X. }
apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x37320 R1 0x373ac M1 P1 K HH Mh Ml ltac:(lia) MS1 MG1 FRZ1').
{ intros a Pa. apply (PMK.cwr_stack L LB M sp 14336 a STK). unfold P1 in Pa. lia. }
{ intros a. repeat apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| |].
{ apply (PMK.ret_to RSEGS fx1 R1 M1 0x373ac (ltac:(oW' 0x373ac%Z)) r (ltac:(oF' 0x373ac%Z)) eq_refl (ltac:(oD' 0x373ac%Z))); [rewrite (KS1 1%nat) by PMK.inl; exact Rra| lia| exact Hr2]. }
set (W1 := [(fb + 48, 1); (fb + 52, 4); (fb + 408, 8)] : list L5.range).
assert (WC1 : forall a, PMK.inW W1 a -> (fb + 48 <= a < fb + 49) \/ (fb + 52 <= a < fb + 56) \/ (fb + 408 <= a < fb + 416)).
{ intros a (r0 & Hin & Hr). unfold W1 in Hin. unfold L5.in_rng in Hr. destruct Hin as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hr; lia. }
assert (WHI1 : forall a, PMK.inW W1 a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply WC1 in I; left; lia).
assert (EK1 : PMK.ek L LB sp 14336 W1 M M1).
{ apply (PMK.ek_piece_in RSEGS L KL LB sp 14336 W1 M M1 P1 FRZ1' STK (PMFR.brange_hi L LB BR)).
intros a [Pa|[Pa|[Pa|Pa]]]; [left; lia| right; apply PMK.inW_here; lia| right; apply PMK.inW_next; apply PMK.inW_here; lia| right; do 2 apply PMK.inW_next; apply PMK.inW_here; lia]. }
assert (NW1 : forall a n, fb + 56 <= a -> a + n <= fb + 408 -> forall i, a <= i < a + n -> ~ PMK.inW W1 i) by (intros a n H1 H2 i Hi I; apply WC1 in I; lia).
assert (NW2 : forall a n, fb + 416 <= a -> a + n <= fb + 752 -> forall i, a <= i < a + n -> ~ PMK.inW W1 i) by (intros a n H1 H2 i Hi I; apply WC1 in I; lia).
assert (NW0 : forall a n, fb <= a -> a + n <= fb + 48 -> forall i, a <= i < a + n -> ~ PMK.inW W1 i) by (intros a n H1 H2 i Hi I; apply WC1 in I; lia).
assert (HLEN1 : (1 <= length stk)%nat) by lia.
apply (KONT fx1 R1 M1 model (PM.PST 1 dn (dp - 1) src tb tg vb vk (removelast stk)) sm e cr).
- apply PMK.preserved_by_index. intros k0 Hk0. apply KS1. revert k0 Hk0. apply (PMPK.sub_in PMUENDP.KS_ueoA). vm_compute. reflexivity.
- unfold PMSP.run_post, PMSP.run_pre, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.o_ec. cbn [pa_off_p pa_off_is pa_off_v pa_off_ec AD PmLayoutU.ADDR_U].
split; [|split; [unfold PMSP.src_step; cbn [PM.p_src]; split; [reflexivity|]; split; [reflexivity|]; split; [lia|]; split; [intros X; exact X| lia]|split; [intros X; exact X| right]]].
+ split.
{ apply (PMPK.parser_pop_upd RSEGS AD M M1 (fb + 40) (fb + 440) (PM.PST mo dn dp src tb tg vb vk stk) PA); cbn [PM.p_stk PM.p_depth PM.p_src PM.p_b PM.p_k PM.p_tb].
- lia.
- lia.
- exact HLEN1.
- intros i Hi. apply FRZ1'; [lia|]. unfold P1. lia.
- intros i Hi. apply FRZ1'; [lia|]. unfold P1. lia.
- intros i Hi. apply FRZ1'; [lia|]. unfold P1. lia.
- intros i Hi. apply FRZ1'; [lia|]. unfold P1. lia.
- apply PMPK.dkr_grows. exact MG1.
- apply PMPK.dkr_grows. exact MG1.
- apply PMPK.dkr_grows. exact MG1.
- exact C8.
- exact C12.
- lia.
- replace (vb + 32 * Z.of_nat (length stk) - 32) with (vb + 32 * Z.of_nat (length stk) - 32) by lia. exact C368.
- apply PMPK.dkr_grows. exact MG1.
- lia.
- clear - V4 STOP. unfold hl_ceil in *. lia.
- intros i Hi. apply FRZ1'; [clear - Hi V0 V4 STOP; unfold hl_ceil in *; lia|]. unfold P1. clear - Hi V4 SLO F1. unfold hl_ceil in *. lia.
- intros c0 n0 q0 _. apply PMPK.dkr_grows. exact MG1. }
split; [apply (PMFR.iss_keep RSEGS AD L KL LB sp 14336 W1 M M1 EK1 STK SC0 BR WHI1); [lia|lia| apply NW2; lia| exact SINC| exact IA]|].
split; [apply (PMFR.visitor_keep RSEGS AD L KL LB sp 14336 W1 M M1 EK1 STK SC0); [lia|lia| apply NW2; lia| exact VIS]|].
split; [apply (PMFR.u64_keep RSEGS L KL LB sp 14336 W1 M M1 EK1 STK SC0); [lia|lia| apply NW2; lia| exact VREF]|].
split; [apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 14336 W1 M M1 EK1); [| | | | exact BASE];
intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply WC1 in I; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutU.ADDR_U] in Ha;
clear - I Ha SLO STOP F1; lia|].
split; [apply (PMKP.err_ok_keep RSEGS AD L KL SF LB sp 14336 W1 M M1 EK1); [| | exact ERR];
intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply WC1 in I; cbn [pa_errcat_guard pa_atexit AD PmLayoutU.ADDR_U] in Ha;
clear - I Ha SLO STOP F1; lia| exact TBOK].
+ split; [apply (PMFR.ec_keep RSEGS L KL LB sp 14336 W1 M M1 EK1 STK SC0); [lia|lia| apply NW0; lia| exact EC0]|].
split.
* unfold PM.inv. cbn [PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_tb PM.p_tg].
split; [reflexivity|]. split; [exact ID|]. split; [rewrite (PMPK.removelast_len stk HLEN1); lia|].
split; [apply (PMPK.stack_shape_pop stk ISH HLEN)| exact ITB].
* unfold PMSP.prog_pop. cbn [PM.p_stk PM.p_src]. split; [|reflexivity].
exists (last stk PM.ps_root). apply app_removelast_last. intros E. rewrite E in HLEN. cbn in HLEN. lia.
- apply (PMK.hpres_of L LBX sp 14336 _ M M1).
+ apply (PMK.ek_weaken L LBX LB sp 14336 sp 14336 _ W1 M M1 EK1); [unfold LB; apply incl_appr; apply incl_refl| intros x Hx; exact Hx|].
intros a O r0 Hr0 Hin. unfold W1 in Hr0. unfold L5.in_rng in Hin.
unfold PMSP.W_run, PMSP.W_srcf, PMSP.err_W, PMSP.o_src, PMSP.o_p, PMSP.o_is, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec in O.
cbn [pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit AD PmLayoutU.ADDR_U app] in O.
destruct Hr0 as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hin.
* apply (O (fb + 40 + 8, 8)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
* apply (O (fb + 40 + 8, 8)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
* apply (O (fb + 40 + 360, 24)); [do 5 right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
+ apply (L5.defined_grows M M1 _ _ MG1). exact SDEF.
+ apply (PMK.dk_grows L LBX sp 14336 M M1 MG1).
- change (PM.pot_parser L (PM.PST 1 dn (dp - 1) src tb tg vb vk (removelast stk))) with (PM.pot_parser L (PM.PST mo dn dp src tb tg vb vk stk)).
unfold PMSP.credit_keep. lia.
- apply L5C.model_but_vm_refl.
- exact HH1.
Qed.
End WithHeap.
End PMUEND.
