(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit PmLayout PmLayoutU PmModel PmModelFacts PmStatics PmSpecs PmSpecsU PmStep PmKeep PmKitU PmFrame PmParSpecs PmParSpecsU PmParKit PmSrcUPeekP.
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
Module PMUIG.
Import PMU.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMU.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKU.klayout_U L LY.
Let SF := PMKU.sfoot_U L LY.
Theorem ignore_ok : PMPSU.fill_buffer_spec L HI -> PMPSU.ignore_spec L HI.
Proof.
intros FB. unfold PMPSU.ignore_spec, PMPS.ignore_spec, PMPS.src_spec.
intros fx R M model K LBX cr sp r fb s str sm Wextra HH MOK K0 ENT FOK A10 ARGS WX PA IA BASE INCS KONT.
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK). destruct FOK as (F1 & F2 & F3). cbn [pa_frame AD PmLayoutU.ADDR_U] in F2.
pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
unfold PMPS.ignore_args in ARGS. rewrite L5K.rl11 in ARGS.
unfold PMSP.no_W in WX. subst Wextra. rewrite app_nil_r in KONT.
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10.
unfold PMSP.o_src, PMSP.o_p, PMSP.o_is in *. cbn [pa_off_p pa_off_is AD PmLayoutU.ADDR_U] in *.
change (PMSP.pm_scr 4) with 20480 in *. unfold PM.CHUNK in *.
assert (SC0 : 0 <= 20480) by lia.
set (LB := PM.parser_own s ++ LBX) in *.
assert (BR : PMFR.brange L LB) by (apply (PMFR.brange_of_heap L HI HIok LB LB cr M _ HH); apply incl_refl).
pose proof (L5C.stk_writable RSEGS _ M sp 20480 STK) as WR.
destruct s as [mo dn dp src tb tg vb vk stk]. destruct src as [qc de rem]. destruct sm as [g eg st].
cbn [PM.p_src PM.sr_qc PM.sr_de PM.sr_rem PM.sm_g PM.sm_eg PM.sm_st] in *.
assert (QIN : In (qc, 16384) LB) by (unfold LB, PM.parser_own, PM.src_own; cbn; left; reflexivity).
assert (SINC : incl (PM.vs_own str) LB) by (unfold LB; apply incl_appr; exact INCS).
destruct (BR qc 16384 QIN) as (Q0 & Q1 & Q4). unfold hl_ceil in Q4.
pose proof PA as (_ & PDEF & _ & _ & _ & _ & _ & _ & _ & PSRC & _).
destruct PSRC as (_ & _ & S256 & S264 & S272 & S280 & S288 & G1 & G2 & G3 & _ & DCH & _).
cbn [PM.p_src PM.sr_qc PM.sr_de PM.sr_rem] in *. unfold PM.CHUNK in *.
set (s0 := PM.PST mo dn dp (PM.SRC qc de rem) tb tg vb vk stk) in *.
assert (PINC : incl (PM.parser_own s0) LB) by (unfold LB; apply incl_appl; apply incl_refl).
assert (AL36 : (fb + 40 + 24) mod 8 = 0) by (replace (fb + 40 + 24) with (fb + 8 * 8) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
assert (WF : L5.writable RSEGS M (fb + 40 + 24 + 256) 40).
{ apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M (fb + 40) 384); [exact PDEF|lia|lia]|lia|lia]. }
set (WS := PMSP.W_srcf AD fb ++ [(qc, 16384)]).
assert (WSE : PMSP.W_src AD fb (PM.SRC qc de rem) = WS) by reflexivity. rewrite WSE in KONT. clear WSE.
assert (WCs : forall a, PMK.inW WS a -> (fb + 320 <= a < fb + 360) \/ (fb + 480 <= a < fb + 488) \/ (fb + 592 <= a < fb + 596) \/ (qc <= a < qc + 16384)).
{ intros a (r0 & Hin & Hr). unfold WS, PMSP.W_srcf, PMSP.o_src, PMSP.o_p, PMSP.o_is in Hin. cbn [pa_off_p pa_off_is AD PmLayoutU.ADDR_U app] in Hin.
unfold L5.in_rng in Hr. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hr; lia. }
assert (INF : forall a, fb + 320 <= a < fb + 360 -> PMK.inW WS a).
{ intros a Ha. unfold WS, PMSP.W_srcf, PMSP.o_src, PMSP.o_p, PMSP.o_is. cbn [pa_off_p pa_off_is AD PmLayoutU.ADDR_U app]. apply PMK.inW_here. lia. }
assert (WHI0 : forall a, PMK.inW [] a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; destruct (PMFR.inW_nil a I)).
unfold PMSP.cfg. cbn [pa_ignore AD PmLayoutU.ADDR_U].
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 8))) as B8.
change (bv_modulus 64) with (2 ^ 64) in *.
assert (REMB : 0 <= rem <= 16384) by lia.
assert (DEB : qc <= de <= qc + 16384) by lia.
set (W1 := [(fb + 320, 40)] : list L5.range).
assert (WHI1 : forall a, PMK.inW W1 a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply PMFR.inW_inv1 in I; left; lia).
assert (EW1 : forall a, L5.outside WS a -> L5.outside W1 a).
{ intros a O r0 Hr0. unfold W1 in Hr0. destruct Hr0 as [<-|[]]. apply O. unfold WS, PMSP.W_srcf, PMSP.o_src, PMSP.o_p, PMSP.o_is. cbn [pa_off_p pa_off_is AD PmLayoutU.ADDR_U app].
left. apply (f_equal2 (@pair Z Z)); lia. }
assert (VIN : In (vb, 32 * 2 ^ vk) LB) by (unfold LB, PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
destruct (BR _ _ VIN) as (V0 & _ & V4). unfold hl_ceil in V4.
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 18))) as B18.
change (bv_modulus 64) with (2 ^ 64) in B9, B18.
destruct (Z_le_gt_dec 1 rem) as [REM1|REM0].
-
assert (HEAD : exists fx1 R1 M1, msteps RSEGS (@mkst fx R (Z_to_bv 64 0x37144) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 0x37230) M1 (seg_rom RSEGS))
/\ mem_grows M M1
/\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (sp - 32 <= i < sp - 32 + 32) -> ~ (fb + 40 + 24 + 256 <= i < fb + 40 + 24 + 256 + 40) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
/\ (forall x, In x [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (PMK.reg x) = getr R (PMK.reg x))
/\ L5.u64_at RSEGS M1 (fb + 40 + 24 + 288) (rem - 1) /\ L5.u64_at RSEGS M1 (fb + 40 + 24 + 280) (de + 1)
/\ L5.u64_at RSEGS M1 (fb + 40 + 24 + 264) qc /\ L5.u64_at RSEGS M1 (fb + 40 + 24 + 272) 16384).
{ destruct (Z.eq_dec rem 1) as [E1|N1].
- subst rem.
cfeed P (PMUPKP.uigA1a_conc fx R M (fun j => match j with 2%nat => sp | 34%nat => qc | 35%nat => de | 36%nat => fb + 40 + 24 | _ => 0 end)) ltac:(first [PMK.sc | unfold PMUPKP.aligned; first [exact A16 | exact AL36] ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG1 & FR1 & FRZ1 & MS1 & KS1 & X10 & _ & X12 & _ & C288 & C280 & _ & _ & _ & _ & C264 & C272)); PMK.pvz_clrT.
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [exact FRZ1|].
split. { intros x Hx. apply KS1. revert x Hx. apply (PMPK.sub_in PMUPKP.KS_uigA1a). vm_compute. reflexivity. }
split; [exact C288|]. split; [exact C280|]. split; [exact C264| exact C272].
- cfeed P (PMUPKP.uigA1b_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => rem | 34%nat => qc | 35%nat => de | 36%nat => fb + 40 + 24 | _ => 0 end)) ltac:(first [PMK.sc | unfold PMUPKP.aligned; first [exact A16 | exact AL36] ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG1 & FR1 & FRZ1 & MS1 & KS1 & X10 & _ & X12 & _ & C288 & C280 & _ & _ & _ & _ & C264 & C272)); PMK.pvz_clrT.
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [exact FRZ1|].
split. { intros x Hx. apply KS1. revert x Hx. apply (PMPK.sub_in PMUPKP.KS_uigA1b). vm_compute. reflexivity. }
split; [exact C288|]. split; [exact C280|]. split; [exact C264| exact C272]. }
destruct HEAD as (fx1 & R1 & M1 & MS1 & MG1 & FRZ1 & KS1 & C288 & C280 & C264 & C272).
set (P1 := fun a => (sp - 32 <= a < sp - 32 + 32) \/ (fb + 320 <= a < fb + 360)).
assert (FRZ1' : forall a, 0 <= a < 2 ^ 64 -> ~ P1 a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha N. apply FRZ1; [exact Ha| |]; intros X; apply N; unfold P1; [left; exact X| right; lia]. }
apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x37144 R1 0x37230 M1 P1 K HH Mh Ml ltac:(lia) MS1 MG1 FRZ1').
{ intros a Pa. apply (PMK.cwr_stack L LB M sp 20480 a STK). unfold P1 in Pa. lia. }
{ intros a. apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| |].
{ apply (PMK.ret_to RSEGS fx1 R1 M1 0x37230 (ltac:(oW' 0x37230%Z)) r (ltac:(oF' 0x37230%Z)) eq_refl (ltac:(oD' 0x37230%Z))); [rewrite (KS1 1%nat) by PMK.inl; exact Rra| lia| exact Hr2]. }
assert (EK1 : PMK.ek L LB sp 20480 W1 M M1).
{ apply (PMK.ek_piece_in RSEGS L KL LB sp 20480 W1 M M1 P1 FRZ1' STK (PMFR.brange_hi L LB BR)). intros a [Pa|Pa]; [left; lia| right; apply PMK.inW_here; lia]. }
apply (KONT fx1 R1 M1 (PM.SRC qc (de + 1) (rem - 1)) (PM.STRM g eg st)).
+ apply PMK.preserved_by_index. intros k Hk. apply KS1. revert k Hk. apply (PMPK.sub_in [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat). vm_compute. reflexivity.
+ apply (PMPK.parser_src_upd RSEGS AD M M1 (fb + 40) (fb + 440) s0 (de + 1) (rem - 1) PA); cbn [s0 PM.p_src PM.p_b PM.p_k PM.p_tb PM.sr_qc]; unfold PM.CHUNK.
* lia.
* lia.
* intros i Hi. apply FRZ1'; [lia|]. unfold P1. lia.
* intros i Hi. apply FRZ1'; [lia|]. unfold P1. lia.
* apply PMPK.dkr_grows. exact MG1.
* apply PMPK.dkr_grows. exact MG1.
* lia.
* lia.
* intros i Hi. apply FRZ1'; [lia|]. unfold P1. lia.
* intros c0 n0 p0 _. apply PMPK.dkr_grows. exact MG1.
* replace (fb + 40 + 288) with (fb + 40 + 24 + 264) by lia. exact C264.
* replace (fb + 40 + 296) with (fb + 40 + 24 + 272) by lia. exact C272.
* replace (fb + 40 + 304) with (fb + 40 + 24 + 280) by lia. exact C280.
* replace (fb + 40 + 312) with (fb + 40 + 24 + 288) by lia. exact C288.
* lia.
* lia.
* lia.
+ apply (PMFR.iss_keep RSEGS AD L KL LB sp 20480 W1 M M1 EK1 STK SC0 BR WHI1); [lia|lia| |exact SINC| exact IA].
intros i Hi I. apply PMFR.inW_inv1 in I. lia.
+ unfold PMSP.src_step, PM.unread. cbn [PM.sr_qc PM.sr_rem PM.sm_eg PM.sm_g PM.sm_st]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [intros E; exact E| lia].
+ unfold PMPS.ignore_res, PMSP.consumed, PM.unread. cbn [PM.sr_rem PM.sm_eg PM.sm_g]. split; [left; lia| intros _; lia].
+ apply (PMK.hpres_of L LB sp 20480 _ M M1).
* apply (PMK.ek_weaken L LB LB sp 20480 sp 20480 WS W1 M M1 EK1); [apply incl_refl| intros x Hx; exact Hx| exact EW1].
* apply (L5.defined_grows M M1 _ _ MG1). exact SDEF.
* apply (PMK.dk_grows L LB sp 20480 M M1 MG1).
+ exact HH1.
-
assert (rem = 0) by lia. subst rem.
cfeed P (PMUPKP.uigA0_conc fx R M (fun j => match j with 2%nat => sp | 34%nat => qc | 35%nat => de | 36%nat => fb + 40 + 24 | _ => 0 end)) ltac:(first [PMK.sc | unfold PMUPKP.aligned; first [exact A16 | exact AL36] ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG1 & FR1 & FRZ1 & MS1 & KS1 & X1 & X2 & X8 & X9 & X11 & X12 & X18 & C280 & C32 & C24 & C16 & C8 & C264 & C272 & C288 & C256)); PMK.pvz_clrT.
set (P1 := fun a => (sp - 32 <= a < sp - 32 + 32) \/ (fb + 320 <= a < fb + 360)).
assert (FRZ1' : forall a, 0 <= a < 2 ^ 64 -> ~ P1 a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha N. apply FRZ1; [exact Ha| |]; intros X; apply N; unfold P1; [left; exact X| right; lia]. }
apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x37144 R1 0x37720 M1 P1 K HH Mh Ml ltac:(lia) MS1 MG1 FRZ1').
{ intros a Pa. apply (PMK.cwr_stack L LB M sp 20480 a STK). unfold P1 in Pa. lia. }
{ intros a. apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
assert (EK1 : PMK.ek L LB sp 20480 W1 M M1).
{ apply (PMK.ek_piece_in RSEGS L KL LB sp 20480 W1 M M1 P1 FRZ1' STK (PMFR.brange_hi L LB BR)). intros a [Pa|Pa]; [left; lia| right; apply PMK.inW_here; lia]. }
assert (STK1 : L5C.stk (hl_sptop L) M1 sp 20480) by (apply (PMK.stk_grows L M M1 sp 20480 MG1 STK)).
set (s1 := PMPS.with_src s0 (PM.SRC qc qc 0)).
assert (PA1 : PM.parser_at RSEGS AD PMSP.T3 PMSP.T4 M1 (fb + 40) (fb + 440) s1).
{ apply (PMPK.parser_src_upd RSEGS AD M M1 (fb + 40) (fb + 440) s0 qc 0 PA); cbn [s0 PM.p_src PM.p_b PM.p_k PM.p_tb PM.sr_qc]; unfold PM.CHUNK.
- lia.
- lia.
- intros i Hi. apply FRZ1'; [lia|]. unfold P1. lia.
- intros i Hi. apply FRZ1'; [lia|]. unfold P1. lia.
- apply PMPK.dkr_grows. exact MG1.
- apply PMPK.dkr_grows. exact MG1.
- lia.
- lia.
- intros i Hi. apply FRZ1'; [lia|]. unfold P1. lia.
- intros c0 n0 p0 _. apply PMPK.dkr_grows. exact MG1.
- replace (fb + 40 + 288) with (fb + 40 + 24 + 264) by lia. exact C264.
- replace (fb + 40 + 296) with (fb + 40 + 24 + 272) by lia. exact C272.
- replace (fb + 40 + 304) with (fb + 40 + 24 + 280) by lia. exact C280.
- replace (fb + 40 + 312) with (fb + 40 + 24 + 288) by lia. exact C288.
- lia.
- lia.
- lia. }
assert (IA1 : PM.iss_at RSEGS AD PMSP.T3 M1 (fb + 440) str (PM.STRM g eg st)).
{ apply (PMFR.iss_keep RSEGS AD L KL LB sp 20480 W1 M M1 EK1 STK SC0 BR WHI1); [lia|lia| |exact SINC| exact IA].
intros i Hi I. apply PMFR.inW_inv1 in I. lia. }
assert (BASE1 : PMST.base_ok RSEGS AD M1).
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 20480 W1 M M1 EK1); first [exact BASE | intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply PMFR.inW_inv1 in I; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutU.ADDR_U] in Ha; lia]. }
assert (STKc : L5C.stk (hl_sptop L) M1 (sp - 32) 18432).
{ apply (PMK.stk_call L M1 sp 20480 (sp - 32) 18432 STK1); [lia|lia|lia|]. replace (sp - 32) with (sp + (-2) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
unfold PMPSU.fill_buffer_spec, PMPS.fill_buffer_spec, PMPS.src_spec in FB. cbn [pa_fill_buffer AD PmLayoutU.ADDR_U] in FB.
apply (FB fx1 R1 M1 model K LBX cr (sp - 32) 225740 fb s1 str (PM.STRM g eg st) [] HH1 MOK K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [split; [lia| reflexivity]|]. split; [exact X2|].
split; [rewrite (KS1 3%nat) by PMK.inl; exact Rgp|]. split; [rewrite (KS1 4%nat) by PMK.inl; exact Rtp|]. exact STKc. }
{ unfold PMSP.frame_ok. cbn [pa_frame AD PmLayoutU.ADDR_U]. split; [lia|]. split; [lia| exact F3]. }
{ rewrite L5K.rl10. rewrite (KS1 10%nat) by PMK.inl. unfold PMSP.o_src, PMSP.o_p. cbn [pa_off_p AD PmLayoutU.ADDR_U]. exact A10. }
{ unfold PMPS.fill_args. rewrite L5K.rl11, L5K.rl12. split; [exact X11| exact X12]. }
{ unfold PMSP.no_W. reflexivity. }
{ unfold PMSP.o_p, PMSP.o_is. cbn [pa_off_p pa_off_is AD PmLayoutU.ADDR_U]. exact PA1. }
{ unfold PMSP.o_is. cbn [pa_off_is AD PmLayoutU.ADDR_U]. exact IA1. }
{ exact BASE1. } { exact INCS. }
intros fx2 R2 M2 src2 sm2 RP2 PA2 IA2 STEP2 RES2 HP2 HH2.
unfold PMPS.fill_res in RES2. destruct RES2 as (-> & c & Y10 & CR & GG2 & _ & _).
unfold PMSP.o_p, PMSP.o_is in PA2, IA2. cbn [pa_off_p pa_off_is AD PmLayoutU.ADDR_U] in PA2, IA2.
change (PMSP.pm_scr 3) with 18432 in HP2. rewrite app_nil_r in HP2.
rewrite L5K.rl10 in Y10. unfold PM.CHUNK in CR.
destruct sm2 as [g2 eg2 st2]. cbn [PM.sm_g PM.sm_eg PM.sm_st] in GG2.
assert (EKc : PMK.ek L LB (sp - 32) 18432 WS M1 M2) by (apply (PMK.ek_of_hpres L); exact HP2).
assert (SCc : 0 <= 18432) by lia.
assert (STK2 : L5C.stk (hl_sptop L) M2 sp 20480) by (apply (PMK.stk_after RSEGS L KL LB M1 M2 sp 20480 (sp - 32) 18432 WS STK1 HP2); lia).
pose proof (L5C.stk_writable RSEGS _ M2 sp 20480 STK2) as WR2.
assert (HI2 : forall a n, sp - 32 <= a -> a + n <= fb + 320 -> L5C.agree_on M1 M2 a n).
{ intros a n H1 H2. apply (PMPK.ag_hi RSEGS L KL LB (sp - 32) 18432 WS M1 M2 EKc STKc SCc a n H1); [lia|]. intros i Hi I. apply WCs in I. lia. }
assert (EK2 : PMK.ek L LB sp 20480 WS M1 M2).
{ apply (PMK.ek_callee_in' RSEGS L KL LB LB sp 20480 (sp - 32) 18432 WS WS M1 M2 HP2 (incl_refl _)); [lia|lia|unfold hl_ceil; lia|lia| exact (PMFR.brange_hi L LB BR)|].
intros a I. right. exact I. }
assert (R2_2 : getr R2 (PMK.reg 2) = Z_to_bv 64 (sp - 32)) by (rewrite (PMK.cs_of_preserved R1 R2 2%nat RP2) by PMK.inl; exact X2).
assert (R2_8 : getr R2 (PMK.reg 8) = Z_to_bv 64 (fb + 40 + 24)) by (rewrite (PMK.cs_of_preserved R1 R2 8%nat RP2) by PMK.inl; exact X8).
assert (R2_9 : getr R2 (PMK.reg 9) = Z_to_bv 64 1) by (rewrite (PMK.cs_of_preserved R1 R2 9%nat RP2) by PMK.inl; exact X9).
assert (R2_18 : getr R2 (PMK.reg 18) = Z_to_bv 64 0) by (rewrite (PMK.cs_of_preserved R1 R2 18%nat RP2) by PMK.inl; exact X18).
pose proof PA2 as (_ & PDEF2 & _ & _ & _ & _ & _ & _ & _ & PSRC2 & _).
destruct PSRC2 as (_ & _ & T256 & T264 & T272 & T280 & T288 & _ & _ & _ & _ & DCH2 & _).
cbn [PMPS.with_src s1 s0 PM.p_src PM.sr_qc PM.sr_de PM.sr_rem] in T264, T280, T288, DCH2. unfold PM.CHUNK in *.
assert (WF2 : L5.writable RSEGS M2 (fb + 40 + 24 + 256) 40).
{ apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M2 (fb + 40) 384); [exact PDEF2|lia|lia]|lia|lia]. }
assert (C8' : L5.u64_at RSEGS M2 (sp - 8) (bv_unsigned (getr R (PMK.reg 1)))) by (apply (L5C.u64_at_agree RSEGS M1 M2); [apply HI2; lia|lia|lia| exact C8]).
assert (C16' : L5.u64_at RSEGS M2 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))) by (apply (L5C.u64_at_agree RSEGS M1 M2); [apply HI2; lia|lia|lia| exact C16]).
assert (C24' : L5.u64_at RSEGS M2 (sp - 24) (bv_unsigned (getr R (PMK.reg 9)))) by (apply (L5C.u64_at_agree RSEGS M1 M2); [apply HI2; lia|lia|lia| exact C24]).
assert (C32' : L5.u64_at RSEGS M2 (sp - 32) (bv_unsigned (getr R (PMK.reg 18)))) by (apply (L5C.u64_at_agree RSEGS M1 M2); [apply HI2; lia|lia|lia| exact C32]).
set (d := Z.min 1 c).
assert (TAIL : exists fx3 R3 M3, msteps RSEGS (@mkst fx2 R2 (Z_to_bv 64 0x371cc) M2 (seg_rom RSEGS)) (@mkst fx3 R3 (Z_to_bv 64 0x37230) M3 (seg_rom RSEGS))
/\ mem_grows M2 M3
/\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (sp - 32 <= i < sp - 32 + 32) -> ~ (fb + 40 + 24 + 256 <= i < fb + 40 + 24 + 256 + 40) -> M3 (Z_to_bv 64 i) = M2 (Z_to_bv 64 i))
/\ (forall x, In x [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (PMK.reg x) = getr R2 (PMK.reg x))
/\ getr R3 (PMK.reg 1) = getr R (PMK.reg 1) /\ getr R3 (PMK.reg 2) = Z_to_bv 64 sp
/\ getr R3 (PMK.reg 8) = getr R (PMK.reg 8) /\ getr R3 (PMK.reg 9) = getr R (PMK.reg 9) /\ getr R3 (PMK.reg 18) = getr R (PMK.reg 18)
/\ L5.u64_at RSEGS M3 (fb + 40 + 24 + 288) (c - d) /\ L5.u64_at RSEGS M3 (fb + 40 + 24 + 280) (qc + d)
/\ L5.u64_at RSEGS M3 (fb + 40 + 24 + 264) qc /\ L5.u64_at RSEGS M3 (fb + 40 + 24 + 272) 16384).
{ destruct (Z.eq_dec c 0) as [E0|N0]; [|destruct (Z.eq_dec c 1) as [E1|N1]].
- subst c. assert (d = 0) as -> by reflexivity.
cfeed P (PMUPKP.uigB0_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 34%nat => qc | 36%nat => fb + 40 + 24
| 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9))
| 43%nat => bv_unsigned (getr R (PMK.reg 18)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMUPKP.aligned; first [exact A16 | exact AL36] ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & FR3 & FRZ3 & MS3 & KS3 & T1 & T2 & T8 & T9 & T18 & D288 & D264 & D272 & D280 & _)); PMK.pvz_clrT.
rewrite PMPK.word_id in T1, T8, T9, T18.
exists fx3, R3, M3. split; [exact MS3|]. split; [exact MG3|]. split; [exact FRZ3|].
split. { intros x Hx. apply KS3. revert x Hx. apply (PMPK.sub_in PMUPKP.KS_uigB0). vm_compute. reflexivity. }
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T9|]. split; [exact T18|].
split; [rewrite Z.sub_0_r; exact D288|]. split; [rewrite Z.add_0_r; exact D280|]. split; [exact D264| exact D272].
- subst c. assert (d = 1) as -> by reflexivity.
cfeed P (PMUPKP.uigB1a_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 34%nat => qc | 36%nat => fb + 40 + 24
| 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9))
| 43%nat => bv_unsigned (getr R (PMK.reg 18)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMUPKP.aligned; first [exact A16 | exact AL36] ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & FR3 & FRZ3 & MS3 & KS3 & T1 & T2 & T8 & T9 & _ & _ & _ & _ & _ & T18 & D288 & D280 & D264 & D272 & _)); PMK.pvz_clrT.
rewrite PMPK.word_id in T1, T8, T9, T18.
exists fx3, R3, M3. split; [exact MS3|]. split; [exact MG3|]. split; [exact FRZ3|].
split. { intros x Hx. apply KS3. revert x Hx. apply (PMPK.sub_in PMUPKP.KS_uigB1a). vm_compute. reflexivity. }
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T9|]. split; [exact T18|].
split; [exact D288|]. split; [exact D280|]. split; [exact D264| exact D272].
- assert (d = 1) as -> by (unfold d; lia).
cfeed P (PMUPKP.uigB1b_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => c | 34%nat => qc | 36%nat => fb + 40 + 24
| 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9))
| 43%nat => bv_unsigned (getr R (PMK.reg 18)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMUPKP.aligned; first [exact A16 | exact AL36] ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & FR3 & FRZ3 & MS3 & KS3 & T1 & T2 & T8 & T9 & _ & _ & _ & _ & _ & T18 & D288 & D280 & D264 & D272 & _)); PMK.pvz_clrT.
rewrite PMPK.word_id in T1, T8, T9, T18.
exists fx3, R3, M3. split; [exact MS3|]. split; [exact MG3|]. split; [exact FRZ3|].
split. { intros x Hx. apply KS3. revert x Hx. apply (PMPK.sub_in PMUPKP.KS_uigB1b). vm_compute. reflexivity. }
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T9|]. split; [exact T18|].
split; [exact D288|]. split; [exact D280|]. split; [exact D264| exact D272]. }
destruct TAIL as (fx3 & R3 & M3 & MS3 & MG3 & FRZ3 & KS3 & T1 & T2 & T8 & T9 & T18 & D288 & D280 & D264 & D272).
assert (DR : 0 <= d <= 1 /\ (1 <= c -> d = 1) /\ (c = 0 -> d = 0)) by (unfold d; lia).
set (P3 := fun a => (sp - 32 <= a < sp - 32 + 32) \/ (fb + 320 <= a < fb + 360)).
assert (FRZ3' : forall a, 0 <= a < 2 ^ 64 -> ~ P3 a -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
{ intros a Ha N. apply FRZ3; [exact Ha| |]; intros X; apply N; unfold P3; [left; exact X| right; lia]. }
apply (PMK.spiece RSEGS L HI KL HIok LB cr M2 model fx2 fx3 R2 0x371cc R3 0x37230 M3 P3 K HH2 Mh Ml ltac:(lia) MS3 MG3 FRZ3').
{ intros a Pa. apply (PMK.cwr_stack L LB M sp 20480 a STK). unfold P3 in Pa. lia. }
{ intros a. apply PMK.or_dec; apply PMK.rng_dec. }
intros HH3.
eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| |].
{ apply (PMK.ret_to RSEGS fx3 R3 M3 0x37230 (ltac:(oW' 0x37230%Z)) r (ltac:(oF' 0x37230%Z)) eq_refl (ltac:(oD' 0x37230%Z))); [rewrite T1; exact Rra| lia| exact Hr2]. }
assert (EK3 : PMK.ek L LB sp 20480 W1 M2 M3).
{ apply (PMK.ek_piece_in RSEGS L KL LB sp 20480 W1 M2 M3 P3 FRZ3' STK2 (PMFR.brange_hi L LB BR)). intros a [Pa|Pa]; [left; lia| right; apply PMK.inW_here; lia]. }
apply (KONT fx3 R3 M3 (PM.SRC qc (qc + d) (c - d)) (PM.STRM g2 eg2 st2)).
+ apply PMK.preserved_by_index. intros k Hk. cbn in Hk.
repeat (destruct Hk as [<-|Hk]; [first [ rewrite T2; symmetry; exact Rsp | exact T8 | exact T9 | exact T18
| (rewrite (KS3 _) by PMK.inl; rewrite (PMK.cs_of_preserved R1 R2 _ RP2) by PMK.inl; apply KS1; PMK.inl) ] |]). destruct Hk.
+ apply (PMPK.parser_src_upd RSEGS AD M2 M3 (fb + 40) (fb + 440) s1 (qc + d) (c - d) PA2); cbn [s1 s0 PMPS.with_src PM.p_src PM.p_b PM.p_k PM.p_tb PM.sr_qc]; unfold PM.CHUNK.
* lia.
* lia.
* intros i Hi. apply FRZ3'; [lia|]. unfold P3. lia.
* intros i Hi. apply FRZ3'; [lia|]. unfold P3. lia.
* apply PMPK.dkr_grows. exact MG3.
* apply PMPK.dkr_grows. exact MG3.
* lia.
* lia.
* intros i Hi. apply FRZ3'; [lia|]. unfold P3. lia.
* intros c0 n0 p0 _. apply PMPK.dkr_grows. exact MG3.
* replace (fb + 40 + 288) with (fb + 40 + 24 + 264) by lia. exact D264.
* replace (fb + 40 + 296) with (fb + 40 + 24 + 272) by lia. exact D272.
* replace (fb + 40 + 304) with (fb + 40 + 24 + 280) by lia. exact D280.
* replace (fb + 40 + 312) with (fb + 40 + 24 + 288) by lia. exact D288.
* lia.
* lia.
* lia.
+ apply (PMFR.iss_keep RSEGS AD L KL LB sp 20480 W1 M2 M3 EK3 STK2 SC0 BR WHI1); [lia|lia| |exact SINC| exact IA2].
intros i Hi I. apply PMFR.inW_inv1 in I. lia.
+ unfold PMSP.src_step, PM.unread in STEP2 |- *. cbn [s1 s0 PMPS.with_src PM.p_src PM.sr_qc PM.sr_rem PM.sm_eg PM.sm_g PM.sm_st] in STEP2 |- *.
destruct STEP2 as (_ & E2 & L2 & S2 & _). split; [reflexivity|]. split; [exact E2|]. split; [exact L2|]. split; [exact S2| lia].
+ unfold PMPS.ignore_res, PMSP.consumed, PM.unread. cbn [PM.sr_rem PM.sm_eg PM.sm_g].
unfold PMSP.src_step in STEP2. cbn [PM.sm_eg] in STEP2. destruct STEP2 as (_ & E2 & _).
split; [|intros X; lia]. destruct (Z.eq_dec d 1); [left; lia| right; lia].
+ apply (PMK.hpres_of L LB sp 20480 _ M M3).
* apply (PMK.ek_trans L LB sp 20480 WS M M1 M3).
{ apply (PMK.ek_weaken L LB LB sp 20480 sp 20480 WS W1 M M1 EK1); [apply incl_refl| intros x Hx; exact Hx| exact EW1]. }
apply (PMK.ek_trans L LB sp 20480 WS M1 M2 M3 EK2).
apply (PMK.ek_weaken L LB LB sp 20480 sp 20480 WS W1 M2 M3 EK3); [apply incl_refl| intros x Hx; exact Hx| exact EW1].
* destruct STK2 as (_ & _ & _ & _ & D2). apply (L5.defined_grows M2 M3 _ _ MG3). exact D2.
* apply (PMK.dk_trans L LB sp 20480 M M1 M3); [apply (PMK.dk_grows L LB sp 20480 M M1 MG1)|].
apply (PMK.dk_trans L LB sp 20480 M1 M2 M3); [|apply (PMK.dk_grows L LB sp 20480 M2 M3 MG3)].
apply (PMK.dk_callee L LB LB sp 20480 (sp - 32) 18432 WS M1 M2 HP2 (incl_refl _)); lia.
+ exact HH3.
Qed.
End WithHeap.
End PMUIG.
