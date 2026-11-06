(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit PmLayout PmLayoutS PmModel PmModelFacts PmStatics PmSpecs PmSpecsS PmStep PmKeep PmKitS PmFrame PmParSpecs PmParSpecsS PmParKit PmTxtSpecs PmSrcSFillP.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Plain.
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc. Local Ltac lia := L5FastLia.plia.
Module PMSFBT.
Import PMS.
Ltac tr64 M0 AG := lazymatch goal with |- L5.u64_at ?sg ?M2 ?a ?v =>
let X := fresh "X" in assert (X : L5.u64_at sg M0 a v) by PMK.gmem;
apply (L5C.u64_at_agree sg M0 M2 a v); [apply AG; lia | lia | lia | exact X] end.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.
Theorem fill_buffer_tb_ok : PMPSS.xsgetn_spec L HI -> PMTXS.fill_buffer_tb_spec RSEGS AD L HI.
Proof.
intros XS. unfold PMTXS.fill_buffer_tb_spec, PMPS.src_spec.
intros fx R M model K LBX cr sp r fb s str sm Wextra HH MOK K0 ENT FOK A10 ARGS WX PA IA BASE INCS KONT.
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK). destruct FOK as (F1 & F2 & F3). cbn [pa_frame AD PmLayoutS.ADDR_S] in F2.
pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
destruct ARGS as (p & A11 & A12 & c0 & n0 & q0 & ETB & Dq1 & Dq2). destruct WX as (p' & A11' & Hp' & ->).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11, A11'. rewrite L5K.rl12 in A12.
unfold PMSP.o_src, PMSP.o_p, PMSP.o_is in *. cbn [pa_off_p pa_off_is AD PmLayoutS.ADDR_S] in *.
change (PMSP.pm_scr 3) with 18432 in *. unfold PM.CHUNK in *.
assert (SC0 : 0 <= 18432) by lia.
set (LB := PM.parser_own s ++ LBX) in *.
assert (BR : PMFR.brange L LB) by (apply (PMFR.brange_of_heap L HI HIok LB LB cr M _ HH); apply incl_refl).
pose proof (L5C.stk_writable RSEGS _ M sp 18432 STK) as WR.
pose proof BASE as (IMG & _). cbn [pa_rw_lo AD PmLayoutS.ADDR_S] in IMG.
destruct s as [mo dn dp src tb tg vb vk stk]. destruct src as [qc de rem]. destruct sm as [g eg st].
cbn [PM.p_src PM.p_tb PM.sr_qc PM.sm_g PM.sm_eg PM.sm_st] in *. subst tb.
assert (QIN : In (qc, 16384) LB) by (unfold LB, PM.parser_own, PM.src_own; cbn; left; reflexivity).
assert (SINC : incl (PM.vs_own str) LB) by (unfold LB; apply incl_appr; exact INCS).
assert (PINC : incl (PM.parser_own (PM.PST mo dn dp (PM.SRC qc de rem) (PM.VLong c0 n0 q0) tg vb vk stk)) LB) by (unfold LB; apply incl_appl; apply incl_refl).
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PSRC & _).
destruct PSRC as (S240 & S248 & _).
pose proof IA as (I0 & IDEF & _ & I16 & _ & _ & I40 & _ & _ & _ & _ & _ & IIOS & _ & IE2).
destruct IIOS as (_ & J32 & J36 & J40 & _ & _ & _ & _ & ST).
cbn [PM.sm_g PM.sm_eg PM.sm_st pa_vp_iss pa_vp_strbuf AD PmLayoutS.ADDR_S] in *.
assert (AL36 : (fb + 40 + 24) mod 8 = 0) by (replace (fb + 40 + 24) with (fb + 8 * 8) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
assert (AL37 : (fb + 440) mod 8 = 0) by (replace (fb + 440) with (fb + 8 * 55) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
assert (WHI0 : forall a, PMK.inW [] a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; destruct (PMFR.inW_nil a I)).
assert (TIN : In (q0, c0) LB) by (unfold LB, PM.parser_own, PM.vs_own; cbn; right; right; left; reflexivity).
destruct (BR q0 c0 TIN) as (T0 & T1' & T4'). unfold hl_ceil in T4'.
assert (Ep : p' = p).
{ rewrite A11 in A11'. apply (f_equal bv_unsigned) in A11'. rewrite !L5.unsigned_lit in A11' by (unfold PM.CHUNK in *; lia). lia. }
subst p'. clear A11'.
set (WS := (PMSP.W_srcf AD fb ++ [(qc, 16384)]) ++ [(p, 16384)]).
assert (WSE : PMSP.W_src AD fb (PM.SRC qc de rem) ++ [(p, 16384)] = WS) by reflexivity. rewrite WSE in KONT. clear WSE.
unfold PMSP.cfg. cbn [pa_fill_buffer AD PmLayoutS.ADDR_S].
destruct ST as [ST0|ST2].
2:{
subst st.
cfeed P (PMSFBP.fbE_conc fx R M (fun j => match j with 2%nat => sp | 36%nat => fb + 40 + 24 | 37%nat => fb + 440 | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSFBP.aligned; first [exact A16 | exact AL36 | exact AL37]]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ & MS & KS & X10 & _)); PMK.pvz_clrT.
set (P := fun a => sp - 32 <= a < sp - 32 + 32).
assert (PF : forall a, P a -> sp - 18432 <= a < sp) by (intros a X; unfold P in X; lia).
apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x36a08 R1 0x36ad4 M1 P K HH Mh Ml ltac:(lia) MS MG FRZ).
{ intros a Pa. apply (PMK.cwr_stack L LB M sp 18432 a STK). apply PF in Pa. lia. }
{ intros a. apply PMK.rng_dec. }
intros HH1.
assert (EK1 : PMK.ek L LB sp 18432 [] M M1) by (apply (PMFR.ek_of_piece RSEGS L KL LB sp 18432 M M1 P FRZ STK (PMFR.brange_hi L LB BR) PF)).
eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| |].
{ apply (PMK.ret_to RSEGS fx1 R1 M1 0x36ad4 (ltac:(oW' 0x36ad4%Z)) r (ltac:(oF' 0x36ad4%Z)) eq_refl (ltac:(oD' 0x36ad4%Z))); [rewrite (KS 1%nat) by PMK.inl; exact Rra| lia| exact Hr2]. }
apply (KONT fx1 R1 M1 (PM.SRC qc de rem) (PM.STRM g eg 2)).
+ apply PMK.preserved_by_index. intros k Hk. apply KS. revert k Hk. apply (PMPK.cs_in PMSFBP.KS_fbE). vm_compute. reflexivity.
+ unfold PMPS.with_src. cbn [PM.p_more PM.p_done PM.p_depth PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk].
apply (PMFR.parser_keep RSEGS AD L KL LB sp 18432 [] M M1 EK1 STK SC0 BR WHI0); [lia|lia| intros i _; apply PMFR.inW_nil| exact PINC| exact PA].
+ apply (PMFR.iss_keep RSEGS AD L KL LB sp 18432 [] M M1 EK1 STK SC0 BR WHI0); [lia|lia| intros i _; apply PMFR.inW_nil| exact SINC| exact IA].
+ unfold PMSP.src_step, PM.unread. cbn [PM.sr_qc PM.sr_rem PM.sm_eg PM.sm_g PM.sm_st]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [intros E; exact E| lia].
+ split.
{ unfold PMPS.fill_res, PM.CHUNK. split; [reflexivity|]. exists 0. cbn [PM.sm_g PM.sm_st]. rewrite L5K.rl10.
split; [exact X10|]. split; [lia|]. split; [lia|]. split; [intros E; discriminate E| intros _; split; reflexivity]. }
exists p, 0. rewrite L5K.rl11, L5K.rl10. split; [exact A11|]. split; [exact X10|]. intros i Hi. lia.
+ apply (PMK.hpres_of L LB sp 18432 _ M M1).
* apply (PMK.ek_weaken L LB LB sp 18432 sp 18432 _ [] M M1 EK1); [apply incl_refl| intros x Hx; exact Hx|]. intros a _. apply L5C.outside_nil.
* apply (L5.defined_grows M M1 _ _ MG). exact SDEF.
* apply (PMK.dk_grows L LB sp 18432 M M1 MG).
+ exact HH1. }
subst st.
assert (TOP47 : hl_sptop L <= 2 ^ 47) by lia.
destruct (BR qc 16384 QIN) as (Q0 & Q1 & Q4). unfold hl_ceil in Q4. rewrite (ly_img_lo L LY), (ly_img_hi L LY) in Q1.
set (Wx := [(fb + 440 + 40, 8); (p, 16384)] : list L5.range).
assert (WCx : forall a, PMK.inW Wx a -> (fb + 480 <= a < fb + 488) \/ (p <= a < p + 16384)).
{ intros a (r0 & Hin & Hr). unfold Wx in Hin. unfold L5.in_rng in Hr. destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; lia. }
assert (WCs : forall a, PMK.inW WS a -> (fb + 320 <= a < fb + 360) \/ (fb + 480 <= a < fb + 488) \/ (fb + 592 <= a < fb + 596) \/ (qc <= a < qc + 16384)
\/ (p <= a < p + 16384)).
{ intros a (r0 & Hin & Hr). unfold WS, PMSP.W_srcf, PMSP.o_src, PMSP.o_p, PMSP.o_is in Hin. cbn [pa_off_p pa_off_is AD PmLayoutS.ADDR_S app] in Hin.
unfold L5.in_rng in Hr. destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hr; lia. }
cfeed P (PMSFBP.fbA_conc fx R M (fun j => match j with 2%nat => sp | 36%nat => fb + 40 + 24 | 37%nat => fb + 440 | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSFBP.aligned; first [exact A16 | exact AL36 | exact AL37]]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG1 & FR1 & FRZ1 & MS1 & KS1 & X1 & X2 & X8 & X10 & X13 & X18 & C32 & C24 & C16 & C8)); PMK.pvz_clrT.
set (P1 := fun a => sp - 32 <= a < sp - 32 + 32).
assert (PF1 : forall a, P1 a -> sp - 18432 <= a < sp) by (intros a X; unfold P1 in X; lia).
apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x36a08 R1 0x5b254 M1 P1 K HH Mh Ml ltac:(lia) MS1 MG1 FRZ1).
{ intros a Pa. apply (PMK.cwr_stack L LB M sp 18432 a STK). apply PF1 in Pa. lia. }
{ intros a. apply PMK.rng_dec. }
intros HH1.
assert (STK1 : L5C.stk (hl_sptop L) M1 sp 18432) by (apply (PMK.stk_grows L M M1 sp 18432 MG1 STK)).
assert (EK1 : PMK.ek L LB sp 18432 [] M M1) by (apply (PMFR.ek_of_piece RSEGS L KL LB sp 18432 M M1 P1 FRZ1 STK (PMFR.brange_hi L LB BR) PF1)).
assert (IA1 : PM.iss_at RSEGS AD PMSP.T3 M1 (fb + 440) str (PM.STRM g eg 0)).
{ apply (PMFR.iss_keep RSEGS AD L KL LB sp 18432 [] M M1 EK1 STK SC0 BR WHI0); [lia|lia| intros i _; apply PMFR.inW_nil| exact SINC| exact IA]. }
assert (BASE1 : PMST.base_ok RSEGS AD M1).
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 18432 [] M M1 EK1); first [exact BASE | intros a _; apply L5C.outside_nil]. }
assert (STKc : L5C.stk (hl_sptop L) M1 (sp - 32) 16384).
{ apply (PMK.stk_call L M1 sp 18432 (sp - 32) 16384 STK1); [lia|lia|lia|]. replace (sp - 32) with (sp + (-2) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
assert (APART : p + 16384 <= g \/ eg <= p).
{ pose proof (PMPK.iss_unread_where RSEGS AD M (fb + 440) str _ IA) as [(Y1 & Y2)|(c1 & n1 & p1 & -> & Y1 & Y2)]; cbn [PM.sm_g PM.sm_eg] in *; [left; lia|].
assert (PIN : In (p1, c1) LBX) by (apply INCS; left; reflexivity).
assert (NEQ : q0 <> p1).
{ apply (PMPK.fst_neq_app (PM.parser_own (PM.PST mo dn dp (PM.SRC qc de rem) (PM.VLong c0 n0 q0) tg vb vk stk)) LBX q0 c0 p1 c1); [| |exact PIN].
- exact (PMPK.heap_nodup L HI HIok LB cr M _ HH).
- unfold PM.parser_own, PM.vs_own; cbn; right; right; left; reflexivity. }
destruct (PMPK.blocks_apart_heap L HI HIok LB cr M _ q0 c0 p1 c1 HH TIN (SINC _ (or_introl eq_refl)) NEQ) as [Z1|Z1]; lia. }
unfold PMPSS.xsgetn_spec, PMPS.xsgetn_spec in XS. cbn [pa_xsgetn AD PmLayoutS.ADDR_S] in XS.
apply (XS fx1 R1 M1 model K LB cr (sp - 32) 223828 (fb + 440) p str (PM.STRM g eg 0) HH1 MOK K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [split; [lia| reflexivity]|]. split; [exact X2|].
split; [rewrite (KS1 3%nat) by PMK.inl; exact Rgp|]. split; [rewrite (KS1 4%nat) by PMK.inl; exact Rtp|]. exact STKc. }
{ rewrite L5K.rl10. exact X10. }
{ rewrite L5K.rl11. rewrite (KS1 11%nat) by PMK.inl. exact A11. }
{ rewrite L5K.rl12. rewrite (KS1 12%nat) by PMK.inl. exact A12. }
{ lia. } { lia. } { exact AL37. } { exact IA1. } { exact BASE1. } { exact SINC. }
{ exists q0, c0. split; [exact TIN| unfold PM.CHUNK; lia]. }
{ unfold PM.CHUNK. cbn [PM.sm_g PM.sm_eg]. exact APART. }
cbn [PM.sm_g PM.sm_eg PM.sm_st]. unfold PM.CHUNK. fold Wx.
intros fx2 R2 M2 c RP2 Y10 CEQ IA2 DD2 HP2 HH2.
rewrite L5K.rl10 in Y10.
pose proof (PMPK.iss_size_lt RSEGS AD M (fb + 440) str _ IA) as SZ. cbn [PM.sm_g PM.sm_eg] in SZ.
assert (CR : 0 <= c <= 16384) by (clear - CEQ SZ; Lia.lia).
assert (EKc : PMK.ek L LB (sp - 32) 16384 Wx M1 M2) by (apply (PMK.ek_of_hpres L); exact HP2).
assert (SCc : 0 <= 16384) by lia.
assert (STK2 : L5C.stk (hl_sptop L) M2 sp 18432) by (apply (PMK.stk_after RSEGS L KL LB M1 M2 sp 18432 (sp - 32) 16384 Wx STK1 HP2); lia).
pose proof (L5C.stk_writable RSEGS _ M2 sp 18432 STK2) as WR2.
assert (HI2 : forall a n, sp - 32 <= a -> a + n <= 2 ^ 64 -> (a + n <= fb + 480 \/ fb + 488 <= a) -> L5C.agree_on M1 M2 a n).
{ intros a n H1 H2 H3. apply (PMPK.ag_hi RSEGS L KL LB (sp - 32) 16384 Wx M1 M2 EKc STKc SCc a n H1 H2). intros i Hi I. apply WCx in I. destruct I as [I|I]; lia. }
assert (HI1 : forall a n, sp <= a -> a + n <= 2 ^ 64 -> L5C.agree_on M M1 a n).
{ intros a n H1 H2 i Hi. apply FRZ1; unfold P1; lia. }
assert (HI02 : forall a n, sp <= a -> a + n <= 2 ^ 64 -> (a + n <= fb + 480 \/ fb + 488 <= a) -> L5C.agree_on M M2 a n).
{ intros a n H1 H2 H3. apply (L5C.agree_on_trans M M1 M2); [apply HI1; lia| apply HI2; lia]. }
assert (BASE2 : PMST.base_ok RSEGS AD M2).
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LB (sp - 32) 16384 Wx M1 M2 EKc); first [exact BASE1 | intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply WCx in I; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutS.ADDR_S] in Ha; rewrite (ly_img_lo L LY), (ly_img_hi L LY) in T1'; destruct I as [I|I]; lia]. }
pose proof BASE2 as (IMG2 & _). cbn [pa_rw_lo AD PmLayoutS.ADDR_S] in IMG2.
pose proof IA2 as (K0' & KDEF & _ & K16 & _ & _ & K40 & _ & _ & _ & _ & _ & KIOS & _ & KE2).
destruct KIOS as (_ & L32 & L36 & L40 & _ & _ & LD & _ & _).
cbn [PM.sm_g PM.sm_eg PM.sm_st pa_vp_iss pa_vp_strbuf AD PmLayoutS.ADDR_S] in *.
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 8))) as B8.
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 18))) as B18.
change (bv_modulus 64) with (2 ^ 64) in *.
assert (R2_2 : getr R2 (PMK.reg 2) = Z_to_bv 64 (sp - 32)) by (rewrite (PMK.cs_of_preserved R1 R2 2%nat RP2) by PMK.inl; exact X2).
assert (R2_8 : getr R2 (PMK.reg 8) = Z_to_bv 64 (fb + 40 + 24)) by (rewrite (PMK.cs_of_preserved R1 R2 8%nat RP2) by PMK.inl; exact X8).
assert (R2_18 : getr R2 (PMK.reg 18) = Z_to_bv 64 16384) by (rewrite (PMK.cs_of_preserved R1 R2 18%nat RP2) by PMK.inl; rewrite X18; exact A12).
set (st' := if Z.ltb c 16384 then 2 else 0).
assert (TAIL : exists fx3 R3 M3, msteps RSEGS (@mkst fx2 R2 (Z_to_bv 64 0x36a54) M2 (seg_rom RSEGS)) (@mkst fx3 R3 (Z_to_bv 64 0x36ad4) M3 (seg_rom RSEGS))
/\ mem_grows M2 M3
/\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (sp - 32 <= i < sp - 32 + 32) -> ~ (fb + 440 + 152 <= i < fb + 440 + 152 + 4) -> M3 (Z_to_bv 64 i) = M2 (Z_to_bv 64 i))
/\ (forall x, In x [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (PMK.reg x) = getr R2 (PMK.reg x))
/\ getr R3 (PMK.reg 1) = getr R (PMK.reg 1) /\ getr R3 (PMK.reg 2) = Z_to_bv 64 sp
/\ getr R3 (PMK.reg 8) = getr R (PMK.reg 8) /\ getr R3 (PMK.reg 9) = getr R (PMK.reg 9) /\ getr R3 (PMK.reg 18) = getr R (PMK.reg 18)
/\ getr R3 (PMK.reg 10) = Z_to_bv 64 c /\ L5.u32_at RSEGS M3 (fb + 440 + 152) st').
{ destruct (Z.eq_dec c 16384) as [E16|N16].
- assert (st' = 0) as -> by (unfold st'; rewrite E16; reflexivity).
pose proof (PMSFBP.fbB1_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 36%nat => fb + 40 + 24 | 37%nat => fb + 440
| 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9))
| 43%nat => bv_unsigned (getr R (PMK.reg 18)) | _ => 0 end)) as P. cbn beta iota in P.
rewrite E16 in Y10.
PMK.feed P ltac:(first [PMK.sc | unfold PMSFBP.aligned; first [exact A16 | exact AL36 | exact AL37] | tr64 M HI02 | tr64 M1 HI2]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ & MS & KS & T1 & T2 & T8 & T9 & T18 & _)); PMK.pvz_clrT.
rewrite PMPK.word_id in T1, T8, T9, T18.
exists fx3, R3, M3. split; [exact MS|]. split; [exact MG|]. split; [intros i Hi N1 _; apply FRZ; assumption|].
split. { intros x Hx. apply KS. revert x Hx. apply (PMPK.sub_in PMSFBP.KS_fbB1). vm_compute. reflexivity. }
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T9|]. split; [exact T18|].
split. { rewrite (KS 10%nat) by PMK.inl. rewrite E16. exact Y10. }
apply (PMF.u32_at_agree RSEGS M2 M3); [|lia|lia|replace (fb + 440 + 152) with (fb + 440 + 120 + 32) by lia; exact L32]. intros i Hi. apply FRZ; lia.
- assert (st' = 2) as -> by (unfold st'; destruct (Z.ltb_spec c 16384); [reflexivity| lia]).
cfeed P (PMSFBP.fbB2_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 35%nat => c | 36%nat => fb + 40 + 24 | 37%nat => fb + 440
| 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9))
| 43%nat => bv_unsigned (getr R (PMK.reg 18)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSFBP.aligned; first [exact A16 | exact AL36 | exact AL37] | tr64 M HI02 | tr64 M1 HI2
| apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M2 (fb + 440 + 120) 152); [exact LD|lia|lia]|lia|lia] ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ & MS & KS & T1 & T2 & T8 & T9 & T11 & T12 & T13 & T18 & CST & _)); PMK.pvz_clrT.
rewrite PMPK.word_id in T1, T8, T9, T18.
exists fx3, R3, M3. split; [exact MS|]. split; [exact MG|]. split; [exact FRZ|].
split. { intros x Hx. apply KS. revert x Hx. apply (PMPK.sub_in PMSFBP.KS_fbB2). vm_compute. reflexivity. }
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T9|]. split; [exact T18|].
split. { rewrite (KS 10%nat) by PMK.inl. exact Y10. }
exact CST. }
destruct TAIL as (fx3 & R3 & M3 & MS3 & MG3 & FRZ3 & KS3 & T1 & T2 & T8 & T9 & T18 & T10 & CST).
set (P3 := fun a => (sp - 32 <= a < sp - 32 + 32) \/ (fb + 440 + 152 <= a < fb + 440 + 152 + 4)).
assert (FRZ3' : forall a, 0 <= a < 2 ^ 64 -> ~ P3 a -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
{ intros a Ha N. apply FRZ3; [exact Ha| |]; intros X; apply N; [left|right]; exact X. }
apply (PMK.spiece RSEGS L HI KL HIok LB cr M2 model fx2 fx3 R2 0x36a54 R3 0x36ad4 M3 P3 K HH2 Mh Ml ltac:(lia) MS3 MG3 FRZ3').
{ intros a Pa. apply (PMK.cwr_stack L LB M sp 18432 a STK). unfold P3 in Pa. lia. }
{ intros a. apply PMK.or_dec; apply PMK.rng_dec. }
intros HH3.
eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| |].
{ apply (PMK.ret_to RSEGS fx3 R3 M3 0x36ad4 (ltac:(oW' 0x36ad4%Z)) r (ltac:(oF' 0x36ad4%Z)) eq_refl (ltac:(oD' 0x36ad4%Z))); [rewrite T1; exact Rra| lia| exact Hr2]. }
assert (EK1w : PMK.ek L LB sp 18432 WS M M1).
{ apply (PMK.ek_weaken L LB LB sp 18432 sp 18432 WS [] M M1 EK1); [apply incl_refl| intros x Hx; exact Hx|]. intros a _. apply L5C.outside_nil. }
assert (EK2w : PMK.ek L LB sp 18432 WS M1 M2).
{ apply (PMK.ek_callee_in' RSEGS L KL LB LB sp 18432 (sp - 32) 16384 WS Wx M1 M2 HP2 (incl_refl _)); [lia|lia|unfold hl_ceil; lia|lia| exact (PMFR.brange_hi L LB BR)|].
intros a I. right. apply WCx in I. unfold WS, PMSP.W_srcf, PMSP.o_src, PMSP.o_p, PMSP.o_is. cbn [pa_off_p pa_off_is AD PmLayoutS.ADDR_S app].
destruct I as [I|I]; [apply PMK.inW_next; apply PMK.inW_here; lia| do 4 apply PMK.inW_next; apply PMK.inW_here; lia]. }
assert (EK3w : PMK.ek L LB sp 18432 WS M2 M3).
{ apply (PMK.ek_piece_in RSEGS L KL LB sp 18432 WS M2 M3 P3 FRZ3' STK2 (PMFR.brange_hi L LB BR)). intros a [Pa|Pa]; [left; lia|]. right.
unfold WS, PMSP.W_srcf, PMSP.o_src, PMSP.o_p, PMSP.o_is. cbn [pa_off_p pa_off_is AD PmLayoutS.ADDR_S app]. do 2 apply PMK.inW_next. apply PMK.inW_here. lia. }
assert (AGP : L5C.agree_on M M3 (fb + 40) 384).
{ apply (L5C.agree_on_trans M M2 M3); [apply HI02; lia|]. intros i Hi. apply FRZ3; lia. }
assert (HI23 : forall a n, sp <= a -> a + n <= 2 ^ 64 -> (a + n <= fb + 592 \/ fb + 596 <= a) -> L5C.agree_on M2 M3 a n).
{ intros a n H1 H2 H3 i Hi. apply FRZ3; lia. }
assert (OTH : forall B m, In (B, m) LB -> B <> q0 -> L5C.agree_on M M3 B m).
{ intros B m Hin NEB. destruct (BR B m Hin) as (Z0 & Z1 & Z4). unfold hl_ceil in Z4.
destruct (PMPK.blocks_apart_heap L HI HIok LB cr M _ B m q0 c0 HH Hin TIN NEB) as [AP|AP].
all: apply (L5C.agree_on_trans M M1 M3); [intros i Hi; apply FRZ1; unfold P1; lia|].
all: apply (L5C.agree_on_trans M1 M2 M3); [|intros i Hi; apply FRZ3; lia].
all: apply (PMPK.ag_blk RSEGS L KL LB (sp - 32) 16384 Wx M1 M2 EKc STKc BR B m Hin); intros i Hi I; apply WCx in I; lia. }
assert (NDL : NoDup (map fst LB)) by exact (PMPK.heap_nodup L HI HIok LB cr M _ HH).
assert (DKT : PMPK.dkr M M3 q0 c0).
{ apply (PMPK.dkr_trans M M1 M3); [apply PMPK.dkr_grows; exact MG1|]. apply (PMPK.dkr_trans M1 M2 M3); [|apply PMPK.dkr_grows; exact MG3].
apply (PMPK.dkr_hpres_blk RSEGS L KL LB (sp - 32) 16384 Wx M1 M2 q0 c0 HP2 TIN BR TOP47). }
assert (DKQ : PMPK.dkr M M3 qc 16384).
{ apply PMPK.dkr_agree. apply (OTH _ _ QIN). intros E.
apply (PMPK.fst_neq_app [(qc, 16384)] (PM.vec_own vb vk ++ PM.vs_own (PM.VLong c0 n0 q0) ++ LBX) qc 16384 q0 c0); [exact NDL| left; reflexivity| right; left; reflexivity| exact E]. }
apply (KONT fx3 R3 M3 (PM.SRC qc de rem) (PM.STRM (g + c) eg st')).
+ apply PMK.preserved_by_index. intros k Hk. cbn in Hk.
repeat (destruct Hk as [<-|Hk]; [first [ rewrite T2; symmetry; exact Rsp | assumption
| (rewrite (KS3 _) by PMK.inl; rewrite (PMK.cs_of_preserved R1 R2 _ RP2) by PMK.inl; apply KS1; PMK.inl) ] |]). destruct Hk.
+ unfold PMPS.with_src. cbn [PM.p_more PM.p_done PM.p_depth PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk].
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC & _). destruct PVEC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _).
apply (PMPK.parser_at_keep RSEGS AD M M3 (fb + 40) (fb + 440) _ PA); cbn [PM.p_src PM.p_b PM.p_k PM.p_tb PM.sr_qc]; unfold PM.CHUNK.
* lia.
* lia.
* exact AGP.
* exact DKQ.
* assert (VIN : In (vb, 32 * 2 ^ vk) LB) by (unfold LB, PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
destruct (BR _ _ VIN) as (Z0 & _). lia.
* assert (VIN : In (vb, 32 * 2 ^ vk) LB) by (unfold LB, PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
destruct (BR _ _ VIN) as (_ & _ & Z4). unfold hl_ceil in Z4. lia.
* assert (VIN : In (vb, 32 * 2 ^ vk) LB) by (unfold LB, PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
apply (OTH _ _ VIN). intros E.
apply (PMPK.fst_neq_app ([(qc, 16384)] ++ PM.vec_own vb vk) (PM.vs_own (PM.VLong c0 n0 q0) ++ LBX) vb (32 * 2 ^ vk) q0 c0);
[rewrite <- app_assoc; exact NDL| right; left; reflexivity| left; reflexivity| exact E].
* intros c1 n1 p1 E1. injection E1 as <- <- <-. exact DKT.
+ apply (PMPK.iss_upd RSEGS AD M2 M3 (fb + 440) str (PM.STRM (g + c) eg 0) (g + c) st' IA2); cbn [PM.sm_g PM.sm_eg PM.sm_st].
* lia.
* lia.
* apply HI23; lia.
* apply HI23; lia.
* apply HI23; lia.
* apply PMPK.dkr_grows. exact MG3.
* apply PMPK.dkr_grows. exact MG3.
* intros c1 n1 p1 _. apply PMPK.dkr_grows. exact MG3.
* apply (L5C.u64_at_agree RSEGS M2 M3); [apply HI23; lia|lia|lia| exact K40].
* exact CST.
* exact KE2.
* unfold st'. destruct (Z.ltb c 16384); [right|left]; reflexivity.
+ unfold PMSP.src_step, PM.unread. cbn [PM.sr_qc PM.sr_rem PM.sm_eg PM.sm_g PM.sm_st]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
split; [intros E; discriminate E| lia].
+ split.
{ unfold PMPS.fill_res, PM.CHUNK. split; [reflexivity|]. exists c. cbn [PM.sm_g PM.sm_eg PM.sm_st]. rewrite L5K.rl10.
split; [exact T10|]. split; [exact CR|]. split; [reflexivity|]. split; [intros _; split; [exact CEQ| reflexivity]| intros E; discriminate E]. }
exists p, c. rewrite L5K.rl11, L5K.rl10. split; [exact A11|]. split; [exact T10|]. apply (L5.defined_grows M2 M3 _ _ MG3). exact DD2.
+ apply (PMK.hpres_of L LB sp 18432 _ M M3).
* apply (PMK.ek_trans L LB sp 18432 WS M M1 M3 EK1w). apply (PMK.ek_trans L LB sp 18432 WS M1 M2 M3 EK2w EK3w).
* destruct STK2 as (_ & _ & _ & _ & D2). apply (L5.defined_grows M2 M3 _ _ MG3). exact D2.
* apply (PMK.dk_trans L LB sp 18432 M M1 M3); [apply (PMK.dk_grows L LB sp 18432 M M1 MG1)|].
apply (PMK.dk_trans L LB sp 18432 M1 M2 M3); [|apply (PMK.dk_grows L LB sp 18432 M2 M3 MG3)].
apply (PMK.dk_callee L LB LB sp 18432 (sp - 32) 16384 Wx M1 M2 HP2 (incl_refl _)); lia.
+ exact HH3.
Qed.
End WithHeap.
End PMSFBT.
