(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-370, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_JE.v, with its addresses and numbers changed; 263 of its 443 lines of code are new or changed and 1282 lines of the source are left out. *)
(* Sub-run D of piece E of segment J of LLVMFuzzerTestOneInput's ASan walk (fuzz_identity.asan 0x81d8c .. 0x81e18,
   BASE + 0x1680 .. BASE + 0x170c): jeD_stmt of LLVMFuzzerTestOneInput_JE.v.
     0x81d8c .. 0x81da0  a6 := the shadow base (mf + 176), a4 := ' ', s2 := ld (mf + 200), a2 := object 10, a3 := 6
     0x81da4 .. 0x81ddc  five iterations (s7 = 1 .. 5): exp_dp[s2] := a4 (its shadow test, zero), a4 := object 10[s7]
                         (its shadow test: the cell is 6, so the slow path 0x81df0 .. 0x81df8 compares s7 with 6)
     0x81e00 .. 0x81e14  exp_dp[ld + 5] := 0 (its shadow test, zero)
   One token run, fully unrolled: s7 is the literal 1 at the start, so every loop test is decided. The six bytes of
   object 10 come from HIMG (llvmf_img, at the state's own read-only image: EPRE's arodata_okS through HRO and
   IdentBase.arodata_ok_journalP); its shadow cell from GM with G_OUT (block_shadow: one cell, value 6), as a region
   at atom 35 that a shadow declaration ties to A_OBJ 10 and a6. The token layer covers the three stores' shadow
   tests with the shent of exp_dp + ld (zero shadow, Pj3). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Rt Require Import MemchrDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require put_dec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec put_dec_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import LLVMFuzzerTestOneInput_Jcut.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import LLVMFuzzerTestOneInput_JE.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic state at 0x81d8c ------------------------------------------------------------------------- *)
(* atom 32 = the shadow base (mf + 176, a6), 33 = ld = |P| (mf + 200, s2), 34 = exp_dp + ld (the alias of s8 + s2),
   35 = the shadow cell of object 10 (the shadow declaration of A_OBJ 10 over a6); s7 = 1. *)
Definition jeD_dp : YP09.region := YP09.mkRegion (Some 34%nat) 0 6 0 6 [].
Definition jeD_mf : YP09.region := YP09.mkRegion (Some 9%nat) 176 208 208 208
  [YP09.mkChunk 176 (CVal 8 (SOff 32 0)); YP09.mkChunk 200 (CVal 8 (SOff 33 0))].
Definition jeD_o10 : YP09.region := YP09.mkRegion (Some (A_OBJ 10)) 0 6 0 0
  [YP09.mkChunk 0 (CVal 1 (SLit 32)); YP09.mkChunk 1 (CVal 1 (SLit 111)); YP09.mkChunk 2 (CVal 1 (SLit 117));
   YP09.mkChunk 3 (CVal 1 (SLit 116)); YP09.mkChunk 4 (CVal 1 (SLit 41)); YP09.mkChunk 5 (CVal 1 (SLit 0))].
Definition jeD_sc : YP09.region := YP09.mkRegion (Some 35%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 6))].
Definition jeD_facts : facts :=
  mkFacts [(32%nat, mkAF SB_E SB_E 0); (34%nat, mkAF 4096 (2 ^ 47 - 64) 0); (A_OBJ 10, mkAF IMG_LO IMG_TOP 3)] []
    [(SAlu ALU_ADD (SOff 24 0) (SOff 33 0), SOff 34 0);
     (SAlu ALU_ADD (SAlu ALU_SRL (SOff (A_OBJ 10) 0) (SLit 3)) (SOff 32 0), SOff 35 0)].
Definition ss_jeD : sstate :=
  mkSS 0x1680 (sr_set sr_atoms 23%bv (SLit 1)) [jeD_dp; jeD_mf; jeD_o10; jeD_sc] None jeD_facts.
Definition Bx_D : sv := SOff 32 0.
Definition SH_jeD : list shent := [mkSHE 34 0 6].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation bz := RcIdentModel.bz.
#[local] Notation nthb := RcIdentModel.nthb.
#[local] Notation zb := RcIdentModel.zb.
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The Section of LLVMFuzzerTestOneInput.v / _inv.v, in the same order. *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
#[local] Notation ACUT := (acut B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation EPRE := (e_pre B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation HBLOCKS := (hblocks B).

(* ---- what the segment takes, each as the contract's Section states it (LLVMFuzzerTestOneInput.v) ----------- *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
(* The contract's own event bound (LLVMFuzzerTestOneInput.v:124): put_dec asks `st_nev Sc <= EV_MAX`, which
   the entry's pre-condition gives only through it. *)
Hypothesis HEV : EV_LLVMF <= EV_LIB.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HMT0 : forall s s' : astate, mo_le MT s s' 0.
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
Variable G : list (Z * Z).
Hypothesis GM : globs_marked SEGS B G.
Hypothesis G_IN : In (VAL (A_OBJ 9), 7) G.
Hypothesis G_OUT : In (VAL (A_OBJ 10), 6) G.
Hypothesis G_REAC : In (VAL (A_OBJ 8), 5) G.
Hypothesis HIMG : forall (W : world SEGS) mem,
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> llvmf_img B G W mem.
Hypothesis PSIG : ident_prog_sig_ok (PI := PI).
Hypothesis HPD : put_dec.tput_dec_spec B.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA IS___interceptor_trampoline_bcmp).
Hypothesis AMEMCHR : amemchr_realizes SEGS B (SIGMA IS___interceptor_trampoline_memchr).
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.

(* ---- the shared layer of segment J (LLVMFuzzerTestOneInput_Jcut.v), at this Section's variables ------------ *)
#[local] Notation jcut := (LLVMFuzzerTestOneInput_Jcut.jcut B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB
  LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation jc := (LLVMFuzzerTestOneInput_Jcut.jc B).
#[local] Notation jcut_mk := (LLVMFuzzerTestOneInput_Jcut.jcut_mk B MT XM_LIB XN_LIB RLO RHI RA_LLVMF A_EMPTY
  LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS MTL HMT0).
#[local] Notation jlay_of := (LLVMFuzzerTestOneInput_Jcut.jlay_of B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK
  EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS HSTK LAWS).
#[local] Notation jcut_close4 := (LLVMFuzzerTestOneInput_Jcut.jcut_close4 B MT XM_LIB XN_LIB RLO RHI RA_LLVMF
  A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS MTL HMT0 AJ_NIL_IO).
#[local] Notation jcut_mk4 := (LLVMFuzzerTestOneInput_Jcut.jcut_mk4 B MT XM_LIB XN_LIB RLO RHI RA_LLVMF A_EMPTY
  LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS MTL HMT0).
#[local] Notation jcut_wr := (LLVMFuzzerTestOneInput_Jcut.jcut_wr B).
#[local] Notation jcls := (LLVMFuzzerTestOneInput_Jcut.jcls B).
#[local] Notation jkeep4 := (LLVMFuzzerTestOneInput_Jcut.jkeep4 B).

Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* Six bytes the memory holds, as garr8. *)
Lemma jd_garr6 : forall (m : word -> option byte) a v0 v1 v2 v3 v4 v5,
  val_mem SEGS m (a + 0) 1 v0 -> val_mem SEGS m (a + 1) 1 v1 -> val_mem SEGS m (a + 2) 1 v2 ->
  val_mem SEGS m (a + 3) 1 v3 -> val_mem SEGS m (a + 4) 1 v4 -> val_mem SEGS m (a + 5) 1 v5 ->
  0 <= v0 < 256 -> 0 <= v1 < 256 -> 0 <= v2 < 256 -> 0 <= v3 < 256 -> 0 <= v4 < 256 -> 0 <= v5 < 256 ->
  garr8 SEGS m a [v0; v1; v2; v3; v4; v5].
Proof.
intros m a v0 v1 v2 v3 v4 v5 H0 H1 H2 H3 H4 H5 R0 R1 R2 R3 R4 R5 j Hj. cbn [length] in Hj.
destruct j as [|[|[|[|[|[|j]]]]]]; cbn [nth].
- split; [exact H0 | exact R0].
- split; [exact H1 | exact R1].
- split; [exact H2 | exact R2].
- split; [exact H3 | exact R3].
- split; [exact H4 | exact R4].
- split; [exact H5 | exact R5].
- lia.
Qed.

(* ---- 0x81d8c .. 0x81e18: " out)" from object 10, then exp_dp[ld] = 0 ------------------------------------- *)
Lemma jeD : LLVMFuzzerTestOneInput_JE.jeD_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
unfold LLVMFuzzerTestOneInput_JE.jeD_stmt.
intros g pos mf ly2 S2 W2 regs2 mem2 md2 HJ Hfrs HK HPRE HG Hwok Hnm21 HM V176 Rsp Rs1 Rgp Rtp R24 R23.
pose proof HG as HG0.
destruct HG0 as (HSF0 & HSF1 & HSFapp & HSF64 & Hmf0 & Hmfb & Hmf32 & Hsp47).
pose proof HM as (ZNM & ZDP & BNM & BDP & Vld).
pose proof asan_consts as (C1 & _).
assert (HES : ASTACK = 16384) by reflexivity.
assert (HWS : 16720 <= LLVMF_STK) by (unfold STK_LLVMF, ASTACK in HSTK; lia).
pose proof HJ as (HAR & Hly & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos HAR Hin4) as (HFal & _ & HFpres & HFSpres).
change (fs_frame_bytes 4) with 1024 in HFpres, HFSpres. rewrite EFa in HFpres, HFSpres.
pose proof (JEModel.nm_pos (e_pl g)) as Hspos.
destruct (JEModel.in_range (e_pl g) Hwok) as [Hin0 Hout0].
pose proof (JEModel.dec_len1 _ Hin0) as Hdi. pose proof (JEModel.dec_len1 _ Hout0) as Hdo.
unfold put_dec_c.dec_len in Hdi, Hdo.
(* object 10: its six bytes (the read-only image, HIMG) and its shadow (a registered global, GM) *)
pose proof HPRE as HPRE0. unfold e_pre, tLLVMFuzzerTestOneInput_pre in HPRE0.
destruct HPRE0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAROS & _).
pose proof (arodata_ok_journalP SEGS _ _ pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ (HRO _ HAROS)) as HRO2.
pose proof (HIMG W2 mem2 HRO2) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HO10 & _).
pose proof (GM ly2 S2 W2 mem2 md2 (VAL (A_OBJ 10)) 6 G_OUT HAR) as (HO10a & _ & HO10s).
pose proof (HO10s 0 ltac:(lia)) as HSC.
change (if 0 <? 6 / 8 then 0 else 6 mod 8) with 6 in HSC. rewrite Z.add_0_r in HSC.
clear HO10s HRO2 HAROS.
pose proof (pa_obj_img 10 ltac:(lia)) as HO10r.
set (V10 := VAL (A_OBJ 10)) in *.
set (SC := shadow_of_addr SHADOW_OFF V10) in *.
assert (HSC8 : 0x7fff8000 + 0x2000 <= SC <= 0x7fff8000 + 0xbf400)
  by (unfold SC, shadow_of_addr, SHADOW_OFF; clear - HO10r; lia).
set (SF := SFa g pos) in *.
(* the frame lies apart from the image *)
assert (HIMGF : forall a, SF <= a < SF + 1024 -> a < IMG_LO \/ IMG_TOP <= a).
{ intros a Ha.
  assert (Hcl : ~ in_zr a (ly_img ly2) /\ ~ in_img SEGS a)
    by (apply (al_client_img _ _ LAWS _ _ _ _ _ a HAR); right; left; exists 4, pos; split;
        [exact Hin4 | rewrite EFa; change (fs_frame_bytes 4) with 1024; exact Ha]).
  pose proof HAR as (_ & LG & _). pose proof (pa_img_cover ly2 S2 md2 LG) as (Hc1 & Hc2).
  destruct Hcl as (Hni & _). unfold in_zr in Hni. clear - Hni Hc1 Hc2. lia. }
set (P := SlotModel.n_EXP_NM (e_pl g) ++ SlotModel.str_bytes " ("%string ++
            IdentSpec.DEC (SlotModel.t_in (e_pl g)) 1 ++ SlotModel.str_bytes " in / "%string ++
            IdentSpec.DEC (SlotModel.t_out (e_pl g)) 1) in *.
assert (HPl : Z.of_nat (length P) = Z.of_nat (length (SlotModel.n_EXP_NM (e_pl g))) + 2 +
   Z.of_nat (length (IdentSpec.DEC (SlotModel.t_in (e_pl g)) 1)) + 6 +
   Z.of_nat (length (IdentSpec.DEC (SlotModel.t_out (e_pl g)) 1)))
  by (unfold P; rewrite !length_app, JEModel.s1_len, JEModel.s2_len; lia).
assert (HDP : SlotModel.n_EXP_DP (e_pl g) = P ++ SlotModel.str_bytes " out)"%string)
  by (unfold P; rewrite JEModel.dp_eq; rewrite <- !app_assoc; reflexivity).
set (ld := Z.of_nat (length P)) in *.
assert (Hld : 11 <= ld <= 33) by (clear - HPl Hspos Hnm21 Hdi Hdo; lia).
assert (Hdp0 : 4096 <= SF + V_dp) by (unfold V_dp; clear - HSF0; lia).
assert (HXI : SF + V_dp + ld + 6 <= V10 \/ V10 + 8 <= SF + V_dp + ld).
{ pose proof (HIMGF (SF + V_dp + ld) ltac:(unfold V_dp; clear - Hld; lia)) as H1.
  pose proof (HIMGF (SF + V_dp + ld + 5) ltac:(unfold V_dp; clear - Hld; lia)) as H2.
  clear - H1 H2 HO10r. lia. }
assert (HXS : SF + V_dp + ld + 6 <= 0x7fff8000 \/ 0x10007fff8000 <= SF).
{ pose proof HSFapp as (_ & HZ). unfold kLowShadowBeg, kHighMemBeg in HZ. unfold V_dp.
  clear - HZ Hld. lia. }
(* the environment: atom 32 = the shadow base, 33 = ld, 34 = exp_dp + ld, 35 = object 10's shadow cell *)
remember (Eimg (Ereg regs2 [w64 SHADOW_OFF; w64 ld; w64 (SF + V_dp + ld); w64 SC])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (ER : regs_ok E sr_atoms regs2) by (rewrite HE; apply regs_ok_Eimg_Ereg).
assert (HAE : env_agree 32 (Ereg regs2 [w64 SHADOW_OFF; w64 ld; w64 (SF + V_dp + ld); w64 SC]) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew E 32 = w64 SHADOW_OFF)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = w64 ld)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = w64 (SF + V_dp + ld))
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
assert (E35 : ew E 35 = w64 SC)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 3)).
assert (EO10 : ew E (A_OBJ 10) = Z_to_bv 64 V10)
  by (rewrite HE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
clear HE.
assert (E9 : ew E 9 = w64 mf) by (rewrite (EE 9%nat 9%bv eq_refl); exact Rs1).
assert (E24 : ew E 24 = w64 (SF + V_dp)) by (rewrite (EE 24%nat 24%bv eq_refl); exact R24).
assert (U9 : bv_unsigned (ew E 9) = mf)
  by (rewrite E9; apply je_unsigned; clear - Hmf0 Hsp47 Hmfb C1 HES; unfold e_sp0 in *; lia).
assert (U34 : bv_unsigned (ew E 34) = SF + V_dp + ld)
  by (rewrite E34; apply je_unsigned; unfold V_dp; clear - HSF0 HSF1 C1 Hld; lia).
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF)
  by (rewrite E32; apply je_unsigned; unfold SHADOW_OFF; clear; lia).
assert (U35 : bv_unsigned (ew E 35) = SC) by (rewrite E35; apply je_unsigned; clear - HSC8; lia).
assert (U10 : bv_unsigned (ew E (A_OBJ 10)) = V10)
  by (rewrite EO10; apply unsigned_lit_small; clear - HO10r; lia).
(* the symbolic state at 0x81d8c *)
assert (HS : st_ok_pi SEGS VAL E ss_jeD
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x1680)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_jeD. apply pa_entry_st_ok_full.
  - apply regs_ok_pin; [exact ER | intros X; discriminate X | rewrite R23; reflexivity].
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    + unfold jeD_dp, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U34.
      split; [clear - Hdp0 Hld; lia|]. split; [unfold V_dp; clear - HSF1 C1 Hld; lia|].
      split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      exact (proj1 (HFpres (SF + V_dp + ld + o) ltac:(unfold V_dp; clear - Ho Hld; lia))).
    + unfold jeD_mf, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
      split; [clear - Hmf0 C1 HES; lia|]. split; [clear - Hsp47 Hmfb; unfold e_sp0 in *; lia|].
      split; [intros o Ho; clear - Ho; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val SEGS E _ mf 176 8 (SOff 32 0) SHADOW_OFF).
        -- apply je_sv. rewrite (je_U E 32 _ 0 E32), Z.add_0_r.
           rewrite Z.mod_small by (unfold SHADOW_OFF; clear; lia). reflexivity.
        -- cbn. unfold SHADOW_OFF. clear. lia.
        -- cbn. lia.
        -- exact V176.
      * apply (chunk_ok_val SEGS E _ mf 200 8 (SOff 33 0) ld).
        -- apply je_sv. rewrite (je_U E 33 _ 0 E33), Z.add_0_r.
           rewrite Z.mod_small by (clear - Hld; lia). reflexivity.
        -- cbn. clear - Hld. lia.
        -- cbn. lia.
        -- unfold M_n2 in Vld. exact Vld.
    + unfold jeD_o10, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U10.
      split; [clear - HO10r; lia|]. split; [clear - HO10r; lia|].
      split; [intros o Ho; clear - Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]]].
      * apply (chunk_ok_val SEGS E _ V10 0 1 (SLit 32) 32);
          [apply je_sv; rewrite je_Ulit; reflexivity | cbn; lia | cbn; lia
          | exact (proj1 (HO10 0%nat ltac:(cbn; lia)))].
      * apply (chunk_ok_val SEGS E _ V10 1 1 (SLit 111) 111);
          [apply je_sv; rewrite je_Ulit; reflexivity | cbn; lia | cbn; lia
          | exact (proj1 (HO10 1%nat ltac:(cbn; lia)))].
      * apply (chunk_ok_val SEGS E _ V10 2 1 (SLit 117) 117);
          [apply je_sv; rewrite je_Ulit; reflexivity | cbn; lia | cbn; lia
          | exact (proj1 (HO10 2%nat ltac:(cbn; lia)))].
      * apply (chunk_ok_val SEGS E _ V10 3 1 (SLit 116) 116);
          [apply je_sv; rewrite je_Ulit; reflexivity | cbn; lia | cbn; lia
          | exact (proj1 (HO10 3%nat ltac:(cbn; lia)))].
      * apply (chunk_ok_val SEGS E _ V10 4 1 (SLit 41) 41);
          [apply je_sv; rewrite je_Ulit; reflexivity | cbn; lia | cbn; lia
          | exact (proj1 (HO10 4%nat ltac:(cbn; lia)))].
      * apply (chunk_ok_val SEGS E _ V10 5 1 (SLit 0) 0);
          [apply je_sv; rewrite je_Ulit; reflexivity | cbn; lia | cbn; lia
          | exact (proj1 (HO10 5%nat ltac:(cbn; lia)))].
    + unfold jeD_sc, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U35.
      split; [clear - HSC8; lia|]. split; [clear - HSC8; lia|].
      split; [intros o Ho; clear - Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ SC 0 1 (SLit 6) 6);
        [apply je_sv; rewrite je_Ulit; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. change (N.to_nat 1) with 1%nat. exact (je_vm1 _ _ _ _ HSC).
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, jeD_dp, jeD_mf, jeD_o10, jeD_sc.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U34, U9, U10, U35.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold V_dp in *. clear - HXI HXS HSC8 HO10r Hld HSF1 Hmf0 C1 HES.
    repeat split; lia.
  - unfold facts_ok, jeD_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; [exact I|]].
    + unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U32, U34, U10. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold SB_E, SHADOW_OFF, V_dp.
      clear - Hld HSF0 HSF1 C1 HO10r HO10a.
      repeat split; try exact I; lia.
    + split; [|split; [|exact I]].
      * rewrite (je_sv E (SOff 34 0) (SF + V_dp + ld))
          by (rewrite (je_U E 34 _ 0 E34), Z.add_0_r; rewrite Z.mod_small;
              [reflexivity | unfold V_dp; clear - HSF0 HSF1 C1 Hld; lia]).
        apply je_sv. rewrite U_SAlu. cbn [zalu_raw].
        rewrite (je_U E 24 _ 0 E24), (je_U E 33 _ 0 E33), !Z.add_0_r.
        unfold zcanon, M64. rewrite <- Zplus_mod. f_equal; clear; lia.
      * apply (shadow_decl_ok E (A_OBJ 10) 32 35 V10 SHADOW_OFF EO10 ltac:(clear - HO10r; lia) E32).
        exact E35. }
assert (SHOK : sh_ok SEGS Bx_D SH_jeD E (mrestrict (w_H W2) mem2)).
{ unfold sh_ok, SH_jeD. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W2) mem2 E Bx_D 34 (SF + V_dp) N_dp (SF + V_dp + ld) 0 6).
  - apply (range_addressable_sub _ _ (SF + V_dp) N_dp);
    [ apply zero_shadow_range; [unfold V_dp; clear - HSF64; lia | unfold N_dp; clear; lia | exact ZDP]
    | clear; lia | clear; lia ].
  - unfold Bx_D. rewrite (je_U E 32 _ 0 E32), Z.add_0_r.
    rewrite Z.mod_small; [reflexivity | unfold SHADOW_OFF; clear; lia].
  - rewrite (je_U E 34 _ 0 E34), Z.add_0_r.
    apply Z.mod_small. unfold V_dp. clear - HSF0 HSF1 C1 Hld. lia.
  - clear - Hld. lia.
  - unfold N_dp. clear - Hld. lia.
  - intros x Hx Hb. unfold SHADOW_OFF in Hb. unfold V_dp in Hx, HXS.
    rewrite Z.min_l in Hx by lia. rewrite Z.max_r in Hx by lia. clear - Hx Hb HXS Hld HSF1 C1. lia. }
pose proof HJ as HJ0.
unfold cfg_at. change (w64 (BASE + 0x1680)) with (Z_to_bv 64 (BASE + 0x1680)).
paj_run_to_tok RUNTO HS HJ SHOK Bspan_E 0x170c;
 [ lazymatch goal with |- awr_ok ?Ex ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 =>
     let rs' := eval vm_compute in rs in change (awr_ok Ex rs' a1 a2 a3 a4 a5 a6 a7) end;
   repeat first
   [ apply awr_ok_nil
   | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
   | eapply awr_ok_cons_gen;
     [ reflexivity | exact U34
     | cbn [YP09.r_wlo YP09.r_whi]; intros aa Haa;
       right; right; right; exists 4, pos; split; [left; reflexivity|];
       unfold in_zr; cbn [fst snd]; rewrite EFa; change (fs_frame_bytes 4) with 1024;
       left; clear - Haa Hld HSF0; unfold V_dp in *; lia
     | ] ]
 | ].
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
  set (mdv := mdx) in *; clearbody mdv end.
(* what the run wrote: " out)" and the NUL at exp_dp + ld, nothing else *)
pose proof (je_kept_of W2 _ _ _ _ (fun a => SF + V_dp + ld <= a < SF + V_dp + ld + 6) HFr
  ltac:(je_win2 U34 U34)) as KEEP.
cbn beta in KEEP.
je_get_region HS 0%nat RDP. cbn [ms_mem restrict] in RDP.
assert (D0 : val_mem SEGS (rd W2 (ms_mem ms)) (SF + V_dp + ld + 0) 1 32)
  by (exact (field_of_region _ _ 34%nat (SF + V_dp + ld) _ 0 6 0 6 0 1%N (SLit 32) 32 RDP
              ltac:(repeat rewrite ew_ewset_other by lia; exact U34) ltac:(je_in)
              ltac:(apply je_sv; rewrite je_Ulit; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia))).
assert (D1 : val_mem SEGS (rd W2 (ms_mem ms)) (SF + V_dp + ld + 1) 1 111)
  by (exact (field_of_region _ _ 34%nat (SF + V_dp + ld) _ 0 6 0 6 1 1%N (SLit 111) 111 RDP
              ltac:(repeat rewrite ew_ewset_other by lia; exact U34) ltac:(je_in)
              ltac:(apply je_sv; rewrite je_Ulit; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia))).
assert (D2 : val_mem SEGS (rd W2 (ms_mem ms)) (SF + V_dp + ld + 2) 1 117)
  by (exact (field_of_region _ _ 34%nat (SF + V_dp + ld) _ 0 6 0 6 2 1%N (SLit 117) 117 RDP
              ltac:(repeat rewrite ew_ewset_other by lia; exact U34) ltac:(je_in)
              ltac:(apply je_sv; rewrite je_Ulit; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia))).
assert (D3 : val_mem SEGS (rd W2 (ms_mem ms)) (SF + V_dp + ld + 3) 1 116)
  by (exact (field_of_region _ _ 34%nat (SF + V_dp + ld) _ 0 6 0 6 3 1%N (SLit 116) 116 RDP
              ltac:(repeat rewrite ew_ewset_other by lia; exact U34) ltac:(je_in)
              ltac:(apply je_sv; rewrite je_Ulit; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia))).
assert (D4 : val_mem SEGS (rd W2 (ms_mem ms)) (SF + V_dp + ld + 4) 1 41)
  by (exact (field_of_region _ _ 34%nat (SF + V_dp + ld) _ 0 6 0 6 4 1%N (SLit 41) 41 RDP
              ltac:(repeat rewrite ew_ewset_other by lia; exact U34) ltac:(je_in)
              ltac:(apply je_sv; rewrite je_Ulit; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia))).
assert (D5 : val_mem SEGS (rd W2 (ms_mem ms)) (SF + V_dp + ld + 5) 1 0)
  by (exact (field_of_region _ _ 34%nat (SF + V_dp + ld) _ 0 6 0 6 5 1%N (SLit 0) 0 RDP
              ltac:(repeat rewrite ew_ewset_other by lia; exact U34) ltac:(je_in)
              ltac:(apply je_sv; rewrite je_Ulit; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia))).
clear RDP.
(* the registers: JE_KEPT untouched, s2 = ld + 5 *)
lazymatch type of HS with
| st_ok_pi _ _ ?Ef _ _ =>
  assert (HAEf : env_agree 32 (Ereg regs2 [w64 SHADOW_OFF; w64 ld; w64 (SF + V_dp + ld); w64 SC]) Ef)
    by (destruct HAE as [HA1 HA2]; split;
        [intros n Hn; repeat rewrite ew_ewset_other by lia; exact (HA1 n Hn) | exact HA2]);
  pose proof (regs_kept_of_st_ok_pi Ef _ _ regs2 _ JE_KEPT HS HAEf ltac:(vm_compute; reflexivity)) as RK;
  assert (E33f : ew Ef 33 = w64 ld) by (repeat rewrite ew_ewset_other by lia; exact E33)
| st_ok _ ?Ef _ _ =>
  assert (HAEf : env_agree 32 (Ereg regs2 [w64 SHADOW_OFF; w64 ld; w64 (SF + V_dp + ld); w64 SC]) Ef)
    by (destruct HAE as [HA1 HA2]; split;
        [intros n Hn; repeat rewrite ew_ewset_other by lia; exact (HA1 n Hn) | exact HA2]);
  pose proof (regs_kept_of_st_ok SEGS Ef _ _ regs2 _ JE_KEPT HS HAEf ltac:(vm_compute; reflexivity)) as RK;
  assert (E33f : ew Ef 33 = w64 ld) by (repeat rewrite ew_ewset_other by lia; exact E33)
end.
cbn [ms_regs restrict] in RK.
je_reg HS (18%bv : bv 5) Q18.
assert (R18F : getr (ms_regs ms) 18 = w64 (SlotModel.n_ld (e_pl g))).
{ rewrite Q18. apply je_sv. rewrite (je_U _ 33 _ 5 E33f). f_equal.
  unfold SlotModel.n_ld. rewrite HDP, length_app, JEModel.s3_len. unfold ld. clear. lia. }
clear Q18.
pmkst HS.
apply SRr_ret.
exists ly2, S2, (ms_regs ms), (ms_mem ms), mdv.
split; [reflexivity|].
split.
{ split; [exact HJ|]. split; [exact Hfrs|]. split; [apply Permutation_refl|].
  split.
  { intros a Ha Hw _. apply KEEP; [exact Ha|]. intros Hc. apply Hw. apply jeWJ_fr.
    unfold V_dp in Hc. clear - Hc Hld. lia. }
  split; [exact RK|].
  destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as [DD1 DD2].
  destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [DD3 DD4].
  split; [intros fd; rewrite DD3, DD1; reflexivity | rewrite DD4, DD2; reflexivity]. }
split.
{ apply (LLVMFuzzerTestOneInput_Jcut.j_zero_shadow_moved (aview SEGS (w_H W2) mem2)); [|exact ZNM].
  intros i Hi. unfold N_nm in Hi. change (32 / 8) with 4 in Hi. apply KEEP.
  - unfold shadow_of_addr, SHADOW_OFF, V_nm.
    assert (0 <= (SF + 528) / 8 <= SF + 528)
      by (split; [apply Z.div_pos; clear - HSF0; lia | apply Z.div_le_upper_bound; clear - HSF0; lia]).
    clear - Hi H HSF0 HSF1 C1. lia.
  - intros Hc.
    apply (je_sh_out SF 1024 (SF + V_nm) i HSFapp HSF0 HSF1 ltac:(clear; lia)
             ltac:(unfold V_nm; clear; lia) ltac:(unfold V_nm; clear; lia) ltac:(clear - Hi; lia)).
    unfold V_dp in Hc. clear - Hc Hld. lia. }
split.
{ apply (LLVMFuzzerTestOneInput_Jcut.j_zero_shadow_moved (aview SEGS (w_H W2) mem2)); [|exact ZDP].
  intros i Hi. unfold N_dp in Hi. change (64 / 8) with 8 in Hi. apply KEEP.
  - unfold shadow_of_addr, SHADOW_OFF, V_dp.
    assert (0 <= (SF + 592) / 8 <= SF + 592)
      by (split; [apply Z.div_pos; clear - HSF0; lia | apply Z.div_le_upper_bound; clear - HSF0; lia]).
    clear - Hi H HSF0 HSF1 C1. lia.
  - intros Hc.
    apply (je_sh_out SF 1024 (SF + V_dp) i HSFapp HSF0 HSF1 ltac:(clear; lia)
             ltac:(unfold V_dp; clear; lia) ltac:(unfold V_dp; clear; lia) ltac:(clear - Hi; lia)).
    unfold V_dp in Hc |- *. clear - Hc Hld. lia. }
split.
{ apply (LLVMFuzzerTestOneInput_Jcut.j_garr8_moved SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms)); [|exact BNM].
  intros k Hk. rewrite length_map, length_app in Hk. cbn [length] in Hk.
  assert (Hk21 : 0 <= k <= 21) by (clear - Hk Hnm21; lia).
  apply KEEP; [clear - Hk21 HSF0 HSF1 C1; unfold V_nm; lia | clear - Hk21 Hld; unfold V_nm, V_dp; lia]. }
split.
{ unfold bytes_at8. rewrite HDP, <- app_assoc, !map_app. apply garr8_app. split.
  - apply (LLVMFuzzerTestOneInput_Jcut.j_garr8_moved SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms)); [|exact BDP].
    intros k Hk. rewrite length_map in Hk. fold ld in Hk.
    apply KEEP; [clear - Hk Hld HSF0 HSF1 C1; unfold V_dp; lia | clear - Hk; lia].
  - rewrite length_map. fold ld. rewrite JEModel.s3_bytes.
    change (map (fun b : byte => bv_unsigned b) [zb 0]) with [0]. cbn [app].
    exact (jd_garr6 _ (SF + V_dp + ld) 32 111 117 116 41 0 D0 D1 D2 D3 D4 D5
             ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
             ltac:(clear; lia)). }
exact R18F.
Qed.

End c.
End b.
End a.
