(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import SFModel Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim SoftFloat FmtFp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require Import G_memset G_memcpy G_fwritex G_pad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_FmtFp_facts2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_FmtFp_facts2.G_frexpl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmodl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmodl.G_divtf3_main.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require FmtFp_splitR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import FmtFp_splitR.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require FmtFp_splitR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_splitH.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_FmtFp_facts2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_FmtFp_facts2.G_FmtFp_facts.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require Import G_FmtFp_facts2 G_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmt_fp_lib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_lib.G_fmt_fp_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require Import G_fmt_fp_pre G_fmt_fp_pre2 G_fmt_fp_pre3 G_fmt_fp_pre4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require ProgAt3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.ProgAt3.Prog_fmt_fp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
 From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RegFold. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgAt. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require ProgAt3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.ProgAt3.ProgAt2. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require JunkAbs.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.LiaClosure.
(* [comment removed for export] *)
From Stdlib Require Import Zify Lia.

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_cond ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz_fast ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.simp_regs ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.find_t_eval_at k t.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_fmt_fp_c58 : CodeAtT img_segs (sym 0x1973c) (fmt_fp_prog_at IMG)}.
  Context {RB_fmt_fp_c58 : RelCode (sym 0x1973c) 5832}.
  Context {RO_103c0 : RoB img_segs (sym 0x103c0) ([BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 176; BV 8 65])}.
  Context {RO_10428 : RoB img_segs (sym 0x10428) ([BV 8 83; BV 8 90; BV 8 155; BV 8 160; BV 8 47; BV 8 184; BV 8 68; BV 8 0])}.
  Context {RO_103f0 : RoB img_segs (sym 0x103f0) ([BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 224; BV 8 63])}.
  Context {RO_103d8 : RoB img_segs (sym 0x103d8) ([BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 240; BV 8 63])}.
  Context {RO_10420 : RoB img_segs (sym 0x10420) ([BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 248; BV 8 63])}.
  Local Notation GLRN a b := (RelNear (sym a) (sym b)) (only parsing). Local Notation GLRS a := (RelSym (sym a)) (only parsing). Context {RN_B_signbitl_1973c : GLRN 0x1973c 0x1b128}.
  Context {RN_B_fpclassifyl_1973c : GLRN 0x1973c 0x1b130}.
  Context {RN_B_frexpl_1973c : GLRN 0x1973c 0x1b174}.
  Context {RN_B_floatsitf_1973c : GLRN 0x1973c 0x1bad0}.
  Context {RN_B_multf3_1973c : GLRN 0x1973c 0x1b3d0}.
  Context {RN_B_letf2_1973c : GLRN 0x1973c 0x1b24c}.
  Context {RN_B_extenddftf2_1973c : GLRN 0x1973c 0x1af98}.
  Context {RN_B_scalbn_1973c : GLRN 0x1973c 0x1bbd8}.
  Context {RN_B_subtf3_1973c : GLRN 0x1973c 0x1bc70}.
  Context {RN_B_addtf3_1973c : GLRN 0x1973c 0x1bc80}.
  Context {RN_B_memset_1973c : GLRN 0x1973c 0x21738}.
  Context {RN_B_fwritex_1973c : GLRN 0x1973c 0x17d50}.
  Context {RN_B_fixunstfsi_1973c : GLRN 0x1973c 0x1c488}.
  Context {RN_B_floatunsitf_1973c : GLRN 0x1973c 0x1c51c}.
  Context {RN_B_fixtfsi_1973c : GLRN 0x1973c 0x1c608}.
  Context {RN_B_divtf3_1973c : GLRN 0x1973c 0x1c6b0}.
  Context {RN_B_pad_1973c : GLRN 0x1973c 0x19668}.
  Context {RN_B_stack_chk_fail_1973c : GLRN 0x1973c 0x15f04}.
  Context {RS_got_ssp : GLRS 0x22e18}.
  Context {RS_K_102ac : GLRS 0x102ac}.
  Context {RS_K_103c0 : GLRS 0x103c0}.
  Context {RS_K_1031d : GLRS 0x1031d}.
  Context {RS_K_10385 : GLRS 0x10385}.
  Context {RS_K_10326 : GLRS 0x10326}.
  Context {RS_K_10381 : GLRS 0x10381}.
  Context {RS_K_10428 : GLRS 0x10428}.
  Context {RS_K_10b9c : GLRS 0x10b9c}.
  Context {RS_K_103f0 : GLRS 0x103f0}.
  Context {RS_K_103d8 : GLRS 0x103d8}.
  Context {RS_K_10420 : GLRS 0x10420}.
  Context {RS_K_102de : GLRS 0x102de}.
  Context {RS_34288 : GLRS 0x34288}.
  Let rp_34288 : (0 <= sym 0x34288 /\ sym 0x34288 < 2^30)%Z := @rel_sym_pf _ RS_34288.
  Context {SPEC_extenddftf2_callv : extenddftf2_callv_c}.
  Context {SPEC_multf3_callq : multf3_callq_c}.
  Context {RL0_0 : ZFact (sym 0x22e18 + 8 <= sym 0x34288)%Z}.
  Let rl0_0 : (sym 0x22e18 + 8 <= sym 0x34288)%Z := @zfact_pf _ RL0_0.
  Context {RQ_34288 : ZFact (0x20000 <= sym 0x34288)%Z}.
  Let rq_34288 : (0x20000 <= sym 0x34288)%Z := @zfact_pf _ RQ_34288.
  Collection ImgHyps := IMG CODE_fmt_fp_c58 RB_fmt_fp_c58 RO_103c0 RO_10428 RO_103f0 RO_103d8 RO_10420 RN_B_signbitl_1973c RN_B_fpclassifyl_1973c RN_B_frexpl_1973c RN_B_floatsitf_1973c RN_B_multf3_1973c RN_B_letf2_1973c RN_B_extenddftf2_1973c RN_B_scalbn_1973c RN_B_subtf3_1973c RN_B_addtf3_1973c RN_B_memset_1973c RN_B_fwritex_1973c RN_B_fixunstfsi_1973c RN_B_floatunsitf_1973c RN_B_fixtfsi_1973c RN_B_divtf3_1973c RN_B_pad_1973c RN_B_stack_chk_fail_1973c RS_got_ssp RS_K_102ac RS_K_103c0 RS_K_1031d RS_K_10385 RS_K_10326 RS_K_10381 RS_K_10428 RS_K_10b9c RS_K_103f0 RS_K_103d8 RS_K_10420 RS_K_102de RS_34288 rp_34288 SPEC_extenddftf2_callv SPEC_multf3_callq RL0_0 rl0_0 RQ_34288 rq_34288.



(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_chunks_extra_wfile m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= transport_call_extra_wfile segs W m m' MU WM.
Local Ltac lia ::= lia3.
Local Ltac step ::= astep2_fast. Local Ltac stepz ::= astep2_fast.   (* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | tlia | split; [ tlia | exact I ] ].
(* [comment removed for export] *)

Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
Local Ltac flia ::= first [ assumption | slim; lia ].   (* [comment removed for export] *)
Local Ltac mlia ::= first [ lia | Z.div_mod_to_equations; lia ].   (* [comment removed for export] *)

Section FmtFp.
  Variables (ra sp gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
            (ya yb fw : word)      (* [comment removed for export] *)
            (F : bvmap 5 word) (m0 : word -> option byte)
            (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (junk0 : list byte) (canary : word)
            (w p fl t : Z) (o0 o1 : list Z) (ret : Z).
  Definition yv : Z := (bv_unsigned ya + 2^64 * bv_unsigned yb)%Z.
  Definition Fp : Z := bv_unsigned fw.
  Definition usp : Z := bv_unsigned sp.

  Hypothesis HM : fmt_fp o0 yv w p fl t = Some (o1, ret).
  Hypothesis SPLO : (5152 <= bv_unsigned sp)%Z.
  Hypothesis SPHI : (bv_unsigned sp < 2^63)%Z.
  Hypothesis GLO : ((sym 0x34288) + 8 <= bv_unsigned sp - 4640)%Z.   (* [comment removed for export] *)
  Hypothesis AF : (bv_unsigned sp <= Fp)%Z.
  Hypothesis AB : (bv_unsigned sp <= B)%Z.
  Hypothesis Hw : (-2^31 <= w <= 1)%Z.
  Hypothesis Hp : (-2^31 <= p < 2^20)%Z.   (* [comment removed for export] *)
  Hypothesis Hfl : (0 <= fl < 2^32)%Z.
  Hypothesis Ht : (0 <= t < 256)%Z.
  Hypothesis Hta : Z.lor t 32 <> 97%Z.
  (* [comment removed for export] *)
  Hypothesis YN0 : Z.land (Z.shiftr (hi64 yv) 48) 0x7fff <> 0%Z \/ f128_le yv F128_ZERO = 0%Z.
  Hypothesis YN1 : Z.land (Z.shiftr (hi64 (Z.lxor yv F128_SIGNBIT)) 48) 0x7fff <> 0%Z \/ f128_le (Z.lxor yv F128_SIGNBIT) F128_ZERO = 0%Z.
  (* [comment removed for export] *)
  Hypothesis DIGB : dig_words_fact yv fl.
  Hypothesis E2B : e2_range_fact yv fl.
  Hypothesis DNB0 : dn_phase_fact yv fl p t.
  (* [comment removed for export] *)
  Hypothesis WBA0 : words_all_fact yv fl p t.
  Hypothesis CAR0 : carry_fact yv fl p t.
  Hypothesis AZR0 : azr_fact yv fl p t.
  Hypothesis BLA0 : below_a_fact yv fl p t.
  (* [comment removed for export] *)
  Lemma WB0 : forall y1 fr e0 y e2 b' z' y' s big a z e2',
    fst (fst (ffp_sign yv fl)) = y1 ->
    frexpl FREXPL_FUEL y1 0 = Some (fr, e0) ->
    (let y2 := f128_mul fr (f128_of_i32 2) in
     let ynz := negb (f128_le y2 F128_ZERO =? 0) in
     y = (if ynz then f128_mul y2 (f128_of_d D_0x1p28) else y2) /\ e2 = (if ynz then e0 - 1 - 28 else e0)%Z) ->
    fmt_fp_dig DIG_FUEL (zrepeat 0 128, (if e2 <? 0 then 0 else 122)%Z, y) = Some (b', z', y') ->
    fmt_fp_up UP_FUEL (b', (if e2 <? 0 then 0 else 122)%Z, z', e2) = Some s ->
    fmt_fp_dn DN_FUEL (if p <? 0 then 6 else p)%Z t (if e2 <? 0 then 0 else 122)%Z s = Some (big, a, z, e2') ->
    forall i, (a <= i < z)%Z -> (0 <= znth big i < 1000000000)%Z.
  Proof using WBA0 ImgHyps.
    intros y1 fr e0 y e2 b' z' y' s big a z e2' HY HFR HD HDG HU HDN i _.
    apply (WBA0 (if p <? 0 then 6 else p)%Z (if e2 <? 0 then 0 else 122)%Z big a z).
    exists y1, fr, e0, y, e2, b', z', y', s, e2'.
    split; [exact HY|]. split; [exact HFR|]. split; [exact HD|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact HDG|]. split; [exact HU|]. exact HDN.
  Qed.
  Hypothesis ROOM : (Z.of_nat (length o1) <= Z.of_nat (length o0) + Z.of_nat (length junk0))%Z.
  Hypothesis J256 : (length junk0 < 256)%nat.

  (* [comment removed for export] *)
  Definition prov_C2 (y2 e0 : Z) : Prop :=
    exists y1 fr, fst (fst (ffp_sign yv fl)) = y1 /\ frexpl FREXPL_FUEL y1 0 = Some (fr, e0) /\ y2 = f128_mul fr (f128_of_i32 2).
  Definition prov_D (y e2 p1 : Z) : Prop :=
    exists y2 e0, prov_C2 y2 e0 /\
      (let ynz := negb (f128_le y2 F128_ZERO =? 0) in
       y = (if ynz then f128_mul y2 (f128_of_d D_0x1p28) else y2) /\ e2 = (if ynz then e0 - 1 - 28 else e0)%Z
       /\ p1 = (if p <? 0 then 6 else p)%Z).
  (* [comment removed for export] *)
  Definition prov_E (p1 : Z) (big : list Z) (r z e2 : Z) : Prop :=
    exists y y', prov_D y e2 p1 /\ r = (if e2 <? 0 then 0 else 122)%Z /\ fmt_fp_dig DIG_FUEL (zrepeat 0 128, r, y) = Some (big, z, y').
  (* [comment removed for export] *)
  Definition prov_F (p1 r : Z) (s : list Z * Z * Z * Z) : Prop :=
    exists big z e2, prov_E p1 big r z e2 /\ fmt_fp_up UP_FUEL (big, r, z, e2) = Some s.
  (* [comment removed for export] *)
  Definition prov_G (p1 r : Z) (s : list Z * Z * Z * Z) : Prop :=
    exists s0, prov_F p1 r s0 /\ fmt_fp_dn DN_FUEL p1 t r s0 = Some s.

  (* [comment removed for export] *)
  Definition prov_R (p1 prefix pl r : Z) (big : list Z) (a z e : Z) : Prop :=
    exists big0 a0 z0 e2' e0, prov_G p1 r (big0, a0, z0, e2') /\ ffp_e big0 a0 r z0 = Some e0 /\
      ffp_R t p1 prefix pl big0 a0 r z0 e0 (ffp_j t p1 e0) = Some (big, a, z, e).

  Lemma WB : forall p1 r big a z e2, prov_G p1 r (big, a, z, e2) -> forall i, (a <= i < z)%Z -> (0 <= znth big i < 1000000000)%Z.
  Proof using WBA0 ImgHyps.
    intros p1 r big a z e2' (s0 & (bg & zz & e2 & (y & y' & (y2 & e0 & (y1 & fr & HY & HFR & Hy2) & HD) & Hr & HDG) & HU) & HDN).
    cbv zeta in HD. (nelim HD 3%nat; intros Hy He2 Hp1). subst y2. subst p1 r.
    exact (WB0 y1 fr e0 y e2 bg zz y' s0 big a z e2' HY HFR (conj Hy He2) HDG HU HDN).
  Qed.

  Lemma provG_run : forall p1 r big a z e2, prov_G p1 r (big, a, z, e2) -> run_to_dn yv fl p t p1 r big a z.
  Proof using  ImgHyps.
    intros p1 r big a z e2' (s0 & (bg & zz & e2 & (y & y' & (y2 & e0 & (y1 & fr & HY & HFR & Hy2) & HD) & Hr & HDG) & HU) & HDN).
    cbv zeta in HD. (nelim HD 3%nat; intros Hy He2 Hp1). subst y2.
    exists y1, fr, e0, y, e2, bg, zz, y', s0, e2'.
    split; [exact HY|]. split; [exact HFR|]. split; [split; [exact Hy | exact He2]|]. split; [exact Hp1|]. split; [exact Hr|].
    subst r. split; [exact HDG|]. split; [exact HU|]. subst p1. exact HDN.
  Qed.
  Lemma WBA : forall p1 r big a z e2, prov_G p1 r (big, a, z, e2) -> forall i, (0 <= znth big i < 1000000000)%Z.
  Proof using WBA0 ImgHyps. intros p1 r big a z e2 PG. exact (WBA0 _ _ _ _ _ (provG_run _ _ _ _ _ _ PG)). Qed.
  Lemma CAR : forall p1 prefix pl r big a z e, prov_R p1 prefix pl r big a z e -> (0 <= a)%Z.
  Proof using CAR0 ImgHyps.
    intros p1 prefix pl r big a z e (big0 & a0 & z0 & e2' & e0 & PG & He & HR).
    exact (CAR0 _ _ _ _ _ (provG_run _ _ _ _ _ _ PG) _ _ _ _ _ _ _ He HR).
  Qed.
  Lemma AZR : forall p1 prefix pl r big a z e zS, prov_R p1 prefix pl r big a z e ->
    fmt_fp_strip BIG_FUEL big a z = Some zS -> Z.lor t 32 <> CHR_f -> (zS <= a)%Z -> a = r.
  Proof using AZR0 ImgHyps.
    intros p1 prefix pl r big a z e zS (big0 & a0 & z0 & e2' & e0 & PG & He & HR) HS Htf Hza.
    exact (AZR0 _ _ _ _ _ (provG_run _ _ _ _ _ _ PG) _ _ _ _ _ _ _ _ He HR HS Htf Hza).
  Qed.

  Lemma BLA : forall p1 r big a z e2, prov_G p1 r (big, a, z, e2) -> forall k, (0 <= k < a)%Z -> znth big k = 0%Z.
  Proof using BLA0 ImgHyps. intros p1 r big a z e2 PG. exact (BLA0 _ _ _ _ _ (provG_run _ _ _ _ _ _ PG)). Qed.

  Lemma DNB : forall p1 r s, prov_F p1 r s -> dn_good p1 t r s.
  Proof using DNB0 ImgHyps.
    intros p1 r s (big & z & e2 & (y & y' & (y2 & e0 & (y1 & fr & HY & HFR & Hy2) & HD) & Hr & HDG) & HU).
    cbv zeta in HD. (nelim HD 3%nat; intros Hy He2 Hp1). subst y2. subst p1 r.
    exact (DNB0 y1 fr e0 y e2 big z y' s HY HFR (conj Hy He2) HDG HU).
  Qed.

  (* [comment removed for export] *)
  Definition ctx_all : unit :=
    let _ := (ra, sp, gp, tp, s0e, s1e, s2e, s3e, s4e, s5e, s6e, s7e, s8e, s9e, s10e, s11e, ya, yb, fw, F, m0,
              fl0, j1, j2, lbfw, B, junk0, canary, w, p, fl, t, o0, o1, ret) in tt.

  Definition Wfp : list (Z * Z) :=
    [(bv_unsigned sp - 4640, bv_unsigned sp);
     (B + Z.of_nat (length o0), B + Z.of_nat (length o1));
     (Fp + 40, Fp + 48)]%Z.

  Definition fmt_fp_post (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Ft fc' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 ret) a1 a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom img_segs)
      /\ munch Wfp m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'
      /\ frm0 fc'
      /\ stk img_segs m' (bv_unsigned sp - 4640) (bv_unsigned sp)
      /\ wfile m' Fp fl0 j1 j2 lbfw B (zb o1) (skipn (length o1 - length o0) junk0)
      /\ ssp_cells m' canary
      /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k).

  (* [comment removed for export] *)
  Definition hi_cells (pad256 : list byte) : list cell :=
    [CB 256 pad256; C8 canary; C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra].

  (* [comment removed for export] *)
  Definition finv (m : word -> option byte) (pad256 : list byte) : Prop :=
    mem_inv img_segs m /\ munch Wfp m0 m /\ wmono img_segs m0 m
    /\ rw_cells img_segs m (bv_unsigned sp + -368) (hi_cells pad256)
    /\ stk img_segs m (bv_unsigned sp - 4640) (bv_unsigned sp + -1056)
    /\ rw_cells img_segs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells img_segs m ssp_guard [C8 canary].
  Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
    let ST := fresh "ST" in let GOT := fresh "GOT" in let SSP := fresh "SSP" in
    (nelim H 7%nat; intros MI MU WM FRhi ST GOT SSP); unfold Wfp in MU; unfold hi_cells in FRhi; unfold got_ssp, ssp_guard in GOT, SSP.
  Ltac mk_finv := unfold finv, Wfp, hi_cells, got_ssp, ssp_guard;
    split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | idtac]|]; split; hyp.

  Ltac dest_wfile H := let FC := fresh "FC" in let BUF := fresh "BUF" in let FLG := fresh "FLG" in let LBF := fresh "LBF" in
    let Bpos := fresh "Bpos" in let Bhi := fresh "Bhi" in let SEPfb := fresh "SEPfb" in
    (nelim H 7%nat; intros FC BUF FLG LBF Bpos Bhi SEPfb); unfold FILE_cells in FC; idtac; idtac .
  Ltac mk_wfile := unfold wfile, FILE_cells; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [lia|]; split; lia.

  (* [comment removed for export] *)
  Definition midv (K : midK) (m : word -> option byte) (fc : bv 32) (e2m : Z) : Prop :=
    finv m (K_pad K) /\ frm0 fc /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get (K_Ft K) k = reg_get F k)
    /\ rw_cells img_segs m (bv_unsigned sp + -544)
         [C8 (Z_to_bv 64 0); CB 40 (K_jk40 K); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t); CB 8 (K_jk8 K); C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 (sym 0x34288));
          C8 (Z_to_bv 64 (K_plz K)); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)]
    /\ rw_cells img_segs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 e2m); CB 3 (K_jk3 K)]
    /\ rw_cells img_segs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells img_segs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ K_plz K = Z.b2z (K_pl K =? 0)%Z /\ K_pfx K = ((sym 0x102ac) + K_prefix K)%Z
    /\ (0 <= K_p1 K < 2^20)%Z.
  Ltac dest_midv H :=
    let FI := fresh "FI" in let FRM := fresh "FRM" in let HFt := fresh "HFt" in let FRs := fresh "FRs" in let E2 := fresh "E2" in
    let EB := fresh "EB" in let BF := fresh "BF" in let WF := fresh "WF" in
    let Hpre := fresh "Hpre" in let Hpl := fresh "Hpl" in let Hplz := fresh "Hplz" in let Hpfx := fresh "Hpfx" in let Hp1 := fresh "Hp1" in
    (nelim H 13%nat; intros FI FRM HFt FRs E2 EB BF WF Hpre Hpl Hplz Hpfx Hp1);
    cbn [K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft] in *;
    dest_finv FI; dest_wfile WF.
  Ltac mk_midv := unfold midv; cbn [K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft];
    split; [mk_finv|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | mk_wfile]|];
    split; [dlia|]; split; [dlia|]; split; [hyp|]; split; [hyp|]; dlia.
  (* [comment removed for export] *)
  Ltac dest_midv2 H :=
    let FI := fresh "FI" in let FRM := fresh "FRM" in let HFt := fresh "HFt" in let FRs := fresh "FRs" in let E2 := fresh "E2" in
    let EB := fresh "EB" in let BF := fresh "BF" in let WF := fresh "WF" in
    let Hpre := fresh "Hpre" in let Hpl := fresh "Hpl" in let Hplz := fresh "Hplz" in let Hpfx := fresh "Hpfx" in let Hp1 := fresh "Hp1" in
    (nelim H 13%nat; intros FI FRM HFt FRs E2 EB BF WF Hpre Hpl Hplz Hpfx Hp1);
    cbn [K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft] in *;
    dest_finv FI.
  (* [comment removed for export] *)
  Definition midw (K : midK) (m : word -> option byte) (fc : bv 32) (e2m : Z) : Prop :=
    finv m (K_pad K) /\ frm0 fc /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get (K_Ft K) k = reg_get F k)
    /\ rw_cells img_segs m (bv_unsigned sp + -544)
         [C8 (Z_to_bv 64 0); CB 40 (K_jk40 K); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t); CB 8 (K_jk8 K); C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 (sym 0x34288));
          C8 (Z_to_bv 64 (K_plz K)); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)]
    /\ rw_cells img_segs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 e2m); CB 3 (K_jk3 K)]
    /\ rw_cells img_segs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells img_segs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ (0 <= K_plz K < 2^64)%Z /\ K_pfx K = ((sym 0x102ac) + K_prefix K)%Z
    /\ (0 <= K_p1 K < 2^20)%Z.
  Lemma midv_w : forall K m fc e2m, midv K m fc e2m -> midw K m fc e2m.
  Proof using Hfl Ht J256 ImgHyps.
    intros K m fc e2m H. (nelim H 13%nat; intros FI FRM HFt FRs E2 EB BF WF Hpre Hpl Hplz Hpfx Hp1).
    unfold midw. split; [exact FI|]. split; [exact FRM|]. split; [exact HFt|]. split; [exact FRs|]. split; [exact E2|].
    split; [exact EB|]. split; [exact BF|]. split; [exact WF|]. split; [exact Hpre|]. split; [exact Hpl|].
    split. { rewrite Hplz. destruct (K_pl K =? 0); cbn; lia. } split; [exact Hpfx | exact Hp1].
  Qed.
  Ltac dest_midw2 H :=
    let FI := fresh "FI" in let FRM := fresh "FRM" in let HFt := fresh "HFt" in let FRs := fresh "FRs" in let E2 := fresh "E2" in
    let EB := fresh "EB" in let BF := fresh "BF" in let WF := fresh "WF" in
    let Hpre := fresh "Hpre" in let Hpl := fresh "Hpl" in let Hplz := fresh "Hplz" in let Hpfx := fresh "Hpfx" in let Hp1 := fresh "Hp1" in
    (nelim H 13%nat; intros FI FRM HFt FRs E2 EB BF WF Hpre Hpl Hplz Hpfx Hp1);
    cbn [K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft] in *;
    dest_finv FI.
  Ltac dest_midw H := dest_midw2 H; match goal with WF : wfile _ _ _ _ _ _ _ _ _ |- _ => dest_wfile WF end.
  Ltac mk_midw := first [ apply midv_w; mk_midv |
    unfold midw; cbn [K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft];
    split; [mk_finv|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | mk_wfile]|];
    split; [dlia|]; split; [dlia|]; split; [dlia|]; split; [hyp|]; dlia ].

  (* [comment removed for export] *)
  Definition midq (K : midK) (cs5 : list cell) (z456 : Z) (m : word -> option byte) (fc : bv 32) : Prop :=
    finv m (K_pad K) /\ frm0 fc /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get (K_Ft K) k = reg_get F k)
    /\ rw_cells img_segs m (bv_unsigned sp + -544)
         ([C8 (Z_to_bv 64 0)] ++ cs5 ++ [C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t); C8 (Z_to_bv 64 (K_p1 K)); C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 (sym 0x34288));
          C8 (Z_to_bv 64 z456); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)])
    /\ rw_cells img_segs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 0); CB 3 (K_jk3 K)]
    /\ rw_cells img_segs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells img_segs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ (0 <= z456 < 2^64)%Z /\ K_pfx K = ((sym 0x102ac) + K_prefix K)%Z
    /\ (0 <= K_p1 K < 2^20)%Z.
  Ltac dest_midq2 H :=
    let FI := fresh "FI" in let FRM := fresh "FRM" in let HFt := fresh "HFt" in let FRs := fresh "FRs" in let E2 := fresh "E2" in
    let EB := fresh "EB" in let BF := fresh "BF" in let WF := fresh "WF" in
    let Hpre := fresh "Hpre" in let Hpl := fresh "Hpl" in let Hplz := fresh "H456" in let Hpfx := fresh "Hpfx" in let Hp1 := fresh "Hp1" in
    (nelim H 13%nat; intros FI FRM HFt FRs E2 EB BF WF Hpre Hpl Hplz Hpfx Hp1);
    cbn [app K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft] in *;
    dest_finv FI.
  Ltac dest_midq H := dest_midq2 H; match goal with WF : wfile _ _ _ _ _ _ _ _ _ |- _ => dest_wfile WF end.
  Ltac mk_midq :=
    unfold midq; cbn [app K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft];
    split; [mk_finv|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | mk_wfile]|];
    split; [dlia|]; split; [dlia|]; split; [dlia|]; split; [hyp|]; dlia.
  (* [comment removed for export] *)
  Definition midq_K (K : midK) (cs5 : list cell) (z456 : Z) : midK :=
    MidK (K_pad K) (cells_bytes cs5) (le8 (Z_to_bv 64 (K_p1 K))) (K_jk3 K) (K_jk12 K) (K_jk37 K) (K_p1 K) (K_prefix K) (K_pl K) z456 (K_pfx K) (K_Ft K).
  Lemma midq_w : forall K cs5 z456 m fc, midq K cs5 z456 m fc -> cells_size cs5 = 40%nat -> midw (midq_K K cs5 z456) m fc 0%Z.
  Proof using  ImgHyps.
    intros K cs5 z456 m fc H Hsz. (nelim H 13%nat; intros FI FRM HFt FRs E2 EB BF WF Hpre Hpl Hplz Hpfx Hp1).
    unfold midw, midq_K. cbn [K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft].
    split; [exact FI|]. split; [exact FRM|]. split; [exact HFt|]. split.
    { apply (rw_cells_merge img_segs m _ [C8 (Z_to_bv 64 0)] cs5) in FRs. rewrite Hsz in FRs.
      apply (rw_cells_merge img_segs m _ [C8 (Z_to_bv 64 0); CB 40 (cells_bytes cs5); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t)] [C8 (Z_to_bv 64 (K_p1 K))]
               [C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 (sym 0x34288)); C8 (Z_to_bv 64 z456); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)]) in FRs.
      cbn [cells_size csize cells_bytes cbytes app Nat.add] in FRs. rewrite app_nil_r in FRs. exact FRs. }
    split; [exact E2|]. split; [exact EB|]. split; [exact BF|]. split; [exact WF|].
    split; [exact Hpre|]. split; [exact Hpl|]. split; [exact Hplz|]. split; [exact Hpfx|]. exact Hp1.
  Qed.

  (* [comment removed for export] *)
  Definition emw (K : midK) (estrp ppl fl2 a8v v440 : Z) (oc : list Z) (m : word -> option byte) (fc : bv 32) : Prop :=
    finv m (K_pad K) /\ frm0 fc /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get (K_Ft K) k = reg_get F k)
    /\ rw_cells img_segs m (bv_unsigned sp + -544)
         [C8 (Z_to_bv 64 0); CB 40 (K_jk40 K); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 estrp); C8 (Z_to_bv 64 ppl); C8 (Z_to_bv 64 fl2); C8 (Z_to_bv 64 (sym 0x34288));
          C8 (Z_to_bv 64 a8v); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 v440); C8 (Z_to_bv 64 Fp)]
    /\ rw_cells img_segs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 0); CB 3 (K_jk3 K)]
    /\ rw_cells img_segs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells img_segs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb oc) (skipn (length oc - length o0) junk0)
    /\ (length o0 <= length oc)%nat
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ K_pfx K = ((sym 0x102ac) + K_prefix K)%Z /\ (0 <= K_p1 K < 2^20)%Z.
  Ltac dest_emw2 H :=
    let FI := fresh "FI" in let FRM := fresh "FRM" in let HFt := fresh "HFt" in let FRs := fresh "FRs" in let E2 := fresh "E2" in
    let EB := fresh "EB" in let BF := fresh "BF" in let WF := fresh "WF" in let LOC := fresh "LOC" in
    let Hpre := fresh "Hpre" in let Hpl := fresh "Hpl" in let Hpfx := fresh "Hpfx" in let Hp1 := fresh "Hp1" in
    (nelim H 13%nat; intros FI FRM HFt FRs E2 EB BF WF LOC Hpre Hpl Hpfx Hp1);
    cbn [K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft] in *;
    dest_finv FI.
  Ltac dest_emw H := dest_emw2 H; match goal with WF : wfile _ _ _ _ _ _ _ _ _ |- _ => dest_wfile WF end.
  Ltac mk_emw :=
    unfold emw; cbn [K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft];
    split; [mk_finv|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | mk_wfile]|];
    split; [first [hyp | dlia | rewrite ?app_length; dlia]|]; split; [dlia|]; split; [dlia|]; split; [first [hyp|dlia]|]; dlia.

  (* [comment removed for export] *)
  Ltac prune := try clear HM; try clear YN0; try clear YN1.
  (* [comment removed for export] *)
  Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
  (* [comment removed for export] *)
  Ltac clear_fat :=
    repeat match goal with
           | H : evt _ _ _ |- _ => clear H
           | H : forall _, _ |- _ => clear H
           | H : _ = Some _ |- _ => clear H
           | H : Some _ = _ |- _ => clear H
           | H : u32arr _ _ _ _ |- _ => clear H
           | H : rw_cells _ _ _ _ |- _ => clear H
           | H : wfile _ _ _ _ _ _ _ _ _ |- _ => clear H
           end.
  (* [comment removed for export] *)
  Ltac clear_logic :=
    repeat match goal with
           | H : _ \/ _ |- _ => clear H
           | H : _ <-> _ |- _ => clear H
           | H : ~ _ |- _ => clear H
           | H : zboxed _ _ |- _ => clear H
           end.
  Local Ltac slia ::= first [ exact I | solve [clear_fat; clear_logic; lia] | solve [clear_fat; lia] | lia | split; [lia|exact I] ].

  Notation POST := (fmt_fp_post m0).
  Notation SPv := (Z_to_bv 64 (bv_unsigned sp + -1056)).
  Notation S0v := (Z_to_bv 64 (bv_unsigned sp)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis L_f70 :
    forall m (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x26 x27 x28 x29 x30 x31 : word) Ft fc pad jk40 jk8 jk3 jk12 jk37 jbig
      (y e2 p1 a aptr prefix pl plz pfx : Z),
    finv m pad -> frm0 fc ->
    (forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k) ->
    rw_cells img_segs m (bv_unsigned sp + -544)
      [C8 (Z_to_bv 64 0); CB 40 jk40; C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t); CB 8 jk8; C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 (sym 0x34288));
       C8 (Z_to_bv 64 plz); C8 (Z_to_bv 64 pfx); C8 (Z_to_bv 64 pl); C8 (Z_to_bv 64 Fp)] ->
    rw_cells img_segs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 e2); CB 3 jk3] ->
    rw_cells img_segs m (bv_unsigned sp + -417) [CB 12 jk12] ->
    rw_cells img_segs m (bv_unsigned sp + -405) [CB 37 jk37] ->
    rw_cells img_segs m (bv_unsigned sp + -1056) [CB 512 jbig] ->
    wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0 ->
    (0 <= prefix <= 6)%Z -> (0 <= pl <= 1)%Z -> plz = Z.b2z (pl =? 0)%Z -> pfx = ((sym 0x102ac) + prefix)%Z ->
    (0 <= p1 < 2^20)%Z -> (-1102 <= e2 <= 1024)%Z ->
    a = (if e2 <? 0 then 0 else 122)%Z -> aptr = (bv_unsigned sp + -1056 + 4 * a)%Z ->
    (forall b' z' y', fmt_fp_dig DIG_FUEL (zrepeat 0 128, a, y) = Some (b', z', y') -> (z' <= a + 6)%Z) ->
    prov_D y e2 p1 ->
    ffp_D o0 w fl t y e2 p1 prefix pl = Some (o1, ret) ->
    evt img_segs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 p1) (Z_to_bv 64 e2) (Z_to_bv 64 (Z.lor t 32)) x21 (Z_to_bv 64 aptr) x23
               (Z_to_bv 64 (lo64 y)) (Z_to_bv 64 (hi64 y)) x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1973c + 1180)) fc None m (seg_rom img_segs)).

  (* [comment removed for export] *)
  Lemma L_c58 : forall m (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) fc pad jk40 jk16 jk3 jk12 jk37 jbig
      (y2 e0 prefix pl plz pfx : Z),
    finv m pad -> frm0 fc ->
    rw_cells img_segs m (bv_unsigned sp + -544)
      [C8 (Z_to_bv 64 0); CB 40 jk40; C8 (Z_to_bv 64 w); CB 16 jk16; C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 (sym 0x34288));
       C8 (Z_to_bv 64 plz); C8 (Z_to_bv 64 pfx); C8 (Z_to_bv 64 pl); C8 (Z_to_bv 64 Fp)] ->
    rw_cells img_segs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 e0); CB 3 jk3] ->
    rw_cells img_segs m (bv_unsigned sp + -417) [CB 12 jk12] ->
    rw_cells img_segs m (bv_unsigned sp + -405) [CB 37 jk37] ->
    rw_cells img_segs m (bv_unsigned sp + -1056) [CB 512 jbig] ->
    wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0 ->
    (0 <= prefix <= 6)%Z -> (0 <= pl <= 1)%Z -> plz = Z.b2z (pl =? 0)%Z -> pfx = ((sym 0x102ac) + prefix)%Z ->
    (-16501 <= e0 <= 16384)%Z ->
    (let ynz := negb (f128_le y2 F128_ZERO =? 0) in let e2 := if ynz then e0 - 1 - 28 else e0 in -1102 <= e2 <= 1024)%Z ->
    (forall b' z' y',
      (let ynz := negb (f128_le y2 F128_ZERO =? 0) in
       let y := if ynz then f128_mul y2 (f128_of_d D_0x1p28) else y2 in
       let e2 := if ynz then e0 - 1 - 28 else e0 in
       fmt_fp_dig DIG_FUEL (zrepeat 0 128, (if e2 <? 0 then 0 else 122), y) = Some (b', z', y') ->
       z' <= (if e2 <? 0 then 0 else 122) + 6)%Z) ->
    prov_C2 y2 e0 ->
    ffp_C2 o0 w fl t y2 e0 p prefix pl = Some (o1, ret) ->
    evt img_segs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (-5)) (Z_to_bv 64 (f128_le y2 F128_ZERO)) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 p) (Z_to_bv 64 t) (Z_to_bv 64 (sym 0x34288)) (Z_to_bv 64 512) SPv (Z_to_bv 64 w) (Z_to_bv 64 (lo64 y2)) (Z_to_bv 64 (hi64 y2)) (Z_to_bv 64 Fp) (Z_to_bv 64 fl) x28 x29 x30 x31)
          F (Z_to_bv 64 (sym 0x1973c + 388)) fc None m (seg_rom img_segs)).
  Proof using AB AF GLO Hp Ht Hta J256 L_f70 SPHI SPLO ImgHyps.
    intros until pfx. intros FI FRM FRs E2 EB BF BIGb WF Hpre Hpl Hplz Hpfx Re0 He2b Hzb PC2 HC. dest_finv FI. dest_wfile WF. pose_word_ranges.
    assert (Rfw : (0 <= Fp < 2^64)%Z) by apply (zr_word fw).
    pose proof (lo64_range y2) as R2lo. pose proof (hi64_range y2) as R2hi.
    unfold ffp_C2 in HC. cbv zeta in Hzb. cbv zeta in He2b. set (ynz := negb (f128_le y2 F128_ZERO =? 0)) in HC, Hzb, He2b.
    (* [comment removed for export] *)
    Ltac goF70 aval pfv HC Hzb :=
      eapply L_f70 with (a := aval) (prefix := pfv);
      [ mk_finv | hyp | | hyp | hyp | hyp | hyp | hyp | mk_wfile | dlia | dlia | hyp | hyp | dlia | dlia | | dlia | | | exact HC ];
      [ intros k Hk; first [ reflexivity | apply fother; exact Hk ]
      | first [ rewrite (proj2 (Z.ltb_lt _ _)) by mlia; reflexivity | rewrite (proj2 (Z.ltb_ge _ _)) by mlia; reflexivity ]
      | let Hd := fresh "Hd" in intros ? ? ? Hd;
        first [ rewrite (proj2 (Z.ltb_lt _ _)) in Hzb by mlia | rewrite (proj2 (Z.ltb_ge _ _)) in Hzb by mlia ]; exact (Hzb _ _ _ Hd)
      | lazymatch goal with PDk : forall p1 e2, _ -> _ -> prov_D _ e2 p1 |- _ =>
          apply PDk; [ destruct (Z.ltb_spec0 p 0); first [ reflexivity | exfalso; mlia ] | mlia ] end ].
    Ltac fixp HC Kp :=
      first [ replace (if p <? 0 then 6 else p)%Z with p in HC by (destruct (Z.ltb_spec0 p 0); [exfalso; mlia | reflexivity])
            | replace (if p <? 0 then 6 else p)%Z with 6%Z in HC by (destruct (Z.ltb_spec0 p 0); [reflexivity | exfalso; mlia]) ].
    Ltac fixa122 :=
      replace (Z_to_bv 64 (bv_unsigned sp + 18446744073709551048)) with (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * 122))
        by (apply Z_to_bv_eqm; change (2^64)%Z with 18446744073709551616%Z; mlia).
    zs. if_cases Kz; zify_cond Kz; rewrite f128_le_land64_zero in Kz.
    - (* [comment removed for export] *)
      assert (Eynz : ynz = false) by (unfold ynz; rewrite Kz; reflexivity). rewrite Eynz in HC, Hzb, He2b. clearbody ynz. cbv beta iota in HC. cbv beta iota in Hzb. cbv beta iota in He2b.
      assert (PDk : forall p1 e2, p1 = (if p <? 0 then 6 else p)%Z -> e2 = e0 -> prov_D y2 e2 p1).
      { intros p1' e2' -> ->. exists y2, e0. split; [exact PC2|]. cbv zeta. rewrite Kz. cbn [Z.eqb negb]. repeat split; reflexivity. }
      zs. zs. zs. zs. if_cases Ka; zify_cond Ka.
      2:{ exfalso. exact (Hta Ka). }
      zs. zs. if_cases Kp; zify_cond Kp; unwrapK Kp; fixp HC Kp.
      + (* [comment removed for export] *) zs. rewrite sx32_lit by lia. zs. if_cases Ke; zify_cond Ke; unwrapK Ke.
        * (* [comment removed for export] *) goF70 0%Z prefix HC Hzb.
        * zs. zs. zs. zs. fixa122. goF70 122%Z prefix HC Hzb.
      + (* [comment removed for export] *)
        zs. zs. rewrite sx32_lit by lia. zs. if_cases Ke; zify_cond Ke; unwrapK Ke.
        * goF70 0%Z prefix HC Hzb.
        * zs. zs. zs. zs. fixa122. goF70 122%Z prefix HC Hzb.
    - (* [comment removed for export] *)
      assert (Eynz : ynz = true) by (unfold ynz; destruct (Z.eqb_spec (f128_le y2 F128_ZERO) 0); [exfalso; exact (Kz ltac:(assumption)) | reflexivity]).
      rewrite Eynz in HC, Hzb, He2b. clearbody ynz. cbv beta iota in HC. cbv beta iota in Hzb. cbv beta iota in He2b.
      assert (PDk : forall p1 e2, p1 = (if p <? 0 then 6 else p)%Z -> e2 = (e0 - 29)%Z -> prov_D (f128_mul y2 (f128_of_d D_0x1p28)) e2 p1).
      { intros p1' e2' -> ->. exists y2, e0. split; [exact PC2|]. cbv zeta.
        destruct (Z.eqb_spec (f128_le y2 F128_ZERO) 0); [exfalso; exact (Kz ltac:(assumption))|]. cbn [negb].
        repeat split; first [reflexivity | lia]. }
      replace (e0 - 1 - 28)%Z with (e0 - 29)%Z in HC, Hzb by lia.
      zs. zs. rewrite sx32_lit by lia. zs. zs. zs. zs. zs. if_cases Ka; zify_cond Ka.
      { exfalso. exact (Hta Ka). }
      zs. zs. if_cases Kp; zify_cond Kp; unwrapK Kp; fixp HC Kp.
      + (* [comment removed for export] *) zs. zs. zs. call SPEC_extenddftf2_callv. 1:{ hyp. } 1:{ unfold D_0x1p28; lia. }
        zs. zs. zs. zs.
        destruct (stk_split img_segs _ _ (bv_unsigned sp + -1056 - 80) _ ST ltac:(lia)) as [STlo STf]. clear ST.
        zs. call SPEC_multf3_callq. 1:{ exact STf. } 1:{ hyp. } 1:{ lia. }
        match goal with X : stk _ _ (bv_unsigned sp + -1056 - 80)%Z _ |- _ =>
          pose proof (stk_merge img_segs _ _ _ _ STlo X ltac:(lia)) as ST; clear STlo X end.
        fold D_0x1p28. set (y3 := f128_mul y2 (f128_of_d D_0x1p28)) in *.
        pose proof (lo64_range y3) as R3lo. pose proof (hi64_range y3) as R3hi.
        zs. zs. zs.
        replace (Z_to_bv 64 (bv_swrap 32 (Z.land e0 18446744073709551615 + -29))) with (Z_to_bv 64 (e0 - 29))
          by (f_equal; rewrite land_W64, swrap32_eq; change (2^64)%Z with 18446744073709551616%Z; mlia).
        zs. zs. if_cases Ke; zify_cond Ke; unwrapK Ke.
        * (* [comment removed for export] *) zs. zs. zs. zs. fixa122. goF70 122%Z prefix HC Hzb.
        * zs. goF70 0%Z prefix HC Hzb.
      + zs. zs. zs. zs. call SPEC_extenddftf2_callv. 1:{ hyp. } 1:{ unfold D_0x1p28; lia. }
        zs. zs. zs. zs.
        destruct (stk_split img_segs _ _ (bv_unsigned sp + -1056 - 80) _ ST ltac:(lia)) as [STlo STf]. clear ST.
        zs. call SPEC_multf3_callq. 1:{ exact STf. } 1:{ hyp. } 1:{ lia. }
        match goal with X : stk _ _ (bv_unsigned sp + -1056 - 80)%Z _ |- _ =>
          pose proof (stk_merge img_segs _ _ _ _ STlo X ltac:(lia)) as ST; clear STlo X end.
        fold D_0x1p28. set (y3 := f128_mul y2 (f128_of_d D_0x1p28)) in *.
        pose proof (lo64_range y3) as R3lo. pose proof (hi64_range y3) as R3hi.
        zs. zs. zs.
        replace (Z_to_bv 64 (bv_swrap 32 (Z.land e0 18446744073709551615 + -29))) with (Z_to_bv 64 (e0 - 29))
          by (f_equal; rewrite land_W64, swrap32_eq; change (2^64)%Z with 18446744073709551616%Z; mlia).
        zs. zs. if_cases Ke; zify_cond Ke; unwrapK Ke.
        * zs. zs. zs. zs. fixa122. goF70 122%Z prefix HC Hzb.
        * zs. goF70 0%Z prefix HC Hzb.
  Qed.

End FmtFp.

End Img.
