(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Sf_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Arr.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim SoftFloat FmtFp.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Sf_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import FmtFp_split FmtFp_splitR FmtFp_splitH FmtFp_facts FmtFp_facts2.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import F_pad F_frexpl F_divtf3_main F_fmt_fp_lib F_fmt_fp_calls F_fmt_fp_pre F_fmt_fp_pre2 F_fmt_fp_pre3 F_fmt_fp_pre4.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import F_memset F_memcpy F_fwritex.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Fe_icalls.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import R_m2s I_consts. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import F_achk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_chunks_extra_wfile m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= transport_call_extra_wfile segs W m m' MU WM.
Local Ltac lia ::= lia3.
Local Ltac mlia ::= first [ lia | Z.div_mod_to_equations; lia ].

Section FmtFp.
  Variables (ra sp gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
            (ya yb fw : word)
            (F : bvmap 5 word) (m0 : word -> option byte)
            (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (junk0 : list byte) (canary : word)
            (w p fl t : Z) (o0 o1 : list Z) (ret : Z).
  Definition yv : Z := (bv_unsigned ya + 2^64 * bv_unsigned yb)%Z.
  Definition Fp : Z := bv_unsigned fw.
  Definition usp : Z := bv_unsigned sp.

  Hypothesis HM : fmt_fp o0 yv w p fl t = Some (o1, ret).
  Hypothesis SPLO : (5152 <= bv_unsigned sp)%Z.
  Hypothesis SPHI : (bv_unsigned sp < 2^63)%Z.
  Hypothesis GLO : (7110320 <= bv_unsigned sp - 6944)%Z.
  Hypothesis AF : (bv_unsigned sp <= Fp)%Z.
  Hypothesis AB : (bv_unsigned sp <= B)%Z.
  Hypothesis Hw : (-2^31 <= w <= 1)%Z.
  Hypothesis Hp : (-2^31 <= p < 2^20)%Z.
  Hypothesis Hfl : (0 <= fl < 2^32)%Z.
  Hypothesis Ht : (0 <= t < 256)%Z.
  Hypothesis Hta : Z.lor t 32 <> 97%Z.

  Hypothesis YN0 : Z.land (Z.shiftr (hi64 yv) 48) 0x7fff <> 0%Z \/ f128_le yv F128_ZERO = 0%Z.
  Hypothesis YN1 : Z.land (Z.shiftr (hi64 (Z.lxor yv F128_SIGNBIT)) 48) 0x7fff <> 0%Z \/ f128_le (Z.lxor yv F128_SIGNBIT) F128_ZERO = 0%Z.

  Hypothesis DIGB : dig_words_fact yv fl.
  Hypothesis E2B : e2_range_fact yv fl.
  Hypothesis DNB0 : dn_phase_fact yv fl p t.

  Hypothesis WBA0 : words_all_fact yv fl p t.
  Hypothesis CAR0 : carry_fact yv fl p t.
  Hypothesis AZR0 : azr_fact yv fl p t.
  Hypothesis BLA0 : below_a_fact yv fl p t.

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
  Proof using WBA0.
    intros y1 fr e0 y e2 b' z' y' s big a z e2' HY HFR HD HDG HU HDN i _.
    apply (WBA0 (if p <? 0 then 6 else p)%Z (if e2 <? 0 then 0 else 122)%Z big a z).
    exists y1, fr, e0, y, e2, b', z', y', s, e2'.
    split; [exact HY|]. split; [exact HFR|]. split; [exact HD|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact HDG|]. split; [exact HU|]. exact HDN.
  Qed.
  Hypothesis ROOM : (Z.of_nat (length o1) <= Z.of_nat (length o0) + Z.of_nat (length junk0))%Z.
  Hypothesis J256 : (length junk0 < 256)%nat.

  Definition SBN : Z := (Z.of_nat (length o0) + Z.of_nat (length junk0))%Z.
  Hypothesis RIP : rip_stmt.
  Hypothesis FXI : ifrexpl_stmt.
  Hypothesis HA0 : fext m0 (bv_unsigned sp - 6944) (bv_unsigned sp) B SBN Fp.

  Definition prov_C2 (y2 e0 : Z) : Prop :=
    exists y1 fr, fst (fst (ffp_sign yv fl)) = y1 /\ frexpl FREXPL_FUEL y1 0 = Some (fr, e0) /\ y2 = f128_mul fr (f128_of_i32 2).
  Definition prov_D (y e2 p1 : Z) : Prop :=
    exists y2 e0, prov_C2 y2 e0 /\
      (let ynz := negb (f128_le y2 F128_ZERO =? 0) in
       y = (if ynz then f128_mul y2 (f128_of_d D_0x1p28) else y2) /\ e2 = (if ynz then e0 - 1 - 28 else e0)%Z
       /\ p1 = (if p <? 0 then 6 else p)%Z).

  Definition prov_E (p1 : Z) (big : list Z) (r z e2 : Z) : Prop :=
    exists y y', prov_D y e2 p1 /\ r = (if e2 <? 0 then 0 else 122)%Z /\ fmt_fp_dig DIG_FUEL (zrepeat 0 128, r, y) = Some (big, z, y').

  Definition prov_F (p1 r : Z) (s : list Z * Z * Z * Z) : Prop :=
    exists big z e2, prov_E p1 big r z e2 /\ fmt_fp_up UP_FUEL (big, r, z, e2) = Some s.

  Definition prov_G (p1 r : Z) (s : list Z * Z * Z * Z) : Prop :=
    exists s0, prov_F p1 r s0 /\ fmt_fp_dn DN_FUEL p1 t r s0 = Some s.

  Definition prov_R (p1 prefix pl r : Z) (big : list Z) (a z e : Z) : Prop :=
    exists big0 a0 z0 e2' e0, prov_G p1 r (big0, a0, z0, e2') /\ ffp_e big0 a0 r z0 = Some e0 /\
      ffp_R t p1 prefix pl big0 a0 r z0 e0 (ffp_j t p1 e0) = Some (big, a, z, e).

  Lemma WB : forall p1 r big a z e2, prov_G p1 r (big, a, z, e2) -> forall i, (a <= i < z)%Z -> (0 <= znth big i < 1000000000)%Z.
  Proof using WBA0.
    intros p1 r big a z e2' (s0 & (bg & zz & e2 & (y & y' & (y2 & e0 & (y1 & fr & HY & HFR & Hy2) & HD) & Hr & HDG) & HU) & HDN).
    cbv zeta in HD. destruct HD as (Hy & He2 & Hp1). subst y2. subst p1 r.
    exact (WB0 y1 fr e0 y e2 bg zz y' s0 big a z e2' HY HFR (conj Hy He2) HDG HU HDN).
  Qed.

  Lemma provG_run : forall p1 r big a z e2, prov_G p1 r (big, a, z, e2) -> run_to_dn yv fl p t p1 r big a z.
  Proof using .
    intros p1 r big a z e2' (s0 & (bg & zz & e2 & (y & y' & (y2 & e0 & (y1 & fr & HY & HFR & Hy2) & HD) & Hr & HDG) & HU) & HDN).
    cbv zeta in HD. destruct HD as (Hy & He2 & Hp1). subst y2.
    exists y1, fr, e0, y, e2, bg, zz, y', s0, e2'.
    split; [exact HY|]. split; [exact HFR|]. split; [split; [exact Hy | exact He2]|]. split; [exact Hp1|]. split; [exact Hr|].
    subst r. split; [exact HDG|]. split; [exact HU|]. subst p1. exact HDN.
  Qed.
  Lemma WBA : forall p1 r big a z e2, prov_G p1 r (big, a, z, e2) -> forall i, (0 <= znth big i < 1000000000)%Z.
  Proof using WBA0. intros p1 r big a z e2 PG. exact (WBA0 _ _ _ _ _ (provG_run _ _ _ _ _ _ PG)). Qed.
  Lemma CAR : forall p1 prefix pl r big a z e, prov_R p1 prefix pl r big a z e -> (0 <= a)%Z.
  Proof using CAR0.
    intros p1 prefix pl r big a z e (big0 & a0 & z0 & e2' & e0 & PG & He & HR).
    exact (CAR0 _ _ _ _ _ (provG_run _ _ _ _ _ _ PG) _ _ _ _ _ _ _ He HR).
  Qed.
  Lemma AZR : forall p1 prefix pl r big a z e zS, prov_R p1 prefix pl r big a z e ->
    fmt_fp_strip BIG_FUEL big a z = Some zS -> Z.lor t 32 <> CHR_f -> (zS <= a)%Z -> a = r.
  Proof using AZR0.
    intros p1 prefix pl r big a z e zS (big0 & a0 & z0 & e2' & e0 & PG & He & HR) HS Htf Hza.
    exact (AZR0 _ _ _ _ _ (provG_run _ _ _ _ _ _ PG) _ _ _ _ _ _ _ _ He HR HS Htf Hza).
  Qed.

  Lemma BLA : forall p1 r big a z e2, prov_G p1 r (big, a, z, e2) -> forall k, (0 <= k < a)%Z -> znth big k = 0%Z.
  Proof using BLA0. intros p1 r big a z e2 PG. exact (BLA0 _ _ _ _ _ (provG_run _ _ _ _ _ _ PG)). Qed.

  Lemma DNB : forall p1 r s, prov_F p1 r s -> dn_good p1 t r s.
  Proof using DNB0.
    intros p1 r s (big & z & e2 & (y & y' & (y2 & e0 & (y1 & fr & HY & HFR & Hy2) & HD) & Hr & HDG) & HU).
    cbv zeta in HD. destruct HD as (Hy & He2 & Hp1). subst y2. subst p1 r.
    exact (DNB0 y1 fr e0 y e2 big z y' s HY HFR (conj Hy He2) HDG HU).
  Qed.

  Definition ctx_all : unit :=
    let _ := (ra, sp, gp, tp, s0e, s1e, s2e, s3e, s4e, s5e, s6e, s7e, s8e, s9e, s10e, s11e, ya, yb, fw, F, m0,
              fl0, j1, j2, lbfw, B, junk0, canary, w, p, fl, t, o0, o1, ret) in tt.

  Definition Wfp : list (Z * Z) :=
    [(bv_unsigned sp - 6944, bv_unsigned sp);
     (B + Z.of_nat (length o0), B + Z.of_nat (length o1));
     (Fp + 40, Fp + 48)]%Z.

  Definition fmt_fp_post (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Ft fc' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 ret) a1 a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ munch Wfp m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ frm0 fc'
      /\ stk asegs m' (bv_unsigned sp - 6944) (bv_unsigned sp)
      /\ wfile m' Fp fl0 j1 j2 lbfw B (zb o1) (skipn (length o1 - length o0) junk0)
      /\ ssp_cells m' canary
      /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k).

  Definition hi_cells (pad256 : list byte) : list cell :=
    [CB 256 pad256; C8 canary; C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra].

  Definition finv (m : word -> option byte) (pad256 : list byte) : Prop :=
    mem_inv asegs m /\ munch Wfp m0 m /\ wmono asegs m0 m
    /\ rw_cells asegs m (bv_unsigned sp + -368) (hi_cells pad256)
    /\ stk asegs m (bv_unsigned sp - 6944) (bv_unsigned sp + -1056)
    /\ ro_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ ro_cells asegs m ssp_guard [C8 canary].
  Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
    let ST := fresh "ST" in let GOT := fresh "GOT" in let SSP := fresh "SSP" in
    destruct H as (MI & MU & WM & FRhi & ST & GOT & SSP); unfold Wfp in MU; unfold hi_cells in FRhi; unfold got_ssp, ssp_guard in GOT, SSP.
  Ltac mk_finv := unfold finv, Wfp, hi_cells, got_ssp, ssp_guard;
    split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | idtac]|]; split; hyp.

  Ltac dest_wfile H := let FC := fresh "FC" in let BUF := fresh "BUF" in let FLG := fresh "FLG" in let LBF := fresh "LBF" in
    let Bpos := fresh "Bpos" in let Bhi := fresh "Bhi" in let SEPfb := fresh "SEPfb" in
    destruct H as (FC & BUF & FLG & LBF & Bpos & Bhi & SEPfb); unfold FILE_cells in FC.
  Ltac mk_wfile := unfold wfile, FILE_cells; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [lia|]; split; lia.

  Lemma Wfp_high : Forall (fun iv => kHighShadowEnd + 8 <= fst iv)%Z Wfp.
  Proof using HA0 AB AF.
    try clear HM; try clear SPLO; try clear SPHI; try clear GLO; try clear Hw; try clear Hp; try clear Hfl; try clear Ht; try clear Hta; try clear YN0; try clear YN1; try clear DIGB; try clear E2B; try clear DNB0; try clear WBA0; try clear CAR0; try clear AZR0; try clear BLA0; try clear J256; try clear RIP; try clear FXI; try clear ROOM; idtac.
    pose proof (fext_hsh _ _ _ _ _ _ HA0) as HSH. unfold Wfp, Fp in *.
    constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor.
  Qed.
  Lemma Wfp_wend : Forall (fun iv => snd iv <= Fp + 32 \/ Fp + 32 + 8 <= fst iv)%Z Wfp.
  Proof using HA0 AF ROOM.
    try clear HM; try clear SPLO; try clear SPHI; try clear GLO; try clear Hw; try clear Hp; try clear Hfl; try clear Ht; try clear Hta; try clear YN0; try clear YN1; try clear DIGB; try clear E2B; try clear DNB0; try clear WBA0; try clear CAR0; try clear AZR0; try clear BLA0; try clear J256; try clear RIP; try clear FXI; try clear AB; idtac.
    destruct HA0 as (_ & _ & _ & _ & _ & _ & _ & SEP0 & _). unfold Wfp, SBN, Fp in *.
    constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor.
  Qed.
  Local Notation fwritex_callR := (fwritex_callRA RIP Wfp m0 (bv_unsigned sp - 6944)%Z (bv_unsigned sp) SBN Fp B Wfp_high Wfp_wend HA0).
  Local Notation pad_callR := (pad_callRA RIP Wfp m0 (bv_unsigned sp - 6944)%Z (bv_unsigned sp) SBN Fp B Wfp_high Wfp_wend HA0).
  Local Notation frexpl_callq := (frexpl_callqA FXI).
  Ltac solve_MU := match goal with H : munch _ m0 _ |- _ => exact H end.
  Ltac solve_WM := match goal with H : wmono _ m0 _ |- _ => exact H end.

  Ltac chk_src :=
    first [ apply (fext_stack _ _ _ _ _ _ _ _ HA0); lia
          | let R := fresh "ROD" in pose proof (fext_rod _ _ _ _ _ _ HA0) as R;
            let R1 := fresh in let R2 := fresh in let R3 := fresh in let R4 := fresh in let R5 := fresh in let R6 := fresh in
            destruct R as (R1 & R2 & R3 & R4 & R5 & R6);
            first [ eapply (chkr_sub _ _ _ _ _ R1); lia | eapply (chkr_sub _ _ _ _ _ R2); lia | eapply (chkr_sub _ _ _ _ _ R3); lia
                  | eapply (chkr_sub _ _ _ _ _ R4); lia | eapply (chkr_sub _ _ _ _ _ R5); lia | eapply (chkr_sub _ _ _ _ _ R6); lia ] ].

  Ltac chk_cur := eapply (chkr_high Wfp m0); [ chk_src | solve_MU | exact Wfp_high ].
  Ltac ictx_cur := eapply (ictx_high Wfp m0); [ exact (proj1 (proj2 HA0)) | solve_MU | solve_WM | exact Wfp_high ].
  Ltac hshq := pose proof (fext_hsh _ _ _ _ _ _ HA0); lia.
  Ltac ifx_cur := eapply (ifx_high Wfp m0); [ exact (fext_ifx _ _ _ _ _ _ HA0) | solve_MU | exact Wfp_high ].

  Definition midv (K : midK) (m : word -> option byte) (fc : bv 32) (e2m : Z) : Prop :=
    finv m (K_pad K) /\ frm0 fc /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get (K_Ft K) k = reg_get F k)
    /\ rw_cells asegs m (bv_unsigned sp + -544)
         [C8 (Z_to_bv 64 0); CB 40 (K_jk40 K); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t); CB 8 (K_jk8 K); C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 7110312);
          C8 (Z_to_bv 64 (K_plz K)); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)]
    /\ rw_cells asegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 e2m); CB 3 (K_jk3 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ K_plz K = Z.b2z (K_pl K =? 0)%Z /\ K_pfx K = (81734 + K_prefix K)%Z
    /\ (0 <= K_p1 K < 2^20)%Z.
  Ltac dest_midv H :=
    let FI := fresh "FI" in let FRM := fresh "FRM" in let HFt := fresh "HFt" in let FRs := fresh "FRs" in let E2 := fresh "E2" in
    let EB := fresh "EB" in let BF := fresh "BF" in let WF := fresh "WF" in
    let Hpre := fresh "Hpre" in let Hpl := fresh "Hpl" in let Hplz := fresh "Hplz" in let Hpfx := fresh "Hpfx" in let Hp1 := fresh "Hp1" in
    destruct H as (FI & FRM & HFt & FRs & E2 & EB & BF & WF & Hpre & Hpl & Hplz & Hpfx & Hp1);
    cbn [K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft] in *;
    dest_finv FI; dest_wfile WF.
  Ltac mk_midv := unfold midv; cbn [K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft];
    split; [mk_finv|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | mk_wfile]|];
    split; [dlia|]; split; [dlia|]; split; [hyp|]; split; [hyp|]; dlia.

  Ltac dest_midv2 H :=
    let FI := fresh "FI" in let FRM := fresh "FRM" in let HFt := fresh "HFt" in let FRs := fresh "FRs" in let E2 := fresh "E2" in
    let EB := fresh "EB" in let BF := fresh "BF" in let WF := fresh "WF" in
    let Hpre := fresh "Hpre" in let Hpl := fresh "Hpl" in let Hplz := fresh "Hplz" in let Hpfx := fresh "Hpfx" in let Hp1 := fresh "Hp1" in
    destruct H as (FI & FRM & HFt & FRs & E2 & EB & BF & WF & Hpre & Hpl & Hplz & Hpfx & Hp1);
    cbn [K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft] in *;
    dest_finv FI.

  Definition midw (K : midK) (m : word -> option byte) (fc : bv 32) (e2m : Z) : Prop :=
    finv m (K_pad K) /\ frm0 fc /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get (K_Ft K) k = reg_get F k)
    /\ rw_cells asegs m (bv_unsigned sp + -544)
         [C8 (Z_to_bv 64 0); CB 40 (K_jk40 K); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t); CB 8 (K_jk8 K); C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 7110312);
          C8 (Z_to_bv 64 (K_plz K)); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)]
    /\ rw_cells asegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 e2m); CB 3 (K_jk3 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ (0 <= K_plz K < 2^64)%Z /\ K_pfx K = (81734 + K_prefix K)%Z
    /\ (0 <= K_p1 K < 2^20)%Z.
  Lemma midv_w : forall K m fc e2m, midv K m fc e2m -> midw K m fc e2m.
  Proof using Hfl Ht J256 RIP FXI HA0 AB AF ROOM.
    intros K m fc e2m H. destruct H as (FI & FRM & HFt & FRs & E2 & EB & BF & WF & Hpre & Hpl & Hplz & Hpfx & Hp1).
    unfold midw. split; [exact FI|]. split; [exact FRM|]. split; [exact HFt|]. split; [exact FRs|]. split; [exact E2|].
    split; [exact EB|]. split; [exact BF|]. split; [exact WF|]. split; [exact Hpre|]. split; [exact Hpl|].
    split. { rewrite Hplz. destruct (K_pl K =? 0); cbn; lia. } split; [exact Hpfx | exact Hp1].
  Qed.
  Ltac dest_midw2 H :=
    let FI := fresh "FI" in let FRM := fresh "FRM" in let HFt := fresh "HFt" in let FRs := fresh "FRs" in let E2 := fresh "E2" in
    let EB := fresh "EB" in let BF := fresh "BF" in let WF := fresh "WF" in
    let Hpre := fresh "Hpre" in let Hpl := fresh "Hpl" in let Hplz := fresh "Hplz" in let Hpfx := fresh "Hpfx" in let Hp1 := fresh "Hp1" in
    destruct H as (FI & FRM & HFt & FRs & E2 & EB & BF & WF & Hpre & Hpl & Hplz & Hpfx & Hp1);
    cbn [K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft] in *;
    dest_finv FI.
  Ltac dest_midw H := dest_midw2 H; match goal with WF : wfile _ _ _ _ _ _ _ _ _ |- _ => dest_wfile WF end.
  Ltac mk_midw := first [ apply midv_w; mk_midv |
    unfold midw; cbn [K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft];
    split; [mk_finv|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | mk_wfile]|];
    split; [dlia|]; split; [dlia|]; split; [dlia|]; split; [hyp|]; dlia ].

  Definition midq (K : midK) (cs5 : list cell) (z456 : Z) (m : word -> option byte) (fc : bv 32) : Prop :=
    finv m (K_pad K) /\ frm0 fc /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get (K_Ft K) k = reg_get F k)
    /\ rw_cells asegs m (bv_unsigned sp + -544)
         ([C8 (Z_to_bv 64 0)] ++ cs5 ++ [C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t); C8 (Z_to_bv 64 (K_p1 K)); C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 7110312);
          C8 (Z_to_bv 64 z456); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)])
    /\ rw_cells asegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 0); CB 3 (K_jk3 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ (0 <= z456 < 2^64)%Z /\ K_pfx K = (81734 + K_prefix K)%Z
    /\ (0 <= K_p1 K < 2^20)%Z.
  Ltac dest_midq2 H :=
    let FI := fresh "FI" in let FRM := fresh "FRM" in let HFt := fresh "HFt" in let FRs := fresh "FRs" in let E2 := fresh "E2" in
    let EB := fresh "EB" in let BF := fresh "BF" in let WF := fresh "WF" in
    let Hpre := fresh "Hpre" in let Hpl := fresh "Hpl" in let Hplz := fresh "H456" in let Hpfx := fresh "Hpfx" in let Hp1 := fresh "Hp1" in
    destruct H as (FI & FRM & HFt & FRs & E2 & EB & BF & WF & Hpre & Hpl & Hplz & Hpfx & Hp1);
    cbn [app K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft] in *;
    dest_finv FI.
  Ltac dest_midq H := dest_midq2 H; match goal with WF : wfile _ _ _ _ _ _ _ _ _ |- _ => dest_wfile WF end.
  Ltac mk_midq :=
    unfold midq; cbn [app K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft];
    split; [mk_finv|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | mk_wfile]|];
    split; [dlia|]; split; [dlia|]; split; [dlia|]; split; [hyp|]; dlia.

  Definition midq_K (K : midK) (cs5 : list cell) (z456 : Z) : midK :=
    MidK (K_pad K) (cells_bytes cs5) (le8 (Z_to_bv 64 (K_p1 K))) (K_jk3 K) (K_jk12 K) (K_jk37 K) (K_p1 K) (K_prefix K) (K_pl K) z456 (K_pfx K) (K_Ft K).
  Lemma midq_w : forall K cs5 z456 m fc, midq K cs5 z456 m fc -> cells_size cs5 = 40%nat -> midw (midq_K K cs5 z456) m fc 0%Z.
  Proof using .
    intros K cs5 z456 m fc H Hsz. destruct H as (FI & FRM & HFt & FRs & E2 & EB & BF & WF & Hpre & Hpl & Hplz & Hpfx & Hp1).
    unfold midw, midq_K. cbn [K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft].
    split; [exact FI|]. split; [exact FRM|]. split; [exact HFt|]. split.
    { apply (rw_cells_merge asegs m _ [C8 (Z_to_bv 64 0)] cs5) in FRs. rewrite Hsz in FRs.
      apply (rw_cells_merge asegs m _ [C8 (Z_to_bv 64 0); CB 40 (cells_bytes cs5); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t)] [C8 (Z_to_bv 64 (K_p1 K))]
               [C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 7110312); C8 (Z_to_bv 64 z456); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)]) in FRs.
      cbn [cells_size csize cells_bytes cbytes app Nat.add] in FRs. rewrite app_nil_r in FRs. exact FRs. }
    split; [exact E2|]. split; [exact EB|]. split; [exact BF|]. split; [exact WF|].
    split; [exact Hpre|]. split; [exact Hpl|]. split; [exact Hplz|]. split; [exact Hpfx|]. exact Hp1.
  Qed.

  Definition emw (K : midK) (estrp ppl fl2 a8v v440 : Z) (oc : list Z) (m : word -> option byte) (fc : bv 32) : Prop :=
    finv m (K_pad K) /\ frm0 fc /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get (K_Ft K) k = reg_get F k)
    /\ rw_cells asegs m (bv_unsigned sp + -544)
         [C8 (Z_to_bv 64 0); CB 40 (K_jk40 K); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 estrp); C8 (Z_to_bv 64 ppl); C8 (Z_to_bv 64 fl2); C8 (Z_to_bv 64 7110312);
          C8 (Z_to_bv 64 a8v); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 v440); C8 (Z_to_bv 64 Fp)]
    /\ rw_cells asegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 0); CB 3 (K_jk3 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb oc) (skipn (length oc - length o0) junk0)
    /\ (length o0 <= length oc)%nat
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ K_pfx K = (81734 + K_prefix K)%Z /\ (0 <= K_p1 K < 2^20)%Z.
  Ltac dest_emw2 H :=
    let FI := fresh "FI" in let FRM := fresh "FRM" in let HFt := fresh "HFt" in let FRs := fresh "FRs" in let E2 := fresh "E2" in
    let EB := fresh "EB" in let BF := fresh "BF" in let WF := fresh "WF" in let LOC := fresh "LOC" in
    let Hpre := fresh "Hpre" in let Hpl := fresh "Hpl" in let Hpfx := fresh "Hpfx" in let Hp1 := fresh "Hp1" in
    destruct H as (FI & FRM & HFt & FRs & E2 & EB & BF & WF & LOC & Hpre & Hpl & Hpfx & Hp1);
    cbn [K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft] in *;
    dest_finv FI.
  Ltac dest_emw H := dest_emw2 H; match goal with WF : wfile _ _ _ _ _ _ _ _ _ |- _ => dest_wfile WF end.
  Ltac mk_emw :=
    unfold emw; cbn [K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft];
    split; [mk_finv|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | mk_wfile]|];
    split; [first [hyp | dlia | rewrite ?app_length; dlia]|]; split; [dlia|]; split; [dlia|]; split; [first [hyp|dlia]|]; dlia.

  Ltac prune := try clear HM; try clear YN0; try clear YN1.

  Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

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

  Hypothesis L_0bc :
    forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x25 x26 x28 x29 x30 x31 : word) fc K
      (ws : list word) (big : list Z) (lo a r rp z zm : Z),
    midv K m fc 0%Z ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (lo <= i < zm)%Z -> znth big i = wval ws i) ->
    (forall i, (zm <= i)%Z -> znth big i = 0%Z) ->
    (0 <= lo <= a)%Z -> (lo <= r)%Z -> (a <= zm)%Z -> (0 <= z <= zm)%Z -> (zm <= 128)%Z -> (r < zm)%Z -> (r = 0 \/ r = 122)%Z -> rp = (bv_unsigned sp + -1056 + 4 * r)%Z ->
    prov_G (K_p1 K) r (big, a, z, 0%Z) ->
    ffp_G o0 w fl t (K_p1 K) (K_prefix K) (K_pl K) big a r z = Some (o1, ret) ->
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (K_p1 K)) x19 (Z_to_bv 64 (Z.lor t 32)) x21 (Z_to_bv 64 rp)
               x23 x24 x25 x26 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x28 x29 x30 x31)
          (K_Ft K) (Z_to_bv 64 0x15550c) fc None m (seg_rom asegs)).

  Lemma L_dnin : forall (k : nat) m (x1 x7 x9 x10 x11 x12 x13 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word) fc K
      (ws : list word) (big big' : list Z) (e2m sh msk q9 lo zm d z c c' : Z),
    midv K m fc e2m ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (lo <= i < zm)%Z -> znth big i = wval ws i) ->
    (forall i, (zm <= i)%Z -> znth big i = 0%Z) ->
    (0 <= lo <= d)%Z -> (d < z)%Z -> (z <= zm <= 128)%Z -> (1 <= sh <= 9)%Z -> msk = (2^sh - 1)%Z -> q9 = Z.shiftr 1000000000 sh ->
    (0 <= c < 1000000000)%Z ->
    fmt_fp_dn_inner sh k z (big, d, c) = Some (big', z, c') ->
    (forall m' ws' (x7' x28' : word),
       midv K m' fc e2m ->
       u32arr asegs m' (bv_unsigned sp + -1056) ws' -> length ws' = 128%nat ->
       length big' = 128%nat -> (forall i, (lo <= i < zm)%Z -> znth big' i = wval ws' i) ->
       (forall i, (zm <= i)%Z -> znth big' i = 0%Z) ->
       (0 <= c' < 1000000000)%Z ->
       evt asegs POST
         (MS (mkR x1 SPv gp tp (Z_to_bv 64 q9) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x7' sp x9 x10 x11 x12 x13 x14
                  (Z_to_bv 64 sh) (Z_to_bv 64 c') (Z_to_bv 64 msk) x18 x19 x20 x21 x22 x23 x24 x25 x26
                  (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x28' x29 x30 x31)
             (K_Ft K) (Z_to_bv 64 0x15568c) fc None m' (seg_rom asegs))) ->
    evt asegs POST
      (MS (mkR x1 SPv gp tp (Z_to_bv 64 q9) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d)) x7 sp x9 x10 x11 x12 x13 x14
               (Z_to_bv 64 sh) (Z_to_bv 64 c) (Z_to_bv 64 msk) x18 x19 x20 x21 x22 x23 x24 x25 x26
               (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x28 x29 x30 x31)
          (K_Ft K) (Z_to_bv 64 0x15566c) fc None m (seg_rom asegs)).
  Proof using AB AF GLO J256 SPHI SPLO RIP FXI HA0 ROOM.
    induction k as [|k IH]; intros until c'; intros MV BIG LW LB REL ZERO Hlo Hdz Hzm Hsh Hmsk Hq9 Hc HI CONT; [discriminate HI|].
    destruct K as [pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft]. dest_midv2 MV. prune.
    pose proof (zr_word sp : (0 <= bv_unsigned sp < 2^64)%Z) as Rsp.
    assert (Rfw : (0 <= Fp < 2^64)%Z) by apply (zr_word fw).
    rewrite fmt_fp_dn_inner_step in HI. rewrite (proj2 (Z.ltb_lt d z)) in HI by lia.
    pose proof (wval_range ws d) as Rv. rewrite <- (REL d) in Rv by lia.
    pose proof (pow2_sh_range sh Hsh) as Rp. assert (Rmsk : (0 <= msk < 512)%Z) by lia.
    pose proof (q9_range sh Hsh) as [Rq1 Rq2]. rewrite <- Hq9 in Rq1, Rq2.
    assert (Rq9 : (0 < q9 <= 500000000)%Z) by nia. clear Rq2.
    destruct (dn_carry_eq (znth big d) sh ltac:(lia) Hsh) as [Ec Rc]. rewrite Ec, <- Hq9 in HI. rewrite <- Hq9 in Rc. clear Ec.
    pose proof (shr_small_range (znth big d) sh Rv Hsh) as Rs.
    unfold u32 in HI. rewrite (Z.mod_small (Z.shiftr (znth big d) sh + c)) in HI by lia.
    pose proof (u32arr_read asegs _ _ _ d _ _ BIG (nth_error_wnth ws d ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
    zs. zs.
    replace (Z.land (bv_unsigned (sx32 (wnth ws d))) msk) with ((znth big d) mod 2^sh)%Z
      by (rewrite Hmsk, land_sx32_mask by lia; fold (wval ws d); rewrite (REL d) by lia; reflexivity).
    pose proof (Z.mod_pos_bound (znth big d) (2^sh) ltac:(lia)) as Rrm.
    set (rm := ((znth big d) mod 2^sh)%Z) in *.
    zs. rewrite ?(land_W64_small sh) by lia. rewrite ?(Z.mod_small sh 32) by lia.
    rewrite wrap32_sx32. fold (wval ws d). rewrite <- (REL d) by lia. rewrite swrap32_shr_small by lia.
    zs.
    set (x := (Z.shiftr (znth big d) sh + c)%Z) in *.
    pose proof (u32arr_store_ok asegs _ _ _ d _ BIG ltac:(lia) eq_refl) as SOK.
    zs.
    pose proof (u32arr_write asegs _ _ _ d (Z_to_bv 64 x) BIG ltac:(lia)) as BIG'. clear BIG.
    store_done. rename BIG' into BIG.
    assert (REL' : forall i, (lo <= i < zm)%Z -> znth (zupd big d x) i = wval (upd ws (Z.to_nat d) (Z_to_bv 64 x)) i).
    { intros i Hi. destruct (Z.eq_dec i d) as [->|Hne].
      - rewrite znth_zupd_eq by (unfold zlength; lia). rewrite wval_upd_same by lia. rewrite unsigned_lit by lia.
        symmetry. apply Z.mod_small. lia.
      - rewrite znth_zupd_neq by lia. rewrite wval_upd_other by lia. apply REL. lia. }
    assert (ZERO' : forall i, (zm <= i)%Z -> znth (zupd big d x) i = 0%Z).
    { intros i Hi. rewrite znth_zupd_neq by lia. apply ZERO. lia. }
    zs. replace (bv_unsigned sp + -1056 + 4 * d + 4)%Z with (bv_unsigned sp + -1056 + 4 * (d + 1))%Z by lia.
    zs.
    replace (bv_swrap 32 (rm * q9)) with (rm * q9)%Z
      by (pose proof Rc as Rc2; set (X := (rm * q9)%Z) in *; clearbody X; rewrite swrap32_eq; mlia).
    zs. if_cases Kd; zify_cond Kd.
    -
      eapply IH with (lo := lo) (zm := zm) (K := MidK pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft);
        [ mk_midv | exact BIG | rewrite upd_length; exact LW | rewrite zupd_length; exact LB | exact REL' | exact ZERO'
        | dlia | dlia | dlia | dlia | exact Hmsk | exact Hq9 | dlia | exact HI | exact CONT ].
    -
      destruct k as [|k']; [discriminate HI|].
      rewrite fmt_fp_dn_inner_step in HI. rewrite (proj2 (Z.ltb_ge _ _)) in HI by lia.
      injection HI as <- Hdz1 <-.
      replace (bv_unsigned sp + -1056 + 4 * (d + 1))%Z with (bv_unsigned sp + -1056 + 4 * z)%Z by lia.
      eapply CONT; [ mk_midv | exact BIG | rewrite upd_length; exact LW | rewrite zupd_length; exact LB | exact REL' | exact ZERO' | dlia ].
  Qed.

  Definition DNH (k : nat) : Prop :=
    forall m (x1 x5 x6 x7 x15 x16 x17 x21 x23 x24 x25 x26 x28 x29 x30 x31 : word) fc K
      (ws : list word) (big big' : list Z) (need e2 lo a z zm a' z' e2' : Z),
    midv K m fc e2 ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (lo <= i < zm)%Z -> znth big i = wval ws i) ->
    (forall i, (zm <= i)%Z -> znth big i = 0%Z) ->
    (-1102 <= e2 < 0)%Z -> (0 <= lo <= a)%Z -> (lo <= 0)%Z -> (z <= zm <= 128)%Z -> (0 < zm)%Z -> need = (1 + (K_p1 K + 45) / 9)%Z ->
    dn_good (K_p1 K) t 0 (big, a, z, e2) ->
    fmt_fp_dn k (K_p1 K) t 0 (big, a, z, e2) = Some (big', a', z', e2') ->
    prov_G (K_p1 K) 0 (big', a', z', e2') ->
    ffp_G o0 w fl t (K_p1 K) (K_prefix K) (K_pl K) big' a' 0 z' = Some (o1, ret) ->
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) (Z_to_bv 64 (-1)) (Z_to_bv 64 1000000000)
               (Z_to_bv 64 need) (Z_to_bv 64 102) (Z_to_bv 64 (4 * need)) x15 x16 x17
               (Z_to_bv 64 (K_p1 K)) (Z_to_bv 64 e2) (Z_to_bv 64 (Z.lor t 32)) x21 SPv
               x23 x24 x25 x26 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x28 x29 x30 x31)
          (K_Ft K) (Z_to_bv 64 0x155644) fc None m (seg_rom asegs)).

  Lemma L_dn : forall k, DNH k.
  Proof using AB AF GLO Ht Hta J256 L_0bc SPHI SPLO RIP FXI HA0 ROOM.
    induction k as [|k IH]; unfold DNH; intros until e2'; intros MV BIG LW LB REL ZERO He2 Ha Hlo0 Hzm Hzm0 Hneed DOK HDn PG HG; [discriminate HDn|].
    destruct K as [pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft]. cbn [K_p1 K_prefix K_pl K_Ft] in Hneed, DOK, HDn, PG, HG.
    dest_midv2 MV. prune. pose proof (zr_word sp : (0 <= bv_unsigned sp < 2^64)%Z) as Rsp.
    assert (Rfw : (0 <= Fp < 2^64)%Z) by apply (zr_word fw).
    destruct (dn_good_now _ _ _ _ _ _ _ DOK ltac:(lia)) as [Daz Dnz].
    rewrite fmt_fp_dn_step in HDn. rewrite (proj2 (Z.ltb_lt e2 0)) in HDn by lia.
    destruct (fmt_fp_dn_body p1 t 0 (big, a, z, e2)) as [s1|] eqn:HB; [|discriminate HDn].
    pose proof (dn_good_next _ _ _ _ _ _ _ _ DOK ltac:(lia) HB) as DOK'.
    destruct (fmt_fp_dn_body_some _ _ _ _ _ _ _ _ HB) as (bigI & dI & cI & HI & Es1). clear HB. subst s1.
    assert (Rneed : (1 <= need < 2^31)%Z) by (rewrite Hneed; mlia).
    replace (1 + u32 (p1 + LDBL_MANT_DIG / 3 + 8) / 9)%Z with need in HDn, DOK'
      by (rewrite Hneed; unfold u32, LDBL_MANT_DIG; change (113 / 3)%Z with 37%Z; rewrite Z.mod_small by lia; lia).
    set (sh := Z.min 9 (- e2)) in *. assert (Hsh : (1 <= sh <= 9)%Z) by (subst sh; lia).
    pose proof (fmt_fp_dn_inner_res _ _ _ _ _ _ _ _ _ HI ltac:(lia)) as (-> & LBI & _ & SAME). rewrite LB in LBI.
    assert (Ra1 : (a <= dn_a1 bigI a <= z /\ dn_a1 bigI a <= a + 1)%Z).
    { unfold dn_a1. destruct (Z.eqb_spec (znth bigI a) 0) as [E|E]; [|lia]. split; [|lia].
      destruct (Z.eq_dec a z) as [Eaz|]; [|lia]. exfalso. rewrite SAME in E by lia. subst z. exact (Dnz eq_refl E). }
    assert (Rz1 : (z <= snd (dn_bz bigI z cI) <= z + 1)%Z) by (unfold dn_bz; destruct (negb (cI =? 0)); cbn [snd]; lia).
    assert (LB1 : length (fst (dn_bz bigI z cI)) = 128%nat) by (unfold dn_bz; destruct (negb (cI =? 0)); cbn [fst]; rewrite ?zupd_length; exact LBI).

    assert (J268 : forall m1 ws1 (x5' x6' x7' x16' x28' : word) zm1,
      midv (MidK pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft) m1 fc e2 ->
      u32arr asegs m1 (bv_unsigned sp + -1056) ws1 -> length ws1 = 128%nat ->
      (forall i, (lo <= i < zm1)%Z -> znth (fst (dn_bz bigI z cI)) i = wval ws1 i) ->
      (forall i, (zm1 <= i)%Z -> znth (fst (dn_bz bigI z cI)) i = 0%Z) ->
      (snd (dn_bz bigI z cI) <= zm1 <= 128)%Z -> (0 < zm1)%Z ->
      evt asegs POST
        (MS (mkR x1 SPv gp tp x5' x6' x7' sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) (Z_to_bv 64 (-1)) (Z_to_bv 64 1000000000)
                 (Z_to_bv 64 need) (Z_to_bv 64 102) (Z_to_bv 64 (4 * need)) (Z_to_bv 64 sh) x16' (Z_to_bv 64 (4 * (dn_a1 bigI a - a)))
                 (Z_to_bv 64 p1) (Z_to_bv 64 e2) (Z_to_bv 64 (Z.lor t 32)) x21 SPv
                 x23 x24 x25 x26 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * snd (dn_bz bigI z cI))) x28' x29 x30 x31)
            Ft (Z_to_bv 64 0x1556b8) fc None m1 (seg_rom asegs))).
    { intros m1 ws1 x5' x6' x7' x16' x28' zm1 MV1 BIG1 LW1 REL1 ZERO1 Hzm1 Hzm2.
      clear MI MU WM FRhi ST GOT SSP FRs E2 EB BF WF BIG REL ZERO. dest_midv2 MV1.
      set (a1 := dn_a1 bigI a) in *. set (z1 := snd (dn_bz bigI z cI)) in *. set (big1 := fst (dn_bz bigI z cI)) in *.
      zs. replace (bv_unsigned sp + -1056 + 4 * a + 4 * (a1 - a))%Z with (bv_unsigned sp + -1056 + 4 * a1)%Z by lia.

      assert (J1e4 : forall (x16'' x17'' : word) zf, zf = dn_zf t 0 need a1 z1 ->
        evt asegs POST
          (MS (mkR x1 SPv gp tp x5' x6' x7' sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a1)) (Z_to_bv 64 (-1)) (Z_to_bv 64 1000000000)
                   (Z_to_bv 64 need) (Z_to_bv 64 102) (Z_to_bv 64 (4 * need)) (Z_to_bv 64 sh) x16'' x17''
                   (Z_to_bv 64 p1) (Z_to_bv 64 e2) (Z_to_bv 64 (Z.lor t 32)) x21 SPv
                   x23 x24 x25 x26 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * zf)) x28' x29 x30 x31)
              Ft (Z_to_bv 64 0x155634) fc None m1 (seg_rom asegs))).
      { intros x16'' x17'' zf Hzf.
        assert (Rzf : (0 <= zf <= z1)%Z).
        { rewrite Hzf. unfold dn_zf, CHR_f. destruct (Z.lor t 32 =? 102); [destruct (Z.ltb_spec0 need (z1 - 0))|destruct (Z.ltb_spec0 need (z1 - a1))]; lia. }
        rewrite <- Hzf in HDn, DOK'.
        zs. rewrite sx32_lit by lia. zs.
        replace (Z_to_bv 64 (bv_swrap 32 (Z.land e2 18446744073709551615 + sh))) with (Z_to_bv 64 (e2 + sh))
          by (f_equal; rewrite land_W64, swrap32_eq; mlia).
        zs. zs. if_cases Kend; zify_cond Kend; rewrite land_W64 in Kend.
        -
          assert (Ez : (e2 + sh = 0)%Z).
          { destruct (Z.eq_dec (e2 + sh) 0) as [|Hne]; [assumption|]. exfalso.
            replace ((e2 + sh) mod 2^64)%Z with (e2 + sh + 2^64)%Z in Kend by (apply Z.mod_unique with (q := (-1)%Z); subst sh; lia). subst sh; lia. }
          rewrite Ez in *. destruct k as [|k']; [discriminate HDn|].
          rewrite fmt_fp_dn_step in HDn. cbn [Z.ltb] in HDn. injection HDn as <- <- <- <-.
          eapply L_0bc with (K := MidK pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft) (zm := zm1) (r := 0%Z) (lo := lo);
            [ mk_midv | exact BIG1 | exact LW1 | exact LB1 | exact REL1 | exact ZERO1 | dlia | dlia | dlia | dlia | dlia | dlia | left; reflexivity | dlia | exact PG | exact HG ].
        -
          assert (Hlt : (e2 + sh < 0)%Z).
          { destruct (Z.lt_ge_cases (e2 + sh) 0) as [|Hge]; [assumption|]. exfalso. rewrite Z.mod_small in Kend by (subst sh; lia). subst sh; lia. }
          eapply IH with (K := MidK pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft) (zm := zm1) (lo := lo);
            [ mk_midv | exact BIG1 | exact LW1 | exact LB1 | exact REL1 | exact ZERO1 | subst sh; dlia | dlia | dlia | dlia | dlia | exact Hneed | exact DOK' | exact HDn | exact PG | exact HG ]. }

      assert (J278 : forall (x17' : word) b bp, b = (if Z.lor t 32 =? 102 then 0 else a1)%Z -> bp = (bv_unsigned sp + -1056 + 4 * b)%Z ->
        evt asegs POST
          (MS (mkR x1 SPv gp tp x5' x6' x7' sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a1)) (Z_to_bv 64 (-1)) (Z_to_bv 64 1000000000)
                   (Z_to_bv 64 need) (Z_to_bv 64 102) (Z_to_bv 64 (4 * need)) (Z_to_bv 64 sh) (Z_to_bv 64 bp) x17'
                   (Z_to_bv 64 p1) (Z_to_bv 64 e2) (Z_to_bv 64 (Z.lor t 32)) x21 SPv
                   x23 x24 x25 x26 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z1)) x28' x29 x30 x31)
              Ft (Z_to_bv 64 0x1556c8) fc None m1 (seg_rom asegs))).
      { intros x17' b bp Hb Hbp. assert (Rb : (0 <= b <= a1)%Z) by (rewrite Hb; destruct (Z.lor t 32 =? 102); lia). subst bp.
        zs. replace (bv_unsigned sp + -1056 + 4 * z1 - (bv_unsigned sp + -1056 + 4 * b))%Z with ((z1 - b) * 2^2)%Z by lia.
        zs. rewrite signed_of_Z by lia. rewrite (Z.shiftr_div_pow2 _ 2) by lia. change (2^2)%Z with 4%Z. rewrite Z.div_mul by lia.
        zs. if_cases Kcap; zify_cond Kcap; rewrite !signed_of_Z in Kcap by lia.
        -
          eapply (J1e4 _ _ z1). unfold dn_zf, CHR_f. rewrite <- Hb. rewrite (proj2 (Z.ltb_ge need (z1 - b))) by lia. reflexivity.
        -
          zs. replace (bv_unsigned sp + -1056 + 4 * b + 4 * need)%Z with (bv_unsigned sp + -1056 + 4 * (b + need))%Z by lia.
          zs. eapply (J1e4 _ _ (b + need)%Z). unfold dn_zf, CHR_f. rewrite <- Hb. rewrite (proj2 (Z.ltb_lt need (z1 - b))) by lia. reflexivity. }
      zs. zs. if_cases Kf; zify_cond Kf.
      - eapply (J278 _ 0%Z); [ rewrite Kf; reflexivity | dlia ].
      - zs. eapply (J278 _ a1); [ destruct (Z.eqb_spec (Z.lor t 32) 102); [exfalso; lia | reflexivity] | reflexivity ]. }

    zs. replace (Z_to_bv 64 (bv_swrap 32 (0 - Z.land e2 18446744073709551615))) with (Z_to_bv 64 (- e2)) by (f_equal; rewrite land_W64, swrap32_eq; mlia).
    assert (J204 : evt asegs POST
        (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) (Z_to_bv 64 (-1)) (Z_to_bv 64 1000000000)
                 (Z_to_bv 64 need) (Z_to_bv 64 102) (Z_to_bv 64 (4 * need)) (Z_to_bv 64 sh) (Z_to_bv 64 9) x17
                 (Z_to_bv 64 p1) (Z_to_bv 64 e2) (Z_to_bv 64 (Z.lor t 32)) x21 SPv
                 x23 x24 x25 x26 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x155654) fc None m (seg_rom asegs))).
    { zs. if_cases Kaz; zify_cond Kaz.
      -
        assert (Eaz : a = z) by lia.
        unfold BIG_FUEL in HI. rewrite fmt_fp_dn_inner_step in HI. rewrite (proj2 (Z.ltb_ge a z)) in HI by lia.
        injection HI as <- Eza <-.
        assert (Hnz : znth big a <> 0%Z) by (apply Dnz; exact Eaz).
        assert (Hazm : (a < zm)%Z) by (destruct (Z.lt_ge_cases a zm) as [|Hge]; [assumption|]; exfalso; apply Hnz; apply ZERO; lia).
        pose proof (u32arr_read asegs _ _ _ a _ _ BIG (nth_error_wnth ws a ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
        zs. zs. zs.
        rewrite (seqz4_eq ws a (znth big a)) by (symmetry; apply REL; lia).
        replace (if znth big a =? 0 then 4 else 0)%Z with (4 * (dn_a1 big a - a))%Z by (unfold dn_a1; destruct (znth big a =? 0); lia).
        eapply J268 with (zm1 := zm); [ mk_midv | exact BIG | exact LW | | | cbn [dn_bz Z.eqb negb snd]; dlia | dlia ].
        + intros i Hi. cbn [dn_bz Z.eqb negb fst]. apply REL. lia.
        + intros i Hi. cbn [dn_bz Z.eqb negb fst]. apply ZERO. lia.
      -
        zs. zs. zs. zs. zs.
        rewrite ?(land_W64_small sh) by lia. rewrite ?(Z.mod_small sh 32) by lia. rewrite dn_mask_eq, dn_q9_eq by lia.
        eapply (L_dnin BIG_FUEL) with (lo := lo) (zm := zm) (K := MidK pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft) (big' := bigI) (c' := cI);
          [ mk_midv | exact BIG | exact LW | exact LB | exact REL | exact ZERO | dlia | dlia | dlia | dlia | reflexivity | reflexivity | dlia | exact HI | ].
        intros m' ws' x7' x28' MV' BIG' LW' LBI' REL' ZERO' RcI.
        clear MI MU WM FRhi ST GOT SSP FRs E2 EB BF WF. dest_midv2 MV'.
        pose proof (u32arr_read asegs _ _ _ a _ _ BIG' (nth_error_wnth ws' a ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
        zs. zs. zs.
        rewrite (seqz4_eq ws' a (znth bigI a)) by (symmetry; apply REL'; lia).
        replace (if znth bigI a =? 0 then 4 else 0)%Z with (4 * (dn_a1 bigI a - a))%Z by (unfold dn_a1; destruct (znth bigI a =? 0); lia).
        zs. if_cases Kc; zify_cond Kc.
        +
          subst cI.
          eapply J268 with (zm1 := zm); [ mk_midv | exact BIG' | exact LW' | | | cbn [dn_bz Z.eqb negb snd]; dlia | dlia ].
          * intros i Hi. cbn [dn_bz Z.eqb negb fst]. apply REL'. lia.
          * intros i Hi. cbn [dn_bz Z.eqb negb fst]. apply ZERO'. lia.
        +
          zs.
          pose proof (u32arr_store_ok asegs _ _ _ z _ BIG' ltac:(lia) eq_refl) as SOK.
          zs.
          pose proof (u32arr_write asegs _ _ _ z (Z_to_bv 64 cI) BIG' ltac:(lia)) as BIG2. clear BIG'.
          store_done.
          zs. zs.
          assert (Ebz : dn_bz bigI z cI = (zupd bigI z cI, (z + 1)%Z)) by (unfold dn_bz; rewrite (proj2 (Z.eqb_neq cI 0) Kc); reflexivity).
          replace (bv_unsigned sp + -1056 + 4 * z + 4)%Z with (bv_unsigned sp + -1056 + 4 * snd (dn_bz bigI z cI))%Z by (rewrite Ebz; cbn [snd]; lia).
          eapply J268 with (zm1 := Z.max zm (z + 1)); [ mk_midv | exact BIG2 | rewrite upd_length; exact LW' | | | rewrite Ebz; cbn [snd]; dlia | dlia ].
          * intros i Hi. rewrite Ebz. cbn [fst]. destruct (Z.eq_dec i z) as [->|Hne].
            -- rewrite znth_zupd_eq by (unfold zlength; lia). rewrite wval_upd_same by lia. rewrite unsigned_lit by lia. symmetry. apply Z.mod_small. lia.
            -- rewrite znth_zupd_neq by lia. rewrite wval_upd_other by lia. apply REL'. lia.
          * intros i Hi. rewrite Ebz. cbn [fst]. rewrite znth_zupd_neq by lia. apply ZERO'. lia. }

    zs. zs. if_cases K9; zify_cond K9.
    - replace (Z_to_bv 64 (- e2)) with (Z_to_bv 64 sh) by (f_equal; subst sh; lia). exact J204.
    - zs. replace (Z_to_bv 64 9) with (Z_to_bv 64 sh) at 1 by (f_equal; subst sh; lia). exact J204.
  Qed.

  Lemma L_0b8 : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x25 x26 x28 x29 x30 x31 : word) fc K
      (ws : list word) (big : list Z) (e2 a r z zm : Z),
    midv K m fc e2 ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (a <= i < zm)%Z -> znth big i = wval ws i) ->
    (-1102 <= e2 <= 0)%Z -> (0 <= a <= z)%Z -> (z <= zm <= 128)%Z -> (r < zm)%Z -> (r = 0 \/ r = 122)%Z -> (a <= r)%Z ->
    prov_F (K_p1 K) r (big, a, z, e2) ->
    ffp_F o0 w fl t (K_p1 K) (K_prefix K) (K_pl K) big a r z e2 = Some (o1, ret) ->
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (K_p1 K)) (Z_to_bv 64 e2) (Z_to_bv 64 (Z.lor t 32)) x21 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * r))
               (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x24 x25 x26 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x28 x29 x30 x31)
          (K_Ft K) (Z_to_bv 64 0x155508) fc None m (seg_rom asegs)).
  Proof using AB AF DNB0 GLO Ht Hta J256 L_0bc SPHI SPLO RIP FXI HA0 ROOM.
    intros until zm; intros MV BIG LW LB REL He2 Haz Hz Hrzm Hr Har PF HF.
    destruct K as [pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft]. cbn [K_p1 K_prefix K_pl] in PF, HF.
    pose proof (DNB _ _ _ PF) as DOK.
    dest_midv2 MV. prune. pose proof (zr_word sp : (0 <= bv_unsigned sp < 2^64)%Z) as Rsp.
    assert (Rfw : (0 <= Fp < 2^64)%Z) by apply (zr_word fw).
    unfold ffp_F in HF.
    destruct (fmt_fp_dn DN_FUEL p1 t r (big, a, z, e2)) as [[[[big' a'] z'] e2']|] eqn:HDn; [|discriminate HF].
    assert (PG : prov_G p1 r (big', a', z', e2')) by (exists (big, a, z, e2); split; [exact PF | exact HDn]).
    zs. if_cases Ke; zify_cond Ke; rewrite land_W64 in Ke.
    -
      assert (He : (e2 < 0)%Z).
      { destruct (Z.lt_ge_cases e2 0) as [|Hge]; [assumption|]. exfalso. rewrite Z.mod_small in Ke by lia. lia. }
      clear Ke.
      assert (Hr0 : r = 0%Z /\ a = r).
      { destruct PF as (b0 & z0 & e20 & PE0 & HU0). destruct PE0 as (yq & yq' & _ & Hr0 & _).
        destruct (Z.ltb_spec0 e20 0).
        - split; [exact Hr0|]. unfold UP_FUEL in HU0. rewrite fmt_fp_up_step in HU0.
          rewrite (proj2 (Z.ltb_ge 0 e20)) in HU0 by lia. injection HU0 as _ <- _ _. reflexivity.
        - exfalso. pose proof (fmt_fp_up_nonneg _ _ _ _ _ _ _ _ _ HU0 ltac:(lia)). lia. }
      destruct Hr0 as [Hr0 Ear].
      assert (ZF : zero_from big z).
      { destruct PF as (b0 & z0 & e20 & PE0 & HU0). destruct PE0 as (yq & yq' & _ & _ & HDG0).
        eapply fmt_fp_up_zero; [exact HU0|]. eapply fmt_fp_dig_zero; [exact HDG0 | lia | apply zero_from_zrepeat; lia]. }
      subst r.
      zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
      rewrite need_magic by lia.
      set (need := ((p1 + 45) / 9 + 1)%Z).
      assert (Rneed : (1 <= need < 2^31)%Z) by (subst need; mlia).
      rewrite (land_W64_small need) by lia. rewrite (Z.shiftl_mul_pow2 need 2) by lia.
      replace (need * 2^2)%Z with (4 * need)%Z by lia.
      replace (bv_unsigned sp + -1056 + 4 * 0)%Z with (bv_unsigned sp + -1056)%Z by lia.
      eapply (L_dn DN_FUEL) with (K := MidK pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft) (zm := zm) (lo := a);
        [ mk_midv | exact BIG | exact LW | exact LB | exact REL | | dlia | dlia | dlia | dlia | dlia | subst need; cbn [K_p1]; lia
        | exact DOK | exact HDn | exact PG | exact HF ].
      intros i Hi. apply ZF. lia.
    -
      assert (He : (e2 = 0)%Z).
      { destruct (Z.eq_dec e2 0) as [|Hne]; [assumption|]. exfalso.
        replace (e2 mod 2^64)%Z with (e2 + 2^64)%Z in Ke by (apply Z.mod_unique with (q := (-1)%Z); lia). lia. }
      clear Ke. subst e2.
      unfold DN_FUEL in HDn. rewrite fmt_fp_dn_step in HDn. cbn [Z.ltb] in HDn. injection HDn as <- <- <- <-.
      assert (ZF : zero_from big z).
      { destruct PF as (b0 & z0 & e20 & PE0 & HU0). destruct PE0 as (yq & yq' & _ & _ & HDG0).
        eapply fmt_fp_up_zero; [exact HU0|]. eapply fmt_fp_dig_zero; [exact HDG0 | destruct (e20 <? 0); lia | apply zero_from_zrepeat; destruct (e20 <? 0); lia]. }
      eapply L_0bc with (K := MidK pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft) (zm := zm) (r := r) (lo := a);
        [ mk_midv | exact BIG | exact LW | exact LB | exact REL | intros i Hi; apply ZF; lia | dlia | dlia | dlia | dlia | dlia | dlia | exact Hr | reflexivity | exact PG | exact HF ].
  Qed.

End FmtFp.
