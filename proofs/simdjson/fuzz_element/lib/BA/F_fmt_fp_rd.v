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

  Hypothesis L_608 :
    forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word) fc K (jk16 : list byte)
      (ws : list word) (big bigq : list Z) (lo a r rp z zm d e i n x round aq dq eq zR : Z),
    midq K [CB 16 jk16; C8 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * (d - 1) + 65536)); C8 (Z_to_bv 64 (lo64 round)); C8 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d))]
         (Z.b2z (K_pl K =? 0)) m fc ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (lo <= i < zm)%Z -> znth big i = wval ws i) ->
    (forall i, (zm <= i)%Z -> znth big i = 0%Z) ->
    (0 <= lo <= a)%Z -> (lo <= r)%Z -> (a <= zm)%Z -> (lo <= d < z)%Z -> (z <= zm <= 128)%Z -> (r < zm)%Z -> (r = 0 \/ r = 122)%Z ->
    rp = (bv_unsigned sp + -1056 + 4 * r)%Z ->
    (forall i, (0 <= znth big i < 1000000000)%Z) ->
    i = (10 ^ n)%Z -> (1 <= n <= 9)%Z -> x = ((znth big d) mod i)%Z -> (-2^20 <= e < 2^20)%Z ->
    ffp_R4 (K_prefix K) (K_pl K) big a r z d i x e round = Some (bigq, aq, dq, eq) -> (0 <= aq)%Z ->
    (f128_le (f128_add (fst (ffp_flip (K_prefix K) (K_pl K) round (ffp_small z d i x))) (snd (ffp_flip (K_prefix K) (K_pl K) round (ffp_small z d i x))))
             (fst (ffp_flip (K_prefix K) (K_pl K) round (ffp_small z d i x))) <> 0%Z -> (a <= d)%Z) ->
    zR = (if dq + 1 <? z then dq + 1 else z)%Z ->
    prov_R (K_p1 K) (K_prefix K) (K_pl K) r bigq aq zR eq ->
    ffp_H o0 w fl t (K_p1 K) (K_prefix K) (K_pl K) bigq aq r zR eq = Some (o1, ret) ->
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10 x11 x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 i) (Z_to_bv 64 (Z.lor t 32)) (Z_to_bv 64 e) (Z_to_bv 64 rp)
               (Z_to_bv 64 x) (Z_to_bv 64 (znth big d)) (Z_to_bv 64 (hi64 round)) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * (d + 1))) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x28 x29 x30 x31)
          (K_Ft K) (Z_to_bv 64 0x155a58) fc None m (seg_rom asegs)).

  Hypothesis L_978 :
    forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x24 x25 x26 x28 x30 x31 : word) fc K
      (ws : list word) (big : list Z) (lo a r rp z zm d e zR : Z),
    midw K m fc 0%Z ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (lo <= i < zm)%Z -> znth big i = wval ws i) ->
    (forall i, (zm <= i)%Z -> znth big i = 0%Z) ->
    (0 <= lo <= a)%Z -> (lo <= r)%Z -> (a <= zm)%Z -> (lo <= d < z)%Z -> (z <= zm <= 128)%Z -> (r < zm)%Z -> (r = 0 \/ r = 122)%Z ->
    rp = (bv_unsigned sp + -1056 + 4 * r)%Z ->
    (forall i, (0 <= znth big i < 1000000000)%Z) ->
    (-2^20 <= e < 2^20)%Z ->
    zR = (if d + 1 <? z then d + 1 else z)%Z ->
    prov_R (K_p1 K) (K_prefix K) (K_pl K) r big a zR e ->
    ffp_H o0 w fl t (K_p1 K) (K_prefix K) (K_pl K) big a r zR e = Some (o1, ret) ->
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (K_p1 K)) x19 (Z_to_bv 64 (Z.lor t 32)) (Z_to_bv 64 e) (Z_to_bv 64 rp)
               (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d)) x24 x25 x26 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x28 (Z_to_bv 64 t) x30 x31)
          (K_Ft K) (Z_to_bv 64 0x155dc8) fc None m (seg_rom asegs)).

  Lemma L_590 : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x15 x16 x17 x28 x29 x30 x31 : word) fc K (jk32 : list byte)
      (ws : list word) (big bigq : list Z) (lo a r rp z zm d e i n x aq dq eq zR : Z),
    midq K [CB 32 jk32; C8 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d))] (Z.b2z (K_pl K =? 0)) m fc ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (lo <= i < zm)%Z -> znth big i = wval ws i) ->
    (forall i, (zm <= i)%Z -> znth big i = 0%Z) ->
    (0 <= lo <= a)%Z -> (lo <= r)%Z -> (a <= zm)%Z -> (lo <= d < z)%Z -> (z <= zm <= 128)%Z -> (r < zm)%Z -> (r = 0 \/ r = 122)%Z ->
    rp = (bv_unsigned sp + -1056 + 4 * r)%Z ->
    (forall i, (0 <= znth big i < 1000000000)%Z) ->
    i = (10 ^ n)%Z -> (1 <= n <= 9)%Z -> x = ((znth big d) mod i)%Z -> (-2^20 <= e < 2^20)%Z ->
    ((d < a)%Z -> x = 0%Z) ->
    ffp_R3 (K_prefix K) (K_pl K) big a r z d i x e = Some (bigq, aq, dq, eq) -> (0 <= aq)%Z ->
    zR = (if dq + 1 <? z then dq + 1 else z)%Z ->
    prov_R (K_p1 K) (K_prefix K) (K_pl K) r bigq aq zR eq ->
    ffp_H o0 w fl t (K_p1 K) (K_prefix K) (K_pl K) bigq aq r zR eq = Some (o1, ret) ->
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10 x11 x12 x13
               (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * (d - 1) + 65536)) x15 x16 x17
               (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d + 65536)) (Z_to_bv 64 i) (Z_to_bv 64 (Z.lor t 32)) (Z_to_bv 64 e) (Z_to_bv 64 rp)
               (Z_to_bv 64 x) (Z_to_bv 64 (znth big d)) (Z_to_bv 64 (znth big d / i)) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * (d + 1))) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x28 x29 x30 x31)
          (K_Ft K) (Z_to_bv 64 0x1559e0) fc None m (seg_rom asegs)).
  Proof using AB AF GLO J256 L_608 SPHI SPLO RIP FXI HA0 ROOM.
    intros until zR; intros MV BIG LW LB REL ZERO Hlo Hlor Ha Hd Hzm Hrzm Hr Hrp ALLW Hi Hn Hx He HXA HR3 Haq HzR PR HH.
    destruct K as [pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft]. cbn [K_p1 K_prefix K_pl K_Ft] in PR, HH |- *.
    dest_midq2 MV. prune. pose proof (zr_word sp : (0 <= bv_unsigned sp < 2^64)%Z) as Rsp.
    assert (Rfw : (0 <= Fp < 2^64)%Z) by apply (zr_word fw).
    pose proof (ALLW d) as Rbd.
    assert (Ri : (10 <= i <= 1000000000)%Z).
    { rewrite Hi. split; [change 10%Z with (10 ^ 1)%Z; apply Z.pow_le_mono_r; lia | change 1000000000%Z with (10 ^ 9)%Z; apply Z.pow_le_mono_r; lia]. }
    assert (Rx : (0 <= x < i)%Z) by (rewrite Hx; apply Z.mod_pos_bound; lia).
    assert (Rq : (0 <= znth big d / i <= znth big d)%Z).
    { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. nia. }
    unfold ffp_R3 in HR3. fold ROUND0 in HR3.

    destruct (zboxed_intro ROUND0) as [R0 HR0]. rewrite <- (zboxed_eq _ _ HR0) in HR3.

    assert (J608 : forall m' fc' (x1' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word) (round : Z),
      (round = R0 \/ round = f128_add R0 (f128_of_i32 2)) ->
      midq (MidK pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft)
           [CB 16 (firstn 16 jk32); C8 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * (d - 1) + 65536)); C8 (Z_to_bv 64 (lo64 round)); C8 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d))]
           (Z.b2z (pl =? 0)) m' fc' ->
      u32arr asegs m' (bv_unsigned sp + -1056) ws ->
      ffp_R4 prefix pl big a r z d i x e round = Some (bigq, aq, dq, eq) ->
      evt asegs POST
        (MS (mkR x1' SPv gp tp x5' x6' x7' sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10' x11' x12' x13' x14' x15' x16' x17'
                 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d + 65536)) (Z_to_bv 64 i) (Z_to_bv 64 (Z.lor t 32)) (Z_to_bv 64 e) (Z_to_bv 64 rp)
                 (Z_to_bv 64 x) (Z_to_bv 64 (znth big d)) (Z_to_bv 64 (hi64 round)) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * (d + 1))) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x28' x29' x30' x31')
            Ft (Z_to_bv 64 0x155a58) fc' None m' (seg_rom asegs))).
    { intros m' fc' x1' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' round Hround MV' BIG' HR4.
      eapply L_608 with (K := MidK pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft) (zm := zm) (lo := lo) (r := r) (n := n) (big := big) (round := round);
        [ exact MV' | exact BIG' | exact LW | exact LB | exact REL | exact ZERO | dlia | dlia | dlia | dlia | dlia | dlia | exact Hr | exact Hrp | exact ALLW
        | exact Hi | exact Hn | exact Hx | exact He | exact HR4 | exact Haq | | exact HzR | exact PR | exact HH ].
      intros Hne. destruct (Z.le_gt_cases a d) as [Hle|Hlt]; [exact Hle|]. exfalso. apply Hne.
      rewrite (HXA Hlt). rewrite ffp_small_x0 by lia. apply rup_half. destruct Hround as [-> | ->]; [left; exact (zboxed_eq _ _ HR0) | right; rewrite (zboxed_eq _ _ HR0); reflexivity]. }
    zs. zs.
    zs. call floatsitf_callp. 1:{ hyp. } 1:{ lia. }
    pose proof (lo64_range (f128_of_i32 2)) as R2lo. pose proof (hi64_range (f128_of_i32 2)) as R2hi.
    zs. zs. zs.
    destruct (stk_split asegs _ _ (bv_unsigned sp + -1056 - 112) _ ST ltac:(lia)) as [STlo STf]. clear ST.
    zs. call divtf3_callk. 1:{ exact STf. } 1:{ hyp. } 1:{ lia. }
    match goal with X : stk _ _ (bv_unsigned sp + -1056 - 112)%Z _ |- _ =>
      pose proof (stk_merge asegs _ _ _ _ STlo X ltac:(lia)) as ST; clear STlo X end.
    replace (f128_div (f128_of_i32 2) K_LDBL_EPSILON) with R0 by (exact (zboxed_eq _ _ HR0)).
    pose proof (lo64_range R0) as Rr0lo. pose proof (hi64_range R0) as Rr0hi.
    zs.

    assert (J5e4 : forall m' (x1' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word),
      midq (MidK pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft)
           [CB 16 (firstn 16 jk32); C8 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * (d - 1) + 65536)); C8 (Z_to_bv 64 (lo64 R0)); C8 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d))]
           (Z.b2z (pl =? 0)) m' fc ->
      u32arr asegs m' (bv_unsigned sp + -1056) ws ->
      ffp_R4 prefix pl big a r z d i x e (f128_add R0 (f128_of_i32 2)) = Some (bigq, aq, dq, eq) ->
      evt asegs POST
        (MS (mkR x1' SPv gp tp x5' x6' x7' sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10' x11' x12' x13' x14' x15' x16' x17'
                 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d + 65536)) (Z_to_bv 64 i) (Z_to_bv 64 (Z.lor t 32)) (Z_to_bv 64 e) (Z_to_bv 64 rp)
                 (Z_to_bv 64 x) (Z_to_bv 64 (znth big d)) (Z_to_bv 64 (hi64 R0)) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * (d + 1))) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x28' x29' x30' x31')
            Ft (Z_to_bv 64 0x155a34) fc None m' (seg_rom asegs))).
    { intros m' x1' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' MV' BIG' HR4.
      clear dependent m. dest_midq2 MV'.
      zs. zs. call floatsitf_callp. 1:{ hyp. } 1:{ lia. }
      zs. zs. zs. zs.
      destruct (stk_split asegs _ _ (bv_unsigned sp + -1056 - 48) _ ST ltac:(lia)) as [STlo STf]. clear ST.
      zs. call addtf3_callq. 1:{ exact STf. } 1:{ hyp. } 1:{ hyp. } 1:{ lia. }
      match goal with X : stk _ _ (bv_unsigned sp + -1056 - 48)%Z _ |- _ =>
        pose proof (stk_merge asegs _ _ _ _ STlo X ltac:(lia)) as ST; clear STlo X end.
      pose proof (lo64_range (f128_add R0 (f128_of_i32 2))) as Rr1lo. pose proof (hi64_range (f128_add R0 (f128_of_i32 2))) as Rr1hi.
      zs. zs.
      eapply J608; [ right; reflexivity | mk_midq | hyp | exact HR4 ]. }
    zs. zs. zs. if_cases Kodd; zify_cond Kodd.
    -
      assert (Eodd : ffp_odd big a d i = true).
      { unfold ffp_odd. destruct (Z.eqb_spec (Z.land (znth big d / i) 1) 0); [lia|reflexivity]. }
      rewrite Eodd in HR3.
      eapply J5e4; [ mk_midq | hyp | exact HR3 ].
    - zs. zs. zs. if_cases K9; zify_cond K9.
      +
        assert (Eodd : ffp_odd big a d i = false).
        { unfold ffp_odd. rewrite (proj2 (Z.eqb_eq _ _) Kodd). rewrite (proj2 (Z.eqb_neq i 1000000000) K9). reflexivity. }
        rewrite Eodd in HR3.
        eapply J608; [ left; reflexivity | mk_midq | hyp | exact HR3 ].
      + zs. zs. if_cases Kad; zify_cond Kad.
        *
          assert (Eodd : ffp_odd big a d i = false).
          { unfold ffp_odd. rewrite (proj2 (Z.eqb_eq _ _) Kodd). rewrite (proj2 (Z.ltb_ge a d)) by lia. rewrite Bool.andb_false_r. reflexivity. }
          rewrite Eodd in HR3.
          eapply J608; [ left; reflexivity | mk_midq | hyp | exact HR3 ].
        *
          zs. zs.
          pose proof (ALLW (d - 1)%Z) as Rbd1.
          lazymatch goal with BIG' : u32arr asegs ?m' _ ws |- _ =>
            pose proof (u8arr_read asegs _ _ _ (4 * (d - 1))%Z _ _ (u8arr_of_u32arr _ _ _ _ BIG') (wnth_low_byte ws (d - 1)%Z ltac:(lia) ltac:(rewrite LW; lia)) ltac:(lia) eq_refl) as RD end.
          zs. cbv beta. rewrite unsigned_b8. rewrite <- (REL (d - 1)%Z) by lia.
          pose proof (Z.mod_pos_bound (znth big (d - 1)%Z) 256 ltac:(lia)) as Rb.
          zs. rewrite land1_mod256 by lia.
          zs. if_cases Kev; zify_cond Kev.
          --
             assert (Eodd : ffp_odd big a d i = false).
             { unfold ffp_odd. rewrite (proj2 (Z.eqb_eq _ _) Kodd). rewrite (proj2 (Z.eqb_eq _ _) Kev). rewrite Bool.andb_false_r. reflexivity. }
             rewrite Eodd in HR3.
             eapply J608; [ left; reflexivity | mk_midq | hyp | exact HR3 ].
          -- assert (Eodd : ffp_odd big a d i = true).
             { unfold ffp_odd. rewrite (proj2 (Z.eqb_eq i 1000000000) K9). rewrite (proj2 (Z.ltb_lt a d)) by lia.
               destruct (Z.eqb_spec (Z.land (znth big (d - 1)%Z) 1) 0); [lia|]. rewrite Bool.orb_true_r. reflexivity. }
             rewrite Eodd in HR3.
             eapply J5e4; [ mk_midq | hyp | exact HR3 ].
  Qed.

  Lemma L_560 : forall m (x1 x5 x6 x7 x10 x11 x13 x15 x16 x17 x23 x24 x25 x28 x29 x30 x31 : word) fc K (jk40 : list byte)
      (ws : list word) (big bigR : list Z) (lo a r rp z zm d e i n aR zR eR : Z),
    midq K [CB 40 jk40] (Z.b2z (K_pl K =? 0)) m fc ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (lo <= i < zm)%Z -> znth big i = wval ws i) ->
    (forall i, (zm <= i)%Z -> znth big i = 0%Z) ->
    (0 <= lo <= a)%Z -> (lo <= r)%Z -> (a <= zm)%Z -> (lo <= d < z)%Z -> (z <= zm <= 128)%Z -> (r < zm)%Z -> (r = 0 \/ r = 122)%Z ->
    rp = (bv_unsigned sp + -1056 + 4 * r)%Z ->
    (forall i, (0 <= znth big i < 1000000000)%Z) ->
    i = (10 ^ n)%Z -> (1 <= n <= 9)%Z -> (-2^20 <= e < 2^20)%Z ->
    ((d < a)%Z -> znth big d = 0%Z) ->
    ffp_R2 (K_prefix K) (K_pl K) big a r z e d i = Some (bigR, aR, zR, eR) -> (0 <= aR)%Z ->
    prov_R (K_p1 K) (K_prefix K) (K_pl K) r bigR aR zR eR ->
    ffp_H o0 w fl t (K_p1 K) (K_prefix K) (K_pl K) bigR aR r zR eR = Some (o1, ret) ->
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10 x11 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d)) x13
               (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * (d - 1) + 65536)) x15 x16 x17
               (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d + 65536)) (Z_to_bv 64 i) (Z_to_bv 64 (Z.lor t 32)) (Z_to_bv 64 e) (Z_to_bv 64 rp)
               x23 x24 x25 (Z_to_bv 64 (-65532)) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x28 x29 x30 x31)
          (K_Ft K) (Z_to_bv 64 0x1559b0) fc None m (seg_rom asegs)).
  Proof using AB AF GLO J256 L_608 L_978 SPHI SPLO RIP FXI HA0 ROOM.
    intros until eR; intros MV BIG LW LB REL ZERO Hlo Hlor Ha Hd Hzm Hrzm Hr Hrp ALLW Hi Hn He HXA HR2 HaR PR HH.
    destruct K as [pad jk40_ jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft]. cbn [K_p1 K_prefix K_pl K_Ft] in PR, HH |- *.
    dest_midq2 MV. prune. pose proof (zr_word sp : (0 <= bv_unsigned sp < 2^64)%Z) as Rsp.
    assert (Rfw : (0 <= Fp < 2^64)%Z) by apply (zr_word fw).
    pose proof (ALLW d) as Rbd.
    assert (Ri : (10 <= i <= 1000000000)%Z).
    { rewrite Hi. split; [change 10%Z with (10 ^ 1)%Z; apply Z.pow_le_mono_r; lia | change 1000000000%Z with (10 ^ 9)%Z; apply Z.pow_le_mono_r; lia]. }
    assert (Rq : (0 <= znth big d / i <= znth big d)%Z).
    { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. nia. }
    assert (Rqi : (0 <= znth big d / i * i <= znth big d)%Z).
    { split; [nia|]. rewrite Z.mul_comm. apply Z.mul_div_le. lia. }
    assert (Ex : (znth big d mod i = znth big d - znth big d / i * i)%Z).
    { rewrite Zmod_eq_full by lia. lia. }
    pose proof (Z.mod_pos_bound (znth big d) i ltac:(lia)) as Rx.
    unfold ffp_R2 in HR2.
    zs.
    pose proof (u32arr_read asegs _ _ _ d _ _ BIG (nth_error_wnth ws d ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
    zs. rewrite (sx32_wval ws d) by (rewrite <- (REL d) by lia; lia). rewrite <- (REL d) by lia.
    zs. rewrite divuw_small by lia.
    zs. zs. replace (bv_swrap 32 (znth big d - znth big d / i * i)) with (znth big d mod i)%Z by (rewrite Ex, swrap32_eq; mlia).
    zs. replace (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d + 4)) with (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * (d + 1))) by word_eq_tac.
    zs. if_cases Kx; zify_cond Kx.
    -
      rewrite (proj2 (Z.eqb_neq (znth big d mod i) 0) Kx) in HR2. cbn [negb orb] in HR2.
      destruct (ffp_R3 prefix pl big a r z d i (znth big d mod i) e) as [[[[bigq aq] dq] eq]|] eqn:HR3; [|discriminate HR2].
      injection HR2 as <- <- HzR <-.
      eapply L_590 with (K := MidK pad jk40_ jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft) (zm := zm) (lo := lo) (r := r) (n := n) (big := big);
        [ mk_midq | exact BIG | exact LW | exact LB | exact REL | exact ZERO | dlia | dlia | dlia | dlia | dlia | dlia | exact Hr | exact Hrp | exact ALLW
        | exact Hi | exact Hn | reflexivity | exact He | intros Hlt; rewrite (HXA Hlt); apply Z.mod_0_l; dlia | exact HR3 | exact HaR | symmetry; exact HzR | exact PR | exact HH ].
    - rewrite (proj2 (Z.eqb_eq (znth big d mod i) 0) Kx) in HR2. cbn [negb orb] in HR2.
      zs. if_cases Kdz; zify_cond Kdz.
      +
        rewrite (proj2 (Z.eqb_neq (d + 1) z)) in HR2 by lia. cbn [negb] in HR2.
        destruct (ffp_R3 prefix pl big a r z d i (znth big d mod i) e) as [[[[bigq aq] dq] eq]|] eqn:HR3; [|discriminate HR2].
        injection HR2 as <- <- HzR <-.
        eapply L_590 with (K := MidK pad jk40_ jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft) (zm := zm) (lo := lo) (r := r) (n := n) (big := big);
          [ mk_midq | exact BIG | exact LW | exact LB | exact REL | exact ZERO | dlia | dlia | dlia | dlia | dlia | dlia | exact Hr | exact Hrp | exact ALLW
          | exact Hi | exact Hn | reflexivity | exact He | intros _; exact Kx | exact HR3 | exact HaR | symmetry; exact HzR | exact PR | exact HH ].
      +
        rewrite (proj2 (Z.eqb_eq (d + 1) z)) in HR2 by lia. cbn [negb] in HR2.
        injection HR2 as <- <- HzR <-.
        zs. zs. zs. zs.
        eapply L_978 with (K := midq_K (MidK pad jk40_ jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft) [CB 32 (firstn 32 jk40); C8 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d))] (Z.b2z (pl =? 0)))
                          (zm := zm) (lo := lo) (r := r) (big := big) (d := d);
          [ apply midq_w; [mk_midq | reflexivity] | exact BIG | exact LW | exact LB | exact REL | exact ZERO
          | dlia | dlia | dlia | dlia | dlia | dlia | exact Hr | exact Hrp | exact ALLW | exact He | symmetry; exact HzR | exact PR | exact HH ].
  Qed.

  Lemma L_powi : forall (k : nat) Q m (x1 x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fc
      (c mexp i0 : Z),
    (- Z.of_nat k <= c < 0)%Z -> (1 <= mexp)%Z -> (mexp - c <= 9)%Z -> i0 = (10 ^ mexp)%Z ->
    (forall x10',
       evt asegs Q
         (MS (mkR x1 SPv gp tp x5 x6 x7 sp x9 x10' (Z_to_bv 64 10) x12 x13 x14 x15 x16 x17
                  x18 (Z_to_bv 64 (10 ^ (mexp - c))) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
             Ft (Z_to_bv 64 0x1555f8) fc None m (seg_rom asegs))) ->
    evt asegs Q
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp x9 (Z_to_bv 64 c) (Z_to_bv 64 10) x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 i0) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 0x1555ec) fc None m (seg_rom asegs)).
  Proof using J256 o0 o1 RIP FXI HA0 AB AF ROOM.
    induction k as [|k IH]; intros until i0; intros Hc Hm Hmc Hi0 CONT; [lia|]. subst i0.
    pose proof (zr_word sp : (0 <= bv_unsigned sp < 2^64)%Z) as Rsp.
    assert (R10 : (10 <= 10 ^ mexp <= 100000000)%Z).
    { split; [change 10%Z with (10 ^ 1)%Z; apply Z.pow_le_mono_r; lia | change 100000000%Z with (10 ^ 8)%Z; apply Z.pow_le_mono_r; lia]. }
    zs. replace (bv_swrap 32 (Z.land c 18446744073709551615 + 1)) with (c + 1)%Z by (rewrite land_W64, swrap32_eq; mlia).
    zs. replace (bv_swrap 32 (10 ^ mexp * 10)) with (10 ^ (mexp + 1))%Z
          by (rewrite swrap32_eq, Z.pow_add_r by lia; change (10 ^ 1)%Z with 10%Z; mlia).
    zs. if_cases Kc; zify_cond Kc.
    -
      eapply IH with (mexp := (mexp + 1)%Z); [ | dlia | dlia | reflexivity | ].
      { rewrite land_W64 in Kc. mlia. }
      intros x10'. replace (mexp + 1 - (c + 1))%Z with (mexp - c)%Z by lia. apply CONT.
    - rewrite land_W64 in Kc. replace (mexp + 1)%Z with (mexp - c)%Z by mlia. apply CONT.
  Qed.

  Lemma L_13c : forall m (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x23 x24 x25 x26 x28 x30 x31 : word) fc K
      (ws : list word) (big bigR : list Z) (lo a r rp z zm e j aR zR eR : Z),
    midv K m fc 0%Z ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (lo <= i < zm)%Z -> znth big i = wval ws i) ->
    (forall i, (zm <= i)%Z -> znth big i = 0%Z) ->
    (0 <= lo <= a)%Z -> (lo <= r)%Z -> (a <= zm)%Z -> (0 <= z <= zm)%Z -> (zm <= 128)%Z -> (r < zm)%Z -> (r = 0 \/ r = 122)%Z -> rp = (bv_unsigned sp + -1056 + 4 * r)%Z ->
    (forall i, (0 <= znth big i < 1000000000)%Z) ->
    (forall k, (0 <= k < a)%Z -> znth big k = 0%Z) ->
    ffp_e big a r z = Some e -> j = ffp_j t (K_p1 K) e -> (j < 9 * (z - r - 1))%Z ->
    prov_G (K_p1 K) r (big, a, z, 0%Z) ->
    ffp_R t (K_p1 K) (K_prefix K) (K_pl K) big a r z e j = Some (bigR, aR, zR, eR) ->
    ffp_H o0 w fl t (K_p1 K) (K_prefix K) (K_pl K) bigR aR r zR eR = Some (o1, ret) ->
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) (Z_to_bv 64 j) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (K_p1 K)) x19 (Z_to_bv 64 (Z.lor t 32)) (Z_to_bv 64 e) (Z_to_bv 64 rp)
               x23 x24 x25 x26 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x28 (Z_to_bv 64 t) x30 x31)
          (K_Ft K) (Z_to_bv 64 0x15558c) fc None m (seg_rom asegs)).
  Proof using AB AF CAR0 GLO J256 L_608 L_978 SPHI SPLO RIP FXI HA0 ROOM.
    intros until eR; intros MV BIG LW LB REL ZERO Hlo Hlor Ha Hz Hzm Hrzm Hr Hrp ALLW BELOW He Hj Hjlt PG HR HH.
    destruct K as [pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft]. cbn [K_p1 K_prefix K_pl K_Ft] in Hj, PG, HR, HH |- *.
    dest_midv2 MV. prune. pose proof (zr_word sp : (0 <= bv_unsigned sp < 2^64)%Z) as Rsp.
    assert (Rfw : (0 <= Fp < 2^64)%Z) by apply (zr_word fw).

    assert (Re : ((a < z)%Z /\ (9 * (r - a) <= e <= 9 * (r - a) + 8)%Z) \/ ((z <= a)%Z /\ e = 0%Z)).
    { unfold ffp_e in He. destruct (Z.ltb_spec0 a z).
      - destruct (fmt_fp_cnt TEN_FUEL (znth big a) (10%Z, (9 * (r - a))%Z)) as [[i1 e1]|] eqn:HC; [|discriminate He].
        injection He as <-. left. change 10%Z with (10 ^ 1)%Z in HC.
        pose proof (fmt_fp_cnt_res9 _ _ _ _ _ _ HC ltac:(lia) (ALLW a)). lia.
      - injection He as <-. right. lia. }

    assert (Rj : exists jt jg, (0 <= jt <= 1)%Z /\ (0 <= jg <= 1)%Z /\ (jg = 1%Z -> p1 <> 0%Z) /\ j = (p1 - jt * e - jg)%Z /\ (jt = 0%Z -> (e <= 0)%Z \/ True)).
    { rewrite Hj. unfold ffp_j. exists (if negb (Z.lor t 32 =? CHR_f) then 1 else 0)%Z, (if (Z.lor t 32 =? CHR_g) && negb (p1 =? 0) then 1 else 0)%Z.
      destruct (Z.lor t 32 =? CHR_f); destruct (Z.lor t 32 =? CHR_g); destruct (Z.eqb_spec p1 0); cbn [negb andb]; repeat split; try lia. }
    destruct Rj as (jt & jg & Rjt & Rjg & Hjg & Ej & _).
    assert (Rjr : (-1200 <= j < 2^20 + 1200)%Z) by (rewrite Ej; destruct (Z.eq_dec jt 0) as [->| ]; [lia| replace jt with 1%Z by lia; lia]).
    destruct (zboxed_intro (j + 147456)%Z) as [N EN]. apply zboxed_eq in EN.
    assert (RN : (145776 <= N < 2^21)%Z) by (rewrite EN; lia).
    destruct (zboxed_intro (N / 9)%Z) as [q Eq]. apply zboxed_eq in Eq.
    destruct (zboxed_intro (N - 9 * q)%Z) as [rm Erm]. apply zboxed_eq in Erm.
    assert (Rq : (16250 <= q < 2^18)%Z) by (rewrite Eq; mlia).
    assert (Rrm : (0 <= rm <= 8)%Z) by (rewrite Erm, Eq; mlia).

    pose proof HR as HRfull. rewrite Hj in HRfull.
    rewrite ffp_R_eq in HR. rewrite (proj2 (Z.ltb_lt j (9 * (z - r - 1))) Hjlt) in HR.
    destruct (ffp_Ri j) as [[i j']|] eqn:HRi; [|discriminate HR]. cbv beta iota in HR.
    destruct (ffp_Ri_res j i j' ltac:(unfold LDBL_MAX_EXP; lia) HRi) as (n & Hn & Hi & Hn9).
    assert (En : n = (9 - rm)%Z).
    { rewrite Hn9. unfold LDBL_MAX_EXP. rewrite Erm, Eq, EN. rewrite Z.rem_mod_nonneg by lia. change (9 * 16384)%Z with 147456%Z. mlia. }
    assert (Ed : ffp_Rd j r = (r + 1 + q - 16384)%Z).
    { unfold ffp_Rd, LDBL_MAX_EXP. rewrite Eq, EN. rewrite Z.quot_div_nonneg by lia. change (9 * 16384)%Z with 147456%Z. lia. }
    rewrite Ed in HR.
    destruct (zboxed_intro (r + 1 + q - 16384)%Z) as [d Edq]. apply zboxed_eq in Edq. rewrite <- Edq in HR.
    assert (Hd : (lo <= d < z)%Z).
    { rewrite Edq. split.
      - destruct Re as [[Haz Ree] | [Hza ->]].
        + rewrite Ej in EN. destruct (Z.eq_dec jt 0) as [-> | Hjt1]; [rewrite Eq, EN; mlia|]. replace jt with 1%Z in EN by lia. rewrite Eq, EN. mlia.
        + rewrite Eq, EN. mlia.
      - rewrite Eq, EN. mlia. }
    assert (HXA : (d < a)%Z -> znth big d = 0%Z) by (intros Hlt; apply BELOW; lia).
    zs. zs. zs. zs. zs.
    zs. replace (bv_swrap 32 (Z.land j 18446744073709551615 + 147456)) with N by (rewrite land_W64, EN, swrap32_eq; mlia).
    zs. zs. zs.
    assert (RNM : (0 <= N * 954437177 < 2^51)%Z) by lia.
    zs. rewrite (Z.shiftr_div_pow2 _ 63) by lia. rewrite (Z.div_small (N * 954437177) (2^63)) by lia.
    zs. rewrite (signed_of_Z (N * 954437177)) by lia. rewrite (Z.shiftr_div_pow2 _ 33), div9_magic, <- Eq by lia.
    zs. rewrite ?Z.add_0_r.
    zs. zs. zs. zs. zs. zs. zs. zs.
    rewrite !Z.shiftl_mul_pow2 by lia. change (2^2)%Z with 4%Z. change (2^3)%Z with 8%Z.
    rewrite (land_W64_small (q * 8 + q)) by lia.
    replace (bv_swrap 32 (N - (q * 8 + q))) with rm by (rewrite Erm, swrap32_eq; mlia).
    replace (Z_to_bv 64 (rp + q * 4 + -65532)) with (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d)) by (f_equal; lia).
    replace (Z_to_bv 64 (rp + q * 4 + 4)) with (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d + 65536)) by (f_equal; lia).
    replace (Z_to_bv 64 (rp + q * 4)) with (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * (d - 1) + 65536)) by (f_equal; lia).

    lazymatch goal with FRs' : rw_cells asegs ?m1 (bv_unsigned sp + -544)%Z _ |- _ => rewrite Hplz in FRs' end.
    assert (PR : prov_R p1 prefix pl r bigR aR zR eR).
    { exists big, a, z, 0%Z, e. split; [exact PG|]. split; [exact He|]. exact HRfull. }
    pose proof (CAR _ _ _ _ _ _ _ _ PR) as HaR.
    assert (R456 : (0 <= Z.b2z (pl =? 0) < 2^64)%Z) by (destruct (pl =? 0); cbn; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mcur _) =>
    assert (J560 : forall (x10' x11' x13' : word),
      evt asegs POST
        (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10' x11' (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d)) x13'
                 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * (d - 1) + 65536)) x15 x16 x17
                 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d + 65536)) (Z_to_bv 64 i) (Z_to_bv 64 (Z.lor t 32)) (Z_to_bv 64 e) (Z_to_bv 64 rp)
                 x23 x24 x25 (Z_to_bv 64 (-65532)) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x28 (Z_to_bv 64 t) x30 x31)
            Ft (Z_to_bv 64 0x1559b0) fc None mcur (seg_rom asegs)))
    end.
    { intros x10' x11' x13'.
      eapply L_560 with (K := MidK pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft) (zm := zm) (lo := lo) (r := r) (n := n) (big := big);
        [ mk_midq | exact BIG | exact LW | exact LB | exact REL | exact ZERO | dlia | dlia | dlia | exact Hd | dlia | dlia | exact Hr | exact Hrp | exact ALLW
        | exact Hi | exact Hn | | exact HXA | exact HR | exact HaR | exact PR | exact HH ].
      destruct Re as [[_ Ree] | [_ ->]]; [|lia]. destruct (Z.eq_dec jt 0) as [-> | ]; [|replace jt with 1%Z in Ej by lia]; lia. }
    zs. if_cases Krm; zify_cond Krm; rewrite !signed_of_Z in Krm by lia.
    -
      zs. replace (Z_to_bv 64 10) with (Z_to_bv 64 i) by (rewrite Hi, En; f_equal; replace (9 - rm)%Z with 1%Z by lia; reflexivity).
      apply J560.
    -
      zs. zs. zs.
      replace (Z_to_bv 64 (rm + -8)) with (Z_to_bv 64 (rm - 8)) by (f_equal; lia).
      eapply (L_powi 8) with (mexp := 1%Z); [ dlia | dlia | dlia | reflexivity | ].
      intros x10'. zs.
      replace (Z_to_bv 64 (10 ^ (1 - (rm - 8)))) with (Z_to_bv 64 i) by (rewrite Hi, En; f_equal; f_equal; lia).
      apply J560.
  Qed.

End FmtFp.
