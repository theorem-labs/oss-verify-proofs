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

  Hypothesis L_eloop :
    forall (k : nat) Q m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x27 x28 x29 x30 x31 : word) fc K
      (estrp ppl fl2 a8 : Z) (oc : list Z) (ws : list word) (big : list Z) (lo a z zm d pr d' p' : Z) (o' : list Z),
    emw K estrp ppl fl2 a8 84566 oc m fc ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (lo <= i < zm)%Z -> znth big i = wval ws i) ->
    (0 <= lo <= a)%Z -> (a <= d < z)%Z -> (z <= zm <= 128)%Z -> (0 <= pr < 2^21)%Z ->
    (forall i, (0 <= znth big i < 1000000000)%Z) ->
    (0 <= a8 <= 8)%Z -> (a8 = 0%Z <-> Z.land fl 8 = 0%Z) ->
    length (K_jk37 K) = 37%nat ->
    fmt_fp_eloop k big a z fl (d, pr, oc) = Some (d', p', o') ->
    (length o' <= length o1)%nat ->
    (forall m1 bf1 (x1' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x21' x26' x27' x28' x29' x30' x31' : word),
       emw (K_set37 K bf1) estrp ppl fl2 a8 84566 o' m1 fc -> u32arr asegs m1 (bv_unsigned sp + -1056) ws -> length bf1 = 37%nat ->
       (-9 <= p' <= pr)%Z ->
       evt asegs Q
         (MS (mkR x1' SPv gp tp x5' x6' x7' sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10' x11' x12' x13' x14' x15' x16' x17'
                  (Z_to_bv 64 p') (Z_to_bv 64 14757395258967641293) (Z_to_bv 64 48) x21' (Z_to_bv 64 10) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z))
                  (Z_to_bv 64 (bv_unsigned sp + -405)) (Z_to_bv 64 99) x26' x27' x28' x29' x30' x31')
             (K_Ft K) (Z_to_bv 64 0x1563ec) fc None m1 (seg_rom asegs))) ->
    forall x1, evt asegs Q
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 pr) (Z_to_bv 64 14757395258967641293) (Z_to_bv 64 48) x21 (Z_to_bv 64 10) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z))
               (Z_to_bv 64 (bv_unsigned sp + -405)) (Z_to_bv 64 99) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d)) x27 x28 x29 x30 x31)
          (K_Ft K) (Z_to_bv 64 0x1562b0) fc None m (seg_rom asegs)).

  Hypothesis L_100 :
    forall m (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) fc K
      (ws : list word) (estrp a8v v440 l : Z) (oc : list Z),
    emw K estrp (K_pl K + l) (Z.land fl 73728) a8v v440 oc m fc ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    (1 <= l < 2^24)%Z ->
    ffp_H6 oc w fl (K_pl K) l = Some (o1, ret) ->
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 (Z_to_bv 64 w) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (K_Ft K) (Z_to_bv 64 0x156550) fc None m (seg_rom asegs)).

  Lemma L_e24 : forall m (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 : word) fc K
      (ws : list word) (big : list Z) (oc : list Z) (lo a r rp z zm e p2 t2 a8 palt l estr estrp : Z) (ebuf0 : list Z),
    emw K estrp (K_pl K + l) (Z.land fl 73728) a8 (K_pl K) oc m fc ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (lo <= i < zm)%Z -> znth big i = wval ws i) ->
    (forall i, (zm <= i)%Z -> znth big i = 0%Z) ->
    (0 <= lo <= a)%Z -> (lo <= r)%Z -> (a <= zm)%Z -> (0 <= z <= zm)%Z -> (zm <= 128)%Z -> (r < zm)%Z -> (r = 0 \/ r = 122)%Z -> rp = (bv_unsigned sp + -1056 + 4 * r)%Z ->
    (forall i, (0 <= znth big i < 1000000000)%Z) ->
    (-2^20 <= e < 2^20)%Z -> (0 <= p2 < 2^21)%Z -> (0 <= t2 < 256)%Z ->
    (a < z -> znth big (z - 1) <> 0)%Z -> (Z.lor t2 32 <> CHR_f -> z <= a -> a = r)%Z ->
    (0 <= a8 <= 8)%Z -> (a8 = 0%Z <-> Z.land fl 8 = 0%Z) ->
    palt = (if negb (p2 =? 0) || negb (Z.land fl ALT_FORM =? 0) then 1 else 0)%Z ->
    (1 + p2 + palt <= l < 2^23)%Z -> (0 <= estrp < 2^64)%Z -> length ebuf0 = 12%nat ->
    (Z.lor t2 32 <> CHR_f -> (1 <= estr <= 10)%Z /\ estrp = (bv_unsigned sp + -417 + estr)%Z /\
       forall k, (estr <= k < 12)%Z -> nth_error (K_jk12 K) (Z.to_nat k) = Some (Z_to_bv 8 (znth ebuf0 k))) ->
    ffp_H5 oc w fl t2 p2 (K_pl K) big a r z l ebuf0 estr = Some (o1, ret) ->
    Z.lor t2 32 <> CHR_f ->
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) (Z_to_bv 64 70) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 p2) x19 (Z_to_bv 64 7110312) (Z_to_bv 64 (K_pl K)) (Z_to_bv 64 rp)
               (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) (Z_to_bv 64 (Z.land t2 18446744073709551583)) (Z_to_bv 64 (Z.lor p2 a8)) (Z_to_bv 64 (K_pl K + l)) (Z_to_bv 64 p2)
               x28 x29 x30 x31)
          (K_Ft K) (Z_to_bv 64 0x156274) fc None m (seg_rom asegs)).
  Proof using AB AF GLO J256 L_100 L_eloop ROOM SPHI SPLO RIP FXI HA0.
    intros until ebuf0; intros MV BIG LW LB REL ZERO Hlo Hlor Ha Hz Hzm Hrzm Hr Hrp ALLW He Hp2 Ht2 Hnz Haz Ha8 Ha8iff Hpalt Hl Hep Leb EBR HH Kf.
    destruct K as [padb jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft]. cbn [K_p1 K_prefix K_pl K_Ft K_jk12 K_jk37] in HH, EBR, MV |- *.
    dest_emw2 MV. prune. pose proof (zr_word sp : (0 <= bv_unsigned sp < 2^64)%Z) as Rsp.
    assert (Rfw : (0 <= Fp < 2^64)%Z) by apply (zr_word fw).
    pose proof (rw_cells_CB_length _ _ _ _ _ BF) as LB37.
    pose proof (rw_cells_CB_length _ _ _ _ _ EB) as LE12.
    assert (Rpalt : (0 <= palt <= 1)%Z) by (rewrite Hpalt; destruct (_ || _); lia).
    destruct (EBR Kf) as (Hestr & Eestrp & RELE). subst estrp.

    unfold ffp_H5 in HH. rewrite (proj2 (Z.eqb_neq _ _) Kf) in HH. unfold fmt_fp_emit_e in HH. cbv zeta in HH.
    destruct (zboxed_intro (if z <=? a then a + 1 else z)%Z) as [z' Ez']. apply zboxed_eq in Ez'. rewrite <- Ez' in HH.
    assert (Rz' : (a < z' /\ z' <= zm)%Z).
    { rewrite Ez'. destruct (Z.leb_spec0 z a); [|lia]. pose proof (Haz Kf ltac:(lia)). lia. }
    destruct (fmt_fp_eloop BIG_FUEL big a z' fl (a, p2, oc)) as [[[d' p'] o']|] eqn:HEL; [|discriminate HH]. cbv beta iota in HH.
    destruct (pad o' CHR_0 (p' + 18) 18 0) as [o2|] eqn:HP; [|discriminate HH]. cbv beta iota in HH.
    pose proof (H6_extends _ _ _ _ _ _ _ HH) as EXT6. apply extends_length in EXT6. unfold out in EXT6. rewrite app_length in EXT6.
    rewrite (zsub_length ebuf0 estr (12 - estr)) in EXT6 by (rewrite ?Leb; lia).
    pose proof (pad_extends _ _ _ _ _ _ HP) as PE. apply extends_length in PE.

    assert (J9c : forall m1 bf1 (x1' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x21' x26' x27' x28' x29' x30' x31' : word),
      emw (MidK padb jk40 jk8 jk3 jk12 bf1 p1 prefix pl plz pfx Ft) (bv_unsigned sp + -417 + estr) (pl + l) (Z.land fl 73728) a8 84566 o' m1 fc ->
      u32arr asegs m1 (bv_unsigned sp + -1056) ws -> (-9 <= p' <= p2)%Z ->
      evt asegs POST
        (MS (mkR x1' SPv gp tp x5' x6' x7' sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10' x11' x12' x13' x14' x15' x16' x17'
                 (Z_to_bv 64 p') (Z_to_bv 64 14757395258967641293) (Z_to_bv 64 48) x21' (Z_to_bv 64 10) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z'))
                 (Z_to_bv 64 (bv_unsigned sp + -405)) (Z_to_bv 64 99) x26' x27' x28' x29' x30' x31')
            Ft (Z_to_bv 64 0x1563ec) fc None m1 (seg_rom asegs))).
    { intros m1 bf1 x1' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x21' x26' x27' x28' x29' x30' x31' MV1 BIG1 Hp'.
      clear dependent m. clear HEL Hnz Haz Ha8iff EBR Hrp ALLW REL ZERO Hr Hlo Hlor Ha Hz Hzm Hrzm He Ht2 Ha8 Hpalt LB Ez' Rz'.
      dest_emw2 MV1. dest_wfile WF.
      pose proof (pad_length _ _ _ _ _ _ HP) as PL. change (negb (Z.land 0 (Z.lor LEFT_ADJ ZERO_PAD) =? 0)%Z) with false in PL. cbn [orb] in PL.
      assert (PL' : (length o2 = length o' + Z.to_nat (Z.max 0 p'))%nat).
      { destruct (Z.le_gt_cases (p' + 18) 18) as [Hc|Hc]; [rewrite (proj2 (Z.leb_le _ _) Hc) in PL | rewrite (proj2 (Z.leb_gt _ _) Hc) in PL]; lia. }
      clear PL. assert (Rp3 : (p' < 256)%Z) by lia.
      zs. replace (bv_swrap 32 (Z.land p' 18446744073709551615 + 18)) with (p' + 18)%Z by (rewrite land_W64, swrap32_eq; mlia).
      zs. zs. zs. zs. zs.
      set (c0 := zb o') in *. assert (Lc0 : length c0 = length o') by (subst c0; apply zb_length).
      set (jk := skipn (length o' - length o0) junk0) in *.
      assert (Ljk : (length jk = length junk0 - (length o' - length o0))%nat) by (subst jk; apply skipn_length).
      assert (Hpn : (pad_n (p' + 18) 18 0 = Z.max 0 p')%Z).
      { unfold pad_n. change (negb (Z.land 0 (Z.lor LEFT_ADJ ZERO_PAD) =? 0)%Z) with false. cbn [orb]. destruct (Z.leb_spec0 (p' + 18) 18); lia. }
      destruct (stk_split asegs _ _ (bv_unsigned sp + -1056 - 2608) _ ST ltac:(lia)) as [STlo STf]. clear ST.
      zs.
      lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
        eapply evt_cut;
        [ eapply pad_callR;
          [ exact FC | exact BUF | exact FLG | exact LBF | exact Bpos | exact Bhi | exact SEPfb | exact GOT | exact SSP
          | exact STf | hyp
          | slia | slia | slia | slia | slia
          | rewrite Hpn, Ljk; clear_fat; clear_logic; lia
          | slia | slia | slia | slia
            | solve_MU | solve_WM | lia | lia ]
        | rewrite Hpn; clear FC BUF STf; post_call segs m ]
      end.
      norm_rsegs.
      match goal with X : stk _ _ (bv_unsigned sp + -1056 - 2608)%Z _ |- _ =>
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (stk_merge asegs mm _ _ _ STlo X ltac:(lia)) as ST end; clear STlo X end.
      try match goal with X : ssp_cells _ _ |- _ => destruct X as [GOT SSP] end. unfold got_ssp, ssp_guard in *.
      rewrite ?Hpn in *.
      lazymatch goal with X : wfile _ _ _ _ _ _ _ (c0 ++ _) _ |- _ =>
        subst c0; subst jk; rewrite skipn_skipn in X;
        replace (zb o' ++ repeat (Z_to_bv 8 48) (Z.to_nat (Z.max 0 p'))) with (zb o2) in X
          by (rewrite (pad_model o' CHR_0 (p' + 18) 18 0 ltac:(clear -Rp3; lia)) in HP; injection HP as <-; rewrite Hpn, zb_app; unfold zb at 2; unfold zrepeat; rewrite map_repeat; reflexivity);
        replace (Z.to_nat (Z.max 0 p') + (length o' - length o0))%nat with (length o2 - length o0)%nat in X by (clear_fat; clear_logic; lia)
      end.

      clear FLG LBF Bpos Bhi SEPfb.
      lazymatch goal with X : wfile _ _ _ _ _ _ _ (zb o2) _ |- _ => dest_wfile X end.
      zs. cbv beta. zs. rewrite FLG. zs. zs. if_cases Kfe; zify_cond Kfe; [exfalso; lia|].
      zs. zs. zs.
      replace (Z_to_bv 64 (bv_unsigned sp + -405 - (bv_unsigned sp + -417 + estr))) with (Z_to_bv 64 (12 - estr)) by (f_equal; lia).
      zs. zs.
      pose proof (u8arr_of_rw_cells _ _ _ _ _ EB) as EBA.
      pose proof (bytes_at_slice _ _ _ (Z.to_nat estr) (Z.to_nat (12 - estr)) (proj1 EBA) ltac:(rewrite LE12; lia)) as SRC. clear EBA.
      rewrite (rel_sliceN jk12 ebuf0 12 estr (12 - estr) RELE ltac:(rewrite LE12; lia) ltac:(rewrite Leb; lia) ltac:(lia) ltac:(lia) ltac:(lia)) in SRC.
      rewrite Z2Nat.id in SRC by lia.
      set (ebs := zsub ebuf0 estr (12 - estr)) in *.
      assert (Lebs : length ebs = Z.to_nat (12 - estr)) by (subst ebs; apply zsub_length; rewrite ?Leb; lia).
      set (pbs := zb ebs) in *. assert (Lpbs : length pbs = Z.to_nat (12 - estr)) by (subst pbs; rewrite zb_length; exact Lebs).
      set (c2 := zb o2) in *. assert (Lc2 : length c2 = length o2) by (subst c2; apply zb_length).
      set (jk2 := skipn (length o2 - length o0) junk0) in *.
      assert (Ljk2 : (length jk2 = length junk0 - (length o2 - length o0))%nat) by (subst jk2; apply skipn_length).
      destruct (stk_split asegs _ _ (bv_unsigned sp + -1056 - 2304) _ ST ltac:(lia)) as [STlo STf]. clear ST.
      zs.
      lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
        eapply evt_cut;
        [ eapply fwritex_callR;
          [ exact FC | exact BUF | exact FLG | exact LBF | exact Bpos | exact Bhi | exact SEPfb
          | exact SRC
          | rewrite Lpbs, Z2Nat.id by lia; reflexivity
          | rewrite Lpbs, Ljk2; clear_fat; clear_logic; lia
          | exact STf
          | hyp
          | slia | slia | slia | slia | slia | slia | slia | slia | slia
          | solve_MU | solve_WM | lia | chk_src ]
        | clear FC BUF STf; post_call segs m ]
      end.
      norm_rsegs.
      match goal with X : stk _ _ (bv_unsigned sp + -1056 - 2304)%Z _ |- _ =>
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (stk_merge asegs mm _ _ _ STlo X ltac:(lia)) as ST end; clear STlo X end.
      lazymatch goal with X : wfile _ _ _ _ _ _ _ (c2 ++ pbs) _ |- _ =>
        subst c2 pbs; rewrite <- zb_app in X; subst jk2; rewrite skipn_skipn, zb_length, Lebs in X;
        replace (Z.to_nat (12 - estr) + (length o2 - length o0))%nat with (length (o2 ++ ebs) - length o0)%nat in X by (rewrite app_length, Lebs; lia) end.
      match goal with X : bytes_at _ _ (bv_unsigned sp + -417 + estr)%Z _ |- _ => clear X end.
      unfold out in HH.
      zs.
      eapply L_100 with (K := MidK padb jk40 jk8 jk3 jk12 bf1 p1 prefix pl plz pfx Ft) (oc := o2 ++ ebs) (estrp := (bv_unsigned sp + -417 + estr)%Z) (a8v := a8) (v440 := 84566%Z) (l := l);
        [ mk_emw | exact BIG1 | exact LW | dlia | exact HH ]. }

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m0cur _) => rename m0cur into mc end.
    assert (J2c : forall (x23' : word), x23' = Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z') ->
      evt asegs POST
        (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) (Z_to_bv 64 70) x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 p2) x19 (Z_to_bv 64 7110312) (Z_to_bv 64 pl) (Z_to_bv 64 rp)
                 x23' (Z_to_bv 64 (Z.land t2 18446744073709551583)) (Z_to_bv 64 (Z.lor p2 a8)) (Z_to_bv 64 (pl + l)) (Z_to_bv 64 p2)
                 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x15627c) fc None mc (seg_rom asegs))).
    2:{ zs. if_cases Kaz; zify_cond Kaz.
        - apply J2c. rewrite Ez'. rewrite (proj2 (Z.leb_gt z a)) by lia. reflexivity.
        - zs. apply J2c. rewrite Ez'. rewrite (proj2 (Z.leb_le z a)) by lia. f_equal. lia. }
    intros x23' ->.
    zs. if_cases Kp; zify_cond Kp.
    { exfalso. first [lia | rewrite land_W64 in Kp; rewrite Z.mod_small in Kp by lia; lia]. }
    do 12 zs.
    eapply (L_eloop BIG_FUEL) with (K := MidK padb jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft) (lo := lo) (zm := zm) (a := a) (z := z') (d := a)
      (oc := oc) (estrp := (bv_unsigned sp + -417 + estr)%Z) (ppl := (pl + l)%Z) (fl2 := Z.land fl 73728) (a8 := a8);
      [ mk_emw | exact BIG | exact LW | exact LB | exact REL | dlia | dlia | dlia | exact Hp2 | exact ALLW | exact Ha8 | exact Ha8iff | exact LB37 | exact HEL | lia | ].
    intros m1 bf1 x1' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x21' x26' x27' x28' x29' x30' x31' MV1 BIG1 LB1 Hp'.
    eapply J9c; [ unfold K_set37 in MV1; cbn [K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft] in MV1; exact MV1 | exact BIG1 | exact Hp' ].
  Qed.

End FmtFp.
