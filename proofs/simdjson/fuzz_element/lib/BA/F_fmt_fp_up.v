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

  Hypothesis L_0b8 :
    forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x25 x26 x28 x29 x30 x31 : word) fc K
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

  Lemma L_strip1 : forall (k : nat) Q m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fc
      (ws : list word) (big : list Z) (lo a z z' : Z),
    mem_inv asegs m -> u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    (forall i, (lo <= i < z)%Z -> znth big i = wval ws i) ->
    (0 <= lo <= a)%Z -> (a <= z <= 128)%Z ->
    fmt_fp_strip k big a z = Some z' ->
    (forall x12' x23', evt asegs Q
       (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10 x11 x12' x13 x14 x15 x16 x17
                x18 x19 x20 x21 x22 x23' x24 x25 x26 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z')) x28 x29 x30 x31)
           Ft (Z_to_bv 64 0x155458) fc None m (seg_rom asegs))) ->
    evt asegs Q
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x24 x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 0x1554c8) fc None m (seg_rom asegs)).
  Proof using GLO J256 SPHI SPLO o0 o1 RIP FXI HA0 AB AF ROOM.
    induction k as [|k IH]; intros until z'; intros MI BIG LW REL Hlo Hz HS CONT; [discriminate HS|].
    pose_word_ranges. rewrite fmt_fp_strip_step in HS.
    zs. zs. if_cases Kaz; zify_cond Kaz.
    -   rewrite (proj2 (Z.ltb_ge a z)) in HS by lia. cbn [andb] in HS. injection HS as <-. apply CONT.
    - rewrite (proj2 (Z.ltb_lt a z)) in HS by lia. cbn [andb] in HS.
      pose proof (u32arr_read asegs _ _ _ (z - 1) _ _ BIG (nth_error_wnth ws (z - 1) ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
      zs. zs. zs. if_cases Kw; zify_cond Kw; [rewrite sx32_zero in Kw | rewrite sx32_nonzero in Kw]; fold (wval ws (z - 1)) in Kw;
        rewrite <- (REL (z - 1)%Z) in Kw by lia.
      +
        rewrite (proj2 (Z.eqb_eq _ _) Kw) in HS.
        replace (bv_unsigned sp + -1056 + 4 * z + -4)%Z with (bv_unsigned sp + -1056 + 4 * (z - 1))%Z by lia.
        pose proof (fmt_fp_strip_res _ _ _ _ _ HS ltac:(lia)) as Hzr.
        eapply IH with (lo := lo); [ exact MI | exact BIG | exact LW | | dlia | dlia | exact HS | exact CONT ].
        intros i Hi. apply REL. lia.
      + rewrite (proj2 (Z.eqb_neq _ _) Kw) in HS. injection HS as <-. zs. apply CONT.
  Qed.

  Lemma L_upin : forall (k : nat) m (x1 x5 x6 x7 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) fc K
      (ws : list word) (big big' : list Z) (e2m sh a d zm c cr c' : Z),
    midv K m fc e2m ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (a <= i < zm)%Z -> znth big i = wval ws i) ->
    (1 <= a <= d)%Z -> (d < zm <= 128)%Z -> (1 <= sh <= 29)%Z -> (0 <= cr < 2^64)%Z -> c = (cr mod 4294967296)%Z ->
    fmt_fp_up_inner sh k a (big, d, c) = Some (big', (a - 1)%Z, c') ->
    (forall m' ws' (x : Z),
       midv K m' fc e2m ->
       u32arr asegs m' (bv_unsigned sp + -1056) ws' -> length ws' = 128%nat ->
       length big' = 128%nat -> (forall i, (a <= i < zm)%Z -> znth big' i = wval ws' i) ->
       (0 <= x < 2^61 + 2^32)%Z -> c' = (x / 1000000000)%Z ->
       evt asegs POST
         (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) (Z_to_bv 64 19342813113834067) (Z_to_bv 64 1000000000)
                  (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * (a - 1))) (Z_to_bv 64 c') (Z_to_bv 64 x) (Z_to_bv 64 (x mod 1000000000)) x16 x17
                  x18 (Z_to_bv 64 sh) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
             (K_Ft K) (Z_to_bv 64 0x1554b8) fc None m' (seg_rom asegs))) ->
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) (Z_to_bv 64 19342813113834067) (Z_to_bv 64 1000000000)
               (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d)) (Z_to_bv 64 cr) x14 x15 x16 x17
               x18 (Z_to_bv 64 sh) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (K_Ft K) (Z_to_bv 64 0x155484) fc None m (seg_rom asegs)).
  Proof using AB AF GLO J256 SPHI SPLO RIP FXI HA0 ROOM.
    induction k as [|k IH]; intros until c'; intros MV BIG LW LB REL Had Hdz Hsh Hcr Hc HI CONT; [discriminate HI|].
    destruct K as [pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft]. dest_midv MV. pose_word_ranges.
    assert (Rfw : (0 <= Fp < 2^64)%Z) by apply (zr_word fw).
    rewrite fmt_fp_up_inner_step in HI. rewrite (proj2 (Z.leb_le a d)) in HI by lia. cbv zeta in HI.
    pose proof (wval_range ws d) as Rv. rewrite <- (REL d) in Rv by lia.
    pose proof (u32arr_read asegs _ _ _ d _ _ BIG (nth_error_wnth ws d ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
    zs. unfold zx32. change ((bv_unsigned (wnth ws d) mod 2 ^ 32)%Z) with (wval ws d). rewrite <- (REL d) by lia.
    set (v := znth big d) in *.
    assert (Hc2 : Z.land cr 4294967295 = c) by (rewrite Hc; change 4294967295%Z with (2^32 - 1)%Z; rewrite zb_land_mask by lia; reflexivity).
    assert (Rc : (0 <= c < 4294967296)%Z) by (rewrite Hc; apply Z.mod_pos_bound; lia).
    zs. zs. rewrite Hc2. zs. rewrite (land63_small sh) by lia. zs.
    assert (Rx : (0 <= Z.shiftl v sh + c < 2^61 + 2^32)%Z).
    { rewrite Z.shiftl_mul_pow2 by lia. assert (2 ^ sh <= 2 ^ 29)%Z by (apply Z.pow_le_mono_r; lia).
      assert (0 < 2 ^ sh)%Z by (apply Z.pow_pos_nonneg; lia). change (2^29)%Z with 536870912%Z in *. nia. }
    set (x := (Z.shiftl v sh + c)%Z) in *.
    zs. zs. zs. rewrite ?(land_W64_small x) by lia. rewrite (land_W64_small _ (mulhu_M_range x ltac:(lia))). rewrite div1e9_magic by lia.
    set (q := (x / 1000000000)%Z) in *.
    assert (Rq : (0 <= q /\ q * 1000000000 <= x /\ x < q * 1000000000 + 1000000000)%Z) by (subst q; Z.div_mod_to_equations; lia).
    zs. zs. rewrite Z_to_bv_swrap32. rewrite ?(land_W64_small x), ?(land_W64_small (q * 1000000000)) by lia.
    rewrite (sext32_small (x - q * 1000000000)) by lia.
    replace (x - q * 1000000000)%Z with (x mod 1000000000)%Z by (subst q; Z.div_mod_to_equations; lia).
    assert (Rxm : (0 <= x mod 1000000000 < 1000000000)%Z) by (apply Z.mod_pos_bound; lia).
    pose proof (u32arr_store_ok asegs _ _ _ d _ BIG ltac:(lia) eq_refl) as SOK.
    zs.
    pose proof (u32arr_write asegs _ _ _ d (Z_to_bv 64 (x mod 1000000000)) BIG ltac:(lia)) as BIG'. clear BIG.
    store_done. rename BIG' into BIG.
    assert (REL' : forall i, (a <= i < zm)%Z -> znth (zupd big d (x mod 1000000000)) i = wval (upd ws (Z.to_nat d) (Z_to_bv 64 (x mod 1000000000))) i).
    { intros i Hi. destruct (Z.eq_dec i d) as [->|Hne].
      - rewrite znth_zupd_eq by (unfold zlength; lia). rewrite wval_upd_same by lia. rewrite unsigned_lit by lia.
        rewrite (Z.mod_small (x mod 1000000000) 4294967296) by lia. reflexivity.
      - rewrite znth_zupd_neq by lia. rewrite wval_upd_other by lia. apply REL. lia. }
    zs. zs. if_cases Kd; zify_cond Kd.
    -
      replace (bv_unsigned sp + -1056 + 4 * d + -4)%Z with (bv_unsigned sp + -1056 + 4 * (d - 1))%Z by lia.
      eapply IH with (c := u32 (x / 1000000000)%Z) (K := MidK pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft);
        [ mk_midv | exact BIG | rewrite upd_length; exact LW | rewrite zupd_length; exact LB | exact REL'
        | dlia | dlia | dlia | subst q; split; [dlia | apply Z.div_lt_upper_bound; lia] | unfold u32; reflexivity | exact HI | exact CONT ].
    -
      destruct k as [|k']; [discriminate HI|].
      rewrite fmt_fp_up_inner_step in HI. rewrite (proj2 (Z.leb_gt _ _)) in HI by lia.
      injection HI as <- Ha1 Hc'. pose proof LB as LB'. rewrite <- (zupd_length big d (x mod 1000000000)) in LB'.
      replace (bv_unsigned sp + -1056 + 4 * d + -4)%Z with (bv_unsigned sp + -1056 + 4 * (a - 1))%Z by lia.
      assert (Eqc : c' = q).
      { rewrite <- Hc'. unfold u32. subst q. apply Z.mod_small. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
      replace (Z_to_bv 64 q) with (Z_to_bv 64 c') by (rewrite Eqc; reflexivity).
      eapply CONT; [ mk_midv | exact BIG | rewrite upd_length; exact LW | exact LB' | | | ].
      + intros i Hi. apply REL'. lia.
      + lia.
      + rewrite Eqc. reflexivity.
  Qed.

  Definition UPH (k : nat) : Prop :=
    forall m (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x21 x24 x25 x26 x27 x28 x29 x30 x31 : word) fc K
      (ws : list word) (big big' : list Z) (e2 a r z zm a' z' e2' : Z),
    midv K m fc e2 ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (a <= i < zm)%Z -> znth big i = wval ws i) ->
    (e2 <= 29 * a)%Z -> (0 < e2 <= 1024)%Z -> (a <= z <= zm)%Z -> (zm <= 128)%Z -> (r < zm)%Z -> (a <= r)%Z -> (r = 0 \/ r = 122)%Z ->
    fmt_fp_up k (big, a, z, e2) = Some (big', a', z', e2') ->
    prov_F (K_p1 K) r (big', a', z', e2') ->
    ffp_F o0 w fl t (K_p1 K) (K_prefix K) (K_pl K) big' a' r z' e2' = Some (o1, ret) ->
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) (Z_to_bv 64 19342813113834067) (Z_to_bv 64 1000000000)
               x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (K_p1 K)) (Z_to_bv 64 e2) (Z_to_bv 64 (Z.lor t 32)) x21 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * r))
               (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x24 x25 x26 x27 x28 x29 x30 x31)
          (K_Ft K) (Z_to_bv 64 0x15546c) fc None m (seg_rom asegs)).

  Lemma L_up078 : forall (k : nat), UPH k ->
    forall m (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x21 x24 x25 x26 x27 x28 x29 x30 x31 : word) fc K
      (ws : list word) (big2 big' : list Z) (e2 sh a2 r z zm z2 a' z' e2' : Z),
    midv K m fc e2 ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big2 = 128%nat -> (forall i, (a2 <= i < zm)%Z -> znth big2 i = wval ws i) ->
    sh = Z.min 29 e2 -> (e2 - sh <= 29 * a2)%Z -> (0 < e2 <= 1024)%Z -> (0 <= a2 <= z)%Z -> (z <= zm <= 128)%Z -> (r < zm)%Z -> (a2 <= r)%Z -> (r = 0 \/ r = 122)%Z ->
    fmt_fp_strip BIG_FUEL big2 a2 z = Some z2 ->
    fmt_fp_up k (big2, a2, z2, (e2 - sh)%Z) = Some (big', a', z', e2') ->
    prov_F (K_p1 K) r (big', a', z', e2') ->
    ffp_F o0 w fl t (K_p1 K) (K_prefix K) (K_pl K) big' a' r z' e2' = Some (o1, ret) ->
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a2)) (Z_to_bv 64 19342813113834067) (Z_to_bv 64 1000000000)
               x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (K_p1 K)) (Z_to_bv 64 sh) (Z_to_bv 64 (Z.lor t 32)) x21 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * r))
               (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x24 x25 x26 x27 x28 x29 x30 x31)
          (K_Ft K) (Z_to_bv 64 0x1554c8) fc None m (seg_rom asegs)).
  Proof using AB AF GLO J256 L_0b8 SPHI SPLO RIP FXI HA0 ROOM.
    intros k IHk. intros until e2'; intros MV BIG LW LB REL Hsh Ha2 He2 Haz Hz Hrzm Har Hr HS HU PF HF.
    destruct K as [pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft]. dest_midv MV. pose_word_ranges.
    assert (Rfw : (0 <= Fp < 2^64)%Z) by apply (zr_word fw).
    pose proof (fmt_fp_strip_res _ _ _ _ _ HS ltac:(lia)) as Hz2.
    eapply (L_strip1 BIG_FUEL) with (lo := a2) (big := big2) (z' := z2);
      [ hyp | exact BIG | exact LW | intros i Hi; apply REL; lia | lia | lia | exact HS | ].
    intros x12' x23'.
    zs. rewrite sx32_lit by lia. zs. rewrite Z_to_bv_swrap32. rewrite (sext32_small (e2 - sh)) by lia.
    zs. zs. zs. if_cases Ke; zify_cond Ke.
    -
      apply Bool.andb_false_iff in Ke.
      assert (Esh : (e2 - sh = 0)%Z) by (destruct Ke as [Ke|Ke]; apply Z.ltb_ge in Ke; lia).
      clear Ke. rewrite Esh in *.
      destruct k as [|k']; [discriminate HU|]. rewrite fmt_fp_up_step in HU. cbn [Z.ltb] in HU. injection HU as <- <- <- <-.
      eapply L_0b8 with (K := MidK pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft) (zm := zm);
        [ mk_midv | exact BIG | exact LW | exact LB | exact REL | dlia | dlia | dlia | dlia | exact Hr | dlia | exact PF | exact HF ].
    -
      eapply (IHk) with (K := MidK pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft) (zm := zm);
        [ mk_midv | exact BIG | exact LW | exact LB | exact REL | dlia | dlia | dlia | dlia | dlia | dlia | exact Hr | exact HU | exact PF | exact HF ].
  Qed.

  Lemma fmt_fp_up_inner_carry : forall sh k a big d c big' d' c',
    fmt_fp_up_inner sh k a (big, d, c) = Some (big', d', c') -> (0 <= c)%Z -> (0 <= c')%Z.
  Proof using J256 o0 o1 RIP FXI HA0 AB AF ROOM.
    induction k as [|k IH]; intros a big d c big' d' c' H Hc; [discriminate H|].
    rewrite fmt_fp_up_inner_step in H. destruct (a <=? d).
    - cbv zeta in H. eapply IH; [exact H|]. unfold u32.
      pose proof (Z.mod_pos_bound ((Z.shiftl (znth big d) sh + c) / 1000000000) (2^32)). lia.
    - injection H; lia.
  Qed.

  Lemma L_up : forall k, UPH k.
  Proof using AB AF GLO J256 L_0b8 SPHI SPLO RIP FXI HA0 ROOM.
    induction k as [|k IH]; unfold UPH; intros until e2'; intros MV BIG LW LB REL Ha He2 Haz Hzm Hrzm Har Hr HU PF HF; [discriminate HU|].
    destruct K as [pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft]. dest_midv MV. pose_word_ranges.
    assert (Rfw : (0 <= Fp < 2^64)%Z) by apply (zr_word fw).
    rewrite fmt_fp_up_step in HU. rewrite (proj2 (Z.ltb_lt 0 e2)) in HU by lia.
    unfold fmt_fp_up_body in HU.
    destruct (fmt_fp_up_inner (Z.min 29 e2) BIG_FUEL a (big, (z - 1)%Z, 0%Z)) as [[[big1 d1] c1]|] eqn:HI; [|discriminate HU].
    pose proof (fmt_fp_up_inner_res _ _ _ _ _ _ _ _ _ HI ltac:(lia)) as [-> LB1].
    destruct (if negb (c1 =? 0) then ((a - 1)%Z, zupd big1 (a - 1) c1) else (a, big1)) as [a2 big2] eqn:Eab.
    destruct (fmt_fp_strip BIG_FUEL big2 a2 z) as [z2|] eqn:HS; [|discriminate HU].
    assert (Hab : (0 <= a2 <= a /\ a - 1 <= a2)%Z /\ length big2 = 128%nat).
    { destruct (negb (c1 =? 0)); injection Eab as <- <-; rewrite ?zupd_length; lia. }
    assert (Hc1 : (0 <= c1)%Z /\ (c1 = 0%Z -> a2 = a /\ big2 = big1) /\ (c1 <> 0%Z -> a2 = (a - 1)%Z /\ big2 = zupd big1 (a - 1) c1)).
    { split; [eapply fmt_fp_up_inner_carry; [exact HI|lia] |].
      revert Eab. destruct (Z.eqb_spec c1 0) as [E|E]; cbn [negb]; intros Eab; injection Eab as <- <-.
      - split; [intros _; split; reflexivity | intros X; exfalso; exact (X E)].
      - split; [intros X; exfalso; exact (E X) | intros _; split; reflexivity]. }

    assert (J028 : evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) (Z_to_bv 64 19342813113834067) (Z_to_bv 64 1000000000)
               (Z_to_bv 64 29) x13 x14 x15 x16 x17
               (Z_to_bv 64 p1) (Z_to_bv 64 (Z.min 29 e2)) (Z_to_bv 64 (Z.lor t 32)) x21 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * r))
               (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x24 x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 0x155478) fc None m (seg_rom asegs))).
    { zs. replace (bv_unsigned sp + -1056 + 4 * z + -4)%Z with (bv_unsigned sp + -1056 + 4 * (z - 1))%Z by lia.
      zs. if_cases Kza; zify_cond Kza.
      -
        unfold BIG_FUEL in HI. rewrite fmt_fp_up_inner_step in HI. rewrite (proj2 (Z.leb_gt _ _)) in HI by lia.
        injection HI as <- Haz1 <-. destruct Hc1 as (_ & Hc1 & _). destruct (Hc1 eq_refl) as [-> ->].
        eapply (L_up078 k IH) with (K := MidK pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft) (e2 := e2) (zm := zm);
          [ mk_midv | exact BIG | exact LW | exact LB | exact REL | reflexivity | dlia | dlia | dlia | dlia | dlia | dlia | exact Hr | exact HS | exact HU | exact PF | exact HF ].
      - zs.
        eapply L_upin with (K := MidK pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft) (d := (z - 1)%Z) (c := 0%Z) (big' := big1) (c' := c1) (zm := zm);
          [ mk_midv | exact BIG | exact LW | exact LB | exact REL | dlia | dlia | dlia | dlia | reflexivity | exact HI | ].
        intros m' ws' x MV' BIG' LW' LB1' REL' Rx Hcx.
        clear MI MU WM FRhi ST GOT SSP FRM FRs E2 EB BF FC BUF.
        dest_midv MV'.
        zs. if_cases Kx; zify_cond Kx.
        +
          assert (c1 = 0%Z) by (rewrite Hcx; apply Z.div_small; lia).
          destruct Hc1 as (_ & Hc1 & _). destruct (Hc1 ltac:(assumption)) as [-> ->].
          eapply (L_up078 k IH) with (K := MidK pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft) (e2 := e2) (zm := zm);
            [ mk_midv | exact BIG' | exact LW' | exact LB1' | exact REL' | reflexivity | dlia | dlia | dlia | dlia | dlia | dlia | exact Hr | exact HS | exact HU | exact PF | exact HF ].
        +
          assert (Hc1nz : c1 <> 0%Z) by (rewrite Hcx; intros E; apply Z.div_small_iff in E; lia).
          destruct Hc1 as (Rc1 & _ & Hc1). destruct (Hc1 Hc1nz) as [-> ->].
          assert (Rc1' : (c1 < 4294967296)%Z) by (rewrite Hcx; apply Z.div_lt_upper_bound; lia).
          clear Hcx Kx Rx Hc1 Eab BIG REL Kza.
          zs. replace (bv_unsigned sp + -1056 + 4 * a + -4)%Z with (bv_unsigned sp + -1056 + 4 * (a - 1))%Z by lia.
          pose proof (u32arr_store_ok asegs _ _ _ (a - 1) _ BIG' ltac:(lia) eq_refl) as SOK.
          zs.
          pose proof (u32arr_write asegs _ _ _ (a - 1) (Z_to_bv 64 c1) BIG' ltac:(lia)) as BIG2. clear BIG'.
          store_done.
          zs.
          eapply (L_up078 k IH) with (K := MidK pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft) (e2 := e2) (zm := zm);
            [ mk_midv | exact BIG2 | rewrite upd_length; exact LW' | rewrite zupd_length; exact LB1' | | reflexivity | dlia | dlia | dlia | dlia | dlia | dlia | exact Hr | exact HS | exact HU | exact PF | exact HF ].
          intros i Hi. destruct (Z.eq_dec i (a - 1)) as [->|Hne].
          * rewrite znth_zupd_eq by (unfold zlength; lia). rewrite wval_upd_same by lia. rewrite unsigned_lit by lia. symmetry. apply Z.mod_small. lia.
          * rewrite znth_zupd_neq by lia. rewrite wval_upd_other by lia. apply REL'. lia. }

    zs. zs. if_cases K29; zify_cond K29.
    - replace (Z_to_bv 64 e2) with (Z_to_bv 64 (Z.min 29 e2)) by (f_equal; lia). exact J028.
    - zs. replace (Z_to_bv 64 29) with (Z_to_bv 64 (Z.min 29 e2)) at 1 by (f_equal; lia). exact J028.
  Qed.

  Lemma L_fec : forall m (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fc pad jk40 jk8 jk3 jk12 jk37
      (ws : list word) (big : list Z) (e2 p1 a z prefix pl plz pfx : Z),
    finv m pad -> frm0 fc ->
    (forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k) ->
    rw_cells asegs m (bv_unsigned sp + -544)
      [C8 (Z_to_bv 64 0); CB 40 jk40; C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t); CB 8 jk8; C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 7110312);
       C8 (Z_to_bv 64 plz); C8 (Z_to_bv 64 pfx); C8 (Z_to_bv 64 pl); C8 (Z_to_bv 64 Fp)] ->
    rw_cells asegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 e2); CB 3 jk3] ->
    rw_cells asegs m (bv_unsigned sp + -417) [CB 12 jk12] ->
    rw_cells asegs m (bv_unsigned sp + -405) [CB 37 jk37] ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (a <= i < z)%Z -> znth big i = wval ws i) ->
    wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0 ->
    (0 <= prefix <= 6)%Z -> (0 <= pl <= 1)%Z -> plz = Z.b2z (pl =? 0)%Z -> pfx = (81734 + prefix)%Z ->
    (0 <= p1 < 2^20)%Z -> (-1102 <= e2 <= 1024)%Z -> (0 <= a < z)%Z -> (z <= 128)%Z ->
    a = (if e2 <? 0 then 0 else 122)%Z -> prov_E p1 big a z e2 ->
    ffp_E o0 w fl t p1 prefix pl big a a z e2 = Some (o1, ret) ->
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 p1) (Z_to_bv 64 e2) (Z_to_bv 64 (Z.lor t 32)) x21 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z))
               x24 x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 0x15543c) fc None m (seg_rom asegs)).
  Proof using AB AF GLO J256 L_0b8 SPHI SPLO RIP FXI HA0 ROOM.
    intros until pfx; intros FI FRM HFt FRs E2 EB BF BIG LW LB REL WF Hpre Hpl Hplz Hpfx Hp1 He2 Haz Hz Ha PE HE.
    dest_finv FI. dest_wfile WF. pose_word_ranges.
    assert (Rfw : (0 <= Fp < 2^64)%Z) by apply (zr_word fw).
    unfold ffp_E in HE.
    destruct (fmt_fp_up UP_FUEL (big, a, z, e2)) as [[[[big' a'] z'] e2']|] eqn:HU; [|discriminate HE].
    assert (PF : prov_F p1 a (big', a', z', e2')) by (exists big, z, e2; split; [exact PE | exact HU]).
    zs. if_cases Ke; zify_cond Ke.
    -
      rewrite land_W64 in Ke.
      assert (He : (e2 <= 0)%Z).
      { destruct (Z.le_gt_cases e2 0) as [|Hgt]; [assumption|]. rewrite Z.mod_small in Ke by lia.
        apply Bool.andb_false_iff in Ke; destruct Ke as [Ke|Ke]; apply Z.ltb_ge in Ke; lia. }
      clear Ke. unfold UP_FUEL in HU. rewrite fmt_fp_up_step in HU. rewrite (proj2 (Z.ltb_ge 0 e2)) in HU by lia. injection HU as <- <- <- <-.
      zs. zs.
      eapply L_0b8 with (K := MidK pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft) (r := a) (zm := z);
        [ mk_midv | exact BIG | exact LW | exact LB | exact REL | dlia | dlia | dlia | dlia | destruct (e2 <? 0); lia | dlia | exact PF | exact HE ].
    -
      rewrite land_W64 in Ke0, Ke1.
      assert (He : (0 < e2)%Z).
      { destruct (Z.le_gt_cases e2 0) as [Hle|]; [|assumption]. exfalso.
        destruct (Z.eq_dec e2 0) as [->|Hne]; [rewrite Zmod_0_l in Ke0; lia|].
        replace (e2 mod 2^64)%Z with (e2 + 2^64)%Z in Ke1 by (apply Z.mod_unique with (q := (-1)%Z); lia). lia. }
      clear Ke0 Ke1. zs. zs. zs. zs. zs. zs.
      eapply (L_up UP_FUEL) with (K := MidK pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft) (r := a) (zm := z);
        [ mk_midv | exact BIG | exact LW | exact LB | exact REL | rewrite (proj2 (Z.ltb_ge e2 0)) in Ha by lia; lia | dlia | dlia | dlia | dlia | dlia | destruct (e2 <? 0); lia | exact HU | exact PF | exact HE ].
  Qed.

End FmtFp.
