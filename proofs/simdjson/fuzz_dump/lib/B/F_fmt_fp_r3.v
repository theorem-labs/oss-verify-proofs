(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Sf_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Arr.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim SoftFloat FmtFp.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Sf_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import FmtFp_split FmtFp_splitR FmtFp_splitH FmtFp_facts FmtFp_facts2.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import F_memset F_memcpy F_fwritex F_pad F_frexpl F_divtf3_main F_fmt_fp_lib F_fmt_fp_calls F_fmt_fp_pre F_fmt_fp_pre2 F_fmt_fp_pre3 F_fmt_fp_pre4.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import R_m2s I_consts F_achk Fe_icalls.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import StoreFast.
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
  Hypothesis GLO : (7123888 <= bv_unsigned sp - 6944)%Z.
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
               Ft (ret_pc ra) fc' None m' (seg_rom bsegs)
      /\ munch Wfp m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ frm0 fc'
      /\ stk bsegs m' (bv_unsigned sp - 6944) (bv_unsigned sp)
      /\ wfile m' Fp fl0 j1 j2 lbfw B (zb o1) (skipn (length o1 - length o0) junk0)
      /\ ssp_cells m' canary
      /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k).

  Definition hi_cells (pad256 : list byte) : list cell :=
    [CB 256 pad256; C8 canary; C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra].

  Definition finv (m : word -> option byte) (pad256 : list byte) : Prop :=
    mem_inv bsegs m /\ munch Wfp m0 m /\ wmono bsegs m0 m
    /\ rw_cells bsegs m (bv_unsigned sp + -368) (hi_cells pad256)
    /\ stk bsegs m (bv_unsigned sp - 6944) (bv_unsigned sp + -1056)
    /\ ro_cells bsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ ro_cells bsegs m ssp_guard [C8 canary].
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
    /\ rw_cells bsegs m (bv_unsigned sp + -544)
         [C8 (Z_to_bv 64 0); CB 40 (K_jk40 K); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t); CB 8 (K_jk8 K); C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 7123880);
          C8 (Z_to_bv 64 (K_plz K)); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)]
    /\ rw_cells bsegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 e2m); CB 3 (K_jk3 K)]
    /\ rw_cells bsegs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells bsegs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ K_plz K = Z.b2z (K_pl K =? 0)%Z /\ K_pfx K = (81572 + K_prefix K)%Z
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
    /\ rw_cells bsegs m (bv_unsigned sp + -544)
         [C8 (Z_to_bv 64 0); CB 40 (K_jk40 K); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t); CB 8 (K_jk8 K); C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 7123880);
          C8 (Z_to_bv 64 (K_plz K)); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)]
    /\ rw_cells bsegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 e2m); CB 3 (K_jk3 K)]
    /\ rw_cells bsegs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells bsegs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ (0 <= K_plz K < 2^64)%Z /\ K_pfx K = (81572 + K_prefix K)%Z
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
    /\ rw_cells bsegs m (bv_unsigned sp + -544)
         ([C8 (Z_to_bv 64 0)] ++ cs5 ++ [C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t); C8 (Z_to_bv 64 (K_p1 K)); C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 7123880);
          C8 (Z_to_bv 64 z456); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)])
    /\ rw_cells bsegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 0); CB 3 (K_jk3 K)]
    /\ rw_cells bsegs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells bsegs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ (0 <= z456 < 2^64)%Z /\ K_pfx K = (81572 + K_prefix K)%Z
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
    { apply (rw_cells_merge bsegs m _ [C8 (Z_to_bv 64 0)] cs5) in FRs. rewrite Hsz in FRs.
      apply (rw_cells_merge bsegs m _ [C8 (Z_to_bv 64 0); CB 40 (cells_bytes cs5); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t)] [C8 (Z_to_bv 64 (K_p1 K))]
               [C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 7123880); C8 (Z_to_bv 64 z456); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)]) in FRs.
      cbn [cells_size csize cells_bytes cbytes app Nat.add] in FRs. rewrite app_nil_r in FRs. exact FRs. }
    split; [exact E2|]. split; [exact EB|]. split; [exact BF|]. split; [exact WF|].
    split; [exact Hpre|]. split; [exact Hpl|]. split; [exact Hplz|]. split; [exact Hpfx|]. exact Hp1.
  Qed.

  Definition emw (K : midK) (estrp ppl fl2 a8v v440 : Z) (oc : list Z) (m : word -> option byte) (fc : bv 32) : Prop :=
    finv m (K_pad K) /\ frm0 fc /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get (K_Ft K) k = reg_get F k)
    /\ rw_cells bsegs m (bv_unsigned sp + -544)
         [C8 (Z_to_bv 64 0); CB 40 (K_jk40 K); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 estrp); C8 (Z_to_bv 64 ppl); C8 (Z_to_bv 64 fl2); C8 (Z_to_bv 64 7123880);
          C8 (Z_to_bv 64 a8v); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 v440); C8 (Z_to_bv 64 Fp)]
    /\ rw_cells bsegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 0); CB 3 (K_jk3 K)]
    /\ rw_cells bsegs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells bsegs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb oc) (skipn (length oc - length o0) junk0)
    /\ (length o0 <= length oc)%nat
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ K_pfx K = (81572 + K_prefix K)%Z /\ (0 <= K_p1 K < 2^20)%Z.
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

  Hypothesis L_988 :
    forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x24 x25 x26 x28 x30 x31 : word) fc K
      (ws : list word) (big : list Z) (lo a r rp z zm e : Z),
    midw K m fc 0%Z ->
    u32arr bsegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (lo <= i < zm)%Z -> znth big i = wval ws i) ->
    (forall i, (zm <= i)%Z -> znth big i = 0%Z) ->
    (0 <= lo <= a)%Z -> (lo <= r)%Z -> (a <= zm)%Z -> (0 <= z <= zm)%Z -> (zm <= 128)%Z -> (r < zm)%Z -> (r = 0 \/ r = 122)%Z -> rp = (bv_unsigned sp + -1056 + 4 * r)%Z ->
    (forall i, (0 <= znth big i < 1000000000)%Z) ->
    (-2^20 <= e < 2^20)%Z ->
    prov_R (K_p1 K) (K_prefix K) (K_pl K) r big a z e ->
    ffp_H o0 w fl t (K_p1 K) (K_prefix K) (K_pl K) big a r z e = Some (o1, ret) ->
    evt bsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (K_p1 K)) x19 (Z_to_bv 64 (Z.lor t 32)) (Z_to_bv 64 e) (Z_to_bv 64 rp)
               x23 x24 x25 x26 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x28 (Z_to_bv 64 t) x30 x31)
          (K_Ft K) (Z_to_bv 64 0x15a138) fc None m (seg_rom bsegs)).

  Lemma L_978 : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x24 x25 x26 x28 x30 x31 : word) fc K
      (ws : list word) (big : list Z) (lo a r rp z zm d e zR : Z),
    midw K m fc 0%Z ->
    u32arr bsegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (lo <= i < zm)%Z -> znth big i = wval ws i) ->
    (forall i, (zm <= i)%Z -> znth big i = 0%Z) ->
    (0 <= lo <= a)%Z -> (lo <= r)%Z -> (a <= zm)%Z -> (lo <= d < z)%Z -> (z <= zm <= 128)%Z -> (r < zm)%Z -> (r = 0 \/ r = 122)%Z ->
    rp = (bv_unsigned sp + -1056 + 4 * r)%Z ->
    (forall i, (0 <= znth big i < 1000000000)%Z) ->
    (-2^20 <= e < 2^20)%Z ->
    zR = (if d + 1 <? z then d + 1 else z)%Z ->
    prov_R (K_p1 K) (K_prefix K) (K_pl K) r big a zR e ->
    ffp_H o0 w fl t (K_p1 K) (K_prefix K) (K_pl K) big a r zR e = Some (o1, ret) ->
    evt bsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (K_p1 K)) x19 (Z_to_bv 64 (Z.lor t 32)) (Z_to_bv 64 e) (Z_to_bv 64 rp)
               (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d)) x24 x25 x26 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x28 (Z_to_bv 64 t) x30 x31)
          (K_Ft K) (Z_to_bv 64 0x15a128) fc None m (seg_rom bsegs)).
  Proof using GLO J256 L_988 SPHI RIP FXI HA0 AB AF ROOM.
    intros until zR; intros MV BIG LW LB REL ZERO Hlo Hlor Ha Hd Hzm Hrzm Hr Hrp ALLW He HzR PR HH.
    pose proof (zr_word sp : (0 <= bv_unsigned sp < 2^64)%Z) as Rsp.
    zs. zs. if_cases Klt; zify_cond Klt.
    -
      assert (EzR : zR = (d + 1)%Z) by (rewrite HzR; rewrite (proj2 (Z.ltb_lt (d + 1) z)) by lia; reflexivity).
      zs. replace (bv_unsigned sp + -1056 + 4 * d + 4)%Z with (bv_unsigned sp + -1056 + 4 * zR)%Z by lia.
      eapply L_988 with (zm := zm) (lo := lo) (r := r);
        [ exact MV | exact BIG | exact LW | exact LB | exact REL | exact ZERO | dlia | dlia | dlia | dlia | dlia | dlia | exact Hr | exact Hrp
        | exact ALLW | dlia | exact PR | exact HH ].
    -
      assert (EzR : zR = z) by (rewrite HzR; rewrite (proj2 (Z.ltb_ge (d + 1) z)) by lia; reflexivity).
      zs. zs. rewrite <- EzR.
      eapply L_988 with (zm := zm) (lo := lo) (r := r);
        [ exact MV | exact BIG | exact LW | exact LB | exact REL | exact ZERO | dlia | dlia | dlia | dlia | dlia | dlia | exact Hr | exact Hrp
        | exact ALLW | dlia | exact PR | exact HH ].
  Qed.

  Lemma L_cnt2 : forall (k : nat) Q m (x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fc
      (n v i e i' e' : Z),
    mem_inv bsegs m -> (1 <= n)%Z -> i = (10 ^ n)%Z -> (i <= v)%Z -> (0 <= v < 1000000000)%Z -> (-100000 <= e)%Z -> (e + Z.of_nat k <= 100020)%Z ->
    fmt_fp_cnt k v (i, e) = Some (i', e') ->
    (forall x12', (-100000 <= e' <= 100020)%Z ->
       evt bsegs Q
         (MS (mkR x1 SPv gp tp x5 x6 x7 sp x9 (Z_to_bv 64 v) (Z_to_bv 64 10) x12' x13 x14 x15 x16 x17
                  x18 x19 x20 (Z_to_bv 64 e') x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
             Ft (Z_to_bv 64 0x15a128) fc None m (seg_rom bsegs))) ->
    evt bsegs Q
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp x9 (Z_to_bv 64 v) (Z_to_bv 64 10) (Z_to_bv 64 i) x13 x14 x15 x16 x17
               x18 x19 x20 (Z_to_bv 64 e) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 0x15a11c) fc None m (seg_rom bsegs)).
  Proof using J256 o0 o1 RIP FXI HA0 AB AF ROOM.
    induction k as [|k IH]; intros until e'; intros MI Hn Hi Hiv Hv He He' HC CONT; [discriminate HC|].
    prune. pose proof (zr_word sp : (0 <= bv_unsigned sp < 2^64)%Z) as Rsp.
    pose proof (pow10_small n v Hn ltac:(rewrite <- Hi; exact Hiv) ltac:(lia)) as Ri. rewrite <- Hi in Ri.
    rewrite fmt_fp_cnt_step in HC. rewrite (proj2 (Z.leb_le i v)) in HC by lia.
    zs. replace (bv_swrap 32 (i * 10)) with (i * 10)%Z by (rewrite swrap32_eq; mlia).
    zs. replace (bv_swrap 32 (Z.land e 18446744073709551615 + 1)) with (e + 1)%Z by (rewrite land_W64, swrap32_eq; mlia).
    zs. if_cases Kc; zify_cond Kc; rewrite ?(land_W64_small (i * 10)) in Kc by lia.
    -
      eapply IH with (n := (n + 1)%Z);
        [ exact MI | lia | rewrite Z.pow_add_r, <- Hi by lia; change (10^1)%Z with 10%Z; lia | dlia | dlia | dlia | dlia | exact HC | exact CONT ].
    -
      destruct k as [|k']; [discriminate HC|]. rewrite fmt_fp_cnt_step in HC. rewrite (proj2 (Z.leb_gt _ _)) in HC by lia.
      injection HC as Hi' <-. apply CONT. lia.
  Qed.

  Lemma L_94c : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x24 x25 x26 x28 x30 x31 : word) fc K
      (ws : list word) (big : list Z) (lo a r rp z zm d e i' zR : Z),
    midw K m fc 0%Z ->
    u32arr bsegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (lo <= i < zm)%Z -> znth big i = wval ws i) ->
    (forall i, (zm <= i)%Z -> znth big i = 0%Z) ->
    (0 <= lo <= a)%Z -> (lo <= r)%Z -> (a <= d < z)%Z -> (z <= zm <= 128)%Z -> (r < zm)%Z -> (r = 0 \/ r = 122)%Z ->
    rp = (bv_unsigned sp + -1056 + 4 * r)%Z ->
    (forall i, (0 <= znth big i < 1000000000)%Z) ->
    fmt_fp_cnt TEN_FUEL (znth big a) (10%Z, (9 * (r - a))%Z) = Some (i', e) ->
    zR = (if d + 1 <? z then d + 1 else z)%Z ->
    prov_R (K_p1 K) (K_prefix K) (K_pl K) r big a zR e ->
    ffp_H o0 w fl t (K_p1 K) (K_prefix K) (K_pl K) big a r zR e = Some (o1, ret) ->
    evt bsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (K_p1 K)) x19 (Z_to_bv 64 (Z.lor t 32)) x21 (Z_to_bv 64 rp)
               (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d)) x24 x25 x26 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x28 (Z_to_bv 64 t) x30 x31)
          (K_Ft K) (Z_to_bv 64 0x15a0fc) fc None m (seg_rom bsegs)).
  Proof using GLO J256 L_988 SPHI RIP FXI HA0 AB AF ROOM.
    intros until zR; intros MV BIG LW LB REL ZERO Hlo Hlor Had Hzm Hrzm Hr Hrp ALLW HC HzR PR HH.
    pose proof (zr_word sp : (0 <= bv_unsigned sp < 2^64)%Z) as Rsp.
    assert (MI : mem_inv bsegs m) by (destruct MV as ((MI & _) & _); exact MI).
    pose proof (ALLW a) as Rv.
    pose proof (u32arr_read bsegs _ _ _ a _ _ BIG (nth_error_wnth ws a ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
    zs. zs. rewrite (sx32_wval ws a) by (rewrite <- (REL a) by lia; lia). rewrite <- (REL a) by lia.
    zs. zs. zs. zs.
    replace (rp - (bv_unsigned sp + -1056 + 4 * a))%Z with (4 * (r - a))%Z by lia. rewrite e9_eq by lia.
    zs. if_cases K10; zify_cond K10.
    -
      unfold TEN_FUEL in HC. rewrite fmt_fp_cnt_step in HC. rewrite (proj2 (Z.leb_gt _ _)) in HC by lia. injection HC as _ <-.
      eapply L_978 with (zm := zm) (lo := lo) (r := r);
        [ exact MV | exact BIG | exact LW | exact LB | exact REL | exact ZERO | dlia | dlia | dlia | dlia | dlia | dlia | exact Hr | exact Hrp
        | exact ALLW | dlia | exact HzR | exact PR | exact HH ].
    - zs.
      eapply (L_cnt2 TEN_FUEL) with (n := 1%Z); [ exact MI | lia | reflexivity | dlia | dlia | dlia | unfold TEN_FUEL; dlia | exact HC | ].
      intros x12' Re'.
      eapply L_978 with (zm := zm) (lo := lo) (r := r);
        [ exact MV | exact BIG | exact LW | exact LB | exact REL | exact ZERO | dlia | dlia | dlia | dlia | dlia | dlia | exact Hr | exact Hrp
        | exact ALLW | dlia | exact HzR | exact PR | exact HH ].
  Qed.

  Definition CARH (k : nat) : Prop :=
    forall m (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x25 x26 x28 x30 x31 : word) fc K
      (ws : list word) (big big' : list Z) (lo a r rp z zm d d' a' i' eR zR : Z),
    midw K m fc 0%Z ->
    u32arr bsegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (lo <= i < zm)%Z -> znth big i = wval ws i) ->
    (forall i, (zm <= i)%Z -> znth big i = 0%Z) ->
    (0 <= lo <= a)%Z -> (lo <= r)%Z -> (a <= d < z)%Z -> (z <= zm <= 128)%Z -> (r < zm)%Z -> (r = 0 \/ r = 122)%Z ->
    rp = (bv_unsigned sp + -1056 + 4 * r)%Z ->
    (forall i, i <> d -> (0 <= znth big i < 1000000000)%Z) ->
    (999999999 < znth big d)%Z ->
    fmt_fp_carry k (big, d, a) = Some (big', d', a') -> (0 <= a')%Z ->
    fmt_fp_cnt TEN_FUEL (znth big' a') (10%Z, (9 * (r - a'))%Z) = Some (i', eR) ->
    zR = (if d' + 1 <? z then d' + 1 else z)%Z ->
    prov_R (K_p1 K) (K_prefix K) (K_pl K) r big' a' zR eR ->
    ffp_H o0 w fl t (K_p1 K) (K_prefix K) (K_pl K) big' a' r zR eR = Some (o1, ret) ->
    evt bsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a))
               (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * (d - 1))) (Z_to_bv 64 999999999) x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (K_p1 K)) x19 (Z_to_bv 64 (Z.lor t 32)) x21 (Z_to_bv 64 rp)
               x23 x24 x25 x26 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x28 (Z_to_bv 64 t) x30 x31)
          (K_Ft K) (Z_to_bv 64 0x15a0c8) fc None m (seg_rom bsegs)).

  Lemma L_carryH : forall k, CARH k.
  Proof using AB AF GLO J256 L_988 SPHI RIP FXI HA0 ROOM.
    induction k as [|k IH]; unfold CARH; intros until zR;
      intros MV BIG LW LB REL ZERO Hlo Hlor Had Hzm Hrzm Hr Hrp INV Hbig HCa Ha' HC HzR PR HH; [discriminate HCa|].
    destruct K as [pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft]. cbn [K_p1 K_prefix K_pl K_Ft] in PR, HH |- *.
    dest_midw2 MV. prune. pose proof (zr_word sp : (0 <= bv_unsigned sp < 2^64)%Z) as Rsp.
    assert (Rfw : (0 <= Fp < 2^64)%Z) by apply (zr_word fw).
    rewrite fmt_fp_carry_step in HCa. rewrite (proj2 (Z.ltb_lt 999999999 (znth big d))) in HCa by lia.
    rewrite fmt_fp_carry_body_eq in HCa. cbv zeta in HCa.
    pose proof (fmt_fp_carry_res _ _ _ _ _ _ _ HCa ltac:(destruct (Z.ltb_spec0 (d - 1) a); lia)) as (Qa & Qd & Qlen & _).

    assert (J904 : forall m1 ws1 (x12' : word) (big1 : list Z) (a1 lo1 : Z),
      midw (MidK pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft) m1 fc 0%Z ->
      u32arr bsegs m1 (bv_unsigned sp + -1056) ws1 -> length ws1 = 128%nat ->
      length big1 = 128%nat -> (forall i, (lo1 <= i < zm)%Z -> znth big1 i = wval ws1 i) ->
      (forall i, (zm <= i)%Z -> znth big1 i = 0%Z) ->
      (0 <= lo1 <= a1)%Z -> (lo1 <= lo)%Z -> (a1 <= d - 1)%Z -> (a' <= a1)%Z ->
      a1 = (if d - 1 <? a then a - 1 else a)%Z ->
      big1 = (if d - 1 <? a then zupd (zupd big d 0) (a - 1) 0 else zupd big d 0) ->
      evt bsegs POST
        (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a1))
                 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * (d - 1))) (Z_to_bv 64 999999999) x12' x13 x14 x15 x16 x17
                 (Z_to_bv 64 p1) x19 (Z_to_bv 64 (Z.lor t 32)) x21 (Z_to_bv 64 rp)
                 x23 x24 x25 x26 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x28 (Z_to_bv 64 t) x30 x31)
            Ft (Z_to_bv 64 0x15a0b4) fc None m1 (seg_rom bsegs))).
    { intros m1 ws1 x12' big1 a1 lo1 MV1 BIG1 LW1 LB1 REL1 ZERO1 Hlo1 Hlo1' Ha1d Ha'1 Ea1 Ebig1.
      clear MI MU WM FRhi ST GOT SSP FRs E2 EB BF WF BIG REL ZERO. dest_midw2 MV1.
      rewrite <- Ea1, <- Ebig1 in HCa.
      assert (INV1 : forall i, (0 <= znth big1 i < 1000000000)%Z).
      { intros i. rewrite Ebig1. destruct (Z.eq_dec i d) as [->|Hne].
        - destruct (d - 1 <? a); rewrite ?(znth_zupd_neq _ (a - 1)) by lia; rewrite znth_zupd_eq by (unfold zlength; rewrite ?zupd_length; lia); lia.
        - destruct (Z.lt_ge_cases i 0).
          + unfold znth. rewrite (proj2 (Z.ltb_lt i 0)) by lia. lia.
          + destruct (d - 1 <? a).
            * destruct (Z.eq_dec i (a - 1)) as [->|Hne'].
              -- destruct (Z.lt_ge_cases (a - 1) 0).
                 ++ unfold znth. rewrite (proj2 (Z.ltb_lt (a - 1) 0)) by lia. lia.
                 ++ rewrite znth_zupd_eq by (unfold zlength; rewrite zupd_length; lia). lia.
              -- rewrite !znth_zupd_neq by lia. apply INV. exact Hne.
            * rewrite znth_zupd_neq by lia. apply INV. exact Hne. }
      pose proof (INV1 (d - 1)%Z) as Rv.
      pose proof (u32arr_read bsegs _ _ _ (d - 1) _ _ BIG1 (nth_error_wnth ws1 (d - 1) ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
      zs. rewrite (sx32_wval ws1 (d - 1)) by (rewrite <- (REL1 (d - 1)%Z) by lia; lia). rewrite <- (REL1 (d - 1)%Z) by lia.
      set (v := znth big1 (d - 1)) in *.
      zs. replace (bv_swrap 32 (v + 1)) with (v + 1)%Z by (rewrite swrap32_eq; mlia).
      pose proof (u32arr_store_ok bsegs _ _ _ (d - 1) _ BIG1 ltac:(lia) eq_refl) as SOK.
      zs.
      pose proof (u32arr_write bsegs _ _ _ (d - 1) (Z_to_bv 64 (v + 1)) BIG1 ltac:(lia)) as BIG2. clear BIG1.
      store_done.
      assert (REL2 : forall i, (lo1 <= i < zm)%Z -> znth (zupd big1 (d - 1) (u32 (v + 1))) i = wval (upd ws1 (Z.to_nat (d - 1)) (Z_to_bv 64 (v + 1))) i).
      { intros i Hi. destruct (Z.eq_dec i (d - 1)) as [->|Hne].
        - rewrite znth_zupd_eq by (unfold zlength; lia). rewrite wval_upd_same by lia. rewrite unsigned_lit by lia.
          unfold u32. rewrite (Z.mod_small _ 4294967296) by lia. symmetry. apply Z.mod_small. lia.
        - rewrite znth_zupd_neq by lia. rewrite wval_upd_other by lia. apply REL1. lia. }
      assert (ZERO2 : forall i, (zm <= i)%Z -> znth (zupd big1 (d - 1) (u32 (v + 1))) i = 0%Z).
      { intros i Hi. rewrite znth_zupd_neq by lia. apply ZERO1. lia. }
      assert (Ev1 : znth (zupd big1 (d - 1) (u32 (v + 1))) (d - 1) = (v + 1)%Z).
      { rewrite znth_zupd_eq by (unfold zlength; lia). unfold u32. apply Z.mod_small. lia. }
      zs. replace (bv_unsigned sp + -1056 + 4 * (d - 1) + -4)%Z with (bv_unsigned sp + -1056 + 4 * (d - 1 - 1))%Z by lia.
      zs. if_cases Kc; zify_cond Kc.
      -
        destruct k as [|k']; [discriminate HCa|]. rewrite fmt_fp_carry_step in HCa.
        rewrite Ev1 in HCa. rewrite (proj2 (Z.ltb_ge 999999999 (v + 1))) in HCa by lia.
        injection HCa as Ebig' <- <-.
        zs. replace (bv_unsigned sp + -1056 + 4 * (d - 1 - 1) + 4)%Z with (bv_unsigned sp + -1056 + 4 * (d - 1))%Z by lia.
        rewrite <- Ebig' in HC, PR, HH.
        eapply L_94c with (K := MidK pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft) (zm := zm) (lo := lo1) (r := r) (big := zupd big1 (d - 1) (u32 (v + 1)));
          [ mk_midw | exact BIG2 | rewrite upd_length; exact LW1 | rewrite zupd_length; exact LB1 | exact REL2 | exact ZERO2
          | dlia | dlia | dlia | dlia | dlia | exact Hr | exact Hrp | | exact HC | exact HzR | exact PR | exact HH ].
        intros i. destruct (Z.eq_dec i (d - 1)) as [->|Hne]; [rewrite Ev1; lia|]. rewrite znth_zupd_neq by lia. apply INV1.
      -
        eapply IH with (K := MidK pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft) (zm := zm) (lo := lo1) (r := r) (big := zupd big1 (d - 1) (u32 (v + 1)));
          [ mk_midw | exact BIG2 | rewrite upd_length; exact LW1 | rewrite zupd_length; exact LB1 | exact REL2 | exact ZERO2
          | dlia | dlia | dlia | dlia | dlia | exact Hr | exact Hrp | | rewrite Ev1; dlia | exact HCa | exact Ha' | exact HC | exact HzR | exact PR | exact HH ].
        intros i Hne. rewrite znth_zupd_neq by lia. apply INV1. }

    pose proof (u32arr_store_ok bsegs _ _ _ d _ BIG ltac:(lia) eq_refl) as SOK.
    zs.
    pose proof (u32arr_write bsegs _ _ _ d (Z_to_bv 64 0) BIG ltac:(lia)) as BIG1. clear BIG.
    store_done.
    assert (REL1 : forall i, (lo <= i < zm)%Z -> znth (zupd big d 0) i = wval (upd ws (Z.to_nat d) (Z_to_bv 64 0)) i).
    { intros i Hi. destruct (Z.eq_dec i d) as [->|Hne].
      - rewrite znth_zupd_eq by (unfold zlength; lia). rewrite wval_upd_same by lia. reflexivity.
      - rewrite znth_zupd_neq by lia. rewrite wval_upd_other by lia. apply REL. lia. }
    zs. if_cases Kda; zify_cond Kda.
    -
      eapply J904 with (lo1 := lo) (big1 := zupd big d 0); [ mk_midw | exact BIG1 | rewrite upd_length; exact LW | rewrite zupd_length; exact LB | exact REL1
        | intros i Hi; rewrite znth_zupd_neq by lia; apply ZERO; lia | dlia | dlia | dlia | rewrite (proj2 (Z.ltb_ge (d - 1) a)) in Qa by lia; dlia
        | rewrite (proj2 (Z.ltb_ge (d - 1) a)) by lia; reflexivity | rewrite (proj2 (Z.ltb_ge (d - 1) a)) by lia; reflexivity ].
    -
      assert (Ha1 : (1 <= a)%Z) by (rewrite (proj2 (Z.ltb_lt (d - 1) a)) in Qa by lia; lia).
      zs. replace (bv_unsigned sp + -1056 + 4 * a + -4)%Z with (bv_unsigned sp + -1056 + 4 * (a - 1))%Z by lia.
      pose proof (u32arr_store_ok bsegs _ _ _ (a - 1) _ BIG1 ltac:(rewrite upd_length; lia) eq_refl) as SOK.
      zs.
      pose proof (u32arr_write bsegs _ _ _ (a - 1) (Z_to_bv 64 0) BIG1 ltac:(rewrite upd_length; lia)) as BIG2. clear BIG1.
      store_done.
      zs. zs.
      eapply J904 with (lo1 := Z.min lo (a - 1)) (big1 := zupd (zupd big d 0) (a - 1) 0); [ mk_midw | exact BIG2 | rewrite !upd_length; exact LW | rewrite !zupd_length; exact LB | |
        | dlia | dlia | dlia | rewrite (proj2 (Z.ltb_lt (d - 1) a)) in Qa by lia; dlia
        | rewrite (proj2 (Z.ltb_lt (d - 1) a)) by lia; reflexivity | rewrite (proj2 (Z.ltb_lt (d - 1) a)) by lia; reflexivity ].
      + intros i Hi. destruct (Z.eq_dec i (a - 1)) as [->|Hne].
        * rewrite znth_zupd_eq by (unfold zlength; rewrite zupd_length; lia). rewrite wval_upd_same by (rewrite ?upd_length; lia). reflexivity.
        * rewrite znth_zupd_neq by lia. rewrite wval_upd_other by lia. apply REL1. lia.
      + intros i Hi. rewrite !znth_zupd_neq by lia. apply ZERO. lia.
  Qed.

  Lemma L_carry : forall (k : nat) m (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x25 x26 x28 x30 x31 : word) fc K
      (ws : list word) (big big' : list Z) (lo a r rp z zm d d' a' i' eR zR : Z),
    midw K m fc 0%Z ->
    u32arr bsegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (lo <= i < zm)%Z -> znth big i = wval ws i) ->
    (forall i, (zm <= i)%Z -> znth big i = 0%Z) ->
    (0 <= lo <= a)%Z -> (lo <= r)%Z -> (a <= d < z)%Z -> (z <= zm <= 128)%Z -> (r < zm)%Z -> (r = 0 \/ r = 122)%Z ->
    rp = (bv_unsigned sp + -1056 + 4 * r)%Z ->
    (forall i, i <> d -> (0 <= znth big i < 1000000000)%Z) ->
    (999999999 < znth big d)%Z ->
    fmt_fp_carry k (big, d, a) = Some (big', d', a') -> (0 <= a')%Z ->
    fmt_fp_cnt TEN_FUEL (znth big' a') (10%Z, (9 * (r - a'))%Z) = Some (i', eR) ->
    zR = (if d' + 1 <? z then d' + 1 else z)%Z ->
    prov_R (K_p1 K) (K_prefix K) (K_pl K) r big' a' zR eR ->
    ffp_H o0 w fl t (K_p1 K) (K_prefix K) (K_pl K) big' a' r zR eR = Some (o1, ret) ->
    evt bsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a))
               (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * (d - 1))) (Z_to_bv 64 999999999) x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (K_p1 K)) x19 (Z_to_bv 64 (Z.lor t 32)) x21 (Z_to_bv 64 rp)
               x23 x24 x25 x26 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x28 (Z_to_bv 64 t) x30 x31)
          (K_Ft K) (Z_to_bv 64 0x15a0c8) fc None m (seg_rom bsegs)).
  Proof using AB AF GLO J256 L_988 SPHI RIP FXI HA0 ROOM. exact L_carryH. Qed.

End FmtFp.
