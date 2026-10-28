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

  Lemma L_fmtu9f : forall (k : nat) Q m (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x25 x26 x28 x29 x30 x31 : word) fc K
      (estrp ppl fl2 a8v v440 : Z) (oc : list Z) (ws : list word) (y s : Z) (b : list Z) (y' s' : Z) (b' : list Z),
    emw K estrp ppl fl2 a8v v440 oc m fc ->
    u32arr bsegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length (K_jk37 K) = 37%nat ->
    (10 <= y)%Z -> (y < 10 ^ s)%Z -> (s <= 9)%Z -> (y < 2^32)%Z ->
    length b = 37%nat ->
    (forall i, (s <= i < 9)%Z -> nth_error (K_jk37 K) (Z.to_nat i) = Some (Z_to_bv 8 (znth b i))) ->
    fmt_u_loop k (y, s, b) = Some (y', s', b') ->
    (forall m1 bf1 q sq bq kq (x12' x13' x14' : word),
       emw (K_set37 K bf1) estrp ppl fl2 a8v v440 oc m1 fc -> u32arr bsegs m1 (bv_unsigned sp + -1056) ws -> length bf1 = 37%nat ->
       (1 <= q <= 9)%Z -> (1 <= sq < s)%Z -> length bq = 37%nat ->
       (forall i, (sq <= i < 9)%Z -> nth_error bf1 (Z.to_nat i) = Some (Z_to_bv 8 (znth bq i))) ->
       fmt_u_loop kq (q, sq, bq) = Some (y', s', b') ->
       evt bsegs Q
         (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 14757395258967641293) (Z_to_bv 64 q) (Z_to_bv 64 (sq - 1)) x12' x13' x14' x15 x16 x17
                  x18 x19 x20 (Z_to_bv 64 10) x22 x23 (Z_to_bv 64 (bv_unsigned sp + -405)) x25 x26 (Z_to_bv 64 99) x28 x29 x30 x31)
             (K_Ft K) (Z_to_bv 64 0x15a554) fc None m1 (seg_rom bsegs))) ->
    evt bsegs Q
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 14757395258967641293) (Z_to_bv 64 y) (Z_to_bv 64 (s - 1)) x12 x13 x14 x15 x16 x17
               x18 x19 x20 (Z_to_bv 64 10) x22 x23 (Z_to_bv 64 (bv_unsigned sp + -405)) x25 x26 (Z_to_bv 64 99) x28 x29 x30 x31)
          (K_Ft K) (Z_to_bv 64 0x15a52c) fc None m (seg_rom bsegs)).
  Proof using AB AF GLO J256 SPHI RIP FXI HA0 ROOM.
    induction k as [|k IH]; intros until b'; intros MV BIG LW LBF Hy Hys Hs Hy32 Lb RELB HU CONT; [discriminate HU|].
    destruct K as [pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft]. cbn [K_p1 K_prefix K_pl K_Ft K_jk12 K_jk37] in LBF, RELB, CONT |- *.
    dest_emw2 MV. prune. pose proof (zr_word sp : (0 <= bv_unsigned sp < 2^64)%Z) as Rsp.
    assert (Rfw : (0 <= Fp < 2^64)%Z) by apply (zr_word fw).
    assert (Hs2 : (2 <= s)%Z).
    { destruct (Z.le_gt_cases 2 s); [assumption|]. assert (10 ^ s <= 10 ^ 1)%Z by (apply Z.pow_le_mono_r; lia). change (10^1)%Z with 10%Z in *. lia. }
    rewrite fmt_u_loop_step in HU. destruct (Z.eqb_spec y 0); [lia|]. cbn [negb] in HU.
    pose proof (Z.div_pos y 10 ltac:(lia) ltac:(lia)) as Rq0.
    pose proof (Z.mod_pos_bound y 10 ltac:(lia)) as Rd.
    assert (Rq : (y / 10 * 10 <= y)%Z) by (rewrite Z.mul_comm; apply Z.mul_div_le; lia).
    zs. zs. zs. zs. rewrite ?(land_W64_small ((y * 14757395258967641293) ≫ 64)) by (rewrite Z.shiftr_div_pow2 by lia; change (2^64)%Z with 18446744073709551616%Z; mlia).
    rewrite div10_magic by lia.
    zs. zs. replace (bv_swrap 32 (y - y / 10 * 10)) with (y mod 10)%Z by (rewrite swrap32_eq; mlia).
    zs. rewrite lor48_digit by lia.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ BF) as BFA. clear BF.
    pose proof (u8arr_store_ok bsegs _ _ _ (s - 1)%Z _ BFA ltac:(rewrite LBF; lia) eq_refl) as SOK.
    zs. rewrite le1_small by lia.
    pose proof (u8arr_write bsegs _ _ _ (s - 1)%Z (Z_to_bv 8 (48 + y mod 10)) BFA ltac:(rewrite LBF; lia)) as BFA'. clear BFA. store_done.
    pose proof (rw_cells_of_u8arr _ _ _ _ BFA') as BF. rewrite upd_length, LBF in BF. clear BFA'.
    assert (LBF' : length (upd jk37 (Z.to_nat (s - 1)) (Z_to_bv 8 (48 + y mod 10))) = 37%nat) by (rewrite upd_length; exact LBF).
    assert (RELB' : forall i, (s - 1 <= i < 9)%Z ->
      nth_error (upd jk37 (Z.to_nat (s - 1)) (Z_to_bv 8 (48 + y mod 10))) (Z.to_nat i) = Some (Z_to_bv 8 (znth (zupd b (s - 1) (CHR_0 + y mod 10)) i))).
    { intros i Hi. destruct (Z.eq_dec i (s - 1)) as [->|Hne].
      - rewrite nth_error_upd_same by (rewrite LBF; lia). rewrite znth_zupd_eq by (unfold zlength; rewrite Lb; lia). reflexivity.
      - rewrite nth_error_upd_other by lia. rewrite znth_zupd_neq by lia. apply RELB. lia. }
    zs. replace (Z_to_bv 64 (s - 1 + -1)) with (Z_to_bv 64 ((s - 1) - 1)) by (f_equal; lia).
    zs. if_cases Kbig; zify_cond Kbig.
    -
      eapply IH with (K := MidK pad jk40 jk8 jk3 jk12 (upd jk37 (Z.to_nat (s - 1)) (Z_to_bv 8 (48 + y mod 10))) p1 prefix pl plz pfx Ft) (b := zupd b (s - 1) (CHR_0 + y mod 10))
        (oc := oc) (estrp := estrp) (ppl := ppl) (fl2 := fl2) (a8v := a8v) (v440 := v440);
        [ mk_emw | exact BIG | exact LW | exact LBF' | mlia | | dlia | mlia | rewrite zupd_length; exact Lb | exact RELB' | exact HU | ].
      { apply Z.div_lt_upper_bound; [lia|]. rewrite <- pow10_succ by lia. exact Hys. }
      intros m2 bf2 q sq bq kq x12' x13' x14' MV1 BIG1 LBF1 Hq Hsq Lbq REL1 HU1.
      eapply CONT; [ exact MV1 | exact BIG1 | exact LBF1 | exact Hq | dlia | exact Lbq | exact REL1 | exact HU1 ].
    -
      eapply (CONT _ (upd jk37 (Z.to_nat (s - 1)) (Z_to_bv 8 (48 + y mod 10))) (y / 10)%Z (s - 1)%Z (zupd b (s - 1) (CHR_0 + y mod 10)) k);
        [ unfold K_set37; cbn [K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft]; mk_emw
        | exact BIG | exact LBF' | mlia | dlia | rewrite zupd_length; exact Lb | exact RELB' | exact HU ].
  Qed.

  Lemma L_zfillf : forall (k : nat) Q m (x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x27 x28 x29 x30 x31 : word) fc K
      (estrp ppl fl2 a8v v440 : Z) (oc : list Z) (ws : list word) (s : Z) (b b' : list Z),
    emw K estrp ppl fl2 a8v v440 oc m fc ->
    u32arr bsegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length (K_jk37 K) = 37%nat -> (1 <= s <= 9)%Z -> (Z.to_nat s <= k)%nat ->
    length b = 37%nat -> length b' = 37%nat ->
    (forall i, (s <= i < 9)%Z -> nth_error (K_jk37 K) (Z.to_nat i) = Some (Z_to_bv 8 (znth b i))) ->
    (forall i, (0 <= i < s)%Z -> znth b' i = CHR_0) -> (forall i, (s <= i)%Z -> znth b' i = znth b i) ->
    (forall m1 bf1,
       emw (K_set37 K bf1) estrp ppl fl2 a8v v440 oc m1 fc -> u32arr bsegs m1 (bv_unsigned sp + -1056) ws -> length bf1 = 37%nat ->
       (forall i, (0 <= i < 9)%Z -> nth_error bf1 (Z.to_nat i) = Some (Z_to_bv 8 (znth b' i))) ->
       evt bsegs Q
         (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 14757395258967641293) (Z_to_bv 64 (bv_unsigned sp + -405)) x11 (Z_to_bv 64 (bv_unsigned sp + -405)) x13 x14 x15 x16 x17
                  x18 x19 x20 x21 x22 x23 (Z_to_bv 64 (bv_unsigned sp + -405)) x25 (Z_to_bv 64 48) x27 x28 x29 x30 x31)
             (K_Ft K) (Z_to_bv 64 0x15a5b0) fc None m1 (seg_rom bsegs))) ->
    evt bsegs Q
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 14757395258967641293) x10 x11 (Z_to_bv 64 (bv_unsigned sp + -405 + s)) x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 (Z_to_bv 64 (bv_unsigned sp + -405)) x25 (Z_to_bv 64 48) x27 x28 x29 x30 x31)
          (K_Ft K) (Z_to_bv 64 0x15a584) fc None m (seg_rom bsegs)).
  Proof using AB AF GLO J256 SPHI SPLO RIP FXI HA0 ROOM.
    induction k as [|k IH]; intros until b'; intros MV BIG LW LBF Hs Hk Lb Lb' RELB Z1 Z2 CONT; [lia|].
    destruct K as [pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft]. cbn [K_p1 K_prefix K_pl K_Ft K_jk12 K_jk37] in LBF, RELB, CONT |- *.
    dest_emw2 MV. prune. pose proof (zr_word sp : (0 <= bv_unsigned sp < 2^64)%Z) as Rsp.
    assert (Rfw : (0 <= Fp < 2^64)%Z) by apply (zr_word fw).
    zs.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ BF) as BFA. clear BF.
    pose proof (u8arr_store_ok bsegs _ _ _ (s - 1)%Z _ BFA ltac:(rewrite LBF; lia) eq_refl) as SOK.
    zs. change (le1 (Z_to_bv 64 48)) with [Z_to_bv 8 48].
    pose proof (u8arr_write bsegs _ _ _ (s - 1)%Z (Z_to_bv 8 48) BFA ltac:(rewrite LBF; lia)) as BFA'. clear BFA. store_done.
    pose proof (rw_cells_of_u8arr _ _ _ _ BFA') as BF. rewrite upd_length, LBF in BF. clear BFA'.
    assert (LBF' : length (upd jk37 (Z.to_nat (s - 1)) (Z_to_bv 8 48)) = 37%nat) by (rewrite upd_length; exact LBF).
    assert (RELB' : forall i, (s - 1 <= i < 9)%Z -> nth_error (upd jk37 (Z.to_nat (s - 1)) (Z_to_bv 8 48)) (Z.to_nat i) = Some (Z_to_bv 8 (znth b' i))).
    { intros i Hi. destruct (Z.eq_dec i (s - 1)) as [->|Hne].
      - rewrite nth_error_upd_same by (rewrite LBF; lia). rewrite Z1 by lia. reflexivity.
      - rewrite nth_error_upd_other by lia. rewrite Z2 by lia. apply RELB. lia. }
    zs. replace (Z_to_bv 64 (bv_unsigned sp + -405 + s + -1)) with (Z_to_bv 64 (bv_unsigned sp + -405 + (s - 1))) by (f_equal; lia).
    zs. if_cases Kmore; zify_cond Kmore.
    - eapply IH with (K := MidK pad jk40 jk8 jk3 jk12 (upd jk37 (Z.to_nat (s - 1)) (Z_to_bv 8 48)) p1 prefix pl plz pfx Ft) (b := b') (b' := b')
        (oc := oc) (estrp := estrp) (ppl := ppl) (fl2 := fl2) (a8v := a8v) (v440 := v440);
        [ mk_emw | exact BIG | exact LW | exact LBF' | dlia | dlia | exact Lb' | exact Lb' | exact RELB' | intros; apply Z1; dlia | intros; reflexivity | exact CONT ].
    - replace (s - 1)%Z with 0%Z in RELB', BF |- * by lia. zs.
      eapply (CONT _ (upd jk37 (Z.to_nat 0) (Z_to_bv 8 48)));
        [ unfold K_set37; cbn [K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft]; mk_emw
        | exact BIG | rewrite upd_length; exact LBF | ].
      intros i Hi. replace (Z.to_nat (s - 1)) with (Z.to_nat 0) in RELB' by lia. apply RELB'. lia.
  Qed.

  Lemma L_fint : forall (k : nat) Q m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x23 x25 x28 x29 x30 x31 : word) fc K
      (estrp ppl fl2 a8v v440 : Z) (oc : list Z) (ws : list word) (big : list Z) (lo a' r rp zm d d' : Z) (o' : list Z),
    emw K estrp ppl fl2 a8v v440 oc m fc ->
    u32arr bsegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (lo <= i < zm)%Z -> znth big i = wval ws i) ->
    (0 <= lo <= a')%Z -> (a' <= d <= r)%Z -> (r < zm <= 128)%Z -> rp = (bv_unsigned sp + -1056 + 4 * r)%Z ->
    (forall i, (0 <= znth big i < 1000000000)%Z) ->
    length (K_jk37 K) = 37%nat ->
    fmt_fp_fint k big a' r (d, oc) = Some (d', o') ->
    (length o' <= length o1)%nat ->
    (forall m1 bf1 (x1' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word),
       emw (K_set37 K bf1) estrp ppl fl2 a8v v440 o' m1 fc -> u32arr bsegs m1 (bv_unsigned sp + -1056) ws -> length bf1 = 37%nat ->
       evt bsegs Q
         (MS (mkR x1' SPv gp tp x5' x6' x7' sp (Z_to_bv 64 14757395258967641293) x10' x11' x12' x13' x14' x15' x16' x17'
                  x18 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d')) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a')) (Z_to_bv 64 10) (Z_to_bv 64 rp) x23
                  (Z_to_bv 64 (bv_unsigned sp + -405)) x25 (Z_to_bv 64 48) (Z_to_bv 64 99) x28' x29' x30' x31')
             (K_Ft K) (Z_to_bv 64 0x15a794) fc None m1 (seg_rom bsegs))) ->
    forall x1, evt bsegs Q
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 14757395258967641293) x10 x11 x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d)) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a')) (Z_to_bv 64 10) (Z_to_bv 64 rp) x23
               (Z_to_bv 64 (bv_unsigned sp + -405)) x25 (Z_to_bv 64 48) (Z_to_bv 64 99) x28 x29 x30 x31)
          (K_Ft K) (Z_to_bv 64 0x15a520) fc None m (seg_rom bsegs)).
  Proof using AB AF GLO J256 ROOM SPHI SPLO RIP FXI HA0.
    induction k as [|k IH]; intros until o'; intros MV BIG LW LB REL Hlo Hd Hr Hrp ALLW LB37 HF Hroom CONT x1; [discriminate HF|].
    destruct K as [pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft]. cbn [K_p1 K_prefix K_pl K_Ft K_jk12 K_jk37] in LB37, CONT |- *.
    pose proof (zr_word sp : (0 <= bv_unsigned sp < 2^64)%Z) as Rsp.
    assert (Rfw : (0 <= Fp < 2^64)%Z) by apply (zr_word fw).

    rewrite fmt_fp_fint_step in HF. rewrite (proj2 (Z.leb_le d r)) in HF by lia.
    unfold fmt_fp_fint_body, fmt_u, FMT_U_FUEL in HF.
    destruct (fmt_u_loop 21 (znth big d, 9%Z, zrepeat 0%Z 37)) as [[[y0 s'] b']|] eqn:HUL; [|discriminate HF]. cbv beta iota zeta in HF.
    pose proof (ALLW d) as Rv.
    pose proof (fmt_u_loop_res _ _ _ _ _ _ _ HUL ltac:(lia)) as (Hy0 & Hs' & Lb' & Hb'1 & Hb'2).
    pose proof (ndig_fuel_le 21 (znth big d) 9 ltac:(lia) ltac:(lia) ltac:(change (10^9)%Z with 1000000000%Z; lia)) as Hnd.
    pose proof (ndig_fuel_nonneg 21 (znth big d)) as Hnd0.
    assert (Lb : length b' = 37%nat) by (rewrite Lb'; reflexivity). clear Lb'. rename Lb into Lb'.
    assert (MI : mem_inv bsegs m) by (destruct MV as ((MI & _) & _); exact MI).
    pose proof (u32arr_read bsegs _ _ _ d _ _ BIG (nth_error_wnth ws d ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
    zs. rewrite zx32_wval. rewrite <- (REL d) by lia.
    set (v := znth big d) in *.

    assert (J00 : forall m2 bf2 (sf : Z) (bfin : list Z) (x11' x12' x13' x14' : word),
      emw (MidK pad jk40 jk8 jk3 jk12 bf2 p1 prefix pl plz pfx Ft) estrp ppl fl2 a8v v440 oc m2 fc ->
      u32arr bsegs m2 (bv_unsigned sp + -1056) ws -> length bf2 = 37%nat ->
      (0 <= sf <= 9)%Z -> length bfin = 37%nat ->
      (forall i, (sf <= i < 9)%Z -> nth_error bf2 (Z.to_nat i) = Some (Z_to_bv 8 (znth bfin i))) ->
      (if negb (d =? a') then fmt_fp_zfill ZFILL_FUEL (s', b') else if s' =? 9 then Some (s' - 1, zupd b' (s' - 1) CHR_0) else Some (s', b'))%Z = Some (sf, bfin) ->
      evt bsegs Q
        (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 14757395258967641293) (Z_to_bv 64 (bv_unsigned sp + -405 + sf)) x11' x12' x13' x14' x15 x16 x17
                 x18 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d)) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a')) (Z_to_bv 64 10) (Z_to_bv 64 rp) x23
                 (Z_to_bv 64 (bv_unsigned sp + -405)) x25 (Z_to_bv 64 48) (Z_to_bv 64 99) x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x15a5b0) fc None m2 (seg_rom bsegs))).
    { intros m2 bf2 sf bfin x11' x12' x13' x14' MV2 BIG2 LB37b Hsf Lbfin REL2 HZF.
      rewrite HZF in HF. cbv beta iota in HF.
      clear dependent m. dest_emw2 MV2. dest_wfile WF.
      zs. zs. cbv beta. zs. rewrite FLG. zs. if_cases Kfe; zify_cond Kfe; [exfalso; lia|].
      zs. zs. replace (Z_to_bv 64 (bv_unsigned sp + -396 - (bv_unsigned sp + -405 + sf))) with (Z_to_bv 64 (9 - sf)) by (f_equal; lia).
      zs.

      pose proof (u8arr_of_rw_cells _ _ _ _ _ BF) as BFA.
      pose proof (bytes_at_slice _ _ _ (Z.to_nat sf) (Z.to_nat (9 - sf)) (proj1 BFA) ltac:(rewrite LB37b; lia)) as SRC. clear BFA.
      rewrite (rel_slice9 bf2 bfin sf REL2 ltac:(rewrite LB37b; lia) ltac:(rewrite Lbfin; lia) ltac:(lia)) in SRC.
      rewrite Z2Nat.id in SRC by lia.
      set (obs := zsub bfin sf (9 - sf)) in *.
      assert (Lobs : length obs = Z.to_nat (9 - sf)) by (subst obs; apply zsub_length; lia).
      set (pbs := zb obs) in *. assert (Lpbs : length pbs = Z.to_nat (9 - sf)) by (subst pbs; rewrite zb_length; exact Lobs).
      set (c0 := zb oc) in *. assert (Lc0 : length c0 = length oc) by (subst c0; apply zb_length).
      set (jk := skipn (length oc - length o0) junk0) in *.
      assert (Ljk : (length jk = length junk0 - (length oc - length o0))%nat) by (subst jk; apply skipn_length).
      pose proof (fint_extends _ _ _ _ _ _ _ _ HF) as EXT. apply extends_length in EXT. unfold out in EXT. rewrite app_length, Lobs in EXT.
      destruct (stk_split bsegs _ _ (bv_unsigned sp + -1056 - 2304) _ ST ltac:(lia)) as [STlo STf]. clear ST.
      zs.
      lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
        eapply evt_cut;
        [ eapply fwritex_callR;
          [ exact FC | exact BUF | exact FLG | exact LBF | exact Bpos | exact Bhi | exact SEPfb
          | exact SRC
          | rewrite Lpbs, Z2Nat.id by lia; reflexivity
          | rewrite Lpbs, Ljk; lia
          | exact STf
          | hyp
          | lia | lia | lia | lia | lia | lia | lia | lia | lia
          | solve_MU | solve_WM | lia | chk_src ]
        | clear FC BUF STf; post_call segs m ]
      end.
      norm_rsegs.
      match goal with X : stk _ _ (bv_unsigned sp + -1056 - 2304)%Z _ |- _ =>
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (stk_merge bsegs mm _ _ _ STlo X ltac:(lia)) as ST end; clear STlo X end.
      lazymatch goal with X : wfile _ _ _ _ _ _ _ (c0 ++ pbs) _ |- _ =>
        subst c0 pbs; rewrite <- zb_app in X; subst jk; rewrite skipn_skipn, zb_length, Lobs in X;
        replace (Z.to_nat (9 - sf) + (length oc - length o0))%nat with (length (oc ++ obs) - length o0)%nat in X by (rewrite app_length, Lobs; lia) end.
      match goal with X : bytes_at _ _ (bv_unsigned sp + -405 + sf)%Z _ |- _ => clear X end.
      unfold out in HF.
      zs. zs. replace (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d + 4)) with (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * (d + 1))) by (f_equal; lia).
      zs. if_cases Kend; zify_cond Kend.
      -
        destruct k as [|k']; [discriminate HF|]. rewrite fmt_fp_fint_step in HF. rewrite (proj2 (Z.leb_gt _ _)) in HF by lia.
        injection HF as <- <-.
        eapply CONT; [ unfold K_set37; cbn [K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft]; mk_emw | exact BIG2 | exact LB37b ].
      - eapply IH with (K := MidK pad jk40 jk8 jk3 jk12 bf2 p1 prefix pl plz pfx Ft) (oc := oc ++ obs) (estrp := estrp) (ppl := ppl) (fl2 := fl2) (a8v := a8v) (v440 := v440) (lo := lo) (zm := zm) (r := r);
          [ mk_emw | exact BIG2 | exact LW | exact LB | exact REL | dlia | dlia | dlia | exact Hrp | exact ALLW | exact LB37b | exact HF | exact Hroom | exact CONT ]. }

    assert (Jc8 : forall m2 bf2 (x10' x12' x13' x14' : word),
      emw (MidK pad jk40 jk8 jk3 jk12 bf2 p1 prefix pl plz pfx Ft) estrp ppl fl2 a8v v440 oc m2 fc ->
      u32arr bsegs m2 (bv_unsigned sp + -1056) ws -> length bf2 = 37%nat ->
      (forall i, (s' <= i < 9)%Z -> nth_error bf2 (Z.to_nat i) = Some (Z_to_bv 8 (znth b' i))) ->
      evt bsegs Q
        (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 14757395258967641293) x10' (Z_to_bv 64 s') x12' x13' x14' x15 x16 x17
                 x18 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d)) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a')) (Z_to_bv 64 10) (Z_to_bv 64 rp) x23
                 (Z_to_bv 64 (bv_unsigned sp + -405)) x25 (Z_to_bv 64 48) (Z_to_bv 64 99) x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x15a578) fc None m2 (seg_rom bsegs))).
    { intros m2 bf2 x10' x12' x13' x14' MV2 BIG2 LB37b REL2.
      clear dependent m. pose proof MV2 as MV. dest_emw2 MV2.
      zs. zs. if_cases Kda; zify_cond Kda.
      -
        assert (Ed : d = a') by lia. rewrite (proj2 (Z.eqb_eq d a') Ed) in J00. cbn [negb] in J00.
        zs. zs. if_cases K9; zify_cond K9.
        +
          rewrite (proj2 (Z.eqb_neq s' 9) K9) in J00.
          zs. eapply J00; [ exact MV | exact BIG2 | exact LB37b | dlia | exact Lb' | exact REL2 | reflexivity ].
        +
          rewrite (proj2 (Z.eqb_eq s' 9) K9) in J00.
          zs.
          pose proof (u8arr_of_rw_cells _ _ _ _ _ BF) as BFA. clear BF.
          pose proof (u8arr_store_ok bsegs _ _ _ (s' - 1)%Z _ BFA ltac:(rewrite LB37b; lia) eq_refl) as SOK.
          zs. change (le1 (Z_to_bv 64 48)) with [Z_to_bv 8 48].
          pose proof (u8arr_write bsegs _ _ _ (s' - 1)%Z (Z_to_bv 8 48) BFA ltac:(rewrite LB37b; lia)) as BFA'. clear BFA. store_done.
          pose proof (rw_cells_of_u8arr _ _ _ _ BFA') as BF. rewrite upd_length, LB37b in BF. clear BFA'.
          zs. replace (Z_to_bv 64 (bv_unsigned sp + -405 + s' + -1)) with (Z_to_bv 64 (bv_unsigned sp + -405 + (s' - 1))) by (f_equal; lia).
          eapply J00; [ mk_emw | exact BIG2 | rewrite upd_length; exact LB37b | dlia | rewrite zupd_length; exact Lb' | | reflexivity ].
          intros i Hi. destruct (Z.eq_dec i (s' - 1)) as [->|Hne].
          * rewrite nth_error_upd_same by (rewrite LB37b; lia). rewrite znth_zupd_eq by (unfold zlength; rewrite Lb'; lia). reflexivity.
          * rewrite nth_error_upd_other by lia. rewrite znth_zupd_neq by lia. apply REL2. lia.
      - rewrite (proj2 (Z.eqb_neq d a')) in J00 by lia. cbn [negb] in J00.
        destruct (fmt_fp_zfill_res ZFILL_FUEL s' b' ltac:(lia) ltac:(unfold ZFILL_FUEL; lia)) as (bz & HZ & Lbz & Z1 & Z2).
        rewrite HZ in J00.
        zs. if_cases K0; zify_cond K0.
        +
          assert (Hs'0 : (s' = 0)%Z) by (apply Bool.andb_false_iff in K0; destruct K0 as [K0|K0]; apply Z.ltb_ge in K0; lia).
          zs. eapply J00; [ exact MV | exact BIG2 | exact LB37b | dlia | rewrite Lbz; exact Lb' | | rewrite Hs'0; reflexivity ].
          intros i Hi. rewrite Z2 by lia. apply REL2. lia.
        + assert (Hs'0 : (0 < s')%Z) by lia.
          eapply (L_zfillf ZFILL_FUEL) with (K := MidK pad jk40 jk8 jk3 jk12 bf2 p1 prefix pl plz pfx Ft) (b := b') (b' := bz)
            (oc := oc) (estrp := estrp) (ppl := ppl) (fl2 := fl2) (a8v := a8v) (v440 := v440);
            [ exact MV | exact BIG2 | exact LW | exact LB37b | dlia | unfold ZFILL_FUEL; dlia | exact Lb' | rewrite Lbz; exact Lb' | exact REL2
            | intros; apply Z1; [dlia | unfold zlength; rewrite Lb'; dlia] | exact Z2 | ].
          intros m3 bf3 MV3 BIG3 LB3 REL3.
          replace (Z_to_bv 64 (bv_unsigned sp + -405)) with (Z_to_bv 64 (bv_unsigned sp + -405 + 0)) at 1 by (f_equal; lia).
          eapply J00; [ unfold K_set37 in MV3; cbn [K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft] in MV3; exact MV3
                      | exact BIG3 | exact LB3 | dlia | rewrite Lbz; exact Lb' | exact REL3 | reflexivity ]. }

    assert (Jb8 : forall m2 bf2 q sq bq kq (x12' x13' x14' : word),
      emw (MidK pad jk40 jk8 jk3 jk12 bf2 p1 prefix pl plz pfx Ft) estrp ppl fl2 a8v v440 oc m2 fc ->
      u32arr bsegs m2 (bv_unsigned sp + -1056) ws -> length bf2 = 37%nat ->
      (1 <= q <= 9)%Z -> (1 <= sq <= 9)%Z -> length bq = 37%nat ->
      (forall i, (sq <= i < 9)%Z -> nth_error bf2 (Z.to_nat i) = Some (Z_to_bv 8 (znth bq i))) ->
      fmt_u_loop kq (q, sq, bq) = Some (y0, s', b') ->
      evt bsegs Q
        (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 14757395258967641293) (Z_to_bv 64 q) (Z_to_bv 64 sq) x12' x13' x14' x15 x16 x17
                 x18 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d)) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a')) (Z_to_bv 64 10) (Z_to_bv 64 rp) x23
                 (Z_to_bv 64 (bv_unsigned sp + -405)) x25 (Z_to_bv 64 48) (Z_to_bv 64 99) x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x15a568) fc None m2 (seg_rom bsegs))).
    { intros m2 bf2 q sq bq kq x12' x13' x14' MV2 BIG2 LB37b Hq Hsq Lbq REL2 HU.
      clear dependent m. dest_emw2 MV2.
      destruct kq as [|kq']; [discriminate HU|]. rewrite fmt_u_loop_step in HU.
      rewrite (proj2 (Z.eqb_neq q 0)) in HU by lia. cbn [negb] in HU.
      destruct kq' as [|kq'']; [discriminate HU|]. rewrite fmt_u_loop_step in HU.
      rewrite (Z.div_small q 10) in HU by lia. cbn [Z.eqb negb] in HU. injection HU as _ Es' Eb'.
      rewrite (Z.mod_small q 10) in Eb' by lia.
      zs. rewrite lor48_digit by lia. zs. zs.
      pose proof (u8arr_of_rw_cells _ _ _ _ _ BF) as BFA. clear BF.
      pose proof (u8arr_store_ok bsegs _ _ _ (sq - 1)%Z _ BFA ltac:(rewrite LB37b; lia) eq_refl) as SOK.
      zs. rewrite le1_small by lia.
      pose proof (u8arr_write bsegs _ _ _ (sq - 1)%Z (Z_to_bv 8 (48 + q)) BFA ltac:(rewrite LB37b; lia)) as BFA'. clear BFA. store_done.
      pose proof (rw_cells_of_u8arr _ _ _ _ BFA') as BF. rewrite upd_length, LB37b in BF. clear BFA'.
      replace (Z_to_bv 64 (sq + -1)) with (Z_to_bv 64 s') by (f_equal; lia).
      eapply Jc8; [ mk_emw | exact BIG2 | rewrite upd_length; exact LB37b | ].
      intros i Hi. subst b'. rewrite <- Es' in *.
      destruct (Z.eq_dec i (sq - 1)) as [->|Hi1].
      { rewrite nth_error_upd_same by (rewrite LB37b; lia). rewrite znth_zupd_eq by (unfold zlength; rewrite Lbq; lia). unfold CHR_0. reflexivity. }
      rewrite nth_error_upd_other by lia. rewrite znth_zupd_neq by lia. apply REL2. lia. }

    pose proof (rw_cells_CB_length _ _ _ _ _ ltac:(destruct MV as (_ & _ & _ & _ & _ & _ & BF & _); exact BF)) as LB37'.
    zs. if_cases K10; zify_cond K10.
    -
      zs. zs. if_cases Kz; zify_cond Kz.
      +
        rewrite Kz in HUL. rewrite fmt_u_loop_step in HUL. cbn in HUL. injection HUL as _ Es' Eb'.
        replace (Z_to_bv 64 9) with (Z_to_bv 64 s') by (f_equal; lia).
        eapply Jc8 with (bf2 := jk37); [ exact MV | exact BIG | exact LB37 | ].
        intros i Hi. lia.
      + eapply Jb8 with (bf2 := jk37) (bq := zrepeat 0%Z 37) (kq := 21%nat); [ exact MV | exact BIG | exact LB37 | subst v; dlia | dlia | reflexivity | intros; lia | exact HUL ].
    -
      zs.
      replace (Z_to_bv 64 8) with (Z_to_bv 64 (9 - 1)) by reflexivity.
      eapply (L_fmtu9f 21) with (K := MidK pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft) (b := zrepeat 0%Z 37)
        (oc := oc) (estrp := estrp) (ppl := ppl) (fl2 := fl2) (a8v := a8v) (v440 := v440);
        [ exact MV | exact BIG | exact LW | exact LB37 | dlia | change (10 ^ 9)%Z with 1000000000%Z; subst v; dlia | dlia | subst v; dlia | reflexivity | intros; lia | exact HUL | ].
      intros m2 bf2 q sq bq kq x12' x13' x14' MV2 BIG2 LB2 Hq Hsq Lbq REL2 HU2.
      clear dependent m. pose proof MV2 as MV. dest_emw2 MV2.
      zs. replace (Z_to_bv 64 (sq - 1 + 1)) with (Z_to_bv 64 sq) by (f_equal; lia).
      zs. if_cases Kq; zify_cond Kq; [|exfalso; lia].
      eapply Jb8; [ unfold K_set37 in MV; cbn [K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft] in MV; exact MV
                  | exact BIG2 | exact LB2 | exact Hq | dlia | exact Lbq | exact REL2 | exact HU2 ].
  Qed.

End FmtFp.
