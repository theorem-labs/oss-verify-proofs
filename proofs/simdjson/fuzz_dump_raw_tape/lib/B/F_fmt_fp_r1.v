(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Sf_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Arr.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import Prelim SoftFloat FmtFp.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Sf_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import FmtFp_split FmtFp_splitR FmtFp_splitH FmtFp_facts FmtFp_facts2.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import F_memset F_memcpy F_fwritex F_pad F_frexpl F_divtf3_main F_fmt_fp_lib F_fmt_fp_calls F_fmt_fp_pre F_fmt_fp_pre2 F_fmt_fp_pre3 F_fmt_fp_pre4.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import R_m2s I_consts F_achk Fe_icalls.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import StoreFast.
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
  Hypothesis GLO : (7126576 <= bv_unsigned sp - 6944)%Z.
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
         [C8 (Z_to_bv 64 0); CB 40 (K_jk40 K); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t); CB 8 (K_jk8 K); C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 7126568);
          C8 (Z_to_bv 64 (K_plz K)); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)]
    /\ rw_cells bsegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 e2m); CB 3 (K_jk3 K)]
    /\ rw_cells bsegs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells bsegs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ K_plz K = Z.b2z (K_pl K =? 0)%Z /\ K_pfx K = (81598 + K_prefix K)%Z
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
         [C8 (Z_to_bv 64 0); CB 40 (K_jk40 K); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t); CB 8 (K_jk8 K); C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 7126568);
          C8 (Z_to_bv 64 (K_plz K)); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)]
    /\ rw_cells bsegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 e2m); CB 3 (K_jk3 K)]
    /\ rw_cells bsegs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells bsegs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ (0 <= K_plz K < 2^64)%Z /\ K_pfx K = (81598 + K_prefix K)%Z
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
         ([C8 (Z_to_bv 64 0)] ++ cs5 ++ [C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t); C8 (Z_to_bv 64 (K_p1 K)); C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 7126568);
          C8 (Z_to_bv 64 z456); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)])
    /\ rw_cells bsegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 0); CB 3 (K_jk3 K)]
    /\ rw_cells bsegs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells bsegs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ (0 <= z456 < 2^64)%Z /\ K_pfx K = (81598 + K_prefix K)%Z
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
               [C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 7126568); C8 (Z_to_bv 64 z456); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)]) in FRs.
      cbn [cells_size csize cells_bytes cbytes app Nat.add] in FRs. rewrite app_nil_r in FRs. exact FRs. }
    split; [exact E2|]. split; [exact EB|]. split; [exact BF|]. split; [exact WF|].
    split; [exact Hpre|]. split; [exact Hpl|]. split; [exact Hplz|]. split; [exact Hpfx|]. exact Hp1.
  Qed.

  Definition emw (K : midK) (estrp ppl fl2 a8v v440 : Z) (oc : list Z) (m : word -> option byte) (fc : bv 32) : Prop :=
    finv m (K_pad K) /\ frm0 fc /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get (K_Ft K) k = reg_get F k)
    /\ rw_cells bsegs m (bv_unsigned sp + -544)
         [C8 (Z_to_bv 64 0); CB 40 (K_jk40 K); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 estrp); C8 (Z_to_bv 64 ppl); C8 (Z_to_bv 64 fl2); C8 (Z_to_bv 64 7126568);
          C8 (Z_to_bv 64 a8v); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 v440); C8 (Z_to_bv 64 Fp)]
    /\ rw_cells bsegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 0); CB 3 (K_jk3 K)]
    /\ rw_cells bsegs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells bsegs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb oc) (skipn (length oc - length o0) junk0)
    /\ (length o0 <= length oc)%nat
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ K_pfx K = (81598 + K_prefix K)%Z /\ (0 <= K_p1 K < 2^20)%Z.
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

  Hypothesis L_8ac :
    forall m (x1 x5 x6 x7 x10 x11 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word) fc K (jk16 : list byte) (v512 : word) (z456 : Z)
      (ws : list word) (big bigq : list Z) (lo a r rp z zm d e i n x round small aq dq eq zR : Z),
    midq K [CB 16 jk16; C8 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * (d - 1) + 65536)); C8 v512; C8 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d))] z456 m fc ->
    u32arr bsegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (lo <= i < zm)%Z -> znth big i = wval ws i) ->
    (forall i, (zm <= i)%Z -> znth big i = 0%Z) ->
    (0 <= lo <= a)%Z -> (lo <= r)%Z -> (a <= zm)%Z -> (lo <= d < z)%Z -> (z <= zm <= 128)%Z -> (r < zm)%Z -> (r = 0 \/ r = 122)%Z ->
    rp = (bv_unsigned sp + -1056 + 4 * r)%Z ->
    (forall i, (0 <= znth big i < 1000000000)%Z) ->
    i = (10 ^ n)%Z -> (1 <= n <= 9)%Z -> x = ((znth big d) mod i)%Z -> (-2^20 <= e < 2^20)%Z ->
    ffp_R6 big a r d i x e round small = Some (bigq, aq, dq, eq) -> (0 <= aq)%Z ->
    (f128_le (f128_add round small) round <> 0%Z -> (a <= d)%Z) ->
    zR = (if dq + 1 <? z then dq + 1 else z)%Z ->
    prov_R (K_p1 K) (K_prefix K) (K_pl K) r bigq aq zR eq ->
    ffp_H o0 w fl t (K_p1 K) (K_prefix K) (K_pl K) bigq aq r zR eq = Some (o1, ret) ->
    evt bsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10 x11 (Z_to_bv 64 (lo64 small)) (Z_to_bv 64 (hi64 small)) x14 x15 x16 x17
               x18 (Z_to_bv 64 i) (Z_to_bv 64 (Z.lor t 32)) (Z_to_bv 64 e) (Z_to_bv 64 rp)
               (Z_to_bv 64 x) (Z_to_bv 64 (znth big d)) (Z_to_bv 64 (hi64 round)) (Z_to_bv 64 (lo64 round)) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x28 x29 x30 x31)
          (K_Ft K) (Z_to_bv 64 0x15a5e8) fc None m (seg_rom bsegs)).

  Lemma L_834 : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x26 x28 x29 x30 x31 : word) fc K (jk16 : list byte)
      (ws : list word) (big bigq : list Z) (lo a r rp z zm d e i n x round D aq dq eq zR : Z),
    midq K [CB 16 jk16; C8 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * (d - 1) + 65536)); C8 (Z_to_bv 64 (lo64 round)); C8 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d))]
         (Z.b2z (K_pl K =? 0)) m fc ->
    u32arr bsegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (lo <= i < zm)%Z -> znth big i = wval ws i) ->
    (forall i, (zm <= i)%Z -> znth big i = 0%Z) ->
    (0 <= lo <= a)%Z -> (lo <= r)%Z -> (a <= zm)%Z -> (lo <= d < z)%Z -> (z <= zm <= 128)%Z -> (r < zm)%Z -> (r = 0 \/ r = 122)%Z ->
    rp = (bv_unsigned sp + -1056 + 4 * r)%Z ->
    (forall i, (0 <= znth big i < 1000000000)%Z) ->
    i = (10 ^ n)%Z -> (1 <= n <= 9)%Z -> x = ((znth big d) mod i)%Z -> (-2^20 <= e < 2^20)%Z ->
    (0 <= D < 2^64)%Z ->
    ffp_R5 (K_prefix K) (K_pl K) big a r d i x e round (f128_of_d D) = Some (bigq, aq, dq, eq) -> (0 <= aq)%Z ->
    (f128_le (f128_add (fst (ffp_flip (K_prefix K) (K_pl K) round (f128_of_d D))) (snd (ffp_flip (K_prefix K) (K_pl K) round (f128_of_d D))))
             (fst (ffp_flip (K_prefix K) (K_pl K) round (f128_of_d D))) <> 0%Z -> (a <= d)%Z) ->
    zR = (if dq + 1 <? z then dq + 1 else z)%Z ->
    prov_R (K_p1 K) (K_prefix K) (K_pl K) r bigq aq zR eq ->
    ffp_H o0 w fl t (K_p1 K) (K_prefix K) (K_pl K) bigq aq r zR eq = Some (o1, ret) ->
    evt bsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10 x11 x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 i) (Z_to_bv 64 (Z.lor t 32)) (Z_to_bv 64 e) (Z_to_bv 64 rp)
               (Z_to_bv 64 x) (Z_to_bv 64 (znth big d)) (Z_to_bv 64 (hi64 round)) x26 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x28 x29 x30 x31)
          (bvmap_set 10 (Z_to_bv 64 D) (K_Ft K)) (Z_to_bv 64 0x15a570) fc None m (seg_rom bsegs)).
  Proof using AB AF GLO J256 L_8ac SPHI SPLO RIP FXI HA0 ROOM.
    intros until zR; intros MV BIG LW LB REL ZERO Hlo Hlor Ha Hd Hzm Hrzm Hr Hrp ALLW Hi Hn Hx He HD HR5 Haq RUP HzR PR HH.
    destruct K as [pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft]. cbn [K_p1 K_prefix K_pl K_Ft] in RUP, PR, HH |- *.
    dest_midq2 MV. prune. pose proof (zr_word sp : (0 <= bv_unsigned sp < 2^64)%Z) as Rsp.
    assert (Rfw : (0 <= Fp < 2^64)%Z) by apply (zr_word fw).
    pose proof (lo64_range round) as Rrlo. pose proof (hi64_range round) as Rrhi.
    pose proof (ALLW d) as Rbd.
    assert (HFt' : forall k : reg, bv_unsigned k <> 10%Z -> reg_get (bvmap_set 10 (Z_to_bv 64 D) Ft) k = reg_get F k).
    { intros k Hk. rewrite (fother Ft _ k Hk). apply HFt. exact Hk. }
    unfold ffp_R5 in HR5.
    zs. call extenddftf2_callv. 1:{ hyp. } 1:{ lia. }
    set (sm0 := f128_of_d D) in *.
    pose proof (lo64_range sm0) as Rslo. pose proof (hi64_range sm0) as Rshi.
    zs. zs. zs. zs.
    zs. if_cases Kpl; zify_cond Kpl.
    -
      assert (EF : ffp_flip prefix pl round sm0 = (round, sm0)) by (unfold ffp_flip; rewrite Kpl; reflexivity).
      rewrite EF in HR5, RUP. cbn [fst snd] in RUP. cbv beta iota in HR5.
      eapply L_8ac with (K := MidK pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx (bvmap_set 10 (Z_to_bv 64 D) Ft)) (zm := zm) (lo := lo) (r := r) (big := big) (n := n);
        [ mk_midq | exact BIG | exact LW | exact LB | exact REL | exact ZERO | dlia | dlia | dlia | dlia | dlia | dlia | exact Hr | exact Hrp | exact ALLW
        | exact Hi | exact Hn | exact Hx | exact He | exact HR5 | exact Haq | exact RUP | exact HzR | exact PR | exact HH ].
    -
      zs. rewrite Hpfx.
      lazymatch goal with MI' : mem_inv bsegs _ |- _ =>
        pose proof (u8ro_read bsegs _ _ _ prefix _ _ (prefix_u8ro _ MI') (zb_nth PREFIX_STR prefix ltac:(lia) ltac:(cbn; lia)) ltac:(lia) eq_refl) as RD end.
      zs. cbv beta. rewrite (unsigned_lit8 (znth PREFIX_STR prefix)) by (pose proof (PREFIX_STR_range prefix); lia).
      pose proof (PREFIX_STR_range prefix) as Rch.
      zs. zs. if_cases Kmin; zify_cond Kmin.
      +
        assert (EF : ffp_flip prefix pl round sm0 = (round, sm0)).
        { unfold ffp_flip, CHR_minus. rewrite (proj2 (Z.eqb_neq (znth PREFIX_STR prefix) 45) Kmin). rewrite Bool.andb_false_r. reflexivity. }

        rewrite EF in HR5, RUP. cbn [fst snd] in RUP. cbv beta iota in HR5.
        eapply L_8ac with (K := MidK pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx (bvmap_set 10 (Z_to_bv 64 D) Ft)) (zm := zm) (lo := lo) (r := r) (big := big) (n := n);
          [ mk_midq | exact BIG | exact LW | exact LB | exact REL | exact ZERO | dlia | dlia | dlia | dlia | dlia | dlia | exact Hr | exact Hrp | exact ALLW
          | exact Hi | exact Hn | exact Hx | exact He | exact HR5 | exact Haq | exact RUP | exact HzR | exact PR | exact HH ].
      +
        assert (EF : ffp_flip prefix pl round sm0 = (f128_mul round (f128_of_i32 (-1)), f128_mul sm0 (f128_of_i32 (-1)))).
        { unfold ffp_flip, CHR_minus. rewrite (proj2 (Z.eqb_eq (znth PREFIX_STR prefix) 45) Kmin). rewrite (proj2 (Z.eqb_neq pl 0) Kpl). reflexivity. }
        rewrite EF in HR5, RUP. cbn [fst snd] in RUP. cbv beta iota in HR5.
        zs. replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity).
        zs. zs. zs. call floatsitf_callv. 1:{ hyp. } 1:{ lia. } 1:{ symmetry; exact sext32_m1. }
        set (m1 := f128_of_i32 (-1)) in *.
        pose proof (lo64_range m1) as Rmlo. pose proof (hi64_range m1) as Rmhi.
        zs. zs. zs. zs. zs. zs.
        destruct (stk_split bsegs _ _ (bv_unsigned sp + -1056 - 80) _ ST ltac:(lia)) as [STlo STf]. clear ST.
        zs. call multf3_callq. 1:{ exact STf. } 1:{ hyp. } 1:{ lia. }
        match goal with X : stk _ _ (bv_unsigned sp + -1056 - 80)%Z _ |- _ =>
          pose proof (stk_merge bsegs _ _ _ _ STlo X ltac:(lia)) as ST; clear STlo X end.
        set (round' := f128_mul round m1) in *.
        pose proof (lo64_range round') as Rr'lo. pose proof (hi64_range round') as Rr'hi.
        zs. zs. zs. zs. zs. zs.
        destruct (stk_split bsegs _ _ (bv_unsigned sp + -1056 - 80) _ ST ltac:(lia)) as [STlo STf]. clear ST.
        zs. call multf3_callq. 1:{ exact STf. } 1:{ hyp. } 1:{ lia. }
        match goal with X : stk _ _ (bv_unsigned sp + -1056 - 80)%Z _ |- _ =>
          pose proof (stk_merge bsegs _ _ _ _ STlo X ltac:(lia)) as ST; clear STlo X end.
        set (small' := f128_mul sm0 m1) in *.
        pose proof (lo64_range small') as Rs'lo. pose proof (hi64_range small') as Rs'hi.
        zs. zs.

        lazymatch goal with FRs' : rw_cells bsegs _ (bv_unsigned sp + -544)%Z _ |- _ =>
          apply (rw_cells_merge bsegs _ _ [C8 (Z_to_bv 64 0)] [C8 (Z_to_bv 64 (hi64 m1)); C8 (Z_to_bv 64 (lo64 sm0))]) in FRs';
          cbn [cells_size csize cells_bytes cbytes app Nat.add] in FRs' end.
        eapply L_8ac with (K := MidK pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx (bvmap_set 10 (Z_to_bv 64 D) Ft)) (zm := zm) (lo := lo) (r := r) (big := big) (n := n);
          [ mk_midq | exact BIG | exact LW | exact LB | exact REL | exact ZERO | dlia | dlia | dlia | dlia | dlia | dlia | exact Hr | exact Hrp | exact ALLW
          | exact Hi | exact Hn | exact Hx | exact He | exact HR5 | exact Haq | exact RUP | exact HzR | exact PR | exact HH ].
  Qed.

  Lemma L_608 : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word) fc K (jk16 : list byte)
      (ws : list word) (big bigq : list Z) (lo a r rp z zm d e i n x round aq dq eq zR : Z),
    midq K [CB 16 jk16; C8 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * (d - 1) + 65536)); C8 (Z_to_bv 64 (lo64 round)); C8 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d))]
         (Z.b2z (K_pl K =? 0)) m fc ->
    u32arr bsegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
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
    evt bsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10 x11 x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 i) (Z_to_bv 64 (Z.lor t 32)) (Z_to_bv 64 e) (Z_to_bv 64 rp)
               (Z_to_bv 64 x) (Z_to_bv 64 (znth big d)) (Z_to_bv 64 (hi64 round)) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * (d + 1))) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x28 x29 x30 x31)
          (K_Ft K) (Z_to_bv 64 0x15a344) fc None m (seg_rom bsegs)).
  Proof using AB AF GLO J256 L_8ac SPHI SPLO RIP FXI HA0 ROOM.
    intros until zR; intros MV BIG LW LB REL ZERO Hlo Hlor Ha Hd Hzm Hrzm Hr Hrp ALLW Hi Hn Hx He HR4 Haq RUP HzR PR HH.
    destruct K as [pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft]. cbn [K_p1 K_prefix K_pl K_Ft] in RUP, PR, HH |- *.
    pose proof (zr_word sp : (0 <= bv_unsigned sp < 2^64)%Z) as Rsp.
    assert (MI : mem_inv bsegs m) by (destruct MV as ((MI & _) & _); exact MI).
    pose proof (ALLW d) as Rbd.
    assert (Ri : (10 <= i <= 1000000000)%Z).
    { rewrite Hi. split; [change 10%Z with (10 ^ 1)%Z; apply Z.pow_le_mono_r; lia | change 1000000000%Z with (10 ^ 9)%Z; apply Z.pow_le_mono_r; lia]. }
    assert (Rx : (0 <= x < i)%Z) by (rewrite Hx; apply Z.mod_pos_bound; lia).
    unfold ffp_R4 in HR4. rewrite ffp_small_D in HR4, RUP.
    assert (J834 : forall D (x10' : word), ffp_smallD z d i x = D -> (0 <= D < 2^64)%Z ->
      evt bsegs POST
        (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10' x11 x12 x13 x14 x15 x16 x17
                 x18 (Z_to_bv 64 i) (Z_to_bv 64 (Z.lor t 32)) (Z_to_bv 64 e) (Z_to_bv 64 rp)
                 (Z_to_bv 64 x) (Z_to_bv 64 (znth big d)) (Z_to_bv 64 (hi64 round)) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * (d + 1))) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x28 x29 x30 x31)
            (bvmap_set 10 (Z_to_bv 64 D) Ft) (Z_to_bv 64 0x15a570) fc None m (seg_rom bsegs))).
    { intros D x10' HDs HD. rewrite HDs in HR4, RUP.
      eapply L_834 with (K := MidK pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft) (zm := zm) (lo := lo) (r := r) (n := n) (big := big);
        [ exact MV | exact BIG | exact LW | exact LB | exact REL | exact ZERO | dlia | dlia | dlia | dlia | dlia | dlia | exact Hr | exact Hrp | exact ALLW
        | exact Hi | exact Hn | exact Hx | exact He | exact HD | exact HR4 | exact Haq | exact RUP | exact HzR | exact PR | exact HH ]. }
    zs. rewrite srliw1_small by lia.
    assert (Eq2 : Z.quot i 2 = (i / 2)%Z) by (apply Z.quot_div_nonneg; lia).
    zs. if_cases Kh; zify_cond Kh.
    -
      zs. if_cases Kh2; zify_cond Kh2.
      +
        zs. zs. eapply J834; [|unfold D_1_5; lia].
        unfold ffp_smallD. rewrite Eq2. rewrite (proj2 (Z.ltb_ge x (i / 2))) by lia. rewrite (proj2 (Z.eqb_neq x (i / 2))) by lia. reflexivity.
      + zs. if_cases Kdz; zify_cond Kdz.
        *
          zs. zs. eapply J834; [|unfold D_1_5; lia].
          unfold ffp_smallD. rewrite Eq2. rewrite (proj2 (Z.ltb_ge x (i / 2))) by lia. rewrite (proj2 (Z.eqb_neq (d + 1) z)) by lia.
          rewrite Bool.andb_false_r. reflexivity.
        *
          zs. zs. zs. eapply J834; [|unfold D_1_0; lia].
          unfold ffp_smallD. rewrite Eq2. rewrite (proj2 (Z.ltb_ge x (i / 2))) by lia. rewrite (proj2 (Z.eqb_eq x (i / 2))) by lia.
          rewrite (proj2 (Z.eqb_eq (d + 1) z)) by lia. reflexivity.
    -
      zs. zs. zs. eapply J834; [|unfold D_0_5; lia].
      unfold ffp_smallD. rewrite Eq2. rewrite (proj2 (Z.ltb_lt x (i / 2))) by lia. reflexivity.
  Qed.

End FmtFp.
