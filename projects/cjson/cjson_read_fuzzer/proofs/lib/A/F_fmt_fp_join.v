(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_musl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require SoftFloat.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FmtFp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_fwritex.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_pad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require FmtFp_facts2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_divtf3_main.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_frexpl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_fmt_fp_pre2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_fmt_fp_pre4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require FmtFp_splitR.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
Module F_fmt_fp_rnd.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_musl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.FmtFp_facts2.F_frexpl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_divtf3_main OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.FmtFp_facts2.FmtFp_facts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.FmtFp_facts2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_frexpl.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_fmt_fp_pre2.F_fmt_fp_pre OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_fmt_fp_pre2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_fmt_fp_pre4.F_fmt_fp_pre3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_fmt_fp_pre4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_splitH.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


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
  Hypothesis GLO : (6280392 <= bv_unsigned sp - 4640)%Z.   (* [comment removed for export] *)
  Hypothesis AF : (bv_unsigned sp <= Fp)%Z.
  Hypothesis AB : (bv_unsigned sp <= B)%Z.
  (* [comment removed for export] *)
  Hypothesis AX : fmtfp_ax m0 (bv_unsigned sp).
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
  Proof.
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
  Proof.
    intros p1 r big a z e2' (s0 & (bg & zz & e2 & (y & y' & (y2 & e0 & (y1 & fr & HY & HFR & Hy2) & HD) & Hr & HDG) & HU) & HDN).
    cbv zeta in HD. destruct HD as (Hy & He2 & Hp1). subst y2. subst p1 r.
    exact (WB0 y1 fr e0 y e2 bg zz y' s0 big a z e2' HY HFR (conj Hy He2) HDG HU HDN).
  Qed.

  Lemma provG_run : forall p1 r big a z e2, prov_G p1 r (big, a, z, e2) -> run_to_dn yv fl p t p1 r big a z.
  Proof.
    intros p1 r big a z e2' (s0 & (bg & zz & e2 & (y & y' & (y2 & e0 & (y1 & fr & HY & HFR & Hy2) & HD) & Hr & HDG) & HU) & HDN).
    cbv zeta in HD. destruct HD as (Hy & He2 & Hp1). subst y2.
    exists y1, fr, e0, y, e2, bg, zz, y', s0, e2'.
    split; [exact HY|]. split; [exact HFR|]. split; [split; [exact Hy | exact He2]|]. split; [exact Hp1|]. split; [exact Hr|].
    subst r. split; [exact HDG|]. split; [exact HU|]. subst p1. exact HDN.
  Qed.
  Lemma WBA : forall p1 r big a z e2, prov_G p1 r (big, a, z, e2) -> forall i, (0 <= znth big i < 1000000000)%Z.
  Proof. intros p1 r big a z e2 PG. exact (WBA0 _ _ _ _ _ (provG_run _ _ _ _ _ _ PG)). Qed.
  Lemma CAR : forall p1 prefix pl r big a z e, prov_R p1 prefix pl r big a z e -> (0 <= a)%Z.
  Proof.
    intros p1 prefix pl r big a z e (big0 & a0 & z0 & e2' & e0 & PG & He & HR).
    exact (CAR0 _ _ _ _ _ (provG_run _ _ _ _ _ _ PG) _ _ _ _ _ _ _ He HR).
  Qed.
  Lemma AZR : forall p1 prefix pl r big a z e zS, prov_R p1 prefix pl r big a z e ->
    fmt_fp_strip BIG_FUEL big a z = Some zS -> Z.lor t 32 <> CHR_f -> (zS <= a)%Z -> a = r.
  Proof.
    intros p1 prefix pl r big a z e zS (big0 & a0 & z0 & e2' & e0 & PG & He & HR) HS Htf Hza.
    exact (AZR0 _ _ _ _ _ (provG_run _ _ _ _ _ _ PG) _ _ _ _ _ _ _ _ He HR HS Htf Hza).
  Qed.

  Lemma BLA : forall p1 r big a z e2, prov_G p1 r (big, a, z, e2) -> forall k, (0 <= k < a)%Z -> znth big k = 0%Z.
  Proof. intros p1 r big a z e2 PG. exact (BLA0 _ _ _ _ _ (provG_run _ _ _ _ _ _ PG)). Qed.

  Lemma DNB : forall p1 r s, prov_F p1 r s -> dn_good p1 t r s.
  Proof.
    intros p1 r s (big & z & e2 & (y & y' & (y2 & e0 & (y1 & fr & HY & HFR & Hy2) & HD) & Hr & HDG) & HU).
    cbv zeta in HD. destruct HD as (Hy & He2 & Hp1). subst y2. subst p1 r.
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
  (* [comment removed for export] *)
  Lemma MR_now : forall m, munch Wfp m0 m -> MRT m.
  Proof using AX AF AB.
    intros m MU.
    try clear SPLO; try clear SPHI; try clear GLO; try clear Hw; try clear Hp; try clear Hfl; try clear Ht; try clear Hta;
    try clear ROOM; try clear J256; try clear HM; try clear YN0; try clear YN1; try clear DIGB; try clear E2B; try clear DNB0;
    try clear WBA0; try clear CAR0; try clear AZR0; try clear BLA0.
    destruct AX as (MR0 & ACEILh & SPKH). eapply MRT_munch; [exact MR0| exact MU|]. unfold Wfp, Fp, usp in *.
    apply Forall_cons; [apply mrt_iv_ok_stack; lia|].
    apply Forall_cons; [apply mrt_iv_ok_stack; lia|].
    apply Forall_cons; [apply mrt_iv_ok_stack; lia| apply Forall_nil].
  Qed.
  Ltac mr_now := match goal with H : munch _ m0 ?mm |- MRT ?mm' => exact (MR_now _ H) end.
  Ltac alia := unfold alloc_ceiling, sp_window_lo, stack_max_size, KHIGHMEM_END, KHIGHMEM_BEG; lia.
  Ltac lstac := unfold lit_or_stack, A_PFX_TBL, A_FPFX_STR, A_DOT_STR; alia.
  Ltac ax_open := lazymatch goal with
                  | _ : MRT m0 |- _ => idtac
                  | _ => let A := fresh "AXc" in pose proof AX as A; destruct A as (MR0 & ACEILh & SPKH);
                         pose proof ACEILh as ACEILn; unfold alloc_ceiling, sp_window_lo, stack_max_size in ACEILn
                  end.

  Definition fmt_fp_post (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Ft fc' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 ret) a1 a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ munch Wfp m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ frm0 fc'
      /\ stk asegs m' (bv_unsigned sp - 4640) (bv_unsigned sp)
      /\ wfile m' Fp fl0 j1 j2 lbfw B (zb o1) (skipn (length o1 - length o0) junk0)
      /\ ssp_cells m' canary
      /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k).

  (* [comment removed for export] *)
  Definition hi_cells (pad256 : list byte) : list cell :=
    [CB 256 pad256; C8 canary; C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra].

  (* [comment removed for export] *)
  Definition finv (m : word -> option byte) (pad256 : list byte) : Prop :=
    mem_inv asegs m /\ munch Wfp m0 m /\ wmono asegs m0 m
    /\ rw_cells asegs m (bv_unsigned sp + -368) (hi_cells pad256)
    /\ stk asegs m (bv_unsigned sp - 4640) (bv_unsigned sp + -1056)
    /\ rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells asegs m ssp_guard [C8 canary].
  Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
    let ST := fresh "ST" in let GOT := fresh "GOT" in let SSP := fresh "SSP" in
    destruct H as (MI & MU & WM & FRhi & ST & GOT & SSP); unfold Wfp in MU; unfold hi_cells in FRhi; unfold got_ssp, ssp_guard in GOT, SSP.
  Ltac mk_finv := unfold finv, Wfp, hi_cells, got_ssp, ssp_guard;
    split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | idtac]|]; split; hyp.

  Ltac dest_wfile H := let FC := fresh "FC" in let BUF := fresh "BUF" in let FLG := fresh "FLG" in let LBF := fresh "LBF" in
    let Bpos := fresh "Bpos" in let Bhi := fresh "Bhi" in let SEPfb := fresh "SEPfb" in
    destruct H as (FC & BUF & FLG & LBF & Bpos & Bhi & SEPfb); unfold FILE_cells in FC; idtac; idtac .
  Ltac mk_wfile := unfold wfile, FILE_cells; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [lia|]; split; lia.

  (* [comment removed for export] *)
  Definition midv (K : midK) (m : word -> option byte) (fc : bv 32) (e2m : Z) : Prop :=
    finv m (K_pad K) /\ frm0 fc /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get (K_Ft K) k = reg_get F k)
    /\ rw_cells asegs m (bv_unsigned sp + -544)
         [C8 (Z_to_bv 64 0); CB 40 (K_jk40 K); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t); CB 8 (K_jk8 K); C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 6279824);
          C8 (Z_to_bv 64 (K_plz K)); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)]
    /\ rw_cells asegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 e2m); CB 3 (K_jk3 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ K_plz K = Z.b2z (K_pl K =? 0)%Z /\ K_pfx K = (79882 + K_prefix K)%Z
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
  (* [comment removed for export] *)
  Ltac dest_midv2 H :=
    let FI := fresh "FI" in let FRM := fresh "FRM" in let HFt := fresh "HFt" in let FRs := fresh "FRs" in let E2 := fresh "E2" in
    let EB := fresh "EB" in let BF := fresh "BF" in let WF := fresh "WF" in
    let Hpre := fresh "Hpre" in let Hpl := fresh "Hpl" in let Hplz := fresh "Hplz" in let Hpfx := fresh "Hpfx" in let Hp1 := fresh "Hp1" in
    destruct H as (FI & FRM & HFt & FRs & E2 & EB & BF & WF & Hpre & Hpl & Hplz & Hpfx & Hp1);
    cbn [K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft] in *;
    dest_finv FI.
  (* [comment removed for export] *)
  Definition midw (K : midK) (m : word -> option byte) (fc : bv 32) (e2m : Z) : Prop :=
    finv m (K_pad K) /\ frm0 fc /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get (K_Ft K) k = reg_get F k)
    /\ rw_cells asegs m (bv_unsigned sp + -544)
         [C8 (Z_to_bv 64 0); CB 40 (K_jk40 K); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t); CB 8 (K_jk8 K); C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 6279824);
          C8 (Z_to_bv 64 (K_plz K)); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)]
    /\ rw_cells asegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 e2m); CB 3 (K_jk3 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ (0 <= K_plz K < 2^64)%Z /\ K_pfx K = (79882 + K_prefix K)%Z
    /\ (0 <= K_p1 K < 2^20)%Z.
  Lemma midv_w : forall K m fc e2m, midv K m fc e2m -> midw K m fc e2m.
  Proof.
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

  (* [comment removed for export] *)
  Definition midq (K : midK) (cs5 : list cell) (z456 : Z) (m : word -> option byte) (fc : bv 32) : Prop :=
    finv m (K_pad K) /\ frm0 fc /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get (K_Ft K) k = reg_get F k)
    /\ rw_cells asegs m (bv_unsigned sp + -544)
         ([C8 (Z_to_bv 64 0)] ++ cs5 ++ [C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t); C8 (Z_to_bv 64 (K_p1 K)); C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 6279824);
          C8 (Z_to_bv 64 z456); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)])
    /\ rw_cells asegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 0); CB 3 (K_jk3 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ (0 <= z456 < 2^64)%Z /\ K_pfx K = (79882 + K_prefix K)%Z
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
  (* [comment removed for export] *)
  Definition midq_K (K : midK) (cs5 : list cell) (z456 : Z) : midK :=
    MidK (K_pad K) (cells_bytes cs5) (le8 (Z_to_bv 64 (K_p1 K))) (K_jk3 K) (K_jk12 K) (K_jk37 K) (K_p1 K) (K_prefix K) (K_pl K) z456 (K_pfx K) (K_Ft K).
  Lemma midq_w : forall K cs5 z456 m fc, midq K cs5 z456 m fc -> cells_size cs5 = 40%nat -> midw (midq_K K cs5 z456) m fc 0%Z.
  Proof.
    intros K cs5 z456 m fc H Hsz. destruct H as (FI & FRM & HFt & FRs & E2 & EB & BF & WF & Hpre & Hpl & Hplz & Hpfx & Hp1).
    unfold midw, midq_K. cbn [K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft].
    split; [exact FI|]. split; [exact FRM|]. split; [exact HFt|]. split.
    { apply (rw_cells_merge asegs m _ [C8 (Z_to_bv 64 0)] cs5) in FRs. rewrite Hsz in FRs.
      apply (rw_cells_merge asegs m _ [C8 (Z_to_bv 64 0); CB 40 (cells_bytes cs5); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t)] [C8 (Z_to_bv 64 (K_p1 K))]
               [C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 6279824); C8 (Z_to_bv 64 z456); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)]) in FRs.
      cbn [cells_size csize cells_bytes cbytes app Nat.add] in FRs. rewrite app_nil_r in FRs. exact FRs. }
    split; [exact E2|]. split; [exact EB|]. split; [exact BF|]. split; [exact WF|].
    split; [exact Hpre|]. split; [exact Hpl|]. split; [exact Hplz|]. split; [exact Hpfx|]. exact Hp1.
  Qed.

  (* [comment removed for export] *)
  Definition emw (K : midK) (estrp ppl fl2 a8v v440 : Z) (oc : list Z) (m : word -> option byte) (fc : bv 32) : Prop :=
    finv m (K_pad K) /\ frm0 fc /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get (K_Ft K) k = reg_get F k)
    /\ rw_cells asegs m (bv_unsigned sp + -544)
         [C8 (Z_to_bv 64 0); CB 40 (K_jk40 K); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 estrp); C8 (Z_to_bv 64 ppl); C8 (Z_to_bv 64 fl2); C8 (Z_to_bv 64 6279824);
          C8 (Z_to_bv 64 a8v); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 v440); C8 (Z_to_bv 64 Fp)]
    /\ rw_cells asegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 0); CB 3 (K_jk3 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb oc) (skipn (length oc - length o0) junk0)
    /\ (length o0 <= length oc)%nat
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ K_pfx K = (79882 + K_prefix K)%Z /\ (0 <= K_p1 K < 2^20)%Z.
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
  Ltac alia ::= first [ solve [clear_fat; clear_logic; unfold alloc_ceiling, sp_window_lo, stack_max_size, KHIGHMEM_END, KHIGHMEM_BEG; lia]
                    | unfold alloc_ceiling, sp_window_lo, stack_max_size, KHIGHMEM_END, KHIGHMEM_BEG; lia ].

  Notation POST := (fmt_fp_post m0).
  Notation SPv := (Z_to_bv 64 (bv_unsigned sp + -1056)).
  Notation S0v := (Z_to_bv 64 (bv_unsigned sp)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis L_988 :
    forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x24 x25 x26 x28 x30 x31 : word) fc K
      (ws : list word) (big : list Z) (lo a r rp z zm e : Z),
    midw K m fc 0%Z ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (lo <= i < zm)%Z -> znth big i = wval ws i) ->
    (forall i, (zm <= i)%Z -> znth big i = 0%Z) ->
    (0 <= lo <= a)%Z -> (lo <= r)%Z -> (a <= zm)%Z -> (0 <= z <= zm)%Z -> (zm <= 128)%Z -> (r < zm)%Z -> (r = 0 \/ r = 122)%Z -> rp = (bv_unsigned sp + -1056 + 4 * r)%Z ->
    (forall i, (0 <= znth big i < 1000000000)%Z) ->
    (-2^20 <= e < 2^20)%Z ->
    prov_R (K_p1 K) (K_prefix K) (K_pl K) r big a z e ->
    ffp_H o0 w fl t (K_p1 K) (K_prefix K) (K_pl K) big a r z e = Some (o1, ret) ->
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (K_p1 K)) x19 (Z_to_bv 64 (Z.lor t 32)) (Z_to_bv 64 e) (Z_to_bv 64 rp)
               x23 x24 x25 x26 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x28 (Z_to_bv 64 t) x30 x31)
          (K_Ft K) (Z_to_bv 64 0x96700) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Hypothesis L_13c :
    forall m (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x23 x24 x25 x26 x28 x30 x31 : word) fc K
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
          (K_Ft K) (Z_to_bv 64 0x95eb4) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Lemma L_cnt : forall (k : nat) Q m (x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fc
      (n v i e i' e' : Z),
    mem_inv asegs m -> (1 <= n)%Z -> i = (10 ^ n)%Z -> (i <= v)%Z -> (0 <= v < 1000000000)%Z -> (-100000 <= e)%Z -> (e + Z.of_nat k <= 100020)%Z ->
    fmt_fp_cnt k v (i, e) = Some (i', e') ->
    (forall x12', (-100000 <= e' <= 100020)%Z ->
       evt asegs Q
         (MS (mkR x1 SPv gp tp x5 x6 x7 sp x9 (Z_to_bv 64 v) (Z_to_bv 64 10) x12' x13 x14 x15 x16 x17
                  x18 x19 x20 (Z_to_bv 64 e') x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
             Ft (Z_to_bv 64 0x95e74) fc None m (seg_rom asegs))) ->
    evt asegs Q
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp x9 (Z_to_bv 64 v) (Z_to_bv 64 10) (Z_to_bv 64 i) x13 x14 x15 x16 x17
               x18 x19 x20 (Z_to_bv 64 e) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 0x95e5c) fc None m (seg_rom asegs)).
  Proof.
    induction k as [|k IH]; intros until e'; intros MI Hn Hi Hiv Hv He He' HC CONT; [discriminate HC|].
    prune. pose proof (zr_word sp : (0 <= bv_unsigned sp < 2^64)%Z) as Rsp.
    pose proof (pow10_small n v Hn ltac:(rewrite <- Hi; exact Hiv) ltac:(lia)) as Ri. rewrite <- Hi in Ri.
    rewrite fmt_fp_cnt_step in HC. rewrite (proj2 (Z.leb_le i v)) in HC by lia.
    zs. replace (bv_swrap 32 (i * 10)) with (i * 10)%Z by (rewrite swrap32_eq; mlia).
    zs. replace (bv_swrap 32 (Z.land e 18446744073709551615 + 1)) with (e + 1)%Z by (rewrite land_W64, swrap32_eq; mlia).
    zs. if_cases Kc; zify_cond Kc; rewrite ?(land_W64_small (i * 10)) in Kc by lia.
    - (* [comment removed for export] *)
      eapply IH with (n := (n + 1)%Z);
        [ exact MI | lia | rewrite Z.pow_add_r, <- Hi by lia; change (10^1)%Z with 10%Z; lia | dlia | dlia | dlia | dlia | exact HC | exact CONT ].
    - (* [comment removed for export] *)
      destruct k as [|k']; [discriminate HC|]. rewrite fmt_fp_cnt_step in HC. rewrite (proj2 (Z.leb_gt _ _)) in HC by lia.
      injection HC as Hi' <-. zs. apply CONT. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma L_0bc : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x25 x26 x28 x29 x30 x31 : word) fc K
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
          (K_Ft K) (Z_to_bv 64 0x95e34) fc None m (seg_rom asegs)).
  Proof.
    intros until zm; intros MV BIG LW LB REL ZERO Hlo Hlor Ha Hz Hzm Hrzm Hr Hrp PG HG.
    destruct K as [pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft]. cbn [K_p1 K_prefix K_pl K_Ft] in PG, HG.
    pose proof (WB _ _ _ _ _ _ PG) as WBa.
    dest_midv2 MV. prune. pose proof (zr_word sp : (0 <= bv_unsigned sp < 2^64)%Z) as Rsp.
    assert (Rfw : (0 <= Fp < 2^64)%Z) by apply (zr_word fw).
    rewrite ffp_G_eq in HG.
    destruct (ffp_e big a r z) as [e|] eqn:He; [|discriminate HG]. cbv beta iota zeta in HG.
    destruct (ffp_R t p1 prefix pl big a r z e (ffp_j t p1 e)) as [[[[bigR aR] zR] eR]|] eqn:HR; [|discriminate HG].
    assert (Re : (9 * (r - a) <= e <= 9 * (r - a) + 12)%Z \/ e = 0%Z).
    { unfold ffp_e in He. destruct (a <? z); [|injection He; lia].
      destruct (fmt_fp_cnt TEN_FUEL (znth big a) (10%Z, (9 * (r - a))%Z)) as [[i1 e1]|] eqn:HC; [|discriminate He].
      injection He as <-. left. pose proof (fmt_fp_cnt_res _ _ _ _ _ _ HC). unfold TEN_FUEL in *. lia. }
    (* [comment removed for export] *)
    assert (J0fc : forall (x10' x11' x12' x13' : word),
      evt asegs POST
        (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10' x11' x12' x13' x14 x15 x16 x17
                 (Z_to_bv 64 p1) x19 (Z_to_bv 64 (Z.lor t 32)) (Z_to_bv 64 e) (Z_to_bv 64 rp)
                 x23 x24 x25 x26 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x28 (Z_to_bv 64 t) x30 x31)
            Ft (Z_to_bv 64 0x95e74) fc None m (seg_rom asegs))).
    { intros x10' x11' x12' x13'.
      do 15 zs.
      replace (bv_unsigned sp + -1056 + 4 * z - rp)%Z with (4 * (z - r))%Z by lia.
      rewrite a9_eq by lia. rewrite j_eq by lia.
      assert (Rj : (-200000 <= ffp_j t p1 e <= 2^20 + 200000)%Z)
        by (unfold ffp_j, CHR_f, CHR_g; destruct (Z.lor t 32 =? 102), (Z.lor t 32 =? 103), (p1 =? 0); cbn [negb andb]; lia).
      zs. if_cases Kj; zify_cond Kj; rewrite !signed_of_Z in Kj by lia.
      - (* [comment removed for export] *)
        unfold ffp_R in HR. rewrite (proj2 (Z.ltb_ge (ffp_j t p1 e) (9 * (z - r - 1)))) in HR by lia. injection HR as <- <- <- <-.
        eapply L_988 with (K := MidK pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft) (zm := zm) (r := r) (lo := lo);
          [ mk_midw | exact BIG | exact LW | exact LB | exact REL | exact ZERO | dlia | dlia | dlia | dlia | dlia | dlia | exact Hr | exact Hrp
          | exact (WBA _ _ _ _ _ _ PG) | dlia | | exact HG ].
        cbn [K_p1 K_prefix K_pl K_Ft]. exists big, a, z, 0%Z, e. split; [exact PG|]. split; [exact He|].
        unfold ffp_R. rewrite (proj2 (Z.ltb_ge (ffp_j t p1 e) (9 * (z - r - 1)))) by lia. reflexivity.
      - (* [comment removed for export] *)
        eapply L_13c with (K := MidK pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft) (zm := zm) (r := r) (lo := lo);
          [ mk_midv | exact BIG | exact LW | exact LB | exact REL | exact ZERO | dlia | dlia | dlia | dlia | dlia | dlia | exact Hr | exact Hrp
          | exact (WBA _ _ _ _ _ _ PG) | exact (BLA _ _ _ _ _ _ PG) | exact He | reflexivity | dlia | exact PG | exact HR | exact HG ]. }
    (* [comment removed for export] *)
    zs. if_cases Kaz; zify_cond Kaz.
    - (* [comment removed for export] *)
      unfold ffp_e in He. rewrite (proj2 (Z.ltb_ge a z)) in He by lia. injection He as <-.
      zs. zs. apply J0fc.
    - (* [comment removed for export] *)
      pose proof (WBa a ltac:(lia)) as Rv.
      pose proof (u32arr_read asegs _ _ _ a _ _ BIG (nth_error_wnth ws a ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
      zs. zs. rewrite (sx32_wval ws a) by (rewrite <- (REL a) by lia; lia). rewrite <- (REL a) by lia.
      zs. zs. zs. zs.
      replace (rp - (bv_unsigned sp + -1056 + 4 * a))%Z with (4 * (r - a))%Z by lia. rewrite e9_eq by lia.
      unfold ffp_e in He. rewrite (proj2 (Z.ltb_lt a z)) in He by lia.
      destruct (fmt_fp_cnt TEN_FUEL (znth big a) (10%Z, (9 * (r - a))%Z)) as [[i1 e1]|] eqn:HC; [|discriminate He]. injection He as ->.
      zs. zs. if_cases K10; zify_cond K10.
      + (* [comment removed for export] *)
        unfold TEN_FUEL in HC. rewrite fmt_fp_cnt_step in HC. rewrite (proj2 (Z.leb_gt _ _)) in HC by lia. injection HC as _ <-.
        apply J0fc.
      + zs.
        eapply (L_cnt TEN_FUEL) with (n := 1%Z); [ exact MI | lia | reflexivity | dlia | dlia | dlia | unfold TEN_FUEL; dlia | exact HC | ].
        intros x12' Re'. apply J0fc.
  Qed.

End FmtFp.


End CeilWrap.
End F_fmt_fp_rnd.

(* [comment removed for export] *)
Module F_fmt_fp_t100.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_musl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.FmtFp_facts2.F_frexpl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_divtf3_main OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.FmtFp_facts2.FmtFp_facts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.FmtFp_facts2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_frexpl.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_fmt_fp_pre2.F_fmt_fp_pre OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_fmt_fp_pre2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_fmt_fp_pre4.F_fmt_fp_pre3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_fmt_fp_pre4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_splitH.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


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
  Hypothesis GLO : (6280392 <= bv_unsigned sp - 4640)%Z.   (* [comment removed for export] *)
  Hypothesis AF : (bv_unsigned sp <= Fp)%Z.
  Hypothesis AB : (bv_unsigned sp <= B)%Z.
  (* [comment removed for export] *)
  Hypothesis AX : fmtfp_ax m0 (bv_unsigned sp).
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
  Proof.
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
  Proof.
    intros p1 r big a z e2' (s0 & (bg & zz & e2 & (y & y' & (y2 & e0 & (y1 & fr & HY & HFR & Hy2) & HD) & Hr & HDG) & HU) & HDN).
    cbv zeta in HD. destruct HD as (Hy & He2 & Hp1). subst y2. subst p1 r.
    exact (WB0 y1 fr e0 y e2 bg zz y' s0 big a z e2' HY HFR (conj Hy He2) HDG HU HDN).
  Qed.

  Lemma provG_run : forall p1 r big a z e2, prov_G p1 r (big, a, z, e2) -> run_to_dn yv fl p t p1 r big a z.
  Proof.
    intros p1 r big a z e2' (s0 & (bg & zz & e2 & (y & y' & (y2 & e0 & (y1 & fr & HY & HFR & Hy2) & HD) & Hr & HDG) & HU) & HDN).
    cbv zeta in HD. destruct HD as (Hy & He2 & Hp1). subst y2.
    exists y1, fr, e0, y, e2, bg, zz, y', s0, e2'.
    split; [exact HY|]. split; [exact HFR|]. split; [split; [exact Hy | exact He2]|]. split; [exact Hp1|]. split; [exact Hr|].
    subst r. split; [exact HDG|]. split; [exact HU|]. subst p1. exact HDN.
  Qed.
  Lemma WBA : forall p1 r big a z e2, prov_G p1 r (big, a, z, e2) -> forall i, (0 <= znth big i < 1000000000)%Z.
  Proof. intros p1 r big a z e2 PG. exact (WBA0 _ _ _ _ _ (provG_run _ _ _ _ _ _ PG)). Qed.
  Lemma CAR : forall p1 prefix pl r big a z e, prov_R p1 prefix pl r big a z e -> (0 <= a)%Z.
  Proof.
    intros p1 prefix pl r big a z e (big0 & a0 & z0 & e2' & e0 & PG & He & HR).
    exact (CAR0 _ _ _ _ _ (provG_run _ _ _ _ _ _ PG) _ _ _ _ _ _ _ He HR).
  Qed.
  Lemma AZR : forall p1 prefix pl r big a z e zS, prov_R p1 prefix pl r big a z e ->
    fmt_fp_strip BIG_FUEL big a z = Some zS -> Z.lor t 32 <> CHR_f -> (zS <= a)%Z -> a = r.
  Proof.
    intros p1 prefix pl r big a z e zS (big0 & a0 & z0 & e2' & e0 & PG & He & HR) HS Htf Hza.
    exact (AZR0 _ _ _ _ _ (provG_run _ _ _ _ _ _ PG) _ _ _ _ _ _ _ _ He HR HS Htf Hza).
  Qed.

  Lemma BLA : forall p1 r big a z e2, prov_G p1 r (big, a, z, e2) -> forall k, (0 <= k < a)%Z -> znth big k = 0%Z.
  Proof. intros p1 r big a z e2 PG. exact (BLA0 _ _ _ _ _ (provG_run _ _ _ _ _ _ PG)). Qed.

  Lemma DNB : forall p1 r s, prov_F p1 r s -> dn_good p1 t r s.
  Proof.
    intros p1 r s (big & z & e2 & (y & y' & (y2 & e0 & (y1 & fr & HY & HFR & Hy2) & HD) & Hr & HDG) & HU).
    cbv zeta in HD. destruct HD as (Hy & He2 & Hp1). subst y2. subst p1 r.
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
  (* [comment removed for export] *)
  Lemma MR_now : forall m, munch Wfp m0 m -> MRT m.
  Proof using AX AF AB.
    intros m MU.
    try clear SPLO; try clear SPHI; try clear GLO; try clear Hw; try clear Hp; try clear Hfl; try clear Ht; try clear Hta;
    try clear ROOM; try clear J256; try clear HM; try clear YN0; try clear YN1; try clear DIGB; try clear E2B; try clear DNB0;
    try clear WBA0; try clear CAR0; try clear AZR0; try clear BLA0.
    destruct AX as (MR0 & ACEILh & SPKH). eapply MRT_munch; [exact MR0| exact MU|]. unfold Wfp, Fp, usp in *.
    apply Forall_cons; [apply mrt_iv_ok_stack; lia|].
    apply Forall_cons; [apply mrt_iv_ok_stack; lia|].
    apply Forall_cons; [apply mrt_iv_ok_stack; lia| apply Forall_nil].
  Qed.
  Ltac mr_now := match goal with H : munch _ m0 ?mm |- MRT ?mm' => exact (MR_now _ H) end.
  Ltac alia := unfold alloc_ceiling, sp_window_lo, stack_max_size, KHIGHMEM_END, KHIGHMEM_BEG; lia.
  Ltac lstac := unfold lit_or_stack, A_PFX_TBL, A_FPFX_STR, A_DOT_STR; alia.
  Ltac ax_open := lazymatch goal with
                  | _ : MRT m0 |- _ => idtac
                  | _ => let A := fresh "AXc" in pose proof AX as A; destruct A as (MR0 & ACEILh & SPKH);
                         pose proof ACEILh as ACEILn; unfold alloc_ceiling, sp_window_lo, stack_max_size in ACEILn
                  end.

  Definition fmt_fp_post (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Ft fc' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 ret) a1 a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ munch Wfp m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ frm0 fc'
      /\ stk asegs m' (bv_unsigned sp - 4640) (bv_unsigned sp)
      /\ wfile m' Fp fl0 j1 j2 lbfw B (zb o1) (skipn (length o1 - length o0) junk0)
      /\ ssp_cells m' canary
      /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k).

  (* [comment removed for export] *)
  Definition hi_cells (pad256 : list byte) : list cell :=
    [CB 256 pad256; C8 canary; C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra].

  (* [comment removed for export] *)
  Definition finv (m : word -> option byte) (pad256 : list byte) : Prop :=
    mem_inv asegs m /\ munch Wfp m0 m /\ wmono asegs m0 m
    /\ rw_cells asegs m (bv_unsigned sp + -368) (hi_cells pad256)
    /\ stk asegs m (bv_unsigned sp - 4640) (bv_unsigned sp + -1056)
    /\ rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells asegs m ssp_guard [C8 canary].
  Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
    let ST := fresh "ST" in let GOT := fresh "GOT" in let SSP := fresh "SSP" in
    destruct H as (MI & MU & WM & FRhi & ST & GOT & SSP); unfold Wfp in MU; unfold hi_cells in FRhi; unfold got_ssp, ssp_guard in GOT, SSP.
  Ltac mk_finv := unfold finv, Wfp, hi_cells, got_ssp, ssp_guard;
    split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | idtac]|]; split; hyp.

  Ltac dest_wfile H := let FC := fresh "FC" in let BUF := fresh "BUF" in let FLG := fresh "FLG" in let LBF := fresh "LBF" in
    let Bpos := fresh "Bpos" in let Bhi := fresh "Bhi" in let SEPfb := fresh "SEPfb" in
    destruct H as (FC & BUF & FLG & LBF & Bpos & Bhi & SEPfb); unfold FILE_cells in FC; idtac; idtac .
  Ltac mk_wfile := unfold wfile, FILE_cells; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [lia|]; split; lia.

  (* [comment removed for export] *)
  Definition midv (K : midK) (m : word -> option byte) (fc : bv 32) (e2m : Z) : Prop :=
    finv m (K_pad K) /\ frm0 fc /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get (K_Ft K) k = reg_get F k)
    /\ rw_cells asegs m (bv_unsigned sp + -544)
         [C8 (Z_to_bv 64 0); CB 40 (K_jk40 K); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t); CB 8 (K_jk8 K); C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 6279824);
          C8 (Z_to_bv 64 (K_plz K)); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)]
    /\ rw_cells asegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 e2m); CB 3 (K_jk3 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ K_plz K = Z.b2z (K_pl K =? 0)%Z /\ K_pfx K = (79882 + K_prefix K)%Z
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
  (* [comment removed for export] *)
  Ltac dest_midv2 H :=
    let FI := fresh "FI" in let FRM := fresh "FRM" in let HFt := fresh "HFt" in let FRs := fresh "FRs" in let E2 := fresh "E2" in
    let EB := fresh "EB" in let BF := fresh "BF" in let WF := fresh "WF" in
    let Hpre := fresh "Hpre" in let Hpl := fresh "Hpl" in let Hplz := fresh "Hplz" in let Hpfx := fresh "Hpfx" in let Hp1 := fresh "Hp1" in
    destruct H as (FI & FRM & HFt & FRs & E2 & EB & BF & WF & Hpre & Hpl & Hplz & Hpfx & Hp1);
    cbn [K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft] in *;
    dest_finv FI.
  (* [comment removed for export] *)
  Definition midw (K : midK) (m : word -> option byte) (fc : bv 32) (e2m : Z) : Prop :=
    finv m (K_pad K) /\ frm0 fc /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get (K_Ft K) k = reg_get F k)
    /\ rw_cells asegs m (bv_unsigned sp + -544)
         [C8 (Z_to_bv 64 0); CB 40 (K_jk40 K); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t); CB 8 (K_jk8 K); C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 6279824);
          C8 (Z_to_bv 64 (K_plz K)); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)]
    /\ rw_cells asegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 e2m); CB 3 (K_jk3 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ (0 <= K_plz K < 2^64)%Z /\ K_pfx K = (79882 + K_prefix K)%Z
    /\ (0 <= K_p1 K < 2^20)%Z.
  Lemma midv_w : forall K m fc e2m, midv K m fc e2m -> midw K m fc e2m.
  Proof.
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

  (* [comment removed for export] *)
  Definition midq (K : midK) (cs5 : list cell) (z456 : Z) (m : word -> option byte) (fc : bv 32) : Prop :=
    finv m (K_pad K) /\ frm0 fc /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get (K_Ft K) k = reg_get F k)
    /\ rw_cells asegs m (bv_unsigned sp + -544)
         ([C8 (Z_to_bv 64 0)] ++ cs5 ++ [C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t); C8 (Z_to_bv 64 (K_p1 K)); C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 6279824);
          C8 (Z_to_bv 64 z456); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)])
    /\ rw_cells asegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 0); CB 3 (K_jk3 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ (0 <= z456 < 2^64)%Z /\ K_pfx K = (79882 + K_prefix K)%Z
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
  (* [comment removed for export] *)
  Definition midq_K (K : midK) (cs5 : list cell) (z456 : Z) : midK :=
    MidK (K_pad K) (cells_bytes cs5) (le8 (Z_to_bv 64 (K_p1 K))) (K_jk3 K) (K_jk12 K) (K_jk37 K) (K_p1 K) (K_prefix K) (K_pl K) z456 (K_pfx K) (K_Ft K).
  Lemma midq_w : forall K cs5 z456 m fc, midq K cs5 z456 m fc -> cells_size cs5 = 40%nat -> midw (midq_K K cs5 z456) m fc 0%Z.
  Proof.
    intros K cs5 z456 m fc H Hsz. destruct H as (FI & FRM & HFt & FRs & E2 & EB & BF & WF & Hpre & Hpl & Hplz & Hpfx & Hp1).
    unfold midw, midq_K. cbn [K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft].
    split; [exact FI|]. split; [exact FRM|]. split; [exact HFt|]. split.
    { apply (rw_cells_merge asegs m _ [C8 (Z_to_bv 64 0)] cs5) in FRs. rewrite Hsz in FRs.
      apply (rw_cells_merge asegs m _ [C8 (Z_to_bv 64 0); CB 40 (cells_bytes cs5); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t)] [C8 (Z_to_bv 64 (K_p1 K))]
               [C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 6279824); C8 (Z_to_bv 64 z456); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)]) in FRs.
      cbn [cells_size csize cells_bytes cbytes app Nat.add] in FRs. rewrite app_nil_r in FRs. exact FRs. }
    split; [exact E2|]. split; [exact EB|]. split; [exact BF|]. split; [exact WF|].
    split; [exact Hpre|]. split; [exact Hpl|]. split; [exact Hplz|]. split; [exact Hpfx|]. exact Hp1.
  Qed.

  (* [comment removed for export] *)
  Definition emw (K : midK) (estrp ppl fl2 a8v v440 : Z) (oc : list Z) (m : word -> option byte) (fc : bv 32) : Prop :=
    finv m (K_pad K) /\ frm0 fc /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get (K_Ft K) k = reg_get F k)
    /\ rw_cells asegs m (bv_unsigned sp + -544)
         [C8 (Z_to_bv 64 0); CB 40 (K_jk40 K); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 estrp); C8 (Z_to_bv 64 ppl); C8 (Z_to_bv 64 fl2); C8 (Z_to_bv 64 6279824);
          C8 (Z_to_bv 64 a8v); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 v440); C8 (Z_to_bv 64 Fp)]
    /\ rw_cells asegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 0); CB 3 (K_jk3 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb oc) (skipn (length oc - length o0) junk0)
    /\ (length o0 <= length oc)%nat
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ K_pfx K = (79882 + K_prefix K)%Z /\ (0 <= K_p1 K < 2^20)%Z.
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
  Ltac alia ::= first [ solve [clear_fat; clear_logic; unfold alloc_ceiling, sp_window_lo, stack_max_size, KHIGHMEM_END, KHIGHMEM_BEG; lia]
                    | unfold alloc_ceiling, sp_window_lo, stack_max_size, KHIGHMEM_END, KHIGHMEM_BEG; lia ].

  Notation POST := (fmt_fp_post m0).
  Notation SPv := (Z_to_bv 64 (bv_unsigned sp + -1056)).
  Notation S0v := (Z_to_bv 64 (bv_unsigned sp)).

  (* [comment removed for export] *)
  Lemma L_100 : forall m (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) fc K
      (ws : list word) (estrp a8v v440 l : Z) (oc : list Z),
    emw K estrp (K_pl K + l) (Z.land fl 73728) a8v v440 oc m fc ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    (1 <= l < 2^24)%Z ->
    ffp_H6 oc w fl (K_pl K) l = Some (o1, ret) ->
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 (Z_to_bv 64 w) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (K_Ft K) (Z_to_bv 64 0x96e78) fc None m (seg_rom asegs)).
  Proof.
    intros until oc; intros MV BIG LW Hl HH.
    destruct K as [padb jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft]. cbn [K_p1 K_prefix K_pl K_Ft K_jk12 K_jk37] in HH, MV |- *.
    dest_emw2 MV. prune. pose proof (zr_word sp : (0 <= bv_unsigned sp < 2^64)%Z) as Rsp.
    assert (Rfw : (0 <= Fp < 2^64)%Z) by apply (zr_word fw).
    assert (Rfl2 : (0 <= Z.land fl 73728 <= 73728)%Z).
    { split; [apply Z.land_nonneg; lia|]. apply land_le_r; lia. }
    (* [comment removed for export] *)
    unfold ffp_H6 in HH. rewrite pad_id in HH by lia. injection HH as Eo1 Eret. rewrite Z.max_r in Eret by lia.
    zs. zs. zs. zs.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mcur _) =>
    assert (J88 : evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp x9 (Z_to_bv 64 8192) (Z_to_bv 64 (Z.land fl 73728)) x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (pl + l)) x19 (Z_to_bv 64 6279824) (Z_to_bv 64 w) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 0x96f00) fc None mcur (seg_rom asegs)))
    end.
    { zs. if_cases Klt; zify_cond Klt; rewrite ?signed_of_Z in Klt by lia; [exfalso; lia|].
      zs. zs. rewrite Eret. zs.
      (* [comment removed for export] *)
      zs. zs. zs. if_cases Kc; zify_cond Kc; try (exfalso; clear -Kc; apply Kc; reflexivity).
      do 15 zs.
      (* [comment removed for export] *)
      pose proof (rw_cells_of_u8arr _ _ _ _ (u8arr_of_u32arr _ _ _ _ BIG)) as FRbig. clear BIG.
      rewrite u32s_length, LW in FRbig.
      release_frame FRbig ST (bv_unsigned sp + -544)%Z.
      release_frame FRs ST (bv_unsigned sp + -424)%Z.
      release_frame E2 ST (bv_unsigned sp + -417)%Z.
      release_frame EB ST (bv_unsigned sp + -405)%Z.
      release_frame BF ST (bv_unsigned sp + -368)%Z.
      release_frame FRhi ST (bv_unsigned sp)%Z.
      zs.
      apply evt_done. unfold fmt_fp_post.
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [ ms_eq | ].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRM|]. split; [exact ST|].
      split; [rewrite <- Eo1; exact WF|]. split; [unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT | exact SSP] | exact HFt]. }
    zs. if_cases Kla; zify_cond Kla.
    - exact J88.
    - zs. if_cases Kge; zify_cond Kge; rewrite ?signed_of_Z in Kge by lia; [exact J88 | exfalso; lia].
  Qed.

End FmtFp.


End CeilWrap.
End F_fmt_fp_t100.

(* [comment removed for export] *)
Module F_fmt_fp_t988.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_musl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.FmtFp_facts2.F_frexpl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_divtf3_main OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.FmtFp_facts2.FmtFp_facts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.FmtFp_facts2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_frexpl.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_fmt_fp_pre2.F_fmt_fp_pre OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_fmt_fp_pre2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_fmt_fp_pre4.F_fmt_fp_pre3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_fmt_fp_pre4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_splitH.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


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
  Hypothesis GLO : (6280392 <= bv_unsigned sp - 4640)%Z.   (* [comment removed for export] *)
  Hypothesis AF : (bv_unsigned sp <= Fp)%Z.
  Hypothesis AB : (bv_unsigned sp <= B)%Z.
  (* [comment removed for export] *)
  Hypothesis AX : fmtfp_ax m0 (bv_unsigned sp).
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
  Proof.
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
  Proof.
    intros p1 r big a z e2' (s0 & (bg & zz & e2 & (y & y' & (y2 & e0 & (y1 & fr & HY & HFR & Hy2) & HD) & Hr & HDG) & HU) & HDN).
    cbv zeta in HD. destruct HD as (Hy & He2 & Hp1). subst y2. subst p1 r.
    exact (WB0 y1 fr e0 y e2 bg zz y' s0 big a z e2' HY HFR (conj Hy He2) HDG HU HDN).
  Qed.

  Lemma provG_run : forall p1 r big a z e2, prov_G p1 r (big, a, z, e2) -> run_to_dn yv fl p t p1 r big a z.
  Proof.
    intros p1 r big a z e2' (s0 & (bg & zz & e2 & (y & y' & (y2 & e0 & (y1 & fr & HY & HFR & Hy2) & HD) & Hr & HDG) & HU) & HDN).
    cbv zeta in HD. destruct HD as (Hy & He2 & Hp1). subst y2.
    exists y1, fr, e0, y, e2, bg, zz, y', s0, e2'.
    split; [exact HY|]. split; [exact HFR|]. split; [split; [exact Hy | exact He2]|]. split; [exact Hp1|]. split; [exact Hr|].
    subst r. split; [exact HDG|]. split; [exact HU|]. subst p1. exact HDN.
  Qed.
  Lemma WBA : forall p1 r big a z e2, prov_G p1 r (big, a, z, e2) -> forall i, (0 <= znth big i < 1000000000)%Z.
  Proof. intros p1 r big a z e2 PG. exact (WBA0 _ _ _ _ _ (provG_run _ _ _ _ _ _ PG)). Qed.
  Lemma CAR : forall p1 prefix pl r big a z e, prov_R p1 prefix pl r big a z e -> (0 <= a)%Z.
  Proof.
    intros p1 prefix pl r big a z e (big0 & a0 & z0 & e2' & e0 & PG & He & HR).
    exact (CAR0 _ _ _ _ _ (provG_run _ _ _ _ _ _ PG) _ _ _ _ _ _ _ He HR).
  Qed.
  Lemma AZR : forall p1 prefix pl r big a z e zS, prov_R p1 prefix pl r big a z e ->
    fmt_fp_strip BIG_FUEL big a z = Some zS -> Z.lor t 32 <> CHR_f -> (zS <= a)%Z -> a = r.
  Proof.
    intros p1 prefix pl r big a z e zS (big0 & a0 & z0 & e2' & e0 & PG & He & HR) HS Htf Hza.
    exact (AZR0 _ _ _ _ _ (provG_run _ _ _ _ _ _ PG) _ _ _ _ _ _ _ _ He HR HS Htf Hza).
  Qed.

  Lemma BLA : forall p1 r big a z e2, prov_G p1 r (big, a, z, e2) -> forall k, (0 <= k < a)%Z -> znth big k = 0%Z.
  Proof. intros p1 r big a z e2 PG. exact (BLA0 _ _ _ _ _ (provG_run _ _ _ _ _ _ PG)). Qed.

  Lemma DNB : forall p1 r s, prov_F p1 r s -> dn_good p1 t r s.
  Proof.
    intros p1 r s (big & z & e2 & (y & y' & (y2 & e0 & (y1 & fr & HY & HFR & Hy2) & HD) & Hr & HDG) & HU).
    cbv zeta in HD. destruct HD as (Hy & He2 & Hp1). subst y2. subst p1 r.
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
  (* [comment removed for export] *)
  Lemma MR_now : forall m, munch Wfp m0 m -> MRT m.
  Proof using AX AF AB.
    intros m MU.
    try clear SPLO; try clear SPHI; try clear GLO; try clear Hw; try clear Hp; try clear Hfl; try clear Ht; try clear Hta;
    try clear ROOM; try clear J256; try clear HM; try clear YN0; try clear YN1; try clear DIGB; try clear E2B; try clear DNB0;
    try clear WBA0; try clear CAR0; try clear AZR0; try clear BLA0.
    destruct AX as (MR0 & ACEILh & SPKH). eapply MRT_munch; [exact MR0| exact MU|]. unfold Wfp, Fp, usp in *.
    apply Forall_cons; [apply mrt_iv_ok_stack; lia|].
    apply Forall_cons; [apply mrt_iv_ok_stack; lia|].
    apply Forall_cons; [apply mrt_iv_ok_stack; lia| apply Forall_nil].
  Qed.
  Ltac mr_now := match goal with H : munch _ m0 ?mm |- MRT ?mm' => exact (MR_now _ H) end.
  Ltac alia := unfold alloc_ceiling, sp_window_lo, stack_max_size, KHIGHMEM_END, KHIGHMEM_BEG; lia.
  Ltac lstac := unfold lit_or_stack, A_PFX_TBL, A_FPFX_STR, A_DOT_STR; alia.
  Ltac ax_open := lazymatch goal with
                  | _ : MRT m0 |- _ => idtac
                  | _ => let A := fresh "AXc" in pose proof AX as A; destruct A as (MR0 & ACEILh & SPKH);
                         pose proof ACEILh as ACEILn; unfold alloc_ceiling, sp_window_lo, stack_max_size in ACEILn
                  end.

  Definition fmt_fp_post (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Ft fc' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 ret) a1 a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ munch Wfp m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ frm0 fc'
      /\ stk asegs m' (bv_unsigned sp - 4640) (bv_unsigned sp)
      /\ wfile m' Fp fl0 j1 j2 lbfw B (zb o1) (skipn (length o1 - length o0) junk0)
      /\ ssp_cells m' canary
      /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k).

  (* [comment removed for export] *)
  Definition hi_cells (pad256 : list byte) : list cell :=
    [CB 256 pad256; C8 canary; C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra].

  (* [comment removed for export] *)
  Definition finv (m : word -> option byte) (pad256 : list byte) : Prop :=
    mem_inv asegs m /\ munch Wfp m0 m /\ wmono asegs m0 m
    /\ rw_cells asegs m (bv_unsigned sp + -368) (hi_cells pad256)
    /\ stk asegs m (bv_unsigned sp - 4640) (bv_unsigned sp + -1056)
    /\ rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells asegs m ssp_guard [C8 canary].
  Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
    let ST := fresh "ST" in let GOT := fresh "GOT" in let SSP := fresh "SSP" in
    destruct H as (MI & MU & WM & FRhi & ST & GOT & SSP); unfold Wfp in MU; unfold hi_cells in FRhi; unfold got_ssp, ssp_guard in GOT, SSP.
  Ltac mk_finv := unfold finv, Wfp, hi_cells, got_ssp, ssp_guard;
    split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | idtac]|]; split; hyp.

  Ltac dest_wfile H := let FC := fresh "FC" in let BUF := fresh "BUF" in let FLG := fresh "FLG" in let LBF := fresh "LBF" in
    let Bpos := fresh "Bpos" in let Bhi := fresh "Bhi" in let SEPfb := fresh "SEPfb" in
    destruct H as (FC & BUF & FLG & LBF & Bpos & Bhi & SEPfb); unfold FILE_cells in FC; idtac; idtac .
  Ltac mk_wfile := unfold wfile, FILE_cells; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [lia|]; split; lia.

  (* [comment removed for export] *)
  Definition midv (K : midK) (m : word -> option byte) (fc : bv 32) (e2m : Z) : Prop :=
    finv m (K_pad K) /\ frm0 fc /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get (K_Ft K) k = reg_get F k)
    /\ rw_cells asegs m (bv_unsigned sp + -544)
         [C8 (Z_to_bv 64 0); CB 40 (K_jk40 K); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t); CB 8 (K_jk8 K); C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 6279824);
          C8 (Z_to_bv 64 (K_plz K)); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)]
    /\ rw_cells asegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 e2m); CB 3 (K_jk3 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ K_plz K = Z.b2z (K_pl K =? 0)%Z /\ K_pfx K = (79882 + K_prefix K)%Z
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
  (* [comment removed for export] *)
  Ltac dest_midv2 H :=
    let FI := fresh "FI" in let FRM := fresh "FRM" in let HFt := fresh "HFt" in let FRs := fresh "FRs" in let E2 := fresh "E2" in
    let EB := fresh "EB" in let BF := fresh "BF" in let WF := fresh "WF" in
    let Hpre := fresh "Hpre" in let Hpl := fresh "Hpl" in let Hplz := fresh "Hplz" in let Hpfx := fresh "Hpfx" in let Hp1 := fresh "Hp1" in
    destruct H as (FI & FRM & HFt & FRs & E2 & EB & BF & WF & Hpre & Hpl & Hplz & Hpfx & Hp1);
    cbn [K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft] in *;
    dest_finv FI.
  (* [comment removed for export] *)
  Definition midw (K : midK) (m : word -> option byte) (fc : bv 32) (e2m : Z) : Prop :=
    finv m (K_pad K) /\ frm0 fc /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get (K_Ft K) k = reg_get F k)
    /\ rw_cells asegs m (bv_unsigned sp + -544)
         [C8 (Z_to_bv 64 0); CB 40 (K_jk40 K); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t); CB 8 (K_jk8 K); C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 6279824);
          C8 (Z_to_bv 64 (K_plz K)); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)]
    /\ rw_cells asegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 e2m); CB 3 (K_jk3 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ (0 <= K_plz K < 2^64)%Z /\ K_pfx K = (79882 + K_prefix K)%Z
    /\ (0 <= K_p1 K < 2^20)%Z.
  Lemma midv_w : forall K m fc e2m, midv K m fc e2m -> midw K m fc e2m.
  Proof.
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

  (* [comment removed for export] *)
  Definition midq (K : midK) (cs5 : list cell) (z456 : Z) (m : word -> option byte) (fc : bv 32) : Prop :=
    finv m (K_pad K) /\ frm0 fc /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get (K_Ft K) k = reg_get F k)
    /\ rw_cells asegs m (bv_unsigned sp + -544)
         ([C8 (Z_to_bv 64 0)] ++ cs5 ++ [C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t); C8 (Z_to_bv 64 (K_p1 K)); C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 6279824);
          C8 (Z_to_bv 64 z456); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)])
    /\ rw_cells asegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 0); CB 3 (K_jk3 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ (0 <= z456 < 2^64)%Z /\ K_pfx K = (79882 + K_prefix K)%Z
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
  (* [comment removed for export] *)
  Definition midq_K (K : midK) (cs5 : list cell) (z456 : Z) : midK :=
    MidK (K_pad K) (cells_bytes cs5) (le8 (Z_to_bv 64 (K_p1 K))) (K_jk3 K) (K_jk12 K) (K_jk37 K) (K_p1 K) (K_prefix K) (K_pl K) z456 (K_pfx K) (K_Ft K).
  Lemma midq_w : forall K cs5 z456 m fc, midq K cs5 z456 m fc -> cells_size cs5 = 40%nat -> midw (midq_K K cs5 z456) m fc 0%Z.
  Proof.
    intros K cs5 z456 m fc H Hsz. destruct H as (FI & FRM & HFt & FRs & E2 & EB & BF & WF & Hpre & Hpl & Hplz & Hpfx & Hp1).
    unfold midw, midq_K. cbn [K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft].
    split; [exact FI|]. split; [exact FRM|]. split; [exact HFt|]. split.
    { apply (rw_cells_merge asegs m _ [C8 (Z_to_bv 64 0)] cs5) in FRs. rewrite Hsz in FRs.
      apply (rw_cells_merge asegs m _ [C8 (Z_to_bv 64 0); CB 40 (cells_bytes cs5); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t)] [C8 (Z_to_bv 64 (K_p1 K))]
               [C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 6279824); C8 (Z_to_bv 64 z456); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)]) in FRs.
      cbn [cells_size csize cells_bytes cbytes app Nat.add] in FRs. rewrite app_nil_r in FRs. exact FRs. }
    split; [exact E2|]. split; [exact EB|]. split; [exact BF|]. split; [exact WF|].
    split; [exact Hpre|]. split; [exact Hpl|]. split; [exact Hplz|]. split; [exact Hpfx|]. exact Hp1.
  Qed.

  (* [comment removed for export] *)
  Definition emw (K : midK) (estrp ppl fl2 a8v v440 : Z) (oc : list Z) (m : word -> option byte) (fc : bv 32) : Prop :=
    finv m (K_pad K) /\ frm0 fc /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get (K_Ft K) k = reg_get F k)
    /\ rw_cells asegs m (bv_unsigned sp + -544)
         [C8 (Z_to_bv 64 0); CB 40 (K_jk40 K); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 estrp); C8 (Z_to_bv 64 ppl); C8 (Z_to_bv 64 fl2); C8 (Z_to_bv 64 6279824);
          C8 (Z_to_bv 64 a8v); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 v440); C8 (Z_to_bv 64 Fp)]
    /\ rw_cells asegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 0); CB 3 (K_jk3 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb oc) (skipn (length oc - length o0) junk0)
    /\ (length o0 <= length oc)%nat
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ K_pfx K = (79882 + K_prefix K)%Z /\ (0 <= K_p1 K < 2^20)%Z.
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
  Ltac alia ::= first [ solve [clear_fat; clear_logic; unfold alloc_ceiling, sp_window_lo, stack_max_size, KHIGHMEM_END, KHIGHMEM_BEG; lia]
                    | unfold alloc_ceiling, sp_window_lo, stack_max_size, KHIGHMEM_END, KHIGHMEM_BEG; lia ].

  Notation POST := (fmt_fp_post m0).
  Notation SPv := (Z_to_bv 64 (bv_unsigned sp + -1056)).
  Notation S0v := (Z_to_bv 64 (bv_unsigned sp)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis L_9a8 :
    forall m (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x24 x25 x26 x27 x28 x30 x31 : word) fc K
      (ws : list word) (big : list Z) (lo a r rp z zm e : Z),
    midw K m fc 0%Z ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (lo <= i < zm)%Z -> znth big i = wval ws i) ->
    (forall i, (zm <= i)%Z -> znth big i = 0%Z) ->
    (0 <= lo <= a)%Z -> (lo <= r)%Z -> (a <= zm)%Z -> (0 <= z <= zm)%Z -> (zm <= 128)%Z -> (r < zm)%Z -> (r = 0 \/ r = 122)%Z -> rp = (bv_unsigned sp + -1056 + 4 * r)%Z ->
    (forall i, (0 <= znth big i < 1000000000)%Z) ->
    (-2^20 <= e < 2^20)%Z ->
    (a < z -> znth big (z - 1) <> 0)%Z -> (Z.lor t 32 <> CHR_f -> z <= a -> a = r)%Z ->
    ffp_H2 o0 w fl t (K_p1 K) (K_prefix K) (K_pl K) big a r z e = Some (o1, ret) ->
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) (Z_to_bv 64 (4 * (z - r))) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (K_p1 K)) x19 (Z_to_bv 64 (Z.lor t 32)) (Z_to_bv 64 e) (Z_to_bv 64 rp)
               (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x24 x25 x26 x27 x28 (Z_to_bv 64 t) x30 x31)
          (K_Ft K) (Z_to_bv 64 0x96720) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Lemma L_strip2 : forall (k : nat) Q m (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word) Ft fc
      (ws : list word) (big : list Z) (lo a r zc zm zS : Z),
    mem_inv asegs m ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    (forall i, (lo <= i < zm)%Z -> znth big i = wval ws i) ->
    (0 <= lo <= a)%Z -> (a <= zm)%Z -> (0 <= zc <= zm)%Z -> (zm <= 128)%Z -> (0 <= r <= 122)%Z ->
    fmt_fp_strip k big a zc = Some zS ->
    (forall (x11' x12' x27' : word),
       (zS <= zc)%Z -> (a <= zc -> a <= zS)%Z -> (zc < a -> zS = zc)%Z ->
       evt asegs Q
         (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) (Z_to_bv 64 (4 * (zS - r))) x11' x12' x13 x14 x15 x16 x17
                  x18 x19 x20 x21 x22 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * zS)) x24 x25 x26 x27' x28 x29 x30 x31)
             Ft (Z_to_bv 64 0x96720) fc None m (seg_rom asegs))) ->
    evt asegs Q
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10 (Z_to_bv 64 (4 * (zc - r))) x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * zc)) x28 x29 x30 x31)
          Ft (Z_to_bv 64 0x96704) fc None m (seg_rom asegs)).
  Proof.
    induction k as [|k IH]; intros until zS; intros MI BIG LW REL Hlo Ha Hzc Hzm Hr HS CONT; [discriminate HS|].
    pose proof (zr_word sp : (0 <= bv_unsigned sp < 2^64)%Z) as Rsp.
    rewrite fmt_fp_strip_step in HS.
    zs. zs. zs. if_cases Kaz; zify_cond Kaz.
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.ltb_ge a zc)) in HS by lia. cbn [andb] in HS. injection HS as <-.
      apply CONT; lia.
    - rewrite (proj2 (Z.ltb_lt a zc)) in HS by lia. cbn [andb] in HS.
      pose proof (wval_range ws (zc - 1)) as Rv.
      pose proof (u32arr_read asegs _ _ _ (zc - 1)%Z _ _ BIG (nth_error_wnth ws (zc - 1)%Z ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
      zs. zs. zs.
      zs. if_cases Kz; zify_cond Kz.
      + (* [comment removed for export] *)
        apply sx32_zero in Kz. change 4294967296%Z with (2^32)%Z in Kz.
        assert (Ez : znth big (zc - 1) = 0%Z) by (rewrite (REL (zc - 1)%Z) by lia; unfold wval; change 4294967296%Z with (2^32)%Z; exact Kz).
        rewrite Ez in HS. cbn [Z.eqb fmt_fp_strip_body] in HS.
        replace (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * zc + -4)) with (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * (zc - 1))) by (f_equal; lia).
        replace (Z_to_bv 64 (4 * (zc - r) + -4)) with (Z_to_bv 64 (4 * ((zc - 1) - r))) by (f_equal; lia).
        eapply IH; [ exact MI | exact BIG | exact LW | exact REL | dlia | dlia | dlia | dlia | dlia | exact HS | ].
        intros x11' x12' x27' H1 H2 H3. apply CONT; lia.
      + apply sx32_nonzero in Kz. change 4294967296%Z with (2^32)%Z in Kz.
        assert (Ez : znth big (zc - 1) <> 0%Z) by (rewrite (REL (zc - 1)%Z) by lia; unfold wval; change 4294967296%Z with (2^32)%Z; exact Kz).
        rewrite (proj2 (Z.eqb_neq _ _) Ez) in HS. injection HS as <-.
        apply CONT; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma L_988 : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x24 x25 x26 x28 x30 x31 : word) fc K
      (ws : list word) (big : list Z) (lo a r rp z zm e : Z),
    midw K m fc 0%Z ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (lo <= i < zm)%Z -> znth big i = wval ws i) ->
    (forall i, (zm <= i)%Z -> znth big i = 0%Z) ->
    (0 <= lo <= a)%Z -> (lo <= r)%Z -> (a <= zm)%Z -> (0 <= z <= zm)%Z -> (zm <= 128)%Z -> (r < zm)%Z -> (r = 0 \/ r = 122)%Z -> rp = (bv_unsigned sp + -1056 + 4 * r)%Z ->
    (forall i, (0 <= znth big i < 1000000000)%Z) ->
    (-2^20 <= e < 2^20)%Z ->
    prov_R (K_p1 K) (K_prefix K) (K_pl K) r big a z e ->
    ffp_H o0 w fl t (K_p1 K) (K_prefix K) (K_pl K) big a r z e = Some (o1, ret) ->
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (K_p1 K)) x19 (Z_to_bv 64 (Z.lor t 32)) (Z_to_bv 64 e) (Z_to_bv 64 rp)
               x23 x24 x25 x26 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x28 (Z_to_bv 64 t) x30 x31)
          (K_Ft K) (Z_to_bv 64 0x96700) fc None m (seg_rom asegs)).
  Proof.
    intros until e; intros MV BIG LW LB REL ZERO Hlo Hlor Ha Hz Hzm Hrzm Hr Hrp ALLW He PR HH.
    pose proof (zr_word sp : (0 <= bv_unsigned sp < 2^64)%Z) as Rsp.
    assert (MI : mem_inv asegs m) by (destruct MV as ((MI & _) & _); exact MI).
    rewrite ffp_H_eq in HH. destruct (fmt_fp_strip BIG_FUEL big a z) as [zS|] eqn:HS; [|discriminate HH].
    zs. replace (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z - rp)) with (Z_to_bv 64 (4 * (z - r))) by (f_equal; lia).
    eapply (L_strip2 BIG_FUEL) with (lo := lo) (zm := zm); [ exact MI | exact BIG | exact LW | exact REL | dlia | dlia | dlia | dlia | dlia | exact HS | ].
    intros x11' x12' x27' H1 H2 H3.
    eapply L_9a8 with (zm := zm) (lo := lo);
      [ exact MV | exact BIG | exact LW | exact LB | exact REL | exact ZERO | dlia | dlia | dlia | dlia | dlia | dlia | exact Hr | exact Hrp | exact ALLW | exact He
      | intros Hlt; exact (fmt_fp_strip_last _ _ _ _ _ HS Hlt) | intros Htf Hza; exact (AZR _ _ _ _ _ _ _ _ _ PR HS Htf Hza) | exact HH ].
  Qed.

End FmtFp.


End CeilWrap.
End F_fmt_fp_t988.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Module F_fmt_fp_ta98.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_musl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.FmtFp_facts2.F_frexpl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_divtf3_main OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.FmtFp_facts2.FmtFp_facts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.FmtFp_facts2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_frexpl.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_fmt_fp_pre2.F_fmt_fp_pre OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_fmt_fp_pre2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_fmt_fp_pre4.F_fmt_fp_pre3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_fmt_fp_pre4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_splitH.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.LiaClosure.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_chunks_extra_wfile m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= transport_call_extra_wfile segs W m m' MU WM.
Local Ltac lia ::= lia3.
Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
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
  Hypothesis GLO : (6280392 <= bv_unsigned sp - 4640)%Z.   (* [comment removed for export] *)
  Hypothesis AF : (bv_unsigned sp <= Fp)%Z.
  Hypothesis AB : (bv_unsigned sp <= B)%Z.
  (* [comment removed for export] *)
  Hypothesis AX : fmtfp_ax m0 (bv_unsigned sp).
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
  Proof using WBA0.
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

  (* [comment removed for export] *)
  Definition ctx_all : unit :=
    let _ := (ra, sp, gp, tp, s0e, s1e, s2e, s3e, s4e, s5e, s6e, s7e, s8e, s9e, s10e, s11e, ya, yb, fw, F, m0,
              fl0, j1, j2, lbfw, B, junk0, canary, w, p, fl, t, o0, o1, ret) in tt.

  Definition Wfp : list (Z * Z) :=
    [(bv_unsigned sp - 4640, bv_unsigned sp);
     (B + Z.of_nat (length o0), B + Z.of_nat (length o1));
     (Fp + 40, Fp + 48)]%Z.
  (* [comment removed for export] *)
  Lemma MR_now : forall m, munch Wfp m0 m -> MRT m.
  Proof using AX AF AB.
    intros m MU.
    try clear SPLO; try clear SPHI; try clear GLO; try clear Hw; try clear Hp; try clear Hfl; try clear Ht; try clear Hta;
    try clear ROOM; try clear J256; try clear HM; try clear YN0; try clear YN1; try clear DIGB; try clear E2B; try clear DNB0;
    try clear WBA0; try clear CAR0; try clear AZR0; try clear BLA0.
    destruct AX as (MR0 & ACEILh & SPKH). eapply MRT_munch; [exact MR0| exact MU|]. unfold Wfp, Fp, usp in *.
    apply Forall_cons; [apply mrt_iv_ok_stack; lia|].
    apply Forall_cons; [apply mrt_iv_ok_stack; lia|].
    apply Forall_cons; [apply mrt_iv_ok_stack; lia| apply Forall_nil].
  Qed.
  Ltac mr_now := match goal with H : munch _ m0 ?mm |- MRT ?mm' => exact (MR_now _ H) end.
  Ltac alia := unfold alloc_ceiling, sp_window_lo, stack_max_size, KHIGHMEM_END, KHIGHMEM_BEG; lia.
  Ltac lstac := unfold lit_or_stack, A_PFX_TBL, A_FPFX_STR, A_DOT_STR; alia.
  Ltac ax_open := lazymatch goal with
                  | _ : MRT m0 |- _ => idtac
                  | _ => let A := fresh "AXc" in pose proof AX as A; destruct A as (MR0 & ACEILh & SPKH);
                         pose proof ACEILh as ACEILn; unfold alloc_ceiling, sp_window_lo, stack_max_size in ACEILn
                  end.

  Definition fmt_fp_post (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Ft fc' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 ret) a1 a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ munch Wfp m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ frm0 fc'
      /\ stk asegs m' (bv_unsigned sp - 4640) (bv_unsigned sp)
      /\ wfile m' Fp fl0 j1 j2 lbfw B (zb o1) (skipn (length o1 - length o0) junk0)
      /\ ssp_cells m' canary
      /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k).

  (* [comment removed for export] *)
  Definition hi_cells (pad256 : list byte) : list cell :=
    [CB 256 pad256; C8 canary; C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra].

  (* [comment removed for export] *)
  Definition finv (m : word -> option byte) (pad256 : list byte) : Prop :=
    mem_inv asegs m /\ munch Wfp m0 m /\ wmono asegs m0 m
    /\ rw_cells asegs m (bv_unsigned sp + -368) (hi_cells pad256)
    /\ stk asegs m (bv_unsigned sp - 4640) (bv_unsigned sp + -1056)
    /\ rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells asegs m ssp_guard [C8 canary].
  Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
    let ST := fresh "ST" in let GOT := fresh "GOT" in let SSP := fresh "SSP" in
    destruct H as (MI & MU & WM & FRhi & ST & GOT & SSP); unfold Wfp in MU; unfold hi_cells in FRhi; unfold got_ssp, ssp_guard in GOT, SSP.
  Ltac mk_finv := unfold finv, Wfp, hi_cells, got_ssp, ssp_guard;
    split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | idtac]|]; split; hyp.

  Ltac dest_wfile H := let FC := fresh "FC" in let BUF := fresh "BUF" in let FLG := fresh "FLG" in let LBF := fresh "LBF" in
    let Bpos := fresh "Bpos" in let Bhi := fresh "Bhi" in let SEPfb := fresh "SEPfb" in
    destruct H as (FC & BUF & FLG & LBF & Bpos & Bhi & SEPfb); unfold FILE_cells in FC; idtac; idtac .
  Ltac mk_wfile := unfold wfile, FILE_cells; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [lia|]; split; lia.

  (* [comment removed for export] *)
  Definition midv (K : midK) (m : word -> option byte) (fc : bv 32) (e2m : Z) : Prop :=
    finv m (K_pad K) /\ frm0 fc /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get (K_Ft K) k = reg_get F k)
    /\ rw_cells asegs m (bv_unsigned sp + -544)
         [C8 (Z_to_bv 64 0); CB 40 (K_jk40 K); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t); CB 8 (K_jk8 K); C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 6279824);
          C8 (Z_to_bv 64 (K_plz K)); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)]
    /\ rw_cells asegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 e2m); CB 3 (K_jk3 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ K_plz K = Z.b2z (K_pl K =? 0)%Z /\ K_pfx K = (79882 + K_prefix K)%Z
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
  (* [comment removed for export] *)
  Ltac dest_midv2 H :=
    let FI := fresh "FI" in let FRM := fresh "FRM" in let HFt := fresh "HFt" in let FRs := fresh "FRs" in let E2 := fresh "E2" in
    let EB := fresh "EB" in let BF := fresh "BF" in let WF := fresh "WF" in
    let Hpre := fresh "Hpre" in let Hpl := fresh "Hpl" in let Hplz := fresh "Hplz" in let Hpfx := fresh "Hpfx" in let Hp1 := fresh "Hp1" in
    destruct H as (FI & FRM & HFt & FRs & E2 & EB & BF & WF & Hpre & Hpl & Hplz & Hpfx & Hp1);
    cbn [K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft] in *;
    dest_finv FI.
  (* [comment removed for export] *)
  Definition midw (K : midK) (m : word -> option byte) (fc : bv 32) (e2m : Z) : Prop :=
    finv m (K_pad K) /\ frm0 fc /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get (K_Ft K) k = reg_get F k)
    /\ rw_cells asegs m (bv_unsigned sp + -544)
         [C8 (Z_to_bv 64 0); CB 40 (K_jk40 K); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t); CB 8 (K_jk8 K); C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 6279824);
          C8 (Z_to_bv 64 (K_plz K)); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)]
    /\ rw_cells asegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 e2m); CB 3 (K_jk3 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ (0 <= K_plz K < 2^64)%Z /\ K_pfx K = (79882 + K_prefix K)%Z
    /\ (0 <= K_p1 K < 2^20)%Z.
  Lemma midv_w : forall K m fc e2m, midv K m fc e2m -> midw K m fc e2m.
  Proof using Hfl Ht J256.
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

  (* [comment removed for export] *)
  Definition midq (K : midK) (cs5 : list cell) (z456 : Z) (m : word -> option byte) (fc : bv 32) : Prop :=
    finv m (K_pad K) /\ frm0 fc /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get (K_Ft K) k = reg_get F k)
    /\ rw_cells asegs m (bv_unsigned sp + -544)
         ([C8 (Z_to_bv 64 0)] ++ cs5 ++ [C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t); C8 (Z_to_bv 64 (K_p1 K)); C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 6279824);
          C8 (Z_to_bv 64 z456); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)])
    /\ rw_cells asegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 0); CB 3 (K_jk3 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ (0 <= z456 < 2^64)%Z /\ K_pfx K = (79882 + K_prefix K)%Z
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
  (* [comment removed for export] *)
  Definition midq_K (K : midK) (cs5 : list cell) (z456 : Z) : midK :=
    MidK (K_pad K) (cells_bytes cs5) (le8 (Z_to_bv 64 (K_p1 K))) (K_jk3 K) (K_jk12 K) (K_jk37 K) (K_p1 K) (K_prefix K) (K_pl K) z456 (K_pfx K) (K_Ft K).
  Lemma midq_w : forall K cs5 z456 m fc, midq K cs5 z456 m fc -> cells_size cs5 = 40%nat -> midw (midq_K K cs5 z456) m fc 0%Z.
  Proof using .
    intros K cs5 z456 m fc H Hsz. destruct H as (FI & FRM & HFt & FRs & E2 & EB & BF & WF & Hpre & Hpl & Hplz & Hpfx & Hp1).
    unfold midw, midq_K. cbn [K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft].
    split; [exact FI|]. split; [exact FRM|]. split; [exact HFt|]. split.
    { apply (rw_cells_merge asegs m _ [C8 (Z_to_bv 64 0)] cs5) in FRs. rewrite Hsz in FRs.
      apply (rw_cells_merge asegs m _ [C8 (Z_to_bv 64 0); CB 40 (cells_bytes cs5); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t)] [C8 (Z_to_bv 64 (K_p1 K))]
               [C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 6279824); C8 (Z_to_bv 64 z456); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)]) in FRs.
      cbn [cells_size csize cells_bytes cbytes app Nat.add] in FRs. rewrite app_nil_r in FRs. exact FRs. }
    split; [exact E2|]. split; [exact EB|]. split; [exact BF|]. split; [exact WF|].
    split; [exact Hpre|]. split; [exact Hpl|]. split; [exact Hplz|]. split; [exact Hpfx|]. exact Hp1.
  Qed.

  (* [comment removed for export] *)
  Definition emw (K : midK) (estrp ppl fl2 a8v v440 : Z) (oc : list Z) (m : word -> option byte) (fc : bv 32) : Prop :=
    finv m (K_pad K) /\ frm0 fc /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get (K_Ft K) k = reg_get F k)
    /\ rw_cells asegs m (bv_unsigned sp + -544)
         [C8 (Z_to_bv 64 0); CB 40 (K_jk40 K); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 estrp); C8 (Z_to_bv 64 ppl); C8 (Z_to_bv 64 fl2); C8 (Z_to_bv 64 6279824);
          C8 (Z_to_bv 64 a8v); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 v440); C8 (Z_to_bv 64 Fp)]
    /\ rw_cells asegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 0); CB 3 (K_jk3 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb oc) (skipn (length oc - length o0) junk0)
    /\ (length o0 <= length oc)%nat
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ K_pfx K = (79882 + K_prefix K)%Z /\ (0 <= K_p1 K < 2^20)%Z.
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
  Ltac alia ::= first [ solve [clear_fat; clear_logic; unfold alloc_ceiling, sp_window_lo, stack_max_size, KHIGHMEM_END, KHIGHMEM_BEG; lia]
                    | unfold alloc_ceiling, sp_window_lo, stack_max_size, KHIGHMEM_END, KHIGHMEM_BEG; lia ].

  Notation POST := (fmt_fp_post m0).
  Notation SPv := (Z_to_bv 64 (bv_unsigned sp + -1056)).
  Notation S0v := (Z_to_bv 64 (bv_unsigned sp)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis L_aec :
    forall m (x1 x5 x6 x7 x14 x15 x16 x17 x19 x26 x31 : word) fc K
      (ws : list word) (big : list Z) (lo a r rp z zm e p2 t2 a8 palt : Z),
    midw K m fc 0%Z ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (lo <= i < zm)%Z -> znth big i = wval ws i) ->
    (forall i, (zm <= i)%Z -> znth big i = 0%Z) ->
    (0 <= lo <= a)%Z -> (lo <= r)%Z -> (a <= zm)%Z -> (0 <= z <= zm)%Z -> (zm <= 128)%Z -> (r < zm)%Z -> (r = 0 \/ r = 122)%Z -> rp = (bv_unsigned sp + -1056 + 4 * r)%Z ->
    (forall i, (0 <= znth big i < 1000000000)%Z) ->
    (-2^20 <= e < 2^20)%Z -> (0 <= p2 < 2^21)%Z -> (0 <= t2 < 256)%Z ->
    (a < z -> znth big (z - 1) <> 0)%Z -> (Z.lor t2 32 <> CHR_f -> z <= a -> a = r)%Z ->
    (0 <= a8 <= 8)%Z -> (a8 = 0%Z <-> Z.land fl 8 = 0%Z) ->
    palt = (if negb (p2 =? 0) || negb (Z.land fl ALT_FORM =? 0) then 1 else 0)%Z ->
    Z.lor t2 32 <> CHR_f ->
    (let? len := fmt_fp_len t2 (1 + p2 + palt) e in
     match len with
     | Ret v => Some (o0, v)
     | Cont (l, ebuf0, estr) => ffp_H4 o0 w fl t2 p2 (K_prefix K) (K_pl K) big a r z l ebuf0 estr
     end) = Some (o1, ret) ->
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) (Z_to_bv 64 (-1)) (Z_to_bv 64 2147483647) (Z_to_bv 64 (p2 + palt + 1)) (Z_to_bv 64 70) x14 x15 x16 x17
               (Z_to_bv 64 p2) x19 (Z_to_bv 64 6279824) (Z_to_bv 64 e) (Z_to_bv 64 rp)
               (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) (Z_to_bv 64 (Z.land t2 18446744073709551583)) (Z_to_bv 64 (Z.lor p2 a8)) x26 (Z_to_bv 64 p2)
               (Z_to_bv 64 fl) (Z_to_bv 64 t2) (Z_to_bv 64 a8) x31)
          (K_Ft K) (Z_to_bv 64 0x96864) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Hypothesis L_bb4 :
    forall m (x1 x5 x6 x7 x10 x14 x15 x16 x19 x26 x31 : word) fc K
      (ws : list word) (big : list Z) (lo a r rp z zm e p2 t2 a8 palt l1 l2 estr estrp : Z) (ebuf0 : list Z),
    midw K m fc 0%Z ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (lo <= i < zm)%Z -> znth big i = wval ws i) ->
    (forall i, (zm <= i)%Z -> znth big i = 0%Z) ->
    (0 <= lo <= a)%Z -> (lo <= r)%Z -> (a <= zm)%Z -> (0 <= z <= zm)%Z -> (zm <= 128)%Z -> (r < zm)%Z -> (r = 0 \/ r = 122)%Z -> rp = (bv_unsigned sp + -1056 + 4 * r)%Z ->
    (forall i, (0 <= znth big i < 1000000000)%Z) ->
    (-2^20 <= e < 2^20)%Z -> (0 <= p2 < 2^21)%Z -> (0 <= t2 < 256)%Z ->
    (a < z -> znth big (z - 1) <> 0)%Z -> (Z.lor t2 32 <> CHR_f -> z <= a -> a = r)%Z ->
    (0 <= a8 <= 8)%Z -> (a8 = 0%Z <-> Z.land fl 8 = 0%Z) ->
    palt = (if negb (p2 =? 0) || negb (Z.land fl ALT_FORM =? 0) then 1 else 0)%Z ->
    l1 = (1 + p2 + palt)%Z -> (0 <= l2 < 2^21)%Z -> (0 <= estrp < 2^64)%Z -> length ebuf0 = 12%nat ->
    (Z.lor t2 32 <> CHR_f -> (1 <= estr <= 10)%Z /\ estrp = (bv_unsigned sp + -417 + estr)%Z /\
       forall k, (estr <= k < 12)%Z -> nth_error (K_jk12 K) (Z.to_nat k) = Some (Z_to_bv 8 (znth ebuf0 k))) ->
    ffp_H4 o0 w fl t2 p2 (K_prefix K) (K_pl K) big a r z (l1 + l2) ebuf0 estr = Some (o1, ret) ->
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10 (Z_to_bv 64 2147483647) (Z_to_bv 64 l1) (Z_to_bv 64 l2) x14 x15 x16
               (Z_to_bv 64 estrp)
               (Z_to_bv 64 p2) x19 (Z_to_bv 64 6279824) (Z_to_bv 64 e) (Z_to_bv 64 rp)
               (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) (Z_to_bv 64 (Z.land t2 18446744073709551583)) (Z_to_bv 64 (Z.lor p2 a8)) x26 (Z_to_bv 64 p2)
               (Z_to_bv 64 fl) (Z_to_bv 64 t2) (Z_to_bv 64 a8) x31)
          (K_Ft K) (Z_to_bv 64 0x9692c) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Lemma L_a98 : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x24 x25 x26 x27 x31 : word) fc K
      (ws : list word) (big : list Z) (lo a r rp z zm e p2 t2 a8 : Z),
    midw K m fc 0%Z ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (lo <= i < zm)%Z -> znth big i = wval ws i) ->
    (forall i, (zm <= i)%Z -> znth big i = 0%Z) ->
    (0 <= lo <= a)%Z -> (lo <= r)%Z -> (a <= zm)%Z -> (0 <= z <= zm)%Z -> (zm <= 128)%Z -> (r < zm)%Z -> (r = 0 \/ r = 122)%Z -> rp = (bv_unsigned sp + -1056 + 4 * r)%Z ->
    (forall i, (0 <= znth big i < 1000000000)%Z) ->
    (-2^20 <= e < 2^20)%Z -> (0 <= p2 < 2^21)%Z -> (0 <= t2 < 256)%Z ->
    (a < z -> znth big (z - 1) <> 0)%Z -> (Z.lor t2 32 <> CHR_f -> z <= a -> a = r)%Z ->
    (0 <= a8 <= 8)%Z -> (a8 = 0%Z <-> Z.land fl 8 = 0%Z) ->
    ffp_H3 o0 w fl t2 p2 (K_prefix K) (K_pl K) big a r z e = Some (o1, ret) ->
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 p2) x19 (Z_to_bv 64 6279824) (Z_to_bv 64 e) (Z_to_bv 64 rp)
               (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x24 x25 x26 x27 (Z_to_bv 64 fl) (Z_to_bv 64 t2) (Z_to_bv 64 a8) x31)
          (K_Ft K) (Z_to_bv 64 0x96810) fc None m (seg_rom asegs)).
  Proof using J256 L_aec L_bb4.
    intros until a8; intros MV BIG LW LB REL ZERO Hlo Hlor Ha Hz Hzm Hrzm Hr Hrp ALLW He Hp2 Ht2 Hnz Haz Ha8 Ha8iff HH.
    destruct K as [pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft]. cbn [K_p1 K_prefix K_pl K_Ft] in HH |- *.
    dest_midw2 MV. prune. pose proof (zr_word sp : (0 <= bv_unsigned sp < 2^64)%Z) as Rsp.
    assert (Rfw : (0 <= Fp < 2^64)%Z) by apply (zr_word fw).
    assert (Rpa : (0 <= Z.lor p2 a8 <= p2 + a8)%Z).
    { pose proof (Z.add_lor_land p2 a8). pose proof (Z.land_nonneg p2 a8). pose proof (Z.lor_nonneg p2 a8). lia. }
    destruct (zboxed_intro (if negb (p2 =? 0) || negb (Z.land fl ALT_FORM =? 0) then 1 else 0)%Z) as [palt Epalt]. apply zboxed_eq in Epalt.
    assert (Hpalt : palt = Z.b2z (0 <? Z.lor p2 a8)%Z) by (rewrite Epalt; apply palt_eq; [lia|lia|exact Ha8iff]).
    assert (Rpalt : (0 <= palt <= 1)%Z) by (rewrite Epalt; destruct (_ || _); lia).
    unfold ffp_H3 in HH. rewrite <- Epalt in HH.
    zs. zs. replace (bv_swrap 32 (p2 + 0)) with p2 by (rewrite swrap32_eq; mlia).
    zs. zs. replace (bv_swrap 32 (Z.lor p2 a8 + 0)) with (Z.lor p2 a8) by (rewrite swrap32_eq; mlia).
    zs. rewrite <- Hpalt. zs. zs. zs. zs. if_cases Kov; zify_cond Kov; rewrite ?signed_of_Z in Kov by lia; [exfalso; lia|].
    rewrite (proj2 (Z.ltb_ge _ p2)) in HH by (unfold INT_MAX; lia).
    zs. zs. zs. zs. zs.
    zs. if_cases Kf; zify_cond Kf; rewrite land_t_m33 in Kf by lia.
    - (* [comment removed for export] *)
      assert (Kf' : Z.lor t2 32 <> 102%Z) by (intros E; apply Kf; apply (proj2 (andn32_70 t2 ltac:(lia))); exact E).
      eapply L_aec with (K := MidK pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft) (zm := zm) (lo := lo) (r := r) (palt := palt);
        [ mk_midw | exact BIG | exact LW | exact LB | exact REL | exact ZERO | dlia | dlia | dlia | dlia | dlia | dlia | exact Hr | exact Hrp | exact ALLW
        | exact He | exact Hp2 | exact Ht2 | exact Hnz | exact Haz | exact Ha8 | exact Ha8iff | exact Epalt | exact Kf' | exact HH ].
    - (* [comment removed for export] *)
      apply (proj1 (andn32_70 t2 ltac:(lia))) in Kf.
      unfold fmt_fp_len, CHR_f in HH. rewrite (proj2 (Z.eqb_eq _ _) Kf) in HH.
      rewrite (proj2 (Z.ltb_ge (INT_MAX - (1 + p2 + palt)) e)) in HH by (unfold INT_MAX; lia). cbv beta iota in HH.
      replace (if 0 <? e then 1 + p2 + palt + e else 1 + p2 + palt)%Z with (1 + p2 + palt + Z.max 0 e)%Z in HH by (destruct (Z.ltb_spec0 0 e); lia).
      zs. zs. if_cases Kov2; zify_cond Kov2. { exfalso. revert Kov2. rewrite ?signed_of_Z by (rewrite ?swrap32_eq; mlia). rewrite swrap32_eq. mlia. }
      zs. zs. zs. rewrite sgtz_max by lia. zs.
      replace x17 with (Z_to_bv 64 (bv_unsigned x17)) by (apply Z_to_bv_bv_unsigned).
      replace (Z_to_bv 64 (p2 + palt + 1)) with (Z_to_bv 64 (1 + p2 + palt)) by (f_equal; lia).
      eapply L_bb4 with (K := MidK pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft) (zm := zm) (lo := lo) (r := r) (estr := 12%Z) (palt := palt) (ebuf0 := zrepeat 0%Z 12);
        [ mk_midw | exact BIG | exact LW | exact LB | exact REL | exact ZERO | dlia | dlia | dlia | dlia | dlia | dlia | exact Hr | exact Hrp | exact ALLW
        | exact He | exact Hp2 | exact Ht2 | exact Hnz | exact Haz | exact Ha8 | exact Ha8iff | exact Epalt | reflexivity | dlia | apply (zr_word x17) | reflexivity
        | intros Hne; exfalso; exact (Hne Kf) | exact HH ].
  Qed.

End FmtFp.


End CeilWrap.
End F_fmt_fp_ta98.

(* [comment removed for export] *)
Module F_fmt_fp_tbb4.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_musl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.FmtFp_facts2.F_frexpl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_divtf3_main OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.FmtFp_facts2.FmtFp_facts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.FmtFp_facts2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_frexpl.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_fmt_fp_pre2.F_fmt_fp_pre OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_fmt_fp_pre2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_fmt_fp_pre4.F_fmt_fp_pre3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_fmt_fp_pre4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_splitH.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.LiaClosure.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_chunks_extra_wfile m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= transport_call_extra_wfile segs W m m' MU WM.
Local Ltac lia ::= lia3.
Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
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
  Hypothesis GLO : (6280392 <= bv_unsigned sp - 4640)%Z.   (* [comment removed for export] *)
  Hypothesis AF : (bv_unsigned sp <= Fp)%Z.
  Hypothesis AB : (bv_unsigned sp <= B)%Z.
  (* [comment removed for export] *)
  Hypothesis AX : fmtfp_ax m0 (bv_unsigned sp).
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
  Proof using WBA0.
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

  (* [comment removed for export] *)
  Definition ctx_all : unit :=
    let _ := (ra, sp, gp, tp, s0e, s1e, s2e, s3e, s4e, s5e, s6e, s7e, s8e, s9e, s10e, s11e, ya, yb, fw, F, m0,
              fl0, j1, j2, lbfw, B, junk0, canary, w, p, fl, t, o0, o1, ret) in tt.

  Definition Wfp : list (Z * Z) :=
    [(bv_unsigned sp - 4640, bv_unsigned sp);
     (B + Z.of_nat (length o0), B + Z.of_nat (length o1));
     (Fp + 40, Fp + 48)]%Z.
  (* [comment removed for export] *)
  Lemma MR_now : forall m, munch Wfp m0 m -> MRT m.
  Proof using AX AF AB.
    intros m MU.
    try clear SPLO; try clear SPHI; try clear GLO; try clear Hw; try clear Hp; try clear Hfl; try clear Ht; try clear Hta;
    try clear ROOM; try clear J256; try clear HM; try clear YN0; try clear YN1; try clear DIGB; try clear E2B; try clear DNB0;
    try clear WBA0; try clear CAR0; try clear AZR0; try clear BLA0.
    destruct AX as (MR0 & ACEILh & SPKH). eapply MRT_munch; [exact MR0| exact MU|]. unfold Wfp, Fp, usp in *.
    apply Forall_cons; [apply mrt_iv_ok_stack; lia|].
    apply Forall_cons; [apply mrt_iv_ok_stack; lia|].
    apply Forall_cons; [apply mrt_iv_ok_stack; lia| apply Forall_nil].
  Qed.
  Ltac mr_now := match goal with H : munch _ m0 ?mm |- MRT ?mm' => exact (MR_now _ H) end.
  Ltac alia := unfold alloc_ceiling, sp_window_lo, stack_max_size, KHIGHMEM_END, KHIGHMEM_BEG; lia.
  Ltac lstac := unfold lit_or_stack, A_PFX_TBL, A_FPFX_STR, A_DOT_STR; alia.
  Ltac ax_open := lazymatch goal with
                  | _ : MRT m0 |- _ => idtac
                  | _ => let A := fresh "AXc" in pose proof AX as A; destruct A as (MR0 & ACEILh & SPKH);
                         pose proof ACEILh as ACEILn; unfold alloc_ceiling, sp_window_lo, stack_max_size in ACEILn
                  end.

  Definition fmt_fp_post (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Ft fc' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 ret) a1 a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ munch Wfp m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ frm0 fc'
      /\ stk asegs m' (bv_unsigned sp - 4640) (bv_unsigned sp)
      /\ wfile m' Fp fl0 j1 j2 lbfw B (zb o1) (skipn (length o1 - length o0) junk0)
      /\ ssp_cells m' canary
      /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k).

  (* [comment removed for export] *)
  Definition hi_cells (pad256 : list byte) : list cell :=
    [CB 256 pad256; C8 canary; C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra].

  (* [comment removed for export] *)
  Definition finv (m : word -> option byte) (pad256 : list byte) : Prop :=
    mem_inv asegs m /\ munch Wfp m0 m /\ wmono asegs m0 m
    /\ rw_cells asegs m (bv_unsigned sp + -368) (hi_cells pad256)
    /\ stk asegs m (bv_unsigned sp - 4640) (bv_unsigned sp + -1056)
    /\ rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells asegs m ssp_guard [C8 canary].
  Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
    let ST := fresh "ST" in let GOT := fresh "GOT" in let SSP := fresh "SSP" in
    destruct H as (MI & MU & WM & FRhi & ST & GOT & SSP); unfold Wfp in MU; unfold hi_cells in FRhi; unfold got_ssp, ssp_guard in GOT, SSP.
  Ltac mk_finv := unfold finv, Wfp, hi_cells, got_ssp, ssp_guard;
    split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | idtac]|]; split; hyp.

  Ltac dest_wfile H := let FC := fresh "FC" in let BUF := fresh "BUF" in let FLG := fresh "FLG" in let LBF := fresh "LBF" in
    let Bpos := fresh "Bpos" in let Bhi := fresh "Bhi" in let SEPfb := fresh "SEPfb" in
    destruct H as (FC & BUF & FLG & LBF & Bpos & Bhi & SEPfb); unfold FILE_cells in FC; idtac; idtac .
  Ltac mk_wfile := unfold wfile, FILE_cells; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [lia|]; split; lia.

  (* [comment removed for export] *)
  Definition midv (K : midK) (m : word -> option byte) (fc : bv 32) (e2m : Z) : Prop :=
    finv m (K_pad K) /\ frm0 fc /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get (K_Ft K) k = reg_get F k)
    /\ rw_cells asegs m (bv_unsigned sp + -544)
         [C8 (Z_to_bv 64 0); CB 40 (K_jk40 K); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t); CB 8 (K_jk8 K); C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 6279824);
          C8 (Z_to_bv 64 (K_plz K)); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)]
    /\ rw_cells asegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 e2m); CB 3 (K_jk3 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ K_plz K = Z.b2z (K_pl K =? 0)%Z /\ K_pfx K = (79882 + K_prefix K)%Z
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
  (* [comment removed for export] *)
  Ltac dest_midv2 H :=
    let FI := fresh "FI" in let FRM := fresh "FRM" in let HFt := fresh "HFt" in let FRs := fresh "FRs" in let E2 := fresh "E2" in
    let EB := fresh "EB" in let BF := fresh "BF" in let WF := fresh "WF" in
    let Hpre := fresh "Hpre" in let Hpl := fresh "Hpl" in let Hplz := fresh "Hplz" in let Hpfx := fresh "Hpfx" in let Hp1 := fresh "Hp1" in
    destruct H as (FI & FRM & HFt & FRs & E2 & EB & BF & WF & Hpre & Hpl & Hplz & Hpfx & Hp1);
    cbn [K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft] in *;
    dest_finv FI.
  (* [comment removed for export] *)
  Definition midw (K : midK) (m : word -> option byte) (fc : bv 32) (e2m : Z) : Prop :=
    finv m (K_pad K) /\ frm0 fc /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get (K_Ft K) k = reg_get F k)
    /\ rw_cells asegs m (bv_unsigned sp + -544)
         [C8 (Z_to_bv 64 0); CB 40 (K_jk40 K); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t); CB 8 (K_jk8 K); C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 6279824);
          C8 (Z_to_bv 64 (K_plz K)); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)]
    /\ rw_cells asegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 e2m); CB 3 (K_jk3 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ (0 <= K_plz K < 2^64)%Z /\ K_pfx K = (79882 + K_prefix K)%Z
    /\ (0 <= K_p1 K < 2^20)%Z.
  Lemma midv_w : forall K m fc e2m, midv K m fc e2m -> midw K m fc e2m.
  Proof using Hfl Ht J256.
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

  (* [comment removed for export] *)
  Definition midq (K : midK) (cs5 : list cell) (z456 : Z) (m : word -> option byte) (fc : bv 32) : Prop :=
    finv m (K_pad K) /\ frm0 fc /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get (K_Ft K) k = reg_get F k)
    /\ rw_cells asegs m (bv_unsigned sp + -544)
         ([C8 (Z_to_bv 64 0)] ++ cs5 ++ [C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t); C8 (Z_to_bv 64 (K_p1 K)); C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 6279824);
          C8 (Z_to_bv 64 z456); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)])
    /\ rw_cells asegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 0); CB 3 (K_jk3 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ (0 <= z456 < 2^64)%Z /\ K_pfx K = (79882 + K_prefix K)%Z
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
  (* [comment removed for export] *)
  Definition midq_K (K : midK) (cs5 : list cell) (z456 : Z) : midK :=
    MidK (K_pad K) (cells_bytes cs5) (le8 (Z_to_bv 64 (K_p1 K))) (K_jk3 K) (K_jk12 K) (K_jk37 K) (K_p1 K) (K_prefix K) (K_pl K) z456 (K_pfx K) (K_Ft K).
  Lemma midq_w : forall K cs5 z456 m fc, midq K cs5 z456 m fc -> cells_size cs5 = 40%nat -> midw (midq_K K cs5 z456) m fc 0%Z.
  Proof using .
    intros K cs5 z456 m fc H Hsz. destruct H as (FI & FRM & HFt & FRs & E2 & EB & BF & WF & Hpre & Hpl & Hplz & Hpfx & Hp1).
    unfold midw, midq_K. cbn [K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft].
    split; [exact FI|]. split; [exact FRM|]. split; [exact HFt|]. split.
    { apply (rw_cells_merge asegs m _ [C8 (Z_to_bv 64 0)] cs5) in FRs. rewrite Hsz in FRs.
      apply (rw_cells_merge asegs m _ [C8 (Z_to_bv 64 0); CB 40 (cells_bytes cs5); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t)] [C8 (Z_to_bv 64 (K_p1 K))]
               [C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 6279824); C8 (Z_to_bv 64 z456); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)]) in FRs.
      cbn [cells_size csize cells_bytes cbytes app Nat.add] in FRs. rewrite app_nil_r in FRs. exact FRs. }
    split; [exact E2|]. split; [exact EB|]. split; [exact BF|]. split; [exact WF|].
    split; [exact Hpre|]. split; [exact Hpl|]. split; [exact Hplz|]. split; [exact Hpfx|]. exact Hp1.
  Qed.

  (* [comment removed for export] *)
  Definition emw (K : midK) (estrp ppl fl2 a8v v440 : Z) (oc : list Z) (m : word -> option byte) (fc : bv 32) : Prop :=
    finv m (K_pad K) /\ frm0 fc /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get (K_Ft K) k = reg_get F k)
    /\ rw_cells asegs m (bv_unsigned sp + -544)
         [C8 (Z_to_bv 64 0); CB 40 (K_jk40 K); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 estrp); C8 (Z_to_bv 64 ppl); C8 (Z_to_bv 64 fl2); C8 (Z_to_bv 64 6279824);
          C8 (Z_to_bv 64 a8v); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 v440); C8 (Z_to_bv 64 Fp)]
    /\ rw_cells asegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 0); CB 3 (K_jk3 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb oc) (skipn (length oc - length o0) junk0)
    /\ (length o0 <= length oc)%nat
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ K_pfx K = (79882 + K_prefix K)%Z /\ (0 <= K_p1 K < 2^20)%Z.
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
  Ltac alia ::= first [ solve [clear_fat; clear_logic; unfold alloc_ceiling, sp_window_lo, stack_max_size, KHIGHMEM_END, KHIGHMEM_BEG; lia]
                    | unfold alloc_ceiling, sp_window_lo, stack_max_size, KHIGHMEM_END, KHIGHMEM_BEG; lia ].

  Notation POST := (fmt_fp_post m0).
  Notation SPv := (Z_to_bv 64 (bv_unsigned sp + -1056)).
  Notation S0v := (Z_to_bv 64 (bv_unsigned sp)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis L_bc4 :
    forall m (x1 x5 x6 x7 x10 x13 x14 x15 x16 x19 x26 x31 : word) fc K
      (ws : list word) (big : list Z) (lo a r rp z zm e p2 t2 a8 palt l estr estrp : Z) (ebuf0 : list Z),
    midw K m fc 0%Z ->
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
    ffp_H4 o0 w fl t2 p2 (K_prefix K) (K_pl K) big a r z l ebuf0 estr = Some (o1, ret) ->
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10 (Z_to_bv 64 (Z.lxor (K_pl K) 2147483647)) (Z_to_bv 64 l) x13 x14 x15 x16
               (Z_to_bv 64 estrp)
               (Z_to_bv 64 p2) x19 (Z_to_bv 64 6279824) (Z_to_bv 64 (K_pl K)) (Z_to_bv 64 rp)
               (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) (Z_to_bv 64 (Z.land t2 18446744073709551583)) (Z_to_bv 64 (Z.lor p2 a8)) x26 (Z_to_bv 64 p2)
               (Z_to_bv 64 fl) (Z_to_bv 64 t2) (Z_to_bv 64 a8) x31)
          (K_Ft K) (Z_to_bv 64 0x9693c) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Lemma L_bb4 : forall m (x1 x5 x6 x7 x10 x14 x15 x16 x19 x26 x31 : word) fc K
      (ws : list word) (big : list Z) (lo a r rp z zm e p2 t2 a8 palt l1 l2 estr estrp : Z) (ebuf0 : list Z),
    midw K m fc 0%Z ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (lo <= i < zm)%Z -> znth big i = wval ws i) ->
    (forall i, (zm <= i)%Z -> znth big i = 0%Z) ->
    (0 <= lo <= a)%Z -> (lo <= r)%Z -> (a <= zm)%Z -> (0 <= z <= zm)%Z -> (zm <= 128)%Z -> (r < zm)%Z -> (r = 0 \/ r = 122)%Z -> rp = (bv_unsigned sp + -1056 + 4 * r)%Z ->
    (forall i, (0 <= znth big i < 1000000000)%Z) ->
    (-2^20 <= e < 2^20)%Z -> (0 <= p2 < 2^21)%Z -> (0 <= t2 < 256)%Z ->
    (a < z -> znth big (z - 1) <> 0)%Z -> (Z.lor t2 32 <> CHR_f -> z <= a -> a = r)%Z ->
    (0 <= a8 <= 8)%Z -> (a8 = 0%Z <-> Z.land fl 8 = 0%Z) ->
    palt = (if negb (p2 =? 0) || negb (Z.land fl ALT_FORM =? 0) then 1 else 0)%Z ->
    l1 = (1 + p2 + palt)%Z -> (0 <= l2 < 2^21)%Z -> (0 <= estrp < 2^64)%Z -> length ebuf0 = 12%nat ->
    (Z.lor t2 32 <> CHR_f -> (1 <= estr <= 10)%Z /\ estrp = (bv_unsigned sp + -417 + estr)%Z /\
       forall k, (estr <= k < 12)%Z -> nth_error (K_jk12 K) (Z.to_nat k) = Some (Z_to_bv 8 (znth ebuf0 k))) ->
    ffp_H4 o0 w fl t2 p2 (K_prefix K) (K_pl K) big a r z (l1 + l2) ebuf0 estr = Some (o1, ret) ->
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10 (Z_to_bv 64 2147483647) (Z_to_bv 64 l1) (Z_to_bv 64 l2) x14 x15 x16
               (Z_to_bv 64 estrp)
               (Z_to_bv 64 p2) x19 (Z_to_bv 64 6279824) (Z_to_bv 64 e) (Z_to_bv 64 rp)
               (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) (Z_to_bv 64 (Z.land t2 18446744073709551583)) (Z_to_bv 64 (Z.lor p2 a8)) x26 (Z_to_bv 64 p2)
               (Z_to_bv 64 fl) (Z_to_bv 64 t2) (Z_to_bv 64 a8) x31)
          (K_Ft K) (Z_to_bv 64 0x9692c) fc None m (seg_rom asegs)).
  Proof using J256 L_bc4.
    intros until ebuf0; intros MV BIG LW LB REL ZERO Hlo Hlor Ha Hz Hzm Hrzm Hr Hrp ALLW He Hp2 Ht2 Hnz Haz Ha8 Ha8iff Hpalt Hl1 Hl2 Hep Leb EBR HH.
    destruct K as [pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft]. cbn [K_p1 K_prefix K_pl K_Ft K_jk12] in HH, EBR |- *.
    dest_midw2 MV. prune. pose proof (zr_word sp : (0 <= bv_unsigned sp < 2^64)%Z) as Rsp.
    assert (Rfw : (0 <= Fp < 2^64)%Z) by apply (zr_word fw).
    assert (Rpalt : (0 <= palt <= 1)%Z) by (rewrite Hpalt; destruct (_ || _); lia).
    zs. replace (bv_swrap 32 (l2 + l1)) with (l1 + l2)%Z by (rewrite swrap32_eq; mlia).
    zs. zs.
    assert (Rx : (Z.lxor pl 2147483647 = 2147483647 - pl)%Z).
    { assert (pl = 0 \/ pl = 1)%Z as [-> | ->] by lia; reflexivity. }
    zs. if_cases Kov; zify_cond Kov; rewrite ?signed_of_Z in Kov by lia; [exfalso; lia|].
    eapply L_bc4 with (K := MidK pad jk40 jk8 jk3 jk12 jk37 p1 prefix pl plz pfx Ft) (zm := zm) (lo := lo) (r := r) (estr := estr) (palt := palt);
      [ mk_midw | exact BIG | exact LW | exact LB | exact REL | exact ZERO | dlia | dlia | dlia | dlia | dlia | dlia | exact Hr | exact Hrp | exact ALLW
      | exact He | exact Hp2 | exact Ht2 | exact Hnz | exact Haz | exact Ha8 | exact Ha8iff | exact Hpalt | dlia | exact Hep | exact Leb | exact EBR | exact HH ].
  Qed.

End FmtFp.


End CeilWrap.
End F_fmt_fp_tbb4.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_defs CJ_iface AShadow ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import ICPT_musl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import SFModel Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim SoftFloat FmtFp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import F_memset F_memcpy F_fwritex F_pad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require FmtFp_facts2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.FmtFp_facts2.F_frexpl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import F_divtf3_main.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require FmtFp_facts2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.FmtFp_facts2.FmtFp_facts.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import FmtFp_facts2 F_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_frexpl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_frexpl.F_fmt_fp_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_fmt_fp_pre2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_fmt_fp_pre2.F_fmt_fp_pre.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import F_fmt_fp_pre2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_fmt_fp_pre4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_fmt_fp_pre4.F_fmt_fp_pre3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import F_fmt_fp_pre4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require FmtFp_splitR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import FmtFp_splitR.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require FmtFp_splitR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_splitH.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_fmt_fp_te1 F_fmt_fp_te3 F_fmt_fp_te4 F_fmt_fp_tf1 F_fmt_fp_tf3 F_fmt_fp_tf5 F_fmt_fp_tbc4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_fmt_fp_taec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_fmt_fp_t9a8.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_fmt_fp_r3 F_fmt_fp_r2 F_fmt_fp_r1 F_fmt_fp_rd.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_fmt_fp_dn F_fmt_fp_up F_fmt_fp_dig F_fmt_fp_c58 F_fmt_fp_c00 F_fmt_fp_entry.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


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
  Hypothesis GLO : (6280392 <= bv_unsigned sp - 4640)%Z.   (* [comment removed for export] *)
  Hypothesis AF : (bv_unsigned sp <= Fp)%Z.
  Hypothesis AB : (bv_unsigned sp <= B)%Z.
  (* [comment removed for export] *)
  Hypothesis AX : fmtfp_ax m0 (bv_unsigned sp).
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
  Proof.
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
  Proof.
    intros p1 r big a z e2' (s0 & (bg & zz & e2 & (y & y' & (y2 & e0 & (y1 & fr & HY & HFR & Hy2) & HD) & Hr & HDG) & HU) & HDN).
    cbv zeta in HD. destruct HD as (Hy & He2 & Hp1). subst y2. subst p1 r.
    exact (WB0 y1 fr e0 y e2 bg zz y' s0 big a z e2' HY HFR (conj Hy He2) HDG HU HDN).
  Qed.

  Lemma provG_run : forall p1 r big a z e2, prov_G p1 r (big, a, z, e2) -> run_to_dn yv fl p t p1 r big a z.
  Proof.
    intros p1 r big a z e2' (s0 & (bg & zz & e2 & (y & y' & (y2 & e0 & (y1 & fr & HY & HFR & Hy2) & HD) & Hr & HDG) & HU) & HDN).
    cbv zeta in HD. destruct HD as (Hy & He2 & Hp1). subst y2.
    exists y1, fr, e0, y, e2, bg, zz, y', s0, e2'.
    split; [exact HY|]. split; [exact HFR|]. split; [split; [exact Hy | exact He2]|]. split; [exact Hp1|]. split; [exact Hr|].
    subst r. split; [exact HDG|]. split; [exact HU|]. subst p1. exact HDN.
  Qed.
  Lemma WBA : forall p1 r big a z e2, prov_G p1 r (big, a, z, e2) -> forall i, (0 <= znth big i < 1000000000)%Z.
  Proof. intros p1 r big a z e2 PG. exact (WBA0 _ _ _ _ _ (provG_run _ _ _ _ _ _ PG)). Qed.
  Lemma CAR : forall p1 prefix pl r big a z e, prov_R p1 prefix pl r big a z e -> (0 <= a)%Z.
  Proof.
    intros p1 prefix pl r big a z e (big0 & a0 & z0 & e2' & e0 & PG & He & HR).
    exact (CAR0 _ _ _ _ _ (provG_run _ _ _ _ _ _ PG) _ _ _ _ _ _ _ He HR).
  Qed.
  Lemma AZR : forall p1 prefix pl r big a z e zS, prov_R p1 prefix pl r big a z e ->
    fmt_fp_strip BIG_FUEL big a z = Some zS -> Z.lor t 32 <> CHR_f -> (zS <= a)%Z -> a = r.
  Proof.
    intros p1 prefix pl r big a z e zS (big0 & a0 & z0 & e2' & e0 & PG & He & HR) HS Htf Hza.
    exact (AZR0 _ _ _ _ _ (provG_run _ _ _ _ _ _ PG) _ _ _ _ _ _ _ _ He HR HS Htf Hza).
  Qed.

  Lemma BLA : forall p1 r big a z e2, prov_G p1 r (big, a, z, e2) -> forall k, (0 <= k < a)%Z -> znth big k = 0%Z.
  Proof. intros p1 r big a z e2 PG. exact (BLA0 _ _ _ _ _ (provG_run _ _ _ _ _ _ PG)). Qed.

  Lemma DNB : forall p1 r s, prov_F p1 r s -> dn_good p1 t r s.
  Proof.
    intros p1 r s (big & z & e2 & (y & y' & (y2 & e0 & (y1 & fr & HY & HFR & Hy2) & HD) & Hr & HDG) & HU).
    cbv zeta in HD. destruct HD as (Hy & He2 & Hp1). subst y2. subst p1 r.
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
  (* [comment removed for export] *)
  Lemma MR_now : forall m, munch Wfp m0 m -> MRT m.
  Proof using AX AF AB.
    intros m MU.
    try clear SPLO; try clear SPHI; try clear GLO; try clear Hw; try clear Hp; try clear Hfl; try clear Ht; try clear Hta;
    try clear ROOM; try clear J256; try clear HM; try clear YN0; try clear YN1; try clear DIGB; try clear E2B; try clear DNB0;
    try clear WBA0; try clear CAR0; try clear AZR0; try clear BLA0.
    destruct AX as (MR0 & ACEILh & SPKH). eapply MRT_munch; [exact MR0| exact MU|]. unfold Wfp, Fp, usp in *.
    apply Forall_cons; [apply mrt_iv_ok_stack; lia|].
    apply Forall_cons; [apply mrt_iv_ok_stack; lia|].
    apply Forall_cons; [apply mrt_iv_ok_stack; lia| apply Forall_nil].
  Qed.
  Ltac mr_now := match goal with H : munch _ m0 ?mm |- MRT ?mm' => exact (MR_now _ H) end.
  Ltac alia := unfold alloc_ceiling, sp_window_lo, stack_max_size, KHIGHMEM_END, KHIGHMEM_BEG; lia.
  Ltac lstac := unfold lit_or_stack, A_PFX_TBL, A_FPFX_STR, A_DOT_STR; alia.
  Ltac ax_open := lazymatch goal with
                  | _ : MRT m0 |- _ => idtac
                  | _ => let A := fresh "AXc" in pose proof AX as A; destruct A as (MR0 & ACEILh & SPKH);
                         pose proof ACEILh as ACEILn; unfold alloc_ceiling, sp_window_lo, stack_max_size in ACEILn
                  end.

  Definition fmt_fp_post (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Ft fc' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 ret) a1 a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ munch Wfp m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ frm0 fc'
      /\ stk asegs m' (bv_unsigned sp - 4640) (bv_unsigned sp)
      /\ wfile m' Fp fl0 j1 j2 lbfw B (zb o1) (skipn (length o1 - length o0) junk0)
      /\ ssp_cells m' canary
      /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k).

  (* [comment removed for export] *)
  Definition hi_cells (pad256 : list byte) : list cell :=
    [CB 256 pad256; C8 canary; C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra].

  (* [comment removed for export] *)
  Definition finv (m : word -> option byte) (pad256 : list byte) : Prop :=
    mem_inv asegs m /\ munch Wfp m0 m /\ wmono asegs m0 m
    /\ rw_cells asegs m (bv_unsigned sp + -368) (hi_cells pad256)
    /\ stk asegs m (bv_unsigned sp - 4640) (bv_unsigned sp + -1056)
    /\ rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells asegs m ssp_guard [C8 canary].
  Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
    let ST := fresh "ST" in let GOT := fresh "GOT" in let SSP := fresh "SSP" in
    destruct H as (MI & MU & WM & FRhi & ST & GOT & SSP); unfold Wfp in MU; unfold hi_cells in FRhi; unfold got_ssp, ssp_guard in GOT, SSP.
  Ltac mk_finv := unfold finv, Wfp, hi_cells, got_ssp, ssp_guard;
    split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | idtac]|]; split; hyp.

  Ltac dest_wfile H := let FC := fresh "FC" in let BUF := fresh "BUF" in let FLG := fresh "FLG" in let LBF := fresh "LBF" in
    let Bpos := fresh "Bpos" in let Bhi := fresh "Bhi" in let SEPfb := fresh "SEPfb" in
    destruct H as (FC & BUF & FLG & LBF & Bpos & Bhi & SEPfb); unfold FILE_cells in FC; idtac; idtac .
  Ltac mk_wfile := unfold wfile, FILE_cells; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [lia|]; split; lia.

  (* [comment removed for export] *)
  Definition midv (K : midK) (m : word -> option byte) (fc : bv 32) (e2m : Z) : Prop :=
    finv m (K_pad K) /\ frm0 fc /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get (K_Ft K) k = reg_get F k)
    /\ rw_cells asegs m (bv_unsigned sp + -544)
         [C8 (Z_to_bv 64 0); CB 40 (K_jk40 K); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t); CB 8 (K_jk8 K); C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 6279824);
          C8 (Z_to_bv 64 (K_plz K)); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)]
    /\ rw_cells asegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 e2m); CB 3 (K_jk3 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ K_plz K = Z.b2z (K_pl K =? 0)%Z /\ K_pfx K = (79882 + K_prefix K)%Z
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
  (* [comment removed for export] *)
  Ltac dest_midv2 H :=
    let FI := fresh "FI" in let FRM := fresh "FRM" in let HFt := fresh "HFt" in let FRs := fresh "FRs" in let E2 := fresh "E2" in
    let EB := fresh "EB" in let BF := fresh "BF" in let WF := fresh "WF" in
    let Hpre := fresh "Hpre" in let Hpl := fresh "Hpl" in let Hplz := fresh "Hplz" in let Hpfx := fresh "Hpfx" in let Hp1 := fresh "Hp1" in
    destruct H as (FI & FRM & HFt & FRs & E2 & EB & BF & WF & Hpre & Hpl & Hplz & Hpfx & Hp1);
    cbn [K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft] in *;
    dest_finv FI.
  (* [comment removed for export] *)
  Definition midw (K : midK) (m : word -> option byte) (fc : bv 32) (e2m : Z) : Prop :=
    finv m (K_pad K) /\ frm0 fc /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get (K_Ft K) k = reg_get F k)
    /\ rw_cells asegs m (bv_unsigned sp + -544)
         [C8 (Z_to_bv 64 0); CB 40 (K_jk40 K); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t); CB 8 (K_jk8 K); C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 6279824);
          C8 (Z_to_bv 64 (K_plz K)); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)]
    /\ rw_cells asegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 e2m); CB 3 (K_jk3 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ (0 <= K_plz K < 2^64)%Z /\ K_pfx K = (79882 + K_prefix K)%Z
    /\ (0 <= K_p1 K < 2^20)%Z.
  Lemma midv_w : forall K m fc e2m, midv K m fc e2m -> midw K m fc e2m.
  Proof.
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

  (* [comment removed for export] *)
  Definition midq (K : midK) (cs5 : list cell) (z456 : Z) (m : word -> option byte) (fc : bv 32) : Prop :=
    finv m (K_pad K) /\ frm0 fc /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get (K_Ft K) k = reg_get F k)
    /\ rw_cells asegs m (bv_unsigned sp + -544)
         ([C8 (Z_to_bv 64 0)] ++ cs5 ++ [C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t); C8 (Z_to_bv 64 (K_p1 K)); C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 6279824);
          C8 (Z_to_bv 64 z456); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)])
    /\ rw_cells asegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 0); CB 3 (K_jk3 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ (0 <= z456 < 2^64)%Z /\ K_pfx K = (79882 + K_prefix K)%Z
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
  (* [comment removed for export] *)
  Definition midq_K (K : midK) (cs5 : list cell) (z456 : Z) : midK :=
    MidK (K_pad K) (cells_bytes cs5) (le8 (Z_to_bv 64 (K_p1 K))) (K_jk3 K) (K_jk12 K) (K_jk37 K) (K_p1 K) (K_prefix K) (K_pl K) z456 (K_pfx K) (K_Ft K).
  Lemma midq_w : forall K cs5 z456 m fc, midq K cs5 z456 m fc -> cells_size cs5 = 40%nat -> midw (midq_K K cs5 z456) m fc 0%Z.
  Proof.
    intros K cs5 z456 m fc H Hsz. destruct H as (FI & FRM & HFt & FRs & E2 & EB & BF & WF & Hpre & Hpl & Hplz & Hpfx & Hp1).
    unfold midw, midq_K. cbn [K_pad K_jk40 K_jk8 K_jk3 K_jk12 K_jk37 K_p1 K_prefix K_pl K_plz K_pfx K_Ft].
    split; [exact FI|]. split; [exact FRM|]. split; [exact HFt|]. split.
    { apply (rw_cells_merge asegs m _ [C8 (Z_to_bv 64 0)] cs5) in FRs. rewrite Hsz in FRs.
      apply (rw_cells_merge asegs m _ [C8 (Z_to_bv 64 0); CB 40 (cells_bytes cs5); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t)] [C8 (Z_to_bv 64 (K_p1 K))]
               [C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 6279824); C8 (Z_to_bv 64 z456); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 (K_pl K)); C8 (Z_to_bv 64 Fp)]) in FRs.
      cbn [cells_size csize cells_bytes cbytes app Nat.add] in FRs. rewrite app_nil_r in FRs. exact FRs. }
    split; [exact E2|]. split; [exact EB|]. split; [exact BF|]. split; [exact WF|].
    split; [exact Hpre|]. split; [exact Hpl|]. split; [exact Hplz|]. split; [exact Hpfx|]. exact Hp1.
  Qed.

  (* [comment removed for export] *)
  Definition emw (K : midK) (estrp ppl fl2 a8v v440 : Z) (oc : list Z) (m : word -> option byte) (fc : bv 32) : Prop :=
    finv m (K_pad K) /\ frm0 fc /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get (K_Ft K) k = reg_get F k)
    /\ rw_cells asegs m (bv_unsigned sp + -544)
         [C8 (Z_to_bv 64 0); CB 40 (K_jk40 K); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 estrp); C8 (Z_to_bv 64 ppl); C8 (Z_to_bv 64 fl2); C8 (Z_to_bv 64 6279824);
          C8 (Z_to_bv 64 a8v); C8 (Z_to_bv 64 (K_pfx K)); C8 (Z_to_bv 64 v440); C8 (Z_to_bv 64 Fp)]
    /\ rw_cells asegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 0); CB 3 (K_jk3 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -417) [CB 12 (K_jk12 K)]
    /\ rw_cells asegs m (bv_unsigned sp + -405) [CB 37 (K_jk37 K)]
    /\ wfile m Fp fl0 j1 j2 lbfw B (zb oc) (skipn (length oc - length o0) junk0)
    /\ (length o0 <= length oc)%nat
    /\ (0 <= K_prefix K <= 6)%Z /\ (0 <= K_pl K <= 1)%Z /\ K_pfx K = (79882 + K_prefix K)%Z /\ (0 <= K_p1 K < 2^20)%Z.
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
  Ltac alia ::= first [ solve [clear_fat; clear_logic; unfold alloc_ceiling, sp_window_lo, stack_max_size, KHIGHMEM_END, KHIGHMEM_BEG; lia]
                    | unfold alloc_ceiling, sp_window_lo, stack_max_size, KHIGHMEM_END, KHIGHMEM_BEG; lia ].

  Notation POST := (fmt_fp_post m0).
  Notation SPv := (Z_to_bv 64 (bv_unsigned sp + -1056)).
  Notation S0v := (Z_to_bv 64 (bv_unsigned sp)).

  (* [comment removed for export] *)
  Lemma L_100 : forall m (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) fc K
      (ws : list word) (estrp a8v v440 l : Z) (oc : list Z),
    emw K estrp (K_pl K + l) (Z.land fl 73728) a8v v440 oc m fc ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    (1 <= l < 2^24)%Z ->
    ffp_H6 oc w fl (K_pl K) l = Some (o1, ret) ->
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 (Z_to_bv 64 w) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (K_Ft K) (Z_to_bv 64 0x96e78) fc None m (seg_rom asegs)).
  Proof. eapply F_fmt_fp_t100.L_100; eassumption. Qed.

  Lemma L_efmtu9e : forall (k : nat) Q m (x1 x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x18 x20 x21 x23 x26 x27 x28 x29 x30 x31 : word) fc K
      (estrp ppl fl2 a8v v440 : Z) (oc : list Z) (ws : list word) (y s : Z) (b : list Z) (y' s' : Z) (b' : list Z),
    emw K estrp ppl fl2 a8v v440 oc m fc ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length (K_jk37 K) = 37%nat ->
    (10 <= y)%Z -> (y < 10 ^ s)%Z -> (s <= 9)%Z -> (y < 2^32)%Z ->
    length b = 37%nat ->
    (forall i, (s <= i < 9)%Z -> nth_error (K_jk37 K) (Z.to_nat i) = Some (Z_to_bv 8 (znth b i))) ->
    fmt_u_loop k (y, s, b) = Some (y', s', b') ->
    (forall m1 bf1 q sq bq kq (x12' x13' x14' : word),
       emw (K_set37 K bf1) estrp ppl fl2 a8v v440 oc m1 fc -> u32arr asegs m1 (bv_unsigned sp + -1056) ws -> length bf1 = 37%nat ->
       (1 <= q <= 9)%Z -> (1 <= sq < s)%Z -> length bq = 37%nat ->
       (forall i, (sq <= i < 9)%Z -> nth_error bf1 (Z.to_nat i) = Some (Z_to_bv 8 (znth bq i))) ->
       fmt_u_loop kq (q, sq, bq) = Some (y', s', b') ->
       evt asegs Q
         (MS (mkR x1 SPv gp tp x5 x6 x7 sp x9 (Z_to_bv 64 q) (Z_to_bv 64 (sq - 1)) x12' x13' x14' x15 x16 x17
                  x18 (Z_to_bv 64 14757395258967641293) x20 x21 (Z_to_bv 64 10) x23 (Z_to_bv 64 (bv_unsigned sp + -405)) (Z_to_bv 64 99) x26 x27 x28 x29 x30 x31)
             (K_Ft K) (Z_to_bv 64 0x96c0c) fc None m1 (seg_rom asegs))) ->
    evt asegs Q
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp x9 (Z_to_bv 64 y) (Z_to_bv 64 (s - 1)) x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 14757395258967641293) x20 x21 (Z_to_bv 64 10) x23 (Z_to_bv 64 (bv_unsigned sp + -405)) (Z_to_bv 64 99) x26 x27 x28 x29 x30 x31)
          (K_Ft K) (Z_to_bv 64 0x96be4) fc None m (seg_rom asegs)).
  Proof. eapply F_fmt_fp_te1.L_efmtu9e; eassumption. Qed.

  Lemma L_ezfill : forall (k : nat) Q m (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word) fc K
      (estrp ppl fl2 a8v v440 : Z) (oc : list Z) (ws : list word) (s : Z) (b b' : list Z),
    emw K estrp ppl fl2 a8v v440 oc m fc ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length (K_jk37 K) = 37%nat -> (1 <= s <= 9)%Z -> (Z.to_nat s <= k)%nat ->
    length b = 37%nat -> length b' = 37%nat ->
    (forall i, (s <= i < 9)%Z -> nth_error (K_jk37 K) (Z.to_nat i) = Some (Z_to_bv 8 (znth b i))) ->
    (forall i, (0 <= i < s)%Z -> znth b' i = CHR_0) -> (forall i, (s <= i)%Z -> znth b' i = znth b i) ->
    (forall m1 bf1,
       emw (K_set37 K bf1) estrp ppl fl2 a8v v440 oc m1 fc -> u32arr asegs m1 (bv_unsigned sp + -1056) ws -> length bf1 = 37%nat ->
       (forall i, (0 <= i < 9)%Z -> nth_error bf1 (Z.to_nat i) = Some (Z_to_bv 8 (znth b' i))) ->
       evt asegs Q
         (MS (mkR x1 SPv gp tp x5 x6 x7 sp x9 (Z_to_bv 64 (bv_unsigned sp + -405)) x11 x12 x13 x14 x15 x16 x17
                  x18 x19 (Z_to_bv 64 48) (Z_to_bv 64 (bv_unsigned sp + -405)) x22 x23 (Z_to_bv 64 (bv_unsigned sp + -405)) x25 x26 x27 x28 x29 x30 x31)
             (K_Ft K) (Z_to_bv 64 0x96cd4) fc None m1 (seg_rom asegs))) ->
    evt asegs Q
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 (Z_to_bv 64 48) (Z_to_bv 64 (bv_unsigned sp + -405 + s)) x22 x23 (Z_to_bv 64 (bv_unsigned sp + -405)) x25 x26 x27 x28 x29 x30 x31)
          (K_Ft K) (Z_to_bv 64 0x96c54) fc None m (seg_rom asegs)).
  Proof. eapply F_fmt_fp_te1.L_ezfill; eassumption. Qed.

  Lemma L_e5c : forall Q m (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x21 x28 x29 x30 x31 : word) fc K
      (estrp ppl fl2 a8v : Z) (od : list Z) (ws : list word) (a z d pr sf ap : Z) (bfin : list Z),
    emw K estrp ppl fl2 a8v 82595 od m fc ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length (K_jk37 K) = 37%nat ->
    (0 <= a <= d)%Z -> (d < z <= 128)%Z -> (0 <= pr < 2^21)%Z -> (0 <= sf <= 9)%Z -> length bfin = 37%nat ->
    (forall i, (sf <= i < 9)%Z -> nth_error (K_jk37 K) (Z.to_nat i) = Some (Z_to_bv 8 (znth bfin i))) ->
    (length od + Z.to_nat (Z.min (9 - sf) pr) <= length o1)%nat -> ap = (bv_unsigned sp + -405 + sf)%Z ->
    (forall m1 (x1' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word),
       emw K estrp ppl fl2 a8v 82595 (out od (zsub bfin sf (Z.min (9 - sf) pr))) m1 fc -> u32arr asegs m1 (bv_unsigned sp + -1056) ws ->
       (d + 1 < z)%Z -> (0 <= pr - (9 - sf))%Z ->
       evt asegs Q
         (MS (mkR x1' SPv gp tp x5' x6' x7' sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10' x11' x12' x13' x14' x15' x16' x17'
                  (Z_to_bv 64 (pr - (9 - sf))) (Z_to_bv 64 14757395258967641293) (Z_to_bv 64 48) x21 (Z_to_bv 64 10) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z))
                  (Z_to_bv 64 (bv_unsigned sp + -405)) (Z_to_bv 64 99) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * (d + 1))) (Z_to_bv 64 pr) x28' x29' x30' x31')
             (K_Ft K) (Z_to_bv 64 0x96bd8) fc None m1 (seg_rom asegs))) ->
    (forall m1 (x1' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word),
       emw K estrp ppl fl2 a8v 82595 (out od (zsub bfin sf (Z.min (9 - sf) pr))) m1 fc -> u32arr asegs m1 (bv_unsigned sp + -1056) ws ->
       ((d + 1 <? z) && (0 <=? pr - (9 - sf)) = false)%Z ->
       evt asegs Q
         (MS (mkR x1' SPv gp tp x5' x6' x7' sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10' x11' x12' x13' x14' x15' x16' x17'
                  (Z_to_bv 64 (pr - (9 - sf))) (Z_to_bv 64 14757395258967641293) (Z_to_bv 64 48) x21 (Z_to_bv 64 10) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z))
                  (Z_to_bv 64 (bv_unsigned sp + -405)) (Z_to_bv 64 99) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * (d + 1))) (Z_to_bv 64 pr) x28' x29' x30' x31')
             (K_Ft K) (Z_to_bv 64 0x96d14) fc None m1 (seg_rom asegs))) ->
    evt asegs Q
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) (Z_to_bv 64 ap) x11 x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 14757395258967641293) (Z_to_bv 64 48) x21 (Z_to_bv 64 10) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z))
               (Z_to_bv 64 (bv_unsigned sp + -405)) (Z_to_bv 64 99) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d)) (Z_to_bv 64 pr) x28 x29 x30 x31)
          (K_Ft K) (Z_to_bv 64 0x96cd4) fc None m (seg_rom asegs)).
  Proof. eapply F_fmt_fp_te1.L_e5c; eassumption. Qed.

  Lemma L_eloop : forall (k : nat) Q m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x27 x28 x29 x30 x31 : word) fc K
      (estrp ppl fl2 a8 : Z) (oc : list Z) (ws : list word) (big : list Z) (lo a z zm d pr d' p' : Z) (o' : list Z),
    emw K estrp ppl fl2 a8 82595 oc m fc ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (lo <= i < zm)%Z -> znth big i = wval ws i) ->
    (0 <= lo <= a)%Z -> (a <= d < z)%Z -> (z <= zm <= 128)%Z -> (0 <= pr < 2^21)%Z ->
    (forall i, (0 <= znth big i < 1000000000)%Z) ->
    (0 <= a8 <= 8)%Z -> (a8 = 0%Z <-> Z.land fl 8 = 0%Z) ->
    length (K_jk37 K) = 37%nat ->
    fmt_fp_eloop k big a z fl (d, pr, oc) = Some (d', p', o') ->
    (length o' <= length o1)%nat ->
    (forall m1 bf1 (x1' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x21' x26' x27' x28' x29' x30' x31' : word),
       emw (K_set37 K bf1) estrp ppl fl2 a8 82595 o' m1 fc -> u32arr asegs m1 (bv_unsigned sp + -1056) ws -> length bf1 = 37%nat ->
       (-9 <= p' <= pr)%Z ->
       evt asegs Q
         (MS (mkR x1' SPv gp tp x5' x6' x7' sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10' x11' x12' x13' x14' x15' x16' x17'
                  (Z_to_bv 64 p') (Z_to_bv 64 14757395258967641293) (Z_to_bv 64 48) x21' (Z_to_bv 64 10) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z))
                  (Z_to_bv 64 (bv_unsigned sp + -405)) (Z_to_bv 64 99) x26' x27' x28' x29' x30' x31')
             (K_Ft K) (Z_to_bv 64 0x96d14) fc None m1 (seg_rom asegs))) ->
    forall x1, evt asegs Q
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 pr) (Z_to_bv 64 14757395258967641293) (Z_to_bv 64 48) x21 (Z_to_bv 64 10) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z))
               (Z_to_bv 64 (bv_unsigned sp + -405)) (Z_to_bv 64 99) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d)) x27 x28 x29 x30 x31)
          (K_Ft K) (Z_to_bv 64 0x96bd8) fc None m (seg_rom asegs)).
  Proof. eapply F_fmt_fp_te3.L_eloop. all: first [ exact L_e5c | exact L_efmtu9e | exact L_ezfill | eassumption ]. Qed.

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
               (Z_to_bv 64 p2) x19 (Z_to_bv 64 6279824) (Z_to_bv 64 (K_pl K)) (Z_to_bv 64 rp)
               (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) (Z_to_bv 64 (Z.land t2 18446744073709551583)) (Z_to_bv 64 (Z.lor p2 a8)) (Z_to_bv 64 (K_pl K + l)) (Z_to_bv 64 p2)
               x28 x29 x30 x31)
          (K_Ft K) (Z_to_bv 64 0x96b9c) fc None m (seg_rom asegs)).
  Proof. eapply F_fmt_fp_te4.L_e24. all: first [ exact L_100 | exact L_eloop | eassumption ]. Qed.

  Lemma L_fint : forall (k : nat) Q m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x23 x25 x28 x29 x30 x31 : word) fc K
      (estrp ppl fl2 a8v v440 : Z) (oc : list Z) (ws : list word) (big : list Z) (lo a' r rp zm d d' : Z) (o' : list Z),
    emw K estrp ppl fl2 a8v v440 oc m fc ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (lo <= i < zm)%Z -> znth big i = wval ws i) ->
    (0 <= lo <= a')%Z -> (a' <= d <= r)%Z -> (r < zm <= 128)%Z -> rp = (bv_unsigned sp + -1056 + 4 * r)%Z ->
    (forall i, (0 <= znth big i < 1000000000)%Z) ->
    length (K_jk37 K) = 37%nat ->
    fmt_fp_fint k big a' r (d, oc) = Some (d', o') ->
    (length o' <= length o1)%nat ->
    (forall m1 bf1 (x1' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word),
       emw (K_set37 K bf1) estrp ppl fl2 a8v v440 o' m1 fc -> u32arr asegs m1 (bv_unsigned sp + -1056) ws -> length bf1 = 37%nat ->
       evt asegs Q
         (MS (mkR x1' SPv gp tp x5' x6' x7' sp (Z_to_bv 64 14757395258967641293) x10' x11' x12' x13' x14' x15' x16' x17'
                  x18 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d')) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a')) (Z_to_bv 64 10) (Z_to_bv 64 rp) x23
                  (Z_to_bv 64 (bv_unsigned sp + -405)) x25 (Z_to_bv 64 48) (Z_to_bv 64 99) x28' x29' x30' x31')
             (K_Ft K) (Z_to_bv 64 0x96d5c) fc None m1 (seg_rom asegs))) ->
    forall x1, evt asegs Q
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 14757395258967641293) x10 x11 x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d)) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a')) (Z_to_bv 64 10) (Z_to_bv 64 rp) x23
               (Z_to_bv 64 (bv_unsigned sp + -405)) x25 (Z_to_bv 64 48) (Z_to_bv 64 99) x28 x29 x30 x31)
          (K_Ft K) (Z_to_bv 64 0x96ae8) fc None m (seg_rom asegs)).
  Proof. eapply F_fmt_fp_tf1.L_fint; eassumption. Qed.

  Lemma L_ffrac : forall (k : nat) Q m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 : word) fc K
      (estrp ppl fl2 a8v v440 : Z) (oc : list Z) (ws : list word) (big : list Z) (lo z zm d pr d' p' : Z) (o' : list Z),
    emw K estrp ppl fl2 a8v v440 oc m fc ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (lo <= i < zm)%Z -> znth big i = wval ws i) ->
    (0 <= lo <= d)%Z -> (d < z)%Z -> (z <= zm <= 128)%Z -> (0 < pr < 2^21)%Z ->
    (forall i, (0 <= znth big i < 1000000000)%Z) ->
    length (K_jk37 K) = 37%nat ->
    fmt_fp_ffrac k big z (d, pr, oc) = Some (d', p', o') ->
    (length o' <= length o1)%nat ->
    (forall m1 bf1 (x1' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x25' x28' x29' x30' x31' : word),
       emw (K_set37 K bf1) estrp ppl fl2 a8v v440 o' m1 fc -> u32arr asegs m1 (bv_unsigned sp + -1056) ws -> length bf1 = 37%nat ->
       (d < d' <= z)%Z -> p' = (pr - 9 * (d' - d))%Z -> (-9 < p')%Z -> ((d' <? z) && (0 <? p') = false)%Z ->
       evt asegs Q
         (MS (mkR x1' SPv gp tp x5' x6' x7' sp (Z_to_bv 64 99) x10' x11' x12' x13' x14' x15' x16' x17'
                  (Z_to_bv 64 p') (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d')) (Z_to_bv 64 10) (Z_to_bv 64 (bv_unsigned sp + -405)) (Z_to_bv 64 48) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z))
                  (Z_to_bv 64 14757395258967641293) x25' (Z_to_bv 64 9) (Z_to_bv 64 Fp) x28' x29' x30' x31')
             (K_Ft K) (Z_to_bv 64 0x96e5c) fc None m1 (seg_rom asegs))) ->
    forall x1, evt asegs Q
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 99) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 pr) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d)) (Z_to_bv 64 10) (Z_to_bv 64 (bv_unsigned sp + -405)) (Z_to_bv 64 48) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z))
               (Z_to_bv 64 14757395258967641293) x25 (Z_to_bv 64 9) (Z_to_bv 64 Fp) x28 x29 x30 x31)
          (K_Ft K) (Z_to_bv 64 0x96db4) fc None m (seg_rom asegs)).
  Proof. eapply F_fmt_fp_tf3.L_ffrac; eassumption. Qed.

  Lemma L_d30 : forall m (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 : word) fc K
      (ws : list word) (big : list Z) (oc : list Z) (lo a r rp z zm e p2 t2 a8 palt l estr estrp : Z) (ebuf0 : list Z),
    emw K estrp (K_pl K + l) (Z.land fl 73728) a8 (K_pl K) oc m fc ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (lo <= i < zm)%Z -> znth big i = wval ws i) ->
    (forall i, (zm <= i)%Z -> znth big i = 0%Z) ->
    (0 <= lo <= a)%Z -> (lo <= r)%Z -> (a <= zm)%Z -> (0 <= z <= zm)%Z -> (zm <= 128)%Z -> (r < zm)%Z -> (r = 0 \/ r = 122)%Z -> rp = (bv_unsigned sp + -1056 + 4 * r)%Z ->
    (forall i, (0 <= znth big i < 1000000000)%Z) ->
    (-2^20 <= e < 2^20)%Z -> (0 <= p2 < 2^21)%Z -> (0 <= t2 < 256)%Z ->
    (a < z -> znth big (z - 1) <> 0)%Z ->
    (0 <= a8 <= 8)%Z -> (a8 = 0%Z <-> Z.land fl 8 = 0%Z) ->
    palt = (if negb (p2 =? 0) || negb (Z.land fl ALT_FORM =? 0) then 1 else 0)%Z ->
    (1 + p2 + palt <= l < 2^23)%Z -> (0 <= estrp < 2^64)%Z -> length ebuf0 = 12%nat ->
    (Z.lor t2 32 <> CHR_f -> (1 <= estr <= 10)%Z /\ estrp = (bv_unsigned sp + -417 + estr)%Z /\
       forall k, (estr <= k < 12)%Z -> nth_error (K_jk12 K) (Z.to_nat k) = Some (Z_to_bv 8 (znth ebuf0 k))) ->
    ffp_H5 oc w fl t2 p2 (K_pl K) big a r z l ebuf0 estr = Some (o1, ret) ->
    Z.lor t2 32 = CHR_f ->
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) (Z_to_bv 64 70) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 p2) x19 (Z_to_bv 64 6279824) (Z_to_bv 64 (K_pl K)) (Z_to_bv 64 rp)
               (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) (Z_to_bv 64 (Z.land t2 18446744073709551583)) (Z_to_bv 64 (Z.lor p2 a8)) (Z_to_bv 64 (K_pl K + l)) (Z_to_bv 64 p2)
               x28 x29 x30 x31)
          (K_Ft K) (Z_to_bv 64 0x96aa8) fc None m (seg_rom asegs)).
  Proof. eapply F_fmt_fp_tf5.L_d30. all: first [ exact L_100 | exact L_e24 | exact L_ffrac | exact L_fint | eassumption ]. Qed.

  Lemma L_bc4 : forall m (x1 x5 x6 x7 x10 x13 x14 x15 x16 x19 x26 x31 : word) fc K
      (ws : list word) (big : list Z) (lo a r rp z zm e p2 t2 a8 palt l estr estrp : Z) (ebuf0 : list Z),
    midw K m fc 0%Z ->
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
    ffp_H4 o0 w fl t2 p2 (K_prefix K) (K_pl K) big a r z l ebuf0 estr = Some (o1, ret) ->
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10 (Z_to_bv 64 (Z.lxor (K_pl K) 2147483647)) (Z_to_bv 64 l) x13 x14 x15 x16
               (Z_to_bv 64 estrp)
               (Z_to_bv 64 p2) x19 (Z_to_bv 64 6279824) (Z_to_bv 64 (K_pl K)) (Z_to_bv 64 rp)
               (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) (Z_to_bv 64 (Z.land t2 18446744073709551583)) (Z_to_bv 64 (Z.lor p2 a8)) x26 (Z_to_bv 64 p2)
               (Z_to_bv 64 fl) (Z_to_bv 64 t2) (Z_to_bv 64 a8) x31)
          (K_Ft K) (Z_to_bv 64 0x9693c) fc None m (seg_rom asegs)).
  Proof. eapply F_fmt_fp_tbc4.L_bc4. all: first [ exact L_d30 | exact L_e24 | eassumption ]. Qed.

  Lemma L_bb4 : forall m (x1 x5 x6 x7 x10 x14 x15 x16 x19 x26 x31 : word) fc K
      (ws : list word) (big : list Z) (lo a r rp z zm e p2 t2 a8 palt l1 l2 estr estrp : Z) (ebuf0 : list Z),
    midw K m fc 0%Z ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (lo <= i < zm)%Z -> znth big i = wval ws i) ->
    (forall i, (zm <= i)%Z -> znth big i = 0%Z) ->
    (0 <= lo <= a)%Z -> (lo <= r)%Z -> (a <= zm)%Z -> (0 <= z <= zm)%Z -> (zm <= 128)%Z -> (r < zm)%Z -> (r = 0 \/ r = 122)%Z -> rp = (bv_unsigned sp + -1056 + 4 * r)%Z ->
    (forall i, (0 <= znth big i < 1000000000)%Z) ->
    (-2^20 <= e < 2^20)%Z -> (0 <= p2 < 2^21)%Z -> (0 <= t2 < 256)%Z ->
    (a < z -> znth big (z - 1) <> 0)%Z -> (Z.lor t2 32 <> CHR_f -> z <= a -> a = r)%Z ->
    (0 <= a8 <= 8)%Z -> (a8 = 0%Z <-> Z.land fl 8 = 0%Z) ->
    palt = (if negb (p2 =? 0) || negb (Z.land fl ALT_FORM =? 0) then 1 else 0)%Z ->
    l1 = (1 + p2 + palt)%Z -> (0 <= l2 < 2^21)%Z -> (0 <= estrp < 2^64)%Z -> length ebuf0 = 12%nat ->
    (Z.lor t2 32 <> CHR_f -> (1 <= estr <= 10)%Z /\ estrp = (bv_unsigned sp + -417 + estr)%Z /\
       forall k, (estr <= k < 12)%Z -> nth_error (K_jk12 K) (Z.to_nat k) = Some (Z_to_bv 8 (znth ebuf0 k))) ->
    ffp_H4 o0 w fl t2 p2 (K_prefix K) (K_pl K) big a r z (l1 + l2) ebuf0 estr = Some (o1, ret) ->
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10 (Z_to_bv 64 2147483647) (Z_to_bv 64 l1) (Z_to_bv 64 l2) x14 x15 x16
               (Z_to_bv 64 estrp)
               (Z_to_bv 64 p2) x19 (Z_to_bv 64 6279824) (Z_to_bv 64 e) (Z_to_bv 64 rp)
               (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) (Z_to_bv 64 (Z.land t2 18446744073709551583)) (Z_to_bv 64 (Z.lor p2 a8)) x26 (Z_to_bv 64 p2)
               (Z_to_bv 64 fl) (Z_to_bv 64 t2) (Z_to_bv 64 a8) x31)
          (K_Ft K) (Z_to_bv 64 0x9692c) fc None m (seg_rom asegs)).
  Proof. eapply F_fmt_fp_tbb4.L_bb4. all: first [ exact L_bc4 | eassumption ]. Qed.

  Lemma L_aec : forall m (x1 x5 x6 x7 x14 x15 x16 x17 x19 x26 x31 : word) fc K
      (ws : list word) (big : list Z) (lo a r rp z zm e p2 t2 a8 palt : Z),
    midw K m fc 0%Z ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (lo <= i < zm)%Z -> znth big i = wval ws i) ->
    (forall i, (zm <= i)%Z -> znth big i = 0%Z) ->
    (0 <= lo <= a)%Z -> (lo <= r)%Z -> (a <= zm)%Z -> (0 <= z <= zm)%Z -> (zm <= 128)%Z -> (r < zm)%Z -> (r = 0 \/ r = 122)%Z -> rp = (bv_unsigned sp + -1056 + 4 * r)%Z ->
    (forall i, (0 <= znth big i < 1000000000)%Z) ->
    (-2^20 <= e < 2^20)%Z -> (0 <= p2 < 2^21)%Z -> (0 <= t2 < 256)%Z ->
    (a < z -> znth big (z - 1) <> 0)%Z -> (Z.lor t2 32 <> CHR_f -> z <= a -> a = r)%Z ->
    (0 <= a8 <= 8)%Z -> (a8 = 0%Z <-> Z.land fl 8 = 0%Z) ->
    palt = (if negb (p2 =? 0) || negb (Z.land fl ALT_FORM =? 0) then 1 else 0)%Z ->
    Z.lor t2 32 <> CHR_f ->
    (let? len := fmt_fp_len t2 (1 + p2 + palt) e in
     match len with
     | Ret v => Some (o0, v)
     | Cont (l, ebuf0, estr) => ffp_H4 o0 w fl t2 p2 (K_prefix K) (K_pl K) big a r z l ebuf0 estr
     end) = Some (o1, ret) ->
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) (Z_to_bv 64 (-1)) (Z_to_bv 64 2147483647) (Z_to_bv 64 (p2 + palt + 1)) (Z_to_bv 64 70) x14 x15 x16 x17
               (Z_to_bv 64 p2) x19 (Z_to_bv 64 6279824) (Z_to_bv 64 e) (Z_to_bv 64 rp)
               (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) (Z_to_bv 64 (Z.land t2 18446744073709551583)) (Z_to_bv 64 (Z.lor p2 a8)) x26 (Z_to_bv 64 p2)
               (Z_to_bv 64 fl) (Z_to_bv 64 t2) (Z_to_bv 64 a8) x31)
          (K_Ft K) (Z_to_bv 64 0x96864) fc None m (seg_rom asegs)).
  Proof. eapply F_fmt_fp_taec.L_aec. all: first [ exact L_bb4 | eassumption ]. Qed.

  Lemma L_a98 : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x24 x25 x26 x27 x31 : word) fc K
      (ws : list word) (big : list Z) (lo a r rp z zm e p2 t2 a8 : Z),
    midw K m fc 0%Z ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (lo <= i < zm)%Z -> znth big i = wval ws i) ->
    (forall i, (zm <= i)%Z -> znth big i = 0%Z) ->
    (0 <= lo <= a)%Z -> (lo <= r)%Z -> (a <= zm)%Z -> (0 <= z <= zm)%Z -> (zm <= 128)%Z -> (r < zm)%Z -> (r = 0 \/ r = 122)%Z -> rp = (bv_unsigned sp + -1056 + 4 * r)%Z ->
    (forall i, (0 <= znth big i < 1000000000)%Z) ->
    (-2^20 <= e < 2^20)%Z -> (0 <= p2 < 2^21)%Z -> (0 <= t2 < 256)%Z ->
    (a < z -> znth big (z - 1) <> 0)%Z -> (Z.lor t2 32 <> CHR_f -> z <= a -> a = r)%Z ->
    (0 <= a8 <= 8)%Z -> (a8 = 0%Z <-> Z.land fl 8 = 0%Z) ->
    ffp_H3 o0 w fl t2 p2 (K_prefix K) (K_pl K) big a r z e = Some (o1, ret) ->
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 p2) x19 (Z_to_bv 64 6279824) (Z_to_bv 64 e) (Z_to_bv 64 rp)
               (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x24 x25 x26 x27 (Z_to_bv 64 fl) (Z_to_bv 64 t2) (Z_to_bv 64 a8) x31)
          (K_Ft K) (Z_to_bv 64 0x96810) fc None m (seg_rom asegs)).
  Proof. eapply F_fmt_fp_ta98.L_a98. all: first [ exact L_aec | exact L_bb4 | eassumption ]. Qed.

  Lemma L_9a8 : forall m (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x24 x25 x26 x27 x28 x30 x31 : word) fc K
      (ws : list word) (big : list Z) (lo a r rp z zm e : Z),
    midw K m fc 0%Z ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (lo <= i < zm)%Z -> znth big i = wval ws i) ->
    (forall i, (zm <= i)%Z -> znth big i = 0%Z) ->
    (0 <= lo <= a)%Z -> (lo <= r)%Z -> (a <= zm)%Z -> (0 <= z <= zm)%Z -> (zm <= 128)%Z -> (r < zm)%Z -> (r = 0 \/ r = 122)%Z -> rp = (bv_unsigned sp + -1056 + 4 * r)%Z ->
    (forall i, (0 <= znth big i < 1000000000)%Z) ->
    (-2^20 <= e < 2^20)%Z ->
    (a < z -> znth big (z - 1) <> 0)%Z -> (Z.lor t 32 <> CHR_f -> z <= a -> a = r)%Z ->
    ffp_H2 o0 w fl t (K_p1 K) (K_prefix K) (K_pl K) big a r z e = Some (o1, ret) ->
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) (Z_to_bv 64 (4 * (z - r))) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (K_p1 K)) x19 (Z_to_bv 64 (Z.lor t 32)) (Z_to_bv 64 e) (Z_to_bv 64 rp)
               (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x24 x25 x26 x27 x28 (Z_to_bv 64 t) x30 x31)
          (K_Ft K) (Z_to_bv 64 0x96720) fc None m (seg_rom asegs)).
  Proof. eapply F_fmt_fp_t9a8.L_9a8. all: first [ exact L_a98 | eassumption ]. Qed.

  Lemma L_988 : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x24 x25 x26 x28 x30 x31 : word) fc K
      (ws : list word) (big : list Z) (lo a r rp z zm e : Z),
    midw K m fc 0%Z ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (lo <= i < zm)%Z -> znth big i = wval ws i) ->
    (forall i, (zm <= i)%Z -> znth big i = 0%Z) ->
    (0 <= lo <= a)%Z -> (lo <= r)%Z -> (a <= zm)%Z -> (0 <= z <= zm)%Z -> (zm <= 128)%Z -> (r < zm)%Z -> (r = 0 \/ r = 122)%Z -> rp = (bv_unsigned sp + -1056 + 4 * r)%Z ->
    (forall i, (0 <= znth big i < 1000000000)%Z) ->
    (-2^20 <= e < 2^20)%Z ->
    prov_R (K_p1 K) (K_prefix K) (K_pl K) r big a z e ->
    ffp_H o0 w fl t (K_p1 K) (K_prefix K) (K_pl K) big a r z e = Some (o1, ret) ->
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (K_p1 K)) x19 (Z_to_bv 64 (Z.lor t 32)) (Z_to_bv 64 e) (Z_to_bv 64 rp)
               x23 x24 x25 x26 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x28 (Z_to_bv 64 t) x30 x31)
          (K_Ft K) (Z_to_bv 64 0x96700) fc None m (seg_rom asegs)).
  Proof. eapply F_fmt_fp_t988.L_988. all: first [ exact L_9a8 | eassumption ]. Qed.

  Lemma L_978 : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x24 x25 x26 x28 x30 x31 : word) fc K
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
          (K_Ft K) (Z_to_bv 64 0x966f0) fc None m (seg_rom asegs)).
  Proof. eapply F_fmt_fp_r3.L_978. all: first [ exact L_988 | eassumption ]. Qed.

  Lemma L_94c : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x24 x25 x26 x28 x30 x31 : word) fc K
      (ws : list word) (big : list Z) (lo a r rp z zm d e i' zR : Z),
    midw K m fc 0%Z ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (lo <= i < zm)%Z -> znth big i = wval ws i) ->
    (forall i, (zm <= i)%Z -> znth big i = 0%Z) ->
    (0 <= lo <= a)%Z -> (lo <= r)%Z -> (a <= d < z)%Z -> (z <= zm <= 128)%Z -> (r < zm)%Z -> (r = 0 \/ r = 122)%Z ->
    rp = (bv_unsigned sp + -1056 + 4 * r)%Z ->
    (forall i, (0 <= znth big i < 1000000000)%Z) ->
    fmt_fp_cnt TEN_FUEL (znth big a) (10%Z, (9 * (r - a))%Z) = Some (i', e) ->
    zR = (if d + 1 <? z then d + 1 else z)%Z ->
    prov_R (K_p1 K) (K_prefix K) (K_pl K) r big a zR e ->
    ffp_H o0 w fl t (K_p1 K) (K_prefix K) (K_pl K) big a r zR e = Some (o1, ret) ->
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (K_p1 K)) x19 (Z_to_bv 64 (Z.lor t 32)) x21 (Z_to_bv 64 rp)
               (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d)) x24 x25 x26 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x28 (Z_to_bv 64 t) x30 x31)
          (K_Ft K) (Z_to_bv 64 0x966c4) fc None m (seg_rom asegs)).
  Proof. eapply F_fmt_fp_r3.L_94c. all: first [ exact L_988 | eassumption ]. Qed.

  Lemma L_carry : forall (k : nat) m (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x25 x26 x28 x30 x31 : word) fc K
      (ws : list word) (big big' : list Z) (lo a r rp z zm d d' a' i' eR zR : Z),
    midw K m fc 0%Z ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
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
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a))
               (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * (d - 1))) (Z_to_bv 64 999999999) x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (K_p1 K)) x19 (Z_to_bv 64 (Z.lor t 32)) x21 (Z_to_bv 64 rp)
               x23 x24 x25 x26 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x28 (Z_to_bv 64 t) x30 x31)
          (K_Ft K) (Z_to_bv 64 0x96690) fc None m (seg_rom asegs)).
  Proof. eapply F_fmt_fp_r3.L_carry. all: first [ exact L_988 | eassumption ]. Qed.

  Lemma L_8ac : forall m (x1 x5 x6 x7 x10 x11 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word) fc K (jk16 : list byte) (v512 : word) (z456 : Z)
      (ws : list word) (big bigq : list Z) (lo a r rp z zm d e i n x round small aq dq eq zR : Z),
    midq K [CB 16 jk16; C8 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * (d - 1) + 65536)); C8 v512; C8 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * d))] z456 m fc ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
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
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) x10 x11 (Z_to_bv 64 (lo64 small)) (Z_to_bv 64 (hi64 small)) x14 x15 x16 x17
               x18 (Z_to_bv 64 i) (Z_to_bv 64 (Z.lor t 32)) (Z_to_bv 64 e) (Z_to_bv 64 rp)
               (Z_to_bv 64 x) (Z_to_bv 64 (znth big d)) (Z_to_bv 64 (hi64 round)) (Z_to_bv 64 (lo64 round)) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z)) x28 x29 x30 x31)
          (K_Ft K) (Z_to_bv 64 0x96624) fc None m (seg_rom asegs)).
  Proof. eapply F_fmt_fp_r2.L_8ac. all: first [ exact L_94c | exact L_978 | exact L_carry | eassumption ]. Qed.

  Lemma L_608 : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word) fc K (jk16 : list byte)
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
          (K_Ft K) (Z_to_bv 64 0x96380) fc None m (seg_rom asegs)).
  Proof. eapply F_fmt_fp_r1.L_608. all: first [ exact L_8ac | eassumption ]. Qed.

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
          (K_Ft K) (Z_to_bv 64 0x95eb4) fc None m (seg_rom asegs)).
  Proof. eapply F_fmt_fp_rd.L_13c. all: first [ exact L_608 | exact L_978 | eassumption ]. Qed.

  Lemma L_0bc : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x25 x26 x28 x29 x30 x31 : word) fc K
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
          (K_Ft K) (Z_to_bv 64 0x95e34) fc None m (seg_rom asegs)).
  Proof. eapply F_fmt_fp_rnd.L_0bc. all: first [ exact L_13c | exact L_988 | eassumption ]. Qed.

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
          (K_Ft K) (Z_to_bv 64 0x95e30) fc None m (seg_rom asegs)).
  Proof. eapply F_fmt_fp_dn.L_0b8. all: first [ exact L_0bc | eassumption ]. Qed.

  Lemma L_fec : forall m (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fc pad jk40 jk8 jk3 jk12 jk37
      (ws : list word) (big : list Z) (e2 p1 a z prefix pl plz pfx : Z),
    finv m pad -> frm0 fc ->
    (forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k) ->
    rw_cells asegs m (bv_unsigned sp + -544)
      [C8 (Z_to_bv 64 0); CB 40 jk40; C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t); CB 8 jk8; C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 6279824);
       C8 (Z_to_bv 64 plz); C8 (Z_to_bv 64 pfx); C8 (Z_to_bv 64 pl); C8 (Z_to_bv 64 Fp)] ->
    rw_cells asegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 e2); CB 3 jk3] ->
    rw_cells asegs m (bv_unsigned sp + -417) [CB 12 jk12] ->
    rw_cells asegs m (bv_unsigned sp + -405) [CB 37 jk37] ->
    u32arr asegs m (bv_unsigned sp + -1056) ws -> length ws = 128%nat ->
    length big = 128%nat -> (forall i, (a <= i < z)%Z -> znth big i = wval ws i) ->
    wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0 ->
    (0 <= prefix <= 6)%Z -> (0 <= pl <= 1)%Z -> plz = Z.b2z (pl =? 0)%Z -> pfx = (79882 + prefix)%Z ->
    (0 <= p1 < 2^20)%Z -> (-1102 <= e2 <= 1024)%Z -> (0 <= a < z)%Z -> (z <= 128)%Z ->
    a = (if e2 <? 0 then 0 else 122)%Z -> prov_E p1 big a z e2 ->
    ffp_E o0 w fl t p1 prefix pl big a a z e2 = Some (o1, ret) ->
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 p1) (Z_to_bv 64 e2) (Z_to_bv 64 (Z.lor t 32)) x21 (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * a)) (Z_to_bv 64 (bv_unsigned sp + -1056 + 4 * z))
               x24 x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 0x95d64) fc None m (seg_rom asegs)).
  Proof. eapply F_fmt_fp_up.L_fec. all: first [ exact L_0b8 | eassumption ]. Qed.

  Lemma L_f70 : forall m (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x26 x27 x28 x29 x30 x31 : word) Ft fc pad jk40 jk8 jk3 jk12 jk37 jbig
      (y e2 p1 a aptr prefix pl plz pfx : Z),
    finv m pad -> frm0 fc ->
    (forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k) ->
    rw_cells asegs m (bv_unsigned sp + -544)
      [C8 (Z_to_bv 64 0); CB 40 jk40; C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 t); CB 8 jk8; C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 6279824);
       C8 (Z_to_bv 64 plz); C8 (Z_to_bv 64 pfx); C8 (Z_to_bv 64 pl); C8 (Z_to_bv 64 Fp)] ->
    rw_cells asegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 e2); CB 3 jk3] ->
    rw_cells asegs m (bv_unsigned sp + -417) [CB 12 jk12] ->
    rw_cells asegs m (bv_unsigned sp + -405) [CB 37 jk37] ->
    rw_cells asegs m (bv_unsigned sp + -1056) [CB 512 jbig] ->
    wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0 ->
    (0 <= prefix <= 6)%Z -> (0 <= pl <= 1)%Z -> plz = Z.b2z (pl =? 0)%Z -> pfx = (79882 + prefix)%Z ->
    (0 <= p1 < 2^20)%Z -> (-1102 <= e2 <= 1024)%Z ->
    a = (if e2 <? 0 then 0 else 122)%Z -> aptr = (bv_unsigned sp + -1056 + 4 * a)%Z ->
    (forall b' z' y', fmt_fp_dig DIG_FUEL (zrepeat 0 128, a, y) = Some (b', z', y') -> (z' <= a + 6)%Z) ->
    prov_D y e2 p1 ->
    ffp_D o0 w fl t y e2 p1 prefix pl = Some (o1, ret) ->
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 p1) (Z_to_bv 64 e2) (Z_to_bv 64 (Z.lor t 32)) x21 (Z_to_bv 64 aptr) x23
               (Z_to_bv 64 (lo64 y)) (Z_to_bv 64 (hi64 y)) x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 0x95ce8) fc None m (seg_rom asegs)).
  Proof. eapply F_fmt_fp_dig.L_f70. all: first [ exact L_fec | eassumption ]. Qed.

  Lemma L_c58 : forall m (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) fc pad jk40 jk16 jk3 jk12 jk37 jbig
      (y2 e0 prefix pl plz pfx : Z),
    finv m pad -> frm0 fc ->
    rw_cells asegs m (bv_unsigned sp + -544)
      [C8 (Z_to_bv 64 0); CB 40 jk40; C8 (Z_to_bv 64 w); CB 16 jk16; C8 (Z_to_bv 64 fl); C8 (Z_to_bv 64 6279824);
       C8 (Z_to_bv 64 plz); C8 (Z_to_bv 64 pfx); C8 (Z_to_bv 64 pl); C8 (Z_to_bv 64 Fp)] ->
    rw_cells asegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 e0); CB 3 jk3] ->
    rw_cells asegs m (bv_unsigned sp + -417) [CB 12 jk12] ->
    rw_cells asegs m (bv_unsigned sp + -405) [CB 37 jk37] ->
    rw_cells asegs m (bv_unsigned sp + -1056) [CB 512 jbig] ->
    wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0 ->
    (0 <= prefix <= 6)%Z -> (0 <= pl <= 1)%Z -> plz = Z.b2z (pl =? 0)%Z -> pfx = (79882 + prefix)%Z ->
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
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (-5)) (Z_to_bv 64 (f128_le y2 F128_ZERO)) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 p) (Z_to_bv 64 t) (Z_to_bv 64 6279824) (Z_to_bv 64 512) SPv (Z_to_bv 64 w) (Z_to_bv 64 (lo64 y2)) (Z_to_bv 64 (hi64 y2)) (Z_to_bv 64 Fp) (Z_to_bv 64 fl) x28 x29 x30 x31)
          F (Z_to_bv 64 0x959d0) fc None m (seg_rom asegs)).
  Proof. eapply F_fmt_fp_c58.L_c58. all: first [ exact L_f70 | eassumption ]. Qed.

  Lemma L_bec : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) fc pad jk80 jk8 jk3 jk12 jk37 jbig
      (y1 prefix pl plz pfx : Z),
    finv m pad -> frm0 fc ->
    rw_cells asegs m (bv_unsigned sp + -544)
      [C8 (Z_to_bv 64 0); CB 80 jk80; C8 (Z_to_bv 64 plz); C8 (Z_to_bv 64 pfx); C8 (Z_to_bv 64 pl); CB 8 jk8] ->
    rw_cells asegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 0); CB 3 jk3] ->
    rw_cells asegs m (bv_unsigned sp + -417) [CB 12 jk12] ->
    rw_cells asegs m (bv_unsigned sp + -405) [CB 37 jk37] ->
    rw_cells asegs m (bv_unsigned sp + -1056) [CB 512 jbig] ->
    wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0 ->
    (0 <= prefix <= 6)%Z -> (0 <= pl <= 1)%Z -> plz = Z.b2z (pl =? 0)%Z -> pfx = (79882 + prefix)%Z ->
    ffp_sign yv fl = (y1, prefix, pl) ->
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (-5)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 p) (Z_to_bv 64 t) (Z_to_bv 64 6279824) (Z_to_bv 64 512) SPv (Z_to_bv 64 w) (Z_to_bv 64 (hi64 y1)) (Z_to_bv 64 (lo64 y1)) (Z_to_bv 64 Fp) (Z_to_bv 64 fl) x28 x29 x30 x31)
          F (Z_to_bv 64 0x95964) fc None m (seg_rom asegs)).
  Proof. eapply F_fmt_fp_c00.L_bec. all: first [ exact L_c58 | eassumption ]. Qed.

  Lemma ffp_entry : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) fc,
    stk asegs m0 (bv_unsigned sp - 4640) (bv_unsigned sp) ->
    mem_inv asegs m0 ->
    frm0 fc ->
    wfile m0 Fp fl0 j1 j2 lbfw B (zb o0) junk0 ->
    ssp_cells m0 canary ->
    a3 = Z_to_bv 64 w -> a4 = Z_to_bv 64 p -> a5 = Z_to_bv 64 fl -> a6 = Z_to_bv 64 t -> bv_unsigned a7 <> 5%Z ->
    evt asegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0e s1e fw ya yb a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
          F (Z_to_bv 64 0x9584c) fc None m0 (seg_rom asegs)).
  Proof. eapply F_fmt_fp_entry.ffp_entry. all: first [ exact L_bec | eassumption ]. Qed.

End FmtFp.


End CeilWrap.
