(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Sf_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Arr.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim SoftFloat FmtFp FmtFpNf.
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

From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require F_fmt_fp_entry F_fmt_fp.

Lemma rw_cells_retype_nf : forall segs m A cs cs',
  rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
  rw_cells segs m A cs'.
Proof.
  intros segs m A cs cs' [[W B] WR] W' EB ES. unfold rw_cells, cells_at. rewrite EB, ES. auto.
Qed.
Definition FILE_cells4 (fl0 b1 b2 b3 : byte) (j1r : list byte) (WEND WPOS : Z) (j2 : list byte) (lbfw : word) : list cell :=
  [C4 (le_bytes_to_word [fl0; b1; b2; b3]); CB 28 j1r; C8 (Z_to_bv 64 WEND); C8 (Z_to_bv 64 WPOS); CB 96 j2; C4 lbfw].
Lemma file_cells4 : forall m Fp fl0 b1 b2 b3 j1r WEND WPOS j2 lbfw,
  rw_cells asegs m Fp (FILE_cells fl0 (b1 :: b2 :: b3 :: j1r) WEND WPOS j2 lbfw) <->
  rw_cells asegs m Fp (FILE_cells4 fl0 b1 b2 b3 j1r WEND WPOS j2 lbfw).
Proof.
  intros. unfold FILE_cells, FILE_cells4.
  assert (E : cells_bytes [C4 (le_bytes_to_word [fl0; b1; b2; b3]); CB 28 j1r; C8 (Z_to_bv 64 WEND); C8 (Z_to_bv 64 WPOS); CB 96 j2; C4 lbfw]
              = cells_bytes [CB 1 [fl0]; CB 31 (b1 :: b2 :: b3 :: j1r); C8 (Z_to_bv 64 WEND); C8 (Z_to_bv 64 WPOS); CB 96 j2; C4 lbfw]).
  { cbn [cells_bytes cbytes app]. rewrite (le4_of_bytes [fl0; b1; b2; b3]) by reflexivity. reflexivity. }
  split; intros H.
  - pose proof H as [[W _] _]. cbn in W.
    eapply rw_cells_retype_nf; [exact H | cbn; repeat split; try lia; destruct W as (_ & W1 & _ & _ & W2 & _); cbn in W1; try lia; exact W2 | exact E | reflexivity].
  - pose proof H as [[W _] _]. cbn in W.
    eapply rw_cells_retype_nf; [exact H | cbn; repeat split; try lia; destruct W as (_ & W1 & _ & _ & W2 & _); try lia; exact W2 | symmetry; exact E | reflexivity].
Qed.

Lemma flags4_ferr : forall (fl0 b1 b2 b3 : byte), Z.land (bv_unsigned fl0) 32 = 0%Z ->
  Z.land (bv_unsigned (le_bytes_to_word [fl0; b1; b2; b3])) 32 = 0%Z.
Proof.
  intros fl0 b1 b2 b3 H. rewrite StrFun.le_bytes_to_word4.
  pose proof (bv_unsigned_in_range 8 fl0). pose proof (bv_unsigned_in_range 8 b1). pose proof (bv_unsigned_in_range 8 b2). pose proof (bv_unsigned_in_range 8 b3).
  unfold bv_modulus in *. cbn -[Z.add Z.mul Z.land bv_unsigned Z.le Z.lt] in *.
  change 32%Z with (2^5)%Z in H |- *. rewrite zb_land_pow2 in H |- * by lia.
  replace ((bv_unsigned fl0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3) / 2 ^ 5)%Z
    with (bv_unsigned fl0 / 2^5 + (4 * bv_unsigned b1 + 1024 * bv_unsigned b2 + 262144 * bv_unsigned b3) * 2)%Z
    by (change (2^5)%Z with 32%Z; Z.to_euclidean_division_equations; lia).
  rewrite Z.mod_add by lia. exact H.
Qed.

Lemma land32_sx32 : forall ww : word, Z.land (bv_unsigned (sx32 ww)) 32 = Z.land (bv_unsigned ww) 32.
Proof.
  intros ww. transitivity (Z.land (Z.land (bv_unsigned (sx32 ww)) 63) 32). { rewrite <- Z.land_assoc. reflexivity. }
  change 63%Z with (2^6 - 1)%Z. rewrite land_sx32_mask by lia.
  transitivity (Z.land (Z.land (bv_unsigned ww) (2^6 - 1)) 32). 2:{ rewrite <- Z.land_assoc. reflexivity. }
  change (2^6 - 1)%Z with (Z.ones 6). rewrite Z.land_ones by lia. f_equal.
  pose proof (bv_unsigned_in_range 64 ww). Z.to_euclidean_division_equations. lia.
Qed.
Lemma zx32_le4 : forall fl0 b1 b2 b3 : byte, bv_unsigned (zx32 (le_bytes_to_word [fl0; b1; b2; b3])) = bv_unsigned (le_bytes_to_word [fl0; b1; b2; b3]).
Proof.
  intros. unfold zx32.
  assert (R : (0 <= bv_unsigned (le_bytes_to_word [fl0; b1; b2; b3]) < 2^32)%Z).
  { rewrite StrFun.le_bytes_to_word4. pose proof (bv_unsigned_in_range 8 fl0). pose proof (bv_unsigned_in_range 8 b1).
    pose proof (bv_unsigned_in_range 8 b2). pose proof (bv_unsigned_in_range 8 b3). unfold bv_modulus in *. cbn -[Z.add Z.mul Z.le Z.lt bv_unsigned] in *. lia. }
  rewrite Z.mod_small by lia. apply unsigned_lit. lia.
Qed.

Lemma nf_strings : forall m, mem_inv asegs m ->
  bytes_at asegs m 0x17e6d (zb [105; 110; 102]%Z) /\ bytes_at asegs m 0x20c56 (zb [110; 97; 110]%Z)
  /\ bytes_at asegs m 0x1a564 (zb [73; 78; 70]%Z) /\ bytes_at asegs m 0x1ffdd (zb [78; 65; 78]%Z).
Proof.
  intros m MI. split; [| split; [| split]]; (apply ro_bytes_at; [exact MI | lia | cbn; lia | apply ro_bytes_b_sound; vm_compute; reflexivity]).
Qed.

Ltac cur_reg R k :=
  let p := eval vm_compute in (bv_key (Z_to_bv 5 k)) in
  eval cbv beta iota delta [tget] in (match tget p R with Some v => v | None => Z_to_bv 64 0 end).

Section FmtFp.
  Variables (ra sp gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
            (ya yb fw : word)
            (F : bvmap 5 word) (m0 : word -> option byte)
            (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (junk0 : list byte) (canary : word)
            (w p fl t : Z) (o0 o1 : list Z) (ret : Z).
  Definition yv : Z := (bv_unsigned ya + 2^64 * bv_unsigned yb)%Z.
  Definition Fp : Z := bv_unsigned fw.
  Definition usp : Z := bv_unsigned sp.

  Hypothesis HM : fmt_fp_nf o0 yv w p fl t = Some (o1, ret).
  Hypothesis SPLO : (5152 <= bv_unsigned sp)%Z.
  Hypothesis SPHI : (bv_unsigned sp < 2^63)%Z.
  Hypothesis GLO : (7110320 <= bv_unsigned sp - 6944)%Z.
  Hypothesis AF : (bv_unsigned sp <= Fp)%Z.
  Hypothesis AB : (bv_unsigned sp <= B)%Z.
  Hypothesis Hw : (-2^31 <= w <= 1)%Z.
  Hypothesis Hw0 : (0 <= w)%Z.
  Hypothesis Hp : (-2^31 <= p < 2^20)%Z.
  Hypothesis Hfl : (0 <= fl < 2^32)%Z.
  Hypothesis Ht : (0 <= t < 256)%Z.
  Hypothesis Hta : Z.lor t 32 <> 97%Z.

  Hypothesis YN0 : Z.land (Z.shiftr (hi64 yv) 48) 0x7fff <> 0%Z \/ f128_le yv F128_ZERO = 0%Z.
  Hypothesis YN1 : Z.land (Z.shiftr (hi64 (Z.lxor yv F128_SIGNBIT)) 48) 0x7fff <> 0%Z \/ f128_le (Z.lxor yv F128_SIGNBIT) F128_ZERO = 0%Z.
  Hypothesis ROOM : (Z.of_nat (length o1) <= Z.of_nat (length o0) + Z.of_nat (length junk0))%Z.
  Hypothesis J256 : (length junk0 < 256)%nat.

  Definition SBN : Z := (Z.of_nat (length o0) + Z.of_nat (length junk0))%Z.
  Hypothesis RIP : rip_stmt.
  Hypothesis FXI : ifrexpl_stmt.
  Hypothesis HA0 : fext m0 (bv_unsigned sp - 6944) (bv_unsigned sp) B SBN Fp.

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

  Lemma L_bec_nf : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) fc pad jk80 jk8 jk3 jk12 jk37 jbig
      (y1 prefix pl plz pfx : Z),
    finv m pad -> frm0 fc ->
    rw_cells asegs m (bv_unsigned sp + -544)
      [C8 (Z_to_bv 64 0); CB 80 jk80; C8 (Z_to_bv 64 plz); C8 (Z_to_bv 64 pfx); C8 (Z_to_bv 64 pl); CB 8 jk8] ->
    rw_cells asegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 0); CB 3 jk3] ->
    rw_cells asegs m (bv_unsigned sp + -417) [CB 12 jk12] ->
    rw_cells asegs m (bv_unsigned sp + -405) [CB 37 jk37] ->
    rw_cells asegs m (bv_unsigned sp + -1056) [CB 512 jbig] ->
    wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0 ->
    (0 <= prefix <= 6)%Z -> (0 <= pl <= 1)%Z -> plz = Z.b2z (pl =? 0)%Z -> pfx = (81734 + prefix)%Z ->
    ffp_sign yv fl = (y1, prefix, pl) ->
    evt asegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (-5)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 p) (Z_to_bv 64 t) (Z_to_bv 64 7110312) (Z_to_bv 64 512) SPv (Z_to_bv 64 w) (Z_to_bv 64 (hi64 y1)) (Z_to_bv 64 (lo64 y1)) (Z_to_bv 64 Fp) (Z_to_bv 64 fl) x28 x29 x30 x31)
          F (Z_to_bv 64 0x15503c) fc None m (seg_rom asegs)).
  Proof using AB AF GLO HM Hfl Hp Ht Hw Hw0 J256 ROOM SPHI SPLO YN0 YN1 RIP FXI HA0.
    intros until pfx. intros FI FRM FRs E2 EB BF BIGb WF Hpre Hpl Hplz Hpfx HS. dest_finv FI. dest_wfile WF. pose_word_ranges.

    pose proof HM as HM'. unfold fmt_fp_nf in HM'. change (nf_sign yv fl) with (ffp_sign yv fl) in HM'. rewrite HS in HM'. cbv beta iota in HM'.
    zs. zs. zs. call fpclassifyl_callv. 1:{ hyp. }
    zs. zs. if_cases Kc; zify_cond Kc; rewrite signed_of_Z in Kc by (pose proof (fpclassifyl_range y1); lia).
    2:{ exfalso. rewrite (proj2 (Z.leb_gt _ _)) in HM' by lia. discriminate HM'. }
    rewrite (proj2 (Z.leb_le _ _) Kc) in HM'. rewrite pad_id in HM' by lia. cbv beta iota in HM'. rewrite pad_id in HM' by lia. cbv beta iota in HM'.
    injection HM' as Eo1 Eret. try clear HM'. rewrite Z.max_r in Eret by lia.
    assert (EL : (Z.of_nat (length o1) = Z.of_nat (length o0) + pl + 3)%Z) by (rewrite <- Eo1; unfold out; rewrite !app_length, nf_str_length, (zsub_length PREFIX_STR) by (cbn; lia); lia).
    assert (LJ1 : length j1 = 31%nat) by (destruct FC as [[W _] _]; cbn in W; tauto).
    assert (EJ : exists b1 b2 b3 j1r, j1 = b1 :: b2 :: b3 :: j1r)
      by (destruct j1 as [|b1 [|b2 [|b3 j1r]]]; try (cbn in LJ1; discriminate LJ1); exists b1, b2, b3, j1r; reflexivity).
    destruct EJ as (b1 & b2 & b3 & j1r & EJ).
    set (c0 := zb o0) in *. assert (Lc0 : length c0 = length o0) by (subst c0; apply zb_length).
    set (pbs := zb (zsub PREFIX_STR prefix pl)) in *.
    assert (Lpx : length (zsub PREFIX_STR prefix pl) = Z.to_nat pl) by (apply zsub_length; cbn; lia).
    assert (Lpbs : length pbs = Z.to_nat pl) by (subst pbs; rewrite zb_length; exact Lpx).
    set (sbs := zb (nf_str y1 t)) in *.
    assert (Lsbs : length sbs = 3%nat) by (subst sbs; rewrite zb_length; apply nf_str_length).

    zs. zs. zs. zs. zs. zs. call letf2_callv. 1:{ hyp. }

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mcur _) =>
    assert (J640 : forall (t0v t1v t2v a0v a1v a2v a3v a4v a5v a6v a7v t3v t4v t5v t6v : word) (S : Z),
      (forall mq, mem_inv asegs mq -> bytes_at asegs mq S sbs) -> (0 <= S)%Z -> (S + 3 <= 7110320)%Z -> chkr m0 S 3 ->
      evt asegs POST
        (MS (mkR (Z_to_bv 64 0x155124) SPv gp tp t0v t1v t2v sp (Z_to_bv 64 (3 + pl)) a0v a1v a2v a3v a4v a5v a6v a7v
                 (Z_to_bv 64 p) (Z_to_bv 64 S) (Z_to_bv 64 7110312) (Z_to_bv 64 pl) SPv (Z_to_bv 64 w) (Z_to_bv 64 (hi64 y1)) (Z_to_bv 64 (lo64 y1)) (Z_to_bv 64 Fp) (Z_to_bv 64 fl) t3v t4v t5v t6v)
            F (Z_to_bv 64 0x155284) fc None mcur (seg_rom asegs)))
    end.
    { intros t0v t1v t2v a0v a1v a2v a3v a4v a5v a6v a7v t3v t4v t5v t6v S SBYf RS0 RS1 CKS0.

      rewrite EJ in FC. apply (proj1 (file_cells4 _ _ _ _ _ _ _ _ _ _ _)) in FC. unfold FILE_cells4 in FC.
      zs. zs. rewrite zx32_le4, (flags4_ferr fl0 b1 b2 b3 FLG). zs. if_cases Kfe; zify_cond Kfe; [exfalso; lia|].

      zs. rewrite Hpfx. zs. zs.
      lazymatch goal with MIq : mem_inv asegs ?mm |- _ =>
        pose proof (bytes_at_slice _ _ _ (Z.to_nat prefix) (Z.to_nat pl) (prefix_u8ro _ MIq) ltac:(rewrite zb_length; cbn; lia)) as SRC end.
      rewrite Z2Nat.id in SRC by lia. rewrite <- zb_zsub in SRC by lia. change (zb (zsub PREFIX_STR prefix pl)) with pbs in SRC.
      destruct (stk_split asegs _ _ (bv_unsigned sp + -1056 - 2304) _ ST ltac:(lia)) as [STlo STf]. clear ST.
      apply (proj2 (file_cells4 _ _ _ _ _ _ _ _ _ _ _)) in FC. rewrite <- EJ in FC.
      zs.
      lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
        eapply evt_cut;
        [ eapply fwritex_callR;
          [ exact FC | exact BUF | exact FLG | exact LBF | exact Bpos | exact Bhi | exact SEPfb
          | exact SRC
          | rewrite Lpbs, Z2Nat.id by lia; reflexivity
          | rewrite Lpbs; lia
          | exact STf
          | hyp
          | lia | lia | lia | lia | lia | lia | lia | lia | lia
          | solve_MU | solve_WM | lia | first [exact CKS0 | chk_src] ]
        | clear FC BUF STf; post_call segs m ]
      end.
      match goal with X : stk _ _ (bv_unsigned sp + -1056 - 2304)%Z _ |- _ =>
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (stk_merge asegs mm _ _ _ STlo X ltac:(lia)) as ST end; clear STlo X end.
      try clear SRC. try clear POST. clear FLG LBF Bpos Bhi SEPfb.
      lazymatch goal with X : wfile _ _ _ _ _ _ _ (c0 ++ pbs) _ |- _ => dest_wfile X end.
      assert (LA : length (c0 ++ pbs) = (length c0 + Z.to_nat pl)%nat) by (rewrite app_length, Lpbs; reflexivity).
      assert (LK : length (skipn (length pbs) junk0) = (length junk0 - Z.to_nat pl)%nat) by (rewrite length_skipn, Lpbs; reflexivity).

      rewrite EJ in FC. apply (proj1 (file_cells4 _ _ _ _ _ _ _ _ _ _ _)) in FC. unfold FILE_cells4 in FC.
      zs. zs. rewrite land32_sx32, (flags4_ferr fl0 b1 b2 b3 FLG). zs. if_cases Kfe2; zify_cond Kfe2; [exfalso; lia|].

      zs. zs. zs.
      lazymatch goal with MIq : mem_inv asegs ?mm |- _ => pose proof (SBYf _ MIq) as SRC2 end.
      destruct (stk_split asegs _ _ (bv_unsigned sp + -1056 - 2304) _ ST ltac:(lia)) as [STlo STf]. clear ST.
      apply (proj2 (file_cells4 _ _ _ _ _ _ _ _ _ _ _)) in FC. rewrite <- EJ in FC.
      zs.
      lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
        eapply evt_cut;
        [ eapply fwritex_callR;
          [ exact FC | exact BUF | exact FLG | exact LBF | exact Bpos | exact Bhi | exact SEPfb
          | exact SRC2
          | rewrite Lsbs; reflexivity
          | rewrite Lsbs; lia
          | exact STf
          | hyp
          | lia | lia | lia | lia | lia | lia | lia | lia | lia
          | solve_MU | solve_WM | lia | first [exact CKS0 | chk_src] ]
        | clear FC BUF STf; post_call segs m ]
      end.
      match goal with X : stk _ _ (bv_unsigned sp + -1056 - 2304)%Z _ |- _ =>
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (stk_merge asegs mm _ _ _ STlo X ltac:(lia)) as ST end; clear STlo X end.
      try clear SRC2. try clear POST.
      lazymatch goal with X : wfile _ _ _ _ _ _ _ ((c0 ++ pbs) ++ sbs) _ |- _ => rename X into WF3 end.

      zs. zs. zs. zs.

      lazymatch goal with |- evt _ _ (MS ?R ?Fq _ ?fcq _ ?mq _) =>
      let y5 := cur_reg R 5%Z in let y6 := cur_reg R 6%Z in let y7 := cur_reg R 7%Z in
      let y10 := cur_reg R 10%Z in let y11 := cur_reg R 11%Z in let y12 := cur_reg R 12%Z in let y13 := cur_reg R 13%Z in
      let y14 := cur_reg R 14%Z in let y15 := cur_reg R 15%Z in let y16 := cur_reg R 16%Z in let y17 := cur_reg R 17%Z in
      let y18 := cur_reg R 18%Z in let y19 := cur_reg R 19%Z in
      let y28 := cur_reg R 28%Z in let y29 := cur_reg R 29%Z in let y30 := cur_reg R 30%Z in let y31 := cur_reg R 31%Z in
      assert (J6fc : evt asegs POST
        (MS (mkR (Z_to_bv 64 0x1552bc) SPv gp tp y5 y6 y7 sp (Z_to_bv 64 (3 + pl)) y10 y11 y12 y13 y14 y15 y16 y17 y18 y19
                 (Z_to_bv 64 7110312) (Z_to_bv 64 pl) SPv (Z_to_bv 64 w) (Z_to_bv 64 (hi64 y1)) (Z_to_bv 64 (lo64 y1)) (Z_to_bv 64 Fp) (Z_to_bv 64 fl) y28 y29 y30 y31)
            Fq (Z_to_bv 64 0x155340) fcq None mq (seg_rom asegs)))
      end.
      { zs. if_cases Klt; zify_cond Klt; [exfalso; lia|].
        zs. zs. rewrite Eret. zs. zs. zs. if_cases Kcan; zify_cond Kcan; try (exfalso; clear -Kcan; apply Kcan; reflexivity).
        do 15 zs.

        release_frame BIGb ST (bv_unsigned sp + -544)%Z.
        release_frame FRs ST (bv_unsigned sp + -424)%Z.
        release_frame E2 ST (bv_unsigned sp + -417)%Z.
        release_frame EB ST (bv_unsigned sp + -405)%Z.
        release_frame BF ST (bv_unsigned sp + -368)%Z.
        release_frame FRhi ST (bv_unsigned sp)%Z.
        zs.
        apply evt_done. unfold fmt_fp_post.
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [ ms_eq | ].
        split; [exact MU|]. split; [exact WM|]. split; [hyp|]. split; [hyp|]. split; [exact ST|].
        split. { replace (zb o1) with ((c0 ++ pbs) ++ sbs) by (subst c0 pbs sbs; rewrite <- Eo1; unfold out; rewrite !zb_app; reflexivity).
                 replace (skipn (length o1 - length o0) junk0) with (skipn (length sbs) (skipn (length pbs) junk0)) by (rewrite skipn_skipn; f_equal; lia).
                 exact WF3. }
        split; [unfold ssp_cells, got_ssp, ssp_guard; split; hyp | intros k Hk; reflexivity ]. }
      if_cases Kzp; zify_cond Kzp; [ exact J6fc |].

      zs. if_cases Kw2; zify_cond Kw2; first [exact J6fc | exfalso; lia]. }

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mcur _) =>
    assert (J5c0 : forall (t0v t1v t2v a0v a1v a2v a3v a4v a5v a6v a7v t3v t4v t5v t6v : word) (S : Z),
      (forall mq, mem_inv asegs mq -> bytes_at asegs mq S sbs) -> (0 <= S)%Z -> (S + 3 <= 7110320)%Z -> chkr m0 S 3 ->
      evt asegs POST
        (MS (mkR (Z_to_bv 64 0x155124) SPv gp tp t0v t1v t2v sp (Z_to_bv 64 (Z.land t 32)) a0v a1v a2v a3v a4v a5v a6v a7v
                 (Z_to_bv 64 p) (Z_to_bv 64 S) (Z_to_bv 64 7110312) (Z_to_bv 64 pl) SPv (Z_to_bv 64 w) (Z_to_bv 64 (hi64 y1)) (Z_to_bv 64 (lo64 y1)) (Z_to_bv 64 Fp) (Z_to_bv 64 fl) t3v t4v t5v t6v)
            F (Z_to_bv 64 0x155204) fc None mcur (seg_rom asegs)))
    end.
    { intros t0v t1v t2v a0v a1v a2v a3v a4v a5v a6v a7v t3v t4v t5v t6v S SBYf RS0 RS1 CKS0.
      zs. zs. try replace (bv_swrap 32 (pl + 3))%Z with (3 + pl)%Z by (rewrite swrap32_eq; mlia). replace (Z_to_bv 64 (pl + 3)) with (Z_to_bv 64 (3 + pl)) by (f_equal; lia).
      zs. if_cases Kla; zify_cond Kla; [ eapply J640; [exact SBYf | lia | lia | exact CKS0] |].
      zs. if_cases Kw1; zify_cond Kw1; first [ eapply J640; [exact SBYf | lia | lia | exact CKS0] | exfalso; lia ]. }

    zs. if_cases Kt; zify_cond Kt.
    -
      zs. zs. zs. zs. zs. zs. if_cases Kn; zify_cond Kn;
        [ | zs ];
        first [ apply (proj1 (F_frexpl.f128_le_land64_zero _ _)) in Kn
              | let K := fresh in assert (K : f128_le y1 y1 <> 0%Z) by (intros E; apply Kn; apply (proj2 (F_frexpl.f128_le_land64_zero _ _)); exact E); clear Kn; rename K into Kn ];
        (eapply J5c0; [ intros mq MIq; subst sbs; unfold nf_str; rewrite Kt;
                        first [ rewrite Kn | replace (f128_le y1 y1 =? 0)%Z with false by (symmetry; exact (proj2 (Z.eqb_neq _ _) Kn)) ];
                        cbn [negb Z.eqb]; pose proof (nf_strings mq MIq) as NS;
                        first [ exact (proj1 NS) | exact (proj1 (proj2 NS)) | exact (proj1 (proj2 (proj2 NS))) | exact (proj2 (proj2 (proj2 NS))) ]
                      | lia | lia | chk_src ]).
    -
      zs. zs. zs. zs. zs. zs. if_cases Kn; zify_cond Kn; zs;
        first [ apply (proj1 (F_frexpl.f128_le_land64_zero _ _)) in Kn
              | let K := fresh in assert (K : f128_le y1 y1 <> 0%Z) by (intros E; apply Kn; apply (proj2 (F_frexpl.f128_le_land64_zero _ _)); exact E); clear Kn; rename K into Kn ];
        (eapply J5c0; [ intros mq MIq; subst sbs; unfold nf_str; replace (Z.land t 32 =? 0)%Z with false by (symmetry; exact (proj2 (Z.eqb_neq _ _) Kt));
                        first [ rewrite Kn | replace (f128_le y1 y1 =? 0)%Z with false by (symmetry; exact (proj2 (Z.eqb_neq _ _) Kn)) ];
                        cbn [negb Z.eqb]; pose proof (nf_strings mq MIq) as NS;
                        first [ exact (proj1 NS) | exact (proj1 (proj2 NS)) | exact (proj1 (proj2 (proj2 NS))) | exact (proj2 (proj2 (proj2 NS))) ]
                      | lia | lia | chk_src ]).
  Qed.

  Lemma ffp_entry_nf : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) fc,
    stk asegs m0 (bv_unsigned sp - 6944) (bv_unsigned sp) ->
    mem_inv asegs m0 ->
    frm0 fc ->
    wfile m0 Fp fl0 j1 j2 lbfw B (zb o0) junk0 ->
    ssp_cells m0 canary ->
    a3 = Z_to_bv 64 w -> a4 = Z_to_bv 64 p -> a5 = Z_to_bv 64 fl -> a6 = Z_to_bv 64 t -> bv_unsigned a7 <> 5%Z ->
    evt asegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0e s1e fw ya yb a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
          F (Z_to_bv 64 0x154f24) fc None m0 (seg_rom asegs)).
  Proof using AB AF GLO HM Hfl Hp Ht Hw Hw0 J256 ROOM SPHI SPLO YN0 YN1 RIP FXI HA0.
    eapply F_fmt_fp_entry.ffp_entry. all: first [ exact L_bec_nf | eassumption ].
  Qed.
End FmtFp.

Definition fmt_fp_nf_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (junk0 : list byte) (canary : word)
         (w p fl t : Z) (o0 o1 : list Z) (ret : Z),
    let y := (bv_unsigned a1 + 2^64 * bv_unsigned a2)%Z in
    let Fp := bv_unsigned a0 in
    fmt_fp_nf o0 y w p fl t = Some (o1, ret) ->
    yn_fact y -> yn_fact (Z.lxor y F128_SIGNBIT) ->
    (5152 <= bv_unsigned sp)%Z -> (bv_unsigned sp < 2^63)%Z -> (7110320 <= bv_unsigned sp - F_fmt_fp.FMT_FP_DEPTH)%Z ->
    (bv_unsigned sp <= Fp)%Z -> (bv_unsigned sp <= B)%Z ->
    (0 <= w <= 1)%Z -> (-2^31 <= p < 2^20)%Z -> (0 <= fl < 2^32)%Z -> (0 <= t < 256)%Z -> Z.lor t 32 <> 97%Z ->
    (Z.of_nat (length o1) <= Z.of_nat (length o0) + Z.of_nat (length junk0))%Z -> (length junk0 < 256)%nat ->
    stk asegs m (bv_unsigned sp - F_fmt_fp.FMT_FP_DEPTH) (bv_unsigned sp) ->
    mem_inv asegs m ->
    frm0 fc ->
    wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0 ->
    ssp_cells m canary ->
    a3 = Z_to_bv 64 w -> a4 = Z_to_bv 64 p -> a5 = Z_to_bv 64 fl -> a6 = Z_to_bv 64 t -> bv_unsigned a7 <> 5%Z ->

    (kHighShadowEnd + 8 <= bv_unsigned sp - F_fmt_fp.FMT_FP_DEPTH)%Z -> ictx m ->
    (forall q n, bv_unsigned sp - F_fmt_fp.FMT_FP_DEPTH <= q -> q + n <= bv_unsigned sp -> chkr m q n)%Z ->
    chkr m B (Z.of_nat (length o0) + Z.of_nat (length junk0)) -> rod_chk_fp m -> ifx_real m ->
    evt asegs (F_fmt_fp.fmt_fp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F Fp fl0 j1 j2 lbfw B o0 o1 junk0 canary ret m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x154f24) fc None m (seg_rom asegs)).

Section WithRT.
Hypothesis RIP : rip_stmt.
Hypothesis FXI : ifrexpl_stmt.
Lemma fmt_fp_nf_spec : fmt_fp_nf_stmt.
Proof using RIP FXI.
  unfold fmt_fp_nf_stmt. intros until ret. cbv zeta.
  intros HM YN0 YN1 SPLO SPHI GLO AF AB Hw Hp Hfl Ht Hta ROOM J256 ST MI FRM WF SSP Ha3 Ha4 Ha5 Ha6 Hps.
  unfold F_fmt_fp.FMT_FP_DEPTH in *.
  intros HSH IC0 CKS CKB ROD IFX.
  assert (HA0 : fext m (bv_unsigned sp - 6944) (bv_unsigned sp) B (Z.of_nat (length o0) + Z.of_nat (length junk0)) (bv_unsigned a0)).
  { pose proof WF as (FC & BUF & FLG & LBF & Bpos & Bhi & SEPfb). rewrite zb_length in FC, Bhi, SEPfb.
    split; [exact HSH|]. split; [exact IC0|]. split; [exact CKS|]. split; [exact CKB|]. split; [lia|]. split; [exact ROD|]. split.
    - unfold FILE_cells in FC.
      apply (proj1 (rw_cells_app asegs _ _ [_; _] _)) in FC. destruct FC as [_ FC]. cbn [cells_size csize Nat.add] in FC.
      apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FC. destruct FC as [FC _].
      replace (bv_unsigned a0 + Z.of_nat 32)%Z with (bv_unsigned a0 + 32)%Z in FC by lia.
      replace (B + Z.of_nat (length o0) + Z.of_nat (length junk0))%Z with (B + (Z.of_nat (length o0) + Z.of_nat (length junk0)))%Z in FC by lia.
      exact FC.
    - split; [lia | exact IFX]. }
  eapply evt_mono.
  { eapply (ffp_entry_nf ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a1 a2 a0 F m fl0 j1 j2 lbfw B junk0 canary w p fl t o0 o1 ret);
      first [eassumption | lia]. }
  intros ms' H. exact H.
Qed.
End WithRT.
