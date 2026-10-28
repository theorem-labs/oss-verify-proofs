(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1 ZdSeqTable.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require FseNCountRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM ZdHufWR ZdHufWX SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memset RZ_huf_iface RZ_hft_iface RZ_hft_rs_iface RZ_hft_kit RZ_hft_bdt_defs RZ_hft_x1_kit huf411_kit_x1_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma x1_f4_pref : forall tl c dt nb sv, x1pref tl c dt -> 0 <= c -> 0 <= nb <= tl -> 4 + 2 * c + 8 <= Z.of_nat (length dt) ->
  x1pref tl (c + 4) (Zupd (4 + 2 * c + 3) sv (Zupd (4 + 2 * c + 2) nb (Zupd (4 + 2 * c + 1) sv (Zupd (4 + 2 * c) nb
    (Zupd (4 + 2 * c + 7) sv (Zupd (4 + 2 * c + 6) nb (Zupd (4 + 2 * c + 5) sv (Zupd (4 + 2 * c + 4) nb dt)))))))).
Proof.
  intros tl c dt nb sv P C0 NB L.
  change (c + 4) with (c + Z.of_nat 4).
  apply (prf_close_c tl c [1; 0; 3; 2] _ 4%nat); [| exact C0 | reflexivity].
  apply (prf_st_sy tl c _ _ 1); [| lia | lia | lia].
  apply (prf_st_nb tl c _ _ 1); [| lia | lia | lia | rewrite !Zupd_length; lia | lia].
  apply (prf_st_sy tl c _ _ 0); [| lia | lia | lia].
  apply (prf_st_nb tl c _ _ 0); [| lia | lia | lia | rewrite !Zupd_length; lia | lia].
  apply (prf_st_sy tl c _ _ 3); [| lia | lia | lia].
  apply (prf_st_nb tl c _ _ 3); [| lia | lia | lia | rewrite !Zupd_length; lia | lia].
  apply (prf_st_sy tl c _ _ 2); [| lia | lia | lia].
  apply (prf_st_nb tl c _ _ 2); [| lia | lia | lia | lia | lia].
  apply prf_open. exact P.
Qed.

Lemma rd_c8_lo4 : forall m A pre (x : word) post a,
  rw_cells usegs m A (pre ++ C8 x :: post) -> a = wa (A + Z.of_nat (cells_size pre)) ->
  ov_read_bytes usegs m a 4 = Some (le4 x).
Proof.
  intros m A pre x post a H ->.
  pose proof (cells_at_wf usegs m A _ (proj1 H)) as WF. apply cells_wf_app in WF. destruct WF as [WFp _].
  pose proof (SysStep.rw_cells_bytes_at usegs m A _ H) as B. rewrite cells_bytes_app in B.
  rewrite <- (cells_bytes_length pre WFp).
  rewrite (bytes_at_ov_read usegs m A _ (length (cells_bytes pre)) 4 B).
  - f_equal. rewrite skipn_app, skipn_all, Nat.sub_diag, skipn_O, app_nil_l. cbn [cells_bytes cbytes].
    rewrite firstn_app, length_le8. reflexivity.
  - rewrite length_app. cbn [cells_bytes cbytes]. rewrite length_app, length_le8. lia.
Qed.

Section X1.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV n DT WK wksz lo : Z).
  Hypothesis LO0 : 4096 <= lo.  Hypothesis LOS : lo <= SPV - HUF_TBL_STACK.  Hypothesis SPR : SPV < 2^47.  Hypothesis SP16 : SPV mod 16 = 0.
  Hypothesis NR : n < 2^32.
  Hypothesis DTL : 4096 <= DT.  Hypothesis DTH : DT + HUF_DTABLE_BYTES < 2^47.  Hypothesis DTAL : DT mod 4 = 0.
  Hypothesis WKL : 4096 <= WK.  Hypothesis WKSZ : 0 <= wksz < 2^32.  Hypothesis WKH : WK + wksz < 2^47.  Hypothesis WKAL : WK mod 4 = 0.
  Hypothesis OFFDT : DT + HUF_DTABLE_BYTES <= lo \/ SPV <= DT.  Hypothesis OFFWK : WK + wksz <= lo \/ SPV <= WK.
  Hypothesis DTWK : DT + HUF_DTABLE_BYTES <= WK \/ WK + wksz <= DT.
  Hypothesis WK1492 : 1492 <= wksz.

  Notation POST := (huf_rd_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DT WK wksz lo false m).
  Notation STF pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -240)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation SAVED := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Variables (flags : word) (f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f104 f112 f120 : list byte).
  Variables (hw rank : list Z) (nbs tl r0 : Z).
  Hypothesis TLR : 1 <= tl <= 12.  Hypothesis R0R : 1 <= r0 <= n.  Hypothesis HWLEN : Z.of_nat (length hw) = 256.  Hypothesis RKLEN : Z.of_nat (length rank) = 13.
  Notation X1S fl wn wt dt rst syb m1 := (x1s DT WK wksz SPV lo m SAVED hw rank fl wn wt dt rst syb m1).
  Notation FLF cur sym c104 c112 :=
    [C8 (Z_to_bv 64 876); C8 flags; CB 8 f16; C8 (Z_to_bv 64 r0); C8 (Z_to_bv 64 ux1_K32); C8 (Z_to_bv 64 (DT + 20));
     C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 (tl + 1)); C8 (Z_to_bv 64 (- (WK + 1))); C8 (Z_to_bv 64 (tl + 1));
     C8 (Z_to_bv 64 cur); C8 (Z_to_bv 64 sym); C8 (Z_to_bv 64 WK); c104; c112; C8 (Z_to_bv 64 ux1_K120)].

  Section FILLW.
  Variables (rst : list Z) (wn wt : word) (w cur sym count len nb : Z).
  Hypothesis NBT : 1 <= nb <= tl.  Hypothesis WR : 1 <= w <= 12.
  Hypothesis SLOTS : forall s, 0 <= s < count -> 0 <= sym + s < 256 /\ 0 <= cur + s * len /\ cur + s * len + len <= 4096.
  Hypothesis CUR0 : 0 <= cur.  Hypothesis CURH : cur <= 4096.  Hypothesis CNT : 0 <= count <= 256.  Hypothesis SYM0 : 0 <= sym <= 256.

  Notation FLW := (FLF cur sym (C8 (Z_to_bv 64 w)) (C8 (Z_to_bv 64 count))).
  Notation KLATCH := (forall m2 dt' syb' y5 y6 y7 y8 y10 y11 y12 y14 y15 y17 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31,
      X1S FLW wn wt dt' rst syb' m2 -> x1pref tl (cur + count * len) dt' ->
      evt usegs POST (STF 0x1f29c m2 (Z_to_bv 64 len) y5 y6 y7 y8 (Z_to_bv 64 (-9)) y10 y11 y12 (Z_to_bv 64 (WK + 980)) y14 y15
                           (Z_to_bv 64 (- (WK + 981))) y17 (Z_to_bv 64 (-17)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (-25))
                           y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)).
  Notation CASE pc mm x5 x6 x7 x8 x10 x11 x14 x15 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (STF pc mm (Z_to_bv 64 len) x5 x6 x7 x8 (Z_to_bv 64 (-9)) x10 x11 (Z_to_bv 64 nb) (Z_to_bv 64 (WK + 980)) x14 x15
         (Z_to_bv 64 (- (WK + 981))) x17 (Z_to_bv 64 (-17)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (-25)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).

  Ltac open_x1s I := unfold x1s in I; destruct I as (DTC & DTLEN & DTBY & HWC & RK & RST & RSTLEN & STS & SYC & SYLEN & WKR & F0 & F0SZ & NSC & FSAV & STK & MI & MU & WM);
                     unfold HUF_TBL_STACK, HUF_DTABLE_BYTES in *.
  Ltac close_x1s := unfold x1s, HUF_TBL_STACK, HUF_DTABLE_BYTES; repeat (split; [eassumption|]); eassumption.
  Ltac brute257 x :=
    let EX := fresh "EX" in let k := fresh "k" in let Hk := fresh "Hk" in
    assert (EX : exists k : nat, (k <= 256)%nat /\ x = Z.of_nat k) by (exists (Z.to_nat x); lia);
    destruct EX as (k & Hk & ->);
    do 257 (destruct k as [|k]; [vm_compute; reflexivity|]); lia.
  Ltac getbyte r sv SVR :=
    lazymatch goal with |- _ => let v := reg_val r in lazymatch v with Z_to_bv 64 ?e =>
      let ESV := fresh "ESV" in remember e as sv eqn:ESV;
      assert (SVR : 0 <= sv < 256) by (subst sv; match goal with |- 0 <= bv_unsigned ?b < 256 => let X := fresh "X" in pose proof (bv_unsigned_in_range 8 b) as X; unfold bv_modulus in X; cbn in X; lia end);
      clear ESV end end.
  Ltac dtstB DTC i v BH := u8_sok DTC i; zstep; u8_store DTC i v; [unfold hidden in BH; rewrite BH; symmetry; apply Z.mod_small; lia|].

  Notation LOOP pc mm s x6 x7 x8 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (STF pc mm (Z_to_bv 64 len) (Z_to_bv 64 (8 * count)) x6 x7 x8 (Z_to_bv 64 (-9)) (Z_to_bv 64 (8 * s)) (Z_to_bv 64 nb)
         (Z_to_bv 64 (sym + s)) (Z_to_bv 64 (WK + 980)) (Z_to_bv 64 (cur + 4 * s)) (Z_to_bv 64 (DT + 4 + 2 * cur))
         (Z_to_bv 64 (- (WK + 981))) (Z_to_bv 64 (8 * (256 - sym))) (Z_to_bv 64 (-17)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (-25))
         x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).

  Lemma x1_f4_loop : forall j m1 dt syb s x6 x7 x8 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    KLATCH -> len = 4 -> Z.to_nat (count - s) = j -> X1S FLW wn wt dt rst syb m1 -> x1pref tl (cur + 4 * s) dt -> 0 <= s < count ->
    evt usegs POST (LOOP 0x1f208 m1 s x6 x7 x8 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    induction j as [|j IH]; intros until x31; intros KL L1 EJ I PR SR; [exfalso; lia|].
    open_x1s I.
    destruct (SLOTS s SR) as (SY & C0 & C1). rewrite L1 in C0, C1.
    zstep. if_cases K1; zify_cond K1; [exfalso; lia|].
    zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
    zstep. zstep. if_cases K3; zify_cond K3; [exfalso; lia|].
    do 4 zstep.
    setreg 7 (Z_to_bv 64 1) ltac:(f_equal; rewrite lxor_sign_small by lia; repeat rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity).
    zstep. if_cases K4; zify_cond K4; [exfalso; lia|].
    zstep.
    pose proof (proj1 SYC) as SYB. lbyte SYB. clear SYB.
    getbyte 7 sv SVR.
    do 6 zstep.
    setreg 7 (Z_to_bv 64 (d4 sv nb)) ltac:(unfold d4, ux1_K120; f_equal; f_equal; reflexivity).
    pose proof (d4_bytes sv nb SVR ltac:(lia)) as (DR & B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7).
    remember (d4 sv nb) as D eqn:ED. clear ED.
    do 6 zstep. rewrite ?(Z.mod_small D 18446744073709551616) by lia.
    hide B0. hide B1. hide B2. hide B3. hide B4. hide B5. hide B6. hide B7.
    setreg 6 (Z_to_bv 64 (DT + (4 + 2 * (cur + 4 * s)))) ltac:(f_equal; lia).
    dtstB DTC (4 + 2 * (cur + 4 * s) + 4) nb B4.
    dtstB DTC (4 + 2 * (cur + 4 * s) + 5) sv B5.
    dtstB DTC (4 + 2 * (cur + 4 * s) + 6) nb B6.
    dtstB DTC (4 + 2 * (cur + 4 * s) + 7) sv B7.
    zstep.
    dtstB DTC (4 + 2 * (cur + 4 * s)) nb B0.
    dtstB DTC (4 + 2 * (cur + 4 * s) + 1) sv B1.
    dtstB DTC (4 + 2 * (cur + 4 * s) + 2) nb B2.
    dtstB DTC (4 + 2 * (cur + 4 * s) + 3) sv B3.
    clear B0 B1 B2 B3 B4 B5 B6 B7 DR.
    pose proof (x1_f4_pref tl (cur + 4 * s) dt nb sv PR ltac:(lia) ltac:(lia) ltac:(lia)) as PR'.
    lazymatch type of DTC with u8arr _ _ _ (map _ ?d) => remember d as dt' eqn:EDT' end.
    assert (DTLEN' : Z.of_nat (length dt') = Z.of_nat (length dt)) by (subst dt'; rewrite !Zupd_length; reflexivity).
    rewrite DTLEN in DTLEN'.
    assert (DTBY' : Forall isbyte dt') by (subst dt'; repeat (apply Forall_Zupd; [|lia]); exact DTBY).
    clear EDT' DTLEN DTBY.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (I' : X1S FLW wn wt dt' rst syb mm) by close_x1s end.
    zstep. if_cases K5; zify_cond K5; [exfalso; rewrite signed_lit in K5 by lia; lia|].
    do 3 zstep. zstep. if_cases KB; zify_cond KB.
    - setreg 10 (Z_to_bv 64 (8 * (s + 1))) ltac:(f_equal; lia).
      setreg 12 (Z_to_bv 64 (sym + (s + 1))) ltac:(f_equal; lia).
      setreg 14 (Z_to_bv 64 (cur + 4 * (s + 1))) ltac:(f_equal; lia).
      replace (cur + 4 * s + 4) with (cur + 4 * (s + 1)) in PR' by lia.
      eapply (IH _ dt' syb (s + 1)); [exact KL | exact L1 | lia | exact I' | exact PR' | lia].
    - eapply KL; [exact I'|]. rewrite L1. replace (cur + count * 4) with (cur + 4 * s + 4) by lia. exact PR'.
  Qed.

  Lemma x1_fill4 : forall m1 dt syb x5 x6 x7 x8 x10 x11 x14 x15 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    KLATCH -> len = 4 -> X1S FLW wn wt dt rst syb m1 -> x1pref tl cur dt ->
    evt usegs POST (CASE 0x1f1c0 m1 x5 x6 x7 x8 x10 x11 x14 x15 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros KL L1 I PR.
    open_x1s I.
    zstep. zstep.
    if_cases K; zify_cond K.
    - assert (C0 : count = 0) by (apply andb_false_iff in K; destruct K as [K|K]; apply Z.ltb_ge in K; lia).
      eapply KL; [close_x1s|]. rewrite C0, Z.mul_0_l, Z.add_0_r. exact PR.
    - do 4 zstep.
      let a := cur_mem_addr in
      pose proof (rd_c8_lo4 m1 (SPV + -240)
        [C8 (Z_to_bv 64 876); C8 flags; CB 8 f16; C8 (Z_to_bv 64 r0); C8 (Z_to_bv 64 ux1_K32); C8 (Z_to_bv 64 (DT + 20));
         C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 (tl + 1)); C8 (Z_to_bv 64 (- (WK + 1))); C8 (Z_to_bv 64 (tl + 1))] (Z_to_bv 64 cur)
        [C8 (Z_to_bv 64 sym); C8 (Z_to_bv 64 WK); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 count); C8 (Z_to_bv 64 ux1_K120)]
        a F0 ltac:(unfold wa; f_equal; cbn [cells_size csize Nat.add]; lia)) as RD4.
      zstep. clear RD4.
      do 11 zstep.
      rewrite (sx32w_small cur) by lia.
      setreg 5 (Z_to_bv 64 (8 * count)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; change (2^3) with 8; lia).
      setreg 10 (Z_to_bv 64 (8 * 0)) ltac:(reflexivity).
      setreg 11 (Z_to_bv 64 nb) ltac:(f_equal; change 255 with (Z.ones 8); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
      setreg 12 (Z_to_bv 64 (sym + 0)) ltac:(f_equal; symmetry; apply swrap32_small; lia).
      setreg 14 (Z_to_bv 64 (cur + 4 * 0)) ltac:(f_equal; lia).
      setreg 15 (Z_to_bv 64 (DT + 4 + 2 * cur)) ltac:(f_equal; rewrite MState.unsigned_lit by lia; rewrite Z.shiftl_mul_pow2 by lia; change (2^1) with 2; lia).
      setreg 17 (Z_to_bv 64 (8 * (256 - sym))) ltac:(f_equal; clear - SYM0; brute257 sym).
      eapply (x1_f4_loop _ m1 dt syb 0); [exact KL | exact L1 | reflexivity | close_x1s | rewrite Z.mul_0_r, Z.add_0_r; exact PR | lia].
  Qed.
  End FILLW.
End X1.
