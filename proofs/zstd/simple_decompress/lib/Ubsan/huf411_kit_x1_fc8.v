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

  Lemma ux1_c8_lw : forall mm A pre y post a,
    rw_cells usegs mm A (pre ++ C8 y :: post) -> a = wa (A + Z.of_nat (cells_size pre)) ->
    ov_read_bytes usegs mm a 4 = Some (le4 y).
  Proof.
    intros mm A pre y post a [[WF B] _] ->.
    assert (WP : cells_wf pre).
    { clear B. induction pre as [|c pre IH]; [exact I|]. destruct WF as [W1 W2]. split; [exact W1|]. apply IH. exact W2. }
    rewrite <- (cells_bytes_length pre WP). rewrite cells_bytes_app in B. cbn [cells_bytes cbytes] in B.
    rewrite (bytes_at_ov_read usegs mm A _ (length (cells_bytes pre)) 4 B).
    - rewrite skipn_app, skipn_all, Nat.sub_diag, app_nil_l, skipn_O.
      rewrite firstn_app, length_le8.
      change (4 - 8)%nat with 0%nat. rewrite firstn_O, app_nil_r. reflexivity.
    - rewrite !length_app, length_le8. lia.
  Qed.

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

  Notation LST s mm x7 x8 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (STF 0x1eecc mm (Z_to_bv 64 len) (Z_to_bv 64 (16 * count)) (Z_to_bv 64 (DT + 4 + 2 * cur)) x7 x8 (Z_to_bv 64 (-9))
         (Z_to_bv 64 (16 * s)) (Z_to_bv 64 (sym + s)) (Z_to_bv 64 (DT + 2 * cur)) (Z_to_bv 64 (WK + 980))
         (Z_to_bv 64 (16 * (256 - sym))) (Z_to_bv 64 (cur + 8 * s)) (Z_to_bv 64 (- (WK + 981))) (Z_to_bv 64 nb)
         (Z_to_bv 64 (-17)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (-25)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).

  Ltac open_x1s I := destruct I as (DTC & DTLEN & DTBY & HWC & RK & RST & RSTLEN & STS & SYC & SYLEN & WKR & F0 & F0SZ & NSC & FSAV & STK & MI & MU & WM);
                     unfold HUF_TBL_STACK, HUF_DTABLE_BYTES in *.
  Ltac close_x1s := unfold x1s, HUF_TBL_STACK, HUF_DTABLE_BYTES; repeat (split; [eassumption|]); eassumption.
  Ltac getbyte r sv SVR :=
    lazymatch goal with |- _ => let v := reg_val r in lazymatch v with Z_to_bv 64 ?e =>
      let ESV := fresh "ESV" in remember e as sv eqn:ESV;
      assert (SVR : 0 <= sv < 256) by (subst sv; match goal with |- 0 <= bv_unsigned ?b < 256 => let X := fresh "X" in pose proof (bv_unsigned_in_range 8 b) as X; unfold bv_modulus in X; cbn in X; lia end);
      clear ESV end end.
  Ltac dtstB DTC i v BH := u8_sok DTC i; zstep; u8_store DTC i v; [unfold hidden in BH; rewrite BH; symmetry; apply Z.mod_small; lia|].
  Ltac zn := first [ lia | rewrite ?swrap32_small by lia; lia ].
  Ltac zsh := rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia; try simpl Z.pow; first [ lia | apply Z.div_mul; lia ].
  Ltac setr r e := let v := reg_val r in replace v with (Z_to_bv 64 e) by (f_equal; zn).
  Ltac setsh r e := let v := reg_val r in replace v with (Z_to_bv 64 e) by (f_equal; zsh).
  Ltac chk K := if_cases K; zify_cond K; [exfalso; rewrite ?signed_lit in K by lia; lia|].
  Ltac zdec := rewrite ?lxor_sign_small by lia; repeat (match goal with
    | |- context [Z.ltb ?a ?b] => first [ rewrite (proj2 (Z.ltb_ge a b)) by lia | rewrite (proj2 (Z.ltb_lt a b)) by lia ]
    end); repeat change (Z.b2z false) with 0; repeat change (Z.b2z true) with 1.

  Lemma ux1_sx32 : forall z, 0 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
  Proof. intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit by lia. apply swrap32_small. lia. Qed.

  Lemma x1_f8_loop : forall j m1 dt syb s x7 x8 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    KLATCH -> len = 8 -> Z.to_nat (count - s) = j -> X1S FLW wn wt dt rst syb m1 -> x1pref tl (cur + 8 * s) dt -> 0 <= s < count ->
    evt usegs POST (LST s m1 x7 x8 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    induction j as [|j IH]; intros m1 dt syb s x7 x8 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 KL L8 EJ I PR SR; [exfalso; lia|].
    open_x1s I.
    destruct (SLOTS s SR) as (SY & C0 & C1). rewrite L8 in C0, C1.
    zstep. chk K1.
    zstep. chk K2.
    zstep. zstep. chk K3.
    zstep. zstep. zdec.
    zstep. zstep.
    zstep. chk K4.
    zstep.
    pose proof (proj1 SYC) as SYB. lbyte SYB. clear SYB. getbyte 28 sv SVR.
    do 6 zstep.
    lazymatch goal with |- _ => let v := reg_val 28 in lazymatch v with Z_to_bv 64 ?e => change e with (d4 sv nb) end end.
    pose proof (d4_bytes sv nb SVR ltac:(lia)) as (DR & B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7).
    remember (d4 sv nb) as D eqn:ED. clear ED.
    do 7 zstep. rewrite ?(Z.mod_small D 18446744073709551616) by lia.
    hide B0. hide B1. hide B2. hide B3. hide B4. hide B5. hide B6. hide B7.
    remember (4 + 2 * (cur + 8 * s)) as bs eqn:EBS.
    dtstB DTC (bs + 4) nb B4.
    dtstB DTC (bs + 5) sv B5.
    dtstB DTC (bs + 6) nb B6.
    dtstB DTC (bs + 7) sv B7.
    dtstB DTC (bs + 0) nb B0.
    dtstB DTC (bs + 1) sv B1.
    dtstB DTC (bs + 2) nb B2.
    dtstB DTC (bs + 3) sv B3.
    zstep. chk K5.
    dtstB DTC (bs + 12) nb B4.
    dtstB DTC (bs + 13) sv B5.
    dtstB DTC (bs + 14) nb B6.
    dtstB DTC (bs + 15) sv B7.
    zstep. zstep.
    dtstB DTC (bs + 8) nb B0.
    dtstB DTC (bs + 9) sv B1.
    dtstB DTC (bs + 10) nb B2.
    dtstB DTC (bs + 11) sv B3.
    zstep. chk K6.
    clear B0 B1 B2 B3 B4 B5 B6 B7 DR.
    lazymatch type of DTC with u8arr _ _ _ (map _ ?d) => remember d as dt' eqn:EDT' end.
    lazymatch type of DTLEN with _ = ?L => assert (DTLEN' : Z.of_nat (length dt') = L) by (subst dt'; rewrite !Zupd_length; exact DTLEN) end.
    assert (DTBY' : Forall isbyte dt') by (subst dt'; repeat (apply Forall_Zupd; [|lia]); exact DTBY).
    assert (PF : x1pref tl (cur + 8 * s + 8) dt').
    { subst dt'. pose proof (prf_open _ _ _ PR) as P0.
      pose proof (prf_st_nb _ _ _ _ 2 (bs + 4) nb P0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite ?Zupd_length; lia) ltac:(lia)) as P1.
      pose proof (prf_st_sy _ _ _ _ 2 (bs + 5) sv P1 ltac:(lia) ltac:(lia) ltac:(lia)) as P2.
      pose proof (prf_st_nb _ _ _ _ 3 (bs + 6) nb P2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite ?Zupd_length; lia) ltac:(lia)) as P3.
      pose proof (prf_st_sy _ _ _ _ 3 (bs + 7) sv P3 ltac:(lia) ltac:(lia) ltac:(lia)) as P4.
      pose proof (prf_st_nb _ _ _ _ 0 (bs + 0) nb P4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite ?Zupd_length; lia) ltac:(lia)) as P5.
      pose proof (prf_st_sy _ _ _ _ 0 (bs + 1) sv P5 ltac:(lia) ltac:(lia) ltac:(lia)) as P6.
      pose proof (prf_st_nb _ _ _ _ 1 (bs + 2) nb P6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite ?Zupd_length; lia) ltac:(lia)) as P7.
      pose proof (prf_st_sy _ _ _ _ 1 (bs + 3) sv P7 ltac:(lia) ltac:(lia) ltac:(lia)) as P8.
      pose proof (prf_st_nb _ _ _ _ 6 (bs + 12) nb P8 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite ?Zupd_length; lia) ltac:(lia)) as P9.
      pose proof (prf_st_sy _ _ _ _ 6 (bs + 13) sv P9 ltac:(lia) ltac:(lia) ltac:(lia)) as P10.
      pose proof (prf_st_nb _ _ _ _ 7 (bs + 14) nb P10 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite ?Zupd_length; lia) ltac:(lia)) as P11.
      pose proof (prf_st_sy _ _ _ _ 7 (bs + 15) sv P11 ltac:(lia) ltac:(lia) ltac:(lia)) as P12.
      pose proof (prf_st_nb _ _ _ _ 4 (bs + 8) nb P12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite ?Zupd_length; lia) ltac:(lia)) as P13.
      pose proof (prf_st_sy _ _ _ _ 4 (bs + 9) sv P13 ltac:(lia) ltac:(lia) ltac:(lia)) as P14.
      pose proof (prf_st_nb _ _ _ _ 5 (bs + 10) nb P14 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite ?Zupd_length; lia) ltac:(lia)) as P15.
      pose proof (prf_st_sy _ _ _ _ 5 (bs + 11) sv P15 ltac:(lia) ltac:(lia) ltac:(lia)) as P16.
      exact (prf_close_c _ _ _ _ 8 P16 ltac:(lia) eq_refl). }
    clear EDT' DTLEN DTBY.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (I' : X1S FLW wn wt dt' rst syb mm) by close_x1s end.
    zstep. zstep. zstep. zstep. if_cases KB; zify_cond KB.
    - setr 15 (cur + 8 * (s + 1)). setr 10 (16 * (s + 1)). setr 11 (sym + (s + 1)).
      eapply (IH _ dt' syb (s + 1)); [exact KL | exact L8 | lia | exact I' | replace (cur + 8 * (s + 1)) with (cur + 8 * s + 8) by lia; exact PF | lia].
    - zstep. eapply KL; [exact I'|]. rewrite L8. replace (cur + count * 8) with (cur + 8 * s + 8) by lia. exact PF.
  Qed.

  Lemma x1_fill8 : forall m1 dt syb x5 x6 x7 x8 x10 x11 x14 x15 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    KLATCH -> len = 8 -> X1S FLW wn wt dt rst syb m1 -> x1pref tl cur dt ->
    evt usegs POST (CASE 0x1ee7c m1 x5 x6 x7 x8 x10 x11 x14 x15 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros m1 dt syb x5 x6 x7 x8 x10 x11 x14 x15 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 KL L8 I PR.
    pose proof I as I0. open_x1s I.
    destruct (Z.eq_dec count 0) as [CZ|CZ].
    { zstep. zstep. if_cases K0; zify_cond K0; try (exfalso; lia).
      eapply KL; [exact I0|]. replace (cur + count * len) with cur by (rewrite CZ; lia). exact PR. }
    assert (HR : ov_read_bytes usegs m1 (wa (SPV + -240 + 80)) 4 = Some (le4 (Z_to_bv 64 cur)))
      by exact (ux1_c8_lw m1 (SPV + -240) (firstn 10 FLW) (Z_to_bv 64 cur) (skipn 11 FLW) _ F0 eq_refl).
    zstep. zstep. chk K0.
    zstep. zstep. zstep. setr 11 sym.
    zstep. clear HR. rewrite (ux1_sx32 cur) by lia.
    zstep. lazymatch goal with |- _ => let v := reg_val 17 in replace v with (Z_to_bv 64 nb)
      by (f_equal; change 255 with (Z.ones 8); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity) end.
    zstep. zstep. setr 12 (256 - sym).
    zstep. zstep. setsh 5 (16 * count).
    zstep. zdec.
    zstep. setsh 6 (2 * cur).
    zstep. setr 14 (-1).
    zstep. first [ lazymatch goal with |- _ => let v := reg_val 14 in lazymatch v with Z_to_bv 64 (Z.land ?x ?y) =>
                     replace v with (Z_to_bv 64 (256 - sym))
                       by (f_equal; change x with (Z.ones 64); rewrite Z.land_comm, Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity) end end
                 | setr 14 (256 - sym) ].
    zstep. zstep. zstep. zstep. setsh 14 (16 * (256 - sym) * 268435456).
    zstep. setsh 14 (16 * (256 - sym)).
    setr 10 (16 * 0). setr 11 (sym + 0). setr 15 (cur + 8 * 0). setr 6 (DT + 4 + 2 * cur). setr 12 (DT + 2 * cur).
    eapply (x1_f8_loop (Z.to_nat (count - 0)) m1 dt syb 0);
      [exact KL | exact L8 | reflexivity | exact I0 | replace (cur + 8 * 0) with cur by lia; exact PR | lia].
  Qed.
  End FILLW.
End X1.
