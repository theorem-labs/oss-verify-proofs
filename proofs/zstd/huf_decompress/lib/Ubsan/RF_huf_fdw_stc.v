From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit HufWalkKit STRW_tac.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface RF_huf_tbl_iface RF_huf_tbl_kit RF_huf_fdw_kit
  RF_huf_bdt_model RF_huf_fdw_stl RF_huf_fdw_cut RF_huf_fdw_st RF_huf_fdw_stb RF_huf_fdw_stp.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac slia ::= slia_sep.

Lemma stc_rl_ovf : forall bs d, 64 < bd_bits d ->
  reload_dstream bs d = Ok (Overflow, mkBD (bd_cont d) (bd_bits d) (bd_ptr d) true).
Proof. intros bs d H. unfold reload_dstream. destruct (Z.ltb_spec 64 (bd_bits d)); [reflexivity | lia]. Qed.

Lemma stc_dec_ok : forall dt s d (k : Z * Z * bitD -> res (list Z)),
  res_ok (bind (decode_sym dt false s d) k) -> exists o s' d', decode_sym dt false s d = Ok (o, s', d').
Proof.
  intros dt s d k H. destruct (decode_sym dt false s d) as [[[o s'] d']|e| |] eqn:E.
  - eauto.
  - exfalso. exact (decode_sym_not_err dt false s d e E).
  - cbn in H. contradiction.
  - cbn in H. contradiction.
Qed.

Lemma stc_rl_ok : forall bs d (k : dstatus * bitD -> res (list Z)),
  res_ok (bind (reload_dstream bs d) k) -> exists st d', reload_dstream bs d = Ok (st, d').
Proof.
  intros bs d k H. destruct (reload_dstream bs d) as [[st d']|e| |] eqn:E.
  - eauto.
  - exfalso. exact (reload_not_err bs d e E).
  - cbn in H. contradiction.
  - cbn in H. contradiction.
Qed.

Ltac stc_len := unfold FseNCount.Zlength in *; rewrite ?length_app in *; cbn [length] in *; lia.
Ltac stc_if H b :=
  match type of H with context [?a <? ?c] =>
    replace (a <? c) with b in H by (symmetry; first [apply Z.ltb_ge | apply Z.ltb_lt]; stc_len) end;
  cbn [bind] in H.

Section STC.
  Variables (SP : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem) (S DT DST dcap lo : Z) (bs : list Z)
            (dt : dtable) (POST : machine_state -> Prop).
  Hypothesis PRE : fdw_pre SP S DT DST dcap lo bs dt.

  Notation tl := (dt_tableLog dt).
  Notation STF pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation STH pc mm x1 j0 j x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (STF pc mm x1 (Z_to_bv 64 64) (Z_to_bv 64 (-1)) (Z_to_bv 64 (DST + j)) (Z_to_bv 64 DST)
         (Z_to_bv 64 (2^61)) (Z_to_bv 64 (-70)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 1) (Z_to_bv 64 1)
         (Z_to_bv 64 (DST + dcap + -2)) (Z_to_bv 64 (2^64 - 1 - BIT_MASK_TAB)) (Z_to_bv 64 2) (Z_to_bv 64 (DST + j + 1))
         (Z_to_bv 64 (2^16 - 1)) (Z_to_bv 64 BIT_MASK_TAB) (Z_to_bv 64 (DST + j0)) (Z_to_bv 64 (j0 - j))
         x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Notation TIb m out s1 s2 d := (exists jp, fdw_mem m0 m SP S DT DST dcap lo bs dt (mkDec out s1 s2 d) jp).

  Hypothesis HEAD : forall m1 out s1 s2 d j0 (x1 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    TIb m1 out s1 s2 d -> 0 <= s1 < 2^tl -> 0 <= s2 < 2^tl -> bitd_ok bs d -> bd_bits d <= 2^29 -> zlen out + 2 <= dcap ->
    (forall o0 s1a d1 m2 (y23 y24 y25 y28 y29 y30 y31 : word), decode_sym dt false s1 d = Ok (o0, s1a, d1) ->
       TIb m2 (out ++ [o0]) s1a s2 d1 -> 0 <= s1a < 2^tl -> 0 <= o0 < 256 -> 64 < bd_bits d1 < 2^30 ->
       0 <= bd_cont d1 < 2^64 ->
       evt usegs POST (STH 0x207b8 m2 x1 j0 (zlen out) y23 y24 y25 x26 x27 y28 y29 y30 y31)) ->
    (forall o0 s1a d1 m2 (y23 y24 y25 y28 y30 y31 : word), decode_sym dt false s1 d = Ok (o0, s1a, d1) ->
       TIb m2 (out ++ [o0]) s1a s2 d1 -> 0 <= s1a < 2^tl -> 0 <= o0 < 256 -> bd_bits d1 <= 64 -> bitd_ok bs d1 ->
       evt usegs POST (STH 0x1feac m2 x1 j0 (zlen out) y23 y24 y25 x26 x27 y28 (Z_to_bv 64 (bd_bits d1)) y30 y31)) ->
    evt usegs POST (STH 0x1fe1c m1 x1 j0 (zlen out) x23 x24 x25 x26 x27 x28 x29 x30 x31).

  Hypothesis FINA : forall m1 out o0 s1a s2 d1 o1 s2' d2 j0
      (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    TIb m1 (out ++ [o0]) s1a s2 d1 -> 0 <= s2 < 2^tl -> 64 < bd_bits d1 < 2^30 -> 0 <= bd_cont d1 < 2^64 ->
    zlen out + 2 <= dcap -> 0 <= o0 < 256 ->
    decode_sym dt false s2 (mkBD (bd_cont d1) (bd_bits d1) (bd_ptr d1) true) = Ok (o1, s2', d2) ->
    fdw_K SP gp tp F fc m0 DST dcap lo POST (Ok ((out ++ [o0]) ++ [o1])) ->
    evt usegs POST (STF 0x207b8 m1 x1 x5 x6 x7 (Z_to_bv 64 DST) x9 x10 x11 x12 x13 x14 x15 x16 x17
                        (Z_to_bv 64 (DST + zlen out + 1)) x19 x20 (Z_to_bv 64 (DST + j0)) (Z_to_bv 64 (j0 - zlen out))
                        x23 x24 x25 x26 x27 x28 x29 x30 x31).

  Hypothesis RA : forall m1 out s1 s2 d st d' j0 j (x1 x23 x24 x25 x26 x27 x28 x30 x31 : word),
    TIb m1 out s1 s2 d -> bitd_ok bs d -> bd_bits d <= 64 -> reload_dstream bs d = Ok (st, d') ->
    (forall m2 (y23 y24 y25 y29 y30 y31 : word), TIb m2 out s1 s2 d' ->
       evt usegs POST (STH 0x1ffa0 m2 x1 j0 j y23 y24 y25 x26 x27 (Z_to_bv 64 (S + 8)) y29 y30 y31)) ->
    evt usegs POST (STH 0x1feac m1 x1 j0 j x23 x24 x25 x26 x27 x28 (Z_to_bv 64 (bd_bits d)) x30 x31).

  Hypothesis MID : forall m1 out o0 s1a s2 d1 j0 (x1 x23 x24 x25 x26 x27 x29 x30 x31 : word),
    TIb m1 (out ++ [o0]) s1a s2 d1 -> 0 <= s1a < 2^tl -> 0 <= s2 < 2^tl -> bitd_ok bs d1 -> bd_bits d1 <= 64 ->
    0 <= o0 < 256 -> zlen out + 2 <= dcap ->
    (dcap - 2 < zlen out + 1 -> fdw_K SP gp tp F fc m0 DST dcap lo POST (Err ZSTD_error_dstSize_tooSmall)) ->
    (zlen out + 3 <= dcap -> forall o1 s2a d2 o2 s1b d3, decode_sym dt false s2 d1 = Ok (o1, s2a, d2) -> 64 < bd_bits d2 ->
       decode_sym dt false s1a (mkBD (bd_cont d2) (bd_bits d2) (bd_ptr d2) true) = Ok (o2, s1b, d3) ->
       fdw_K SP gp tp F fc m0 DST dcap lo POST (Ok ((out ++ [o0; o1]) ++ [o2]))) ->
    (forall o1 s2a d2 m2 (y23 y24 y25 y30 y31 : word), decode_sym dt false s2 d1 = Ok (o1, s2a, d2) ->
       TIb m2 ((out ++ [o0]) ++ [o1]) s1a s2a d2 -> 0 <= s2a < 2^tl -> 0 <= o1 < 256 -> bd_bits d2 <= 64 ->
       bitd_ok bs d2 -> zlen out + 3 <= dcap ->
       evt usegs POST (STH 0x20030 m2 x1 j0 (zlen out) y23 y24 y25 x26 x27 (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (bd_bits d2))
                           y30 y31)) ->
    evt usegs POST (STH 0x1ffa0 m1 x1 j0 (zlen out) x23 x24 x25 x26 x27 (Z_to_bv 64 (S + 8)) x29 x30 x31).

  Hypothesis RB : forall m1 out s1 s2 d st d' j0 j (x1 x23 x24 x25 x26 x27 x30 x31 : word),
    TIb m1 out s1 s2 d -> bitd_ok bs d -> bd_bits d <= 64 -> reload_dstream bs d = Ok (st, d') ->
    (forall m2 (y23 y24 y25 y28 y29 y30 y31 : word), TIb m2 out s1 s2 d' ->
       evt usegs POST (STH 0x1fe08 m2 x1 j0 j y23 y24 y25 x26 x27 y28 y29 y30 y31)) ->
    evt usegs POST (STH 0x20030 m1 x1 j0 j x23 x24 x25 x26 x27 (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (bd_bits d)) x30 x31).

  Hypothesis J2 : forall m1 out s1 s2 d j0 j (x1 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    TIb m1 out s1 s2 d -> zlen out = j + 2 -> 0 <= j -> j + 2 <= dcap ->
    (dcap - 2 < zlen out -> fdw_K SP gp tp F fc m0 DST dcap lo POST (Err ZSTD_error_dstSize_tooSmall)) ->
    (zlen out + 2 <= dcap -> forall y28 : word,
       evt usegs POST (STH 0x1fe1c m1 x1 j0 (j + 2) x23 x24 x25 x26 x27 y28 x29 x30 x31)) ->
    evt usegs POST (STH 0x1fe08 m1 x1 j0 j x23 x24 x25 x26 x27 x28 x29 x30 x31).

  Hypothesis TPREP : forall m1 out s1 s2 d jp (y1 y5 y6 y7 y10 y15 y16 y17 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
    fdw_mem m0 m1 SP S DT DST dcap lo bs dt (mkDec out s1 s2 d) jp -> zlen out <= dcap ->
    (dcap - 2 < zlen out -> fdw_K SP gp tp F fc m0 DST dcap lo POST (Err ZSTD_error_dstSize_tooSmall)) ->
    (zlen out + 2 <= dcap -> forall (z1 z23 z24 z25 z26 z27 z28 z29 z30 z31 : word),
       evt usegs POST (STH 0x1fe1c m1 z1 (zlen out) (zlen out) z23 z24 z25 z26 z27 z28 z29 z30 z31)) ->
    evt usegs POST (MS (mkR y1 (Z_to_bv 64 SP) gp tp y5 y6 y7 (Z_to_bv 64 DST) (Z_to_bv 64 (2^61)) y10
                            (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 1) (Z_to_bv 64 1) y15 y16 y17
                            (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (2^16 - 1)) (Z_to_bv 64 BIT_MASK_TAB)
                            (Z_to_bv 64 (DST + zlen out)) y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                        F (Z_to_bv 64 PFDW_T1) fc None m1 (seg_rom usegs)).

  Lemma stc_loop : forall (f : nat) m1 out s1 s2 d r j0 (x1 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    tail_loop bs dt dcap false f (mkDec out s1 s2 d) = r -> res_ok r -> fdw_K SP gp tp F fc m0 DST dcap lo POST r ->
    TIb m1 out s1 s2 d -> 0 <= s1 < 2^tl -> 0 <= s2 < 2^tl -> bitd_ok bs d -> bd_bits d <= 2^29 ->
    zlen out + 2 <= dcap ->
    evt usegs POST (STH 0x1fe1c m1 x1 j0 (zlen out) x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof using All.
    pose proof PRE as (_ & _ & _ & BYS & _).
    induction f as [|f IH]; intros m1 out s1 s2 d r j0 x1 x23 x24 x25 x26 x27 x28 x29 x30 x31 TL RO K TI S1 S2 BD BB OL.
    { cbn [tail_loop] in TL. subst r. contradiction RO. }
    cbn [tail_loop de_out de_s1 de_s2 de_bd] in TL. stc_if TL false.
    eapply HEAD; [exact TI | exact S1 | exact S2 | exact BD | exact BB | exact OL | |].
    - intros o0 s1a d1 m2 y23 y24 y25 y28 y29 y30 y31 D1 TI2 S1A O0 B1 C1.
      rewrite D1 in TL. cbn [bind] in TL.
      rewrite (stc_rl_ovf bs d1 ltac:(lia)) in TL. cbn [bind dstatus_eqb] in TL.
      assert (RO1 := RO). rewrite <- TL in RO1. destruct (stc_dec_ok _ _ _ _ RO1) as (o1 & s2' & d2 & D2).
      rewrite D2 in TL. cbn [bind] in TL. subst r.
      eapply FINA with (o1 := o1) (s2' := s2') (d2 := d2);
        [exact TI2 | exact S2 | lia | lia | exact OL | exact O0 | exact D2 | rewrite <- app_assoc; exact K].
    - intros o0 s1a d1 m2 y23 y24 y25 y28 y30 y31 D1 TI2 S1A O0 B1 BD1.
      rewrite D1 in TL. cbn [bind] in TL.
      assert (RO1 := RO). rewrite <- TL in RO1. destruct (stc_rl_ok _ _ _ RO1) as (st1 & d1r & R1).
      destruct (reload_facts bs d1 st1 d1r BYS BD1 B1 R1) as (BD1r & B1r & Z1r & NO1).
      rewrite R1 in TL. cbn [bind] in TL. rewrite NO1 in TL. cbn [bind] in TL.
      eapply RA; [exact TI2 | exact BD1 | exact B1 | exact R1 |].
      intros m3 z23 z24 z25 z29 z30 z31 TI3.
      eapply MID; [exact TI3 | exact S1A | exact S2 | exact BD1r | lia | exact O0 | exact OL | | |].
      + intros E. stc_if TL true. subst r. exact K.
      + intros OL3 o1 s2a d2 o2 s1b d3 D2 B2 D3.
        stc_if TL false. rewrite D2 in TL. cbn [bind] in TL.
        rewrite (stc_rl_ovf bs d2 B2) in TL. cbn [bind dstatus_eqb] in TL.
        rewrite D3 in TL. cbn [bind] in TL. subst r.
        replace ((out ++ [o0; o1]) ++ [o2]) with ((out ++ [o0]) ++ [o1; o2]) by (rewrite <- !app_assoc; reflexivity).
        exact K.
      + intros o1 s2a d2 m4 w23 w24 w25 w30 w31 D2 TI4 S2A O1 B2 BD2 OL3.
        stc_if TL false. rewrite D2 in TL. cbn [bind] in TL.
        assert (RO2 := RO). rewrite <- TL in RO2. destruct (stc_rl_ok _ _ _ RO2) as (st2 & d2r & R2).
        destruct (reload_facts bs d2 st2 d2r BYS BD2 B2 R2) as (BD2r & B2r & Z2r & NO2).
        rewrite R2 in TL. cbn [bind] in TL. rewrite NO2 in TL. cbn [bind] in TL.
        eapply RB; [exact TI4 | exact BD2 | exact B2 | exact R2 |].
        intros m5 v23 v24 v25 v28 v29 v30 v31 TI5.
        eapply (J2 m5 ((out ++ [o0]) ++ [o1]) s1a s2a d2r j0 (zlen out)); [exact TI5 | stc_len | lia | lia | |].
        * intros E. destruct f as [|f']; [cbn [tail_loop] in TL; subst r; contradiction RO|].
          cbn [tail_loop de_out] in TL. stc_if TL true. subst r. exact K.
        * intros OL5 u28.
          replace (zlen out + 2) with (zlen ((out ++ [o0]) ++ [o1])) by stc_len.
          eapply IH; [exact TL | exact RO | exact K | exact TI5 | exact S1A | exact S2A | exact BD2r | lia | exact OL5].
  Qed.

  Lemma stc_t1 : forall (f : nat) (x : dec) (r : res (list Z)),
    tail_loop bs dt dcap false f x = r -> res_ok r -> fdw_K SP gp tp F fc m0 DST dcap lo POST r ->
    fdw_t1_K SP gp tp F fc m0 S DT DST dcap lo bs dt POST x.
  Proof using All.
    intros f [out s1 s2 d] r TL RO K. unfold fdw_t1_K.
    intros m1 jp y1 y5 y6 y7 y10 y15 y16 y17 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 SMO STO MEM.
    unfold sm_okr, st_ok in *. cbn [de_out de_s1 de_s2 de_bd] in *.
    destruct SMO as (BD & BB & OL & OB). destruct STO as (S1 & S2).
    eapply TPREP; [exact MEM | exact OL | |].
    - intros E. destruct f as [|f]; [cbn [tail_loop] in TL; subst r; contradiction RO|].
      cbn [tail_loop de_out] in TL. stc_if TL true. subst r. exact K.
    - intros OL2 z1 z23 z24 z25 z26 z27 z28 z29 z30 z31.
      eapply stc_loop; [exact TL | exact RO | exact K | exists jp; exact MEM | exact S1 | exact S2 | exact BD | exact BB
                       | exact OL2].
  Qed.
End STC.

Theorem fdw_t1_proof : fdw_t1_stmt.
Proof.
  intros SP gp tp F fc m0 S DT DST dcap lo bs dt POST f x r PRE TL RO K.
  exact (stc_t1 SP gp tp F fc m0 S DT DST dcap lo bs dt POST PRE
           (st_head SP gp tp F fc m0 S DT DST dcap lo bs dt POST PRE)
           (st_finA SP gp tp F fc m0 S DT DST dcap lo bs dt POST PRE)
           (stb_rA SP gp tp F fc m0 S DT DST dcap lo bs dt POST PRE)
           (st_mid SP gp tp F fc m0 S DT DST dcap lo bs dt POST PRE)
           (stb_rB SP gp tp F fc m0 S DT DST dcap lo bs dt POST PRE)
           (stp_j2 SP gp tp F fc m0 S DT DST dcap lo bs dt POST PRE)
           (stp_tprep SP gp tp F fc m0 S DT DST dcap lo bs dt POST PRE) f x r TL RO K).
Qed.
