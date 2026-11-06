(** check_csv's tail (plain image), 0x14820 .. ret: `bne s1, a7` (len = n, not taken); `beqz a1`: buflen = 0 reads
    buf[0] = 0x5a; else c = min(len, buflen - 1), bcmp(buf, want, c) = 0, buf[c] = 0; then the epilogue. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import RateCfg RateCsv.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import bcmp_c ccsv_lem.
Import ListNotations.
Open Scope Z_scope.

Lemma rw_cells_cb_len2 : forall segs m A a x b y rest,
  rw_cells segs m A (CB a x :: CB b y :: rest) -> length x = a /\ length y = b.
Proof. intros segs m A a x b y rest [[(H1 & H2 & _) _] _]. split; assumption. Qed.

(** want's first |csv_cut L n| bytes are csv_cut L n. *)
Lemma ccsv_want_prefix : forall L n (wj : list byte), 1 <= n ->
  csv_bytes (csv_cut L n) = firstn (length (csv_cut L n)) (csv_bytes L ++ wj).
Proof.
  intros L n wj Hn. rewrite firstn_app, csv_bytes_length.
  replace (length (csv_cut L n) - length L)%nat with 0%nat by (rewrite csv_cut_length by lia; lia).
  rewrite firstn_O, app_nil_r. unfold csv_bytes. rewrite firstn_map. f_equal. apply csv_cut_firstn.
Qed.

Section CCSV.
Variables (ra gp tp s0 s1 e2 e3 e4 s5 s6 s7 s8 s9 s10 s11 bufw lenw a1 a3 : word) (F : bvmap 5 word) (fc : bv 32)
  (Sp lo : Z) (m0 : word -> option byte).
Hypothesis RS0 : 0 <= Sp + -96.
Hypothesis RS1 : Sp <= 2^64.

Local Abbreviation SV := (ccsv_SV ra s0 s1 e2 e3 e4).
Local Abbreviation CS := (ccsv_CS ra gp tp bufw lenw a1 a3 s5 s6 s7 s8 s9 s10 s11 F fc Sp).
Local Abbreviation POST := (ccsv_post ra gp tp s0 s1 e2 e3 e4 s5 s6 s7 s8 s9 s10 s11 F fc Sp lo m0).

Lemma ccsv_tail : forall (m : word -> option byte) (dj wj : list byte) (y18 y19 y20 y29 y30 y31 : word),
  bcmp_contract ->
  bv_unsigned lenw = Z.of_nat (length (csv_list (bv_unsigned a3))) -> bv_unsigned a1 <= 23 ->
  (bv_unsigned a1 = 0 -> bytes_at rsegs m0 (bv_unsigned bufw) [Z_to_bv 8 0x5a]) ->
  (0 < bv_unsigned a1 ->
     bytes_at rsegs m0 (bv_unsigned bufw) (csv_bytes (csv_cut (csv_list (bv_unsigned a3)) (bv_unsigned a1) ++ [0]))) ->
  (bv_unsigned bufw + Z.max (bv_unsigned a1) 1 <= lo \/ Sp <= bv_unsigned bufw) -> lo + 96 <= Sp ->
  rw_cells rsegs m (Sp + -96) (CB 8 dj :: CB 40 (csv_bytes (csv_list (bv_unsigned a3)) ++ wj) :: SV) ->
  munch [(Sp + -96, Sp)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m lo (Sp + -96) ->
  evt rsegs POST (CS 0x14820 3 (Z.of_nat (length (csv_list (bv_unsigned a3)))) y18 y19 y20 y29 y30 y31 m).
Proof.
  intros m dj wj y18 y19 y20 y29 y30 y31 BC HL HN HB0 HB1 HBS HLO FR MU WM MI ST.
  unfold bcmp_contract, BCMP in BC.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. pose proof (bv_unsigned_in_range 64 bufw) as Rb.
  pose proof (bv_unsigned_in_range 64 a3) as Ra3. unfold bv_modulus in Ra1, Rb, Ra3.
  assert (LL : (length (csv_list (bv_unsigned a3)) <= 17)%nat) by (apply csv_list_length; lia).
  assert (Elen : lenw = Z_to_bv 64 (Z.of_nat (length (csv_list (bv_unsigned a3))))).
  { rewrite <- HL. symmetry. apply Z_to_bv_lit_self. }
  assert (Ea1 : a1 = Z_to_bv 64 (bv_unsigned a1)) by (symmetry; apply Z_to_bv_lit_self).
  set (L := csv_list (bv_unsigned a3)) in *. set (n := bv_unsigned a1) in *. clearbody L n.
  pose proof (rw_cells_cb_len2 _ _ _ _ _ _ _ _ FR) as [Ldj Lw].
  unfold ccsv_CS, ccsv_SV in *. rewrite Elen, Ea1.
  (* 0x14820 bne s1, a7: s1 = a7 = |L| *)
  cstep. cbr.
  (* 0x14824 beqz a1 *)
  cstep. rewrite eqb_lit by lia. destruct (Z.eqb_spec n 0) as [N0|N0]; cbv iota.
  - (* buflen = 0: 0x14874 lbu a0, 0(s0); addi a1, zero, 0x5a; beq a0, a1 -> 0x14854 *)
    specialize (HB0 N0).
    apply (bytes_at_transport rsegs [(Sp + -96, Sp)] m0 m) in HB0;
      [ | exact MU | cbn [disjoint_from length]; split; [lia | exact I] ].
    assert (HR : ov_read_bytes rsegs m bufw 1 = Some [Z_to_bv 8 0x5a]).
    { pose proof (bytes_at_ov_read rsegs m _ _ 0 1 HB0 ltac:(cbn; lia)) as R. cbn [firstn skipn] in R.
      rewrite <- R. f_equal. symmetry. apply wa_of_var. lia. }
    cstep. cstep. cstep. cbr.
    (* 0x14854: ld ra, s0-s4; addi sp, sp, 0x60; ret *)
    do 8 cstep.
    release_frame FR ST Sp.
    finish.
  - (* buflen > 0 *)
    specialize (HB1 ltac:(lia)).
    assert (LC : length (csv_cut L n) = Z.to_nat (Z.min (Z.of_nat (length L)) (n - 1))) by (apply csv_cut_length; lia).
    remember (Z.min (Z.of_nat (length L)) (n - 1)) as cc eqn:Ecc.
    rewrite csv_bytes_app in HB1. change (csv_bytes [0]) with [Z_to_bv 8 0] in HB1.
    apply (bytes_at_transport rsegs [(Sp + -96, Sp)] m0 m) in HB1;
      [ | exact MU | cbn [disjoint_from]; rewrite length_app, csv_bytes_length, LC; cbn [length]; split; [lia | exact I] ].
    apply bytes_at_app in HB1. destruct HB1 as [Hbuf Hnul].
    assert (Hwant : bytes_at rsegs m (Sp + -88) (csv_bytes (csv_cut L n))).
    { pose proof FR as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. apply bytes_at_app in Hb. destruct Hb as [_ Hb].
      rewrite Ldj in Hb. apply bytes_at_app in Hb. destruct Hb as [Hb _].
      rewrite (ccsv_want_prefix L n wj) by lia. apply bytes_at_firstn.
      replace (Sp + -88) with (Sp + -96 + Z.of_nat 8) by lia. exact Hb. }
    (* 0x14828 addi a1, a1, -1; bltu s1, a1 *)
    cstep. cstep. rewrite ltu_lit by lia.
    destruct (Z.ltb_spec (Z.of_nat (length L)) (n + -1)) as [LT|GE]; cbv iota;
      [ replace (Z_to_bv 64 (Z.of_nat (length L))) with (Z_to_bv 64 cc) by (f_equal; lia)
      | cstep; replace (Z_to_bv 64 (n + -1)) with (Z_to_bv 64 cc) by (f_equal; lia) ].
    (* 0x14834 addi a1, sp, 8; mv a0, s0; mv a2, s1; jal bcmp *)
    all: cstep; cstep; cstep; cstep.
    all: eapply evt_cut;
      [ eapply BC with (ls := csv_bytes (csv_cut L n)) (rs := csv_bytes (csv_cut L n)) (v := 0);
        [ exact Hbuf
        | rewrite unsigned_lit by lia; exact Hwant
        | rewrite unsigned_lit by lia; apply ccsv_memcmp; rewrite csv_bytes_length, LC; lia
        | exact MI ]
      | post_call rsegs m ].
    (* 0x14844 bnez a0 (a0 = 0); add s0, s0, s1; lbu a0, 0(s0) with buf[c] = 0; bnez a0 *)
    all: cstep; cbr; cstep.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
             assert (HR : ov_read_bytes rsegs mm (Z_to_bv 64 (bv_unsigned bufw + cc)) 1 = Some [Z_to_bv 8 0]);
             [ pose proof (bytes_at_ov_read rsegs mm _ _ 0 1 Hnul ltac:(cbn; lia)) as R; cbn [firstn skipn] in R;
               rewrite <- R; f_equal; unfold wa; f_equal; rewrite csv_bytes_length, LC; lia | ]
         end.
    all: cstep; cstep; cbr.
    (* 0x14854: ld ra, s0-s4; addi sp, sp, 0x60; ret *)
    all: do 8 cstep.
    all: release_frame FR ST Sp.
    all: finish.
Qed.

End CCSV.
