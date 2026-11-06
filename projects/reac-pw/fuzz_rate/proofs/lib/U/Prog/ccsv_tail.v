(** The tail of check_csv in the UBSan image (0x14994 .. 0x14a14), after the loop: want's first |L| bytes hold
    csv_bytes L with L = csv_list mask, t6 = |L|.
      0x14994 `bne s1,t6` (len = |L|: not taken); `beqz a1`:
        buflen = 0: 0x14a04 `lbu a0,0(s0)` reads main's 0x5a, `beq` to the epilogue 0x149d0;
        buflen > 0: c = min(|L|, buflen - 1) (0x1499c .. 0x149a4), bcmp(buf, want, c) (0x149b4 -> 0x1d1e0): buf's
          first c bytes and want's first c bytes are csv_bytes (csv_cut L buflen), so bcmp returns 0 and `bnez` is
          not taken; the trap test 0x149c0 `bltu ~buf,c` is not taken (buf + c + 1 <= 2^64, buf's bytes_at bound);
          `lbu buf[c]` reads the NUL, `bnez` not taken;
      0x149d0 .. 0x14a00 restores ra, s0-s9, frees the frame, ret. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge Image.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import RateCfg RateCsv.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import bcmp_c ccsv_lemmas.
Import ListNotations.
Open Scope Z_scope.

(** From 0x149a8 (c = min(|L|, buflen - 1) in s1, a1 = buflen - 1) to the return. *)
Lemma ccsv_cmp : bcmp_contract ->
  forall (L : list Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a3 x18 x19 x20 x21 x22 x23 x24 x25 : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (lo Sp c : Z) (j : list byte),
    (length L <= 17)%nat ->
    0 < bv_unsigned a1 -> bv_unsigned a1 <= 23 -> c = Z.min (Z.of_nat (length L)) (bv_unsigned a1 - 1) ->
    bytes_at rsegs m (bv_unsigned a0) (csv_bytes (csv_cut L (bv_unsigned a1) ++ [0])) ->
    0 <= lo -> lo + 144 <= Sp -> Sp <= 2^64 ->
    rw_cells rsegs m (Sp + -144) (CB 56 j :: ccsv_saves ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) ->
    bytes_at rsegs m (Sp + -128) (csv_bytes L) ->
    stk rsegs m lo (Sp + -144) -> munch [(Sp + -144, Sp)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
    evt rsegs (ccsv_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Sp F fc m0 lo)
      (MS (mkR ra (Z_to_bv 64 (Sp + -144)) gp tp (Z_to_bv 64 (Sp + -128)) (Z_to_bv 64 18446744073709551576)
               (Z_to_bv 64 39) a0 (Z_to_bv 64 c) (Z_to_bv 64 3) (Z_to_bv 64 (bv_unsigned a1 + -1)) (Z_to_bv 64 3) a3
               (Z_to_bv 64 8) (Z_to_bv 64 10) (Z_to_bv 64 (Sp + -136)) (Z_to_bv 64 18) x18 x19 x20 x21 x22 x23 x24
               x25 s10 s11 (Z_to_bv 64 67112) (Z_to_bv 64 1717986919) (Z_to_bv 64 44)
               (Z_to_bv 64 (Z.of_nat (length L))))
          F (Z_to_bv 64 0x149a8) fc None m (seg_rom rsegs)).
Proof.
  intros BC L ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a3 x18 x19 x20 x21 x22 x23 x24 x25 F fc m0 m
    lo Sp c j HL Hn0 Hn Hc Hbuf Hlo HK Hhi FR HW ST MU WM MI.
  unfold ccsv_saves in FR.
  pose proof (bv_unsigned_in_range 64 a0) as R0. change (bv_modulus 64) with (2^64) in R0.
  assert (Hcut : length (csv_cut L (bv_unsigned a1)) = Z.to_nat c)
    by (rewrite csv_cut_length by lia; rewrite Hc; reflexivity).
  assert (Hlen : length (csv_bytes (csv_cut L (bv_unsigned a1) ++ [0])) = (Z.to_nat c + 1)%nat)
    by (rewrite csv_bytes_length, length_app, Hcut; cbn [length]; lia).
  pose proof (bytes_at_bound _ _ _ _ Hbuf) as HBB. rewrite Hlen in HBB.
  assert (HB1 : bytes_at rsegs m (bv_unsigned a0) (csv_bytes (csv_cut L (bv_unsigned a1)))).
  { pose proof Hbuf as Hb'. rewrite csv_bytes_app in Hb'. apply (proj1 (bytes_at_app _ _ _ _ _)) in Hb'.
    exact (proj1 Hb'). }
  assert (E : csv_cut L (bv_unsigned a1) ++ skipn (length (csv_cut L (bv_unsigned a1))) L = L).
  { rewrite csv_cut_length by lia. unfold csv_cut. apply firstn_skipn. }
  assert (HB2 : bytes_at rsegs m (Sp + -128) (csv_bytes (csv_cut L (bv_unsigned a1)))).
  { pose proof HW as Hw'. rewrite <- E in Hw'. rewrite csv_bytes_app in Hw'.
    apply (proj1 (bytes_at_app _ _ _ _ _)) in Hw'. exact (proj1 Hw'). }
  clear E.
  (* addi a1,sp,16; mv a0,s0; mv a2,s1; jal bcmp *)
  step. step. step. step.
  eapply evt_cut.
  { eapply BC with (ls := csv_bytes (csv_cut L (bv_unsigned a1))) (rs := csv_bytes (csv_cut L (bv_unsigned a1)))
                   (v := 0).
    - exact HB1.
    - rewrite unsigned_lit by lia. exact HB2.
    - rewrite unsigned_lit by lia. apply ccsv_memcmp. rewrite csv_bytes_length, Hcut. lia.
    - exact MI. }
  post_call rsegs m.
  (* bnez a0 (a0 = 0); not a0,s0; bltu a0,s1 (the pointer-overflow trap test: not taken) *)
  step. br. step. rewrite zb_lxor_ones by lia. step. zbr.
  (* add s0,s0,s1; lbu a0,0(s0) reads buf[c] = 0 *)
  step.
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with
      | Hb : bytes_at rsegs mm (bv_unsigned a0) (csv_bytes (csv_cut L (bv_unsigned a1) ++ [0])) |- _ =>
          pose proof (bytes_at_read rsegs mm (bv_unsigned a0) _ c 1 Hb ltac:(lia) ltac:(rewrite Hlen; lia)) as HR
      end
  end.
  rewrite csv_bytes_app in HR.
  replace (Z.to_nat c) with (length (csv_bytes (csv_cut L (bv_unsigned a1)))) in HR
    by (rewrite csv_bytes_length; exact Hcut).
  rewrite skipn_app_exact in HR. cbn [csv_bytes map firstn] in HR.
  step. step. br.
  (* epilogue *)
  do 13 step.
  release_frame FR ST Sp.
  finish.
Qed.

(** From the loop's exit 0x14994 to the return. *)
Lemma ccsv_tail : bcmp_contract ->
  forall (L : list Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a3 x18 x19 x20 x21 x22 x23 x24 x25 : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (lo Sp : Z) (j : list byte),
    (length L <= 17)%nat ->
    bv_unsigned a1 <= 23 ->
    (bv_unsigned a1 = 0 -> bytes_at rsegs m0 (bv_unsigned a0) [Z_to_bv 8 0x5a]) ->
    (0 < bv_unsigned a1 -> bytes_at rsegs m0 (bv_unsigned a0) (csv_bytes (csv_cut L (bv_unsigned a1) ++ [0]))) ->
    (bv_unsigned a0 + Z.max (bv_unsigned a1) 1 <= lo \/ Sp <= bv_unsigned a0) ->
    0 <= lo -> lo + 144 <= Sp -> Sp <= 2^64 ->
    rw_cells rsegs m (Sp + -144) (CB 56 j :: ccsv_saves ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) ->
    bytes_at rsegs m (Sp + -128) (csv_bytes L) ->
    stk rsegs m lo (Sp + -144) -> munch [(Sp + -144, Sp)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
    evt rsegs (ccsv_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Sp F fc m0 lo)
      (hd_st 0x14994 3 (Z.of_nat (length L)) Sp ra gp tp a0 (Z_to_bv 64 (Z.of_nat (length L))) a1 a3
             x18 x19 x20 x21 x22 x23 x24 x25 s10 s11 F fc m).
Proof.
  intros BC L ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a3 x18 x19 x20 x21 x22 x23 x24 x25 F fc m0 m
    lo Sp j HL Hn H0 Hpos Hdj Hlo HK Hhi FR HW ST MU WM MI.
  unfold hd_st.
  pose proof (bv_unsigned_in_range 64 a0) as R0. pose proof (bv_unsigned_in_range 64 a1) as R1.
  change (bv_modulus 64) with (2^64) in R0, R1.
  (* bne s1,t6: len = |L| *)
  step. zbr.
  (* beqz a1 *)
  step.
  destruct (Z.eq_dec (bv_unsigned a1) 0) as [E0|N0].
  - zbr.
    assert (Hb : bytes_at rsegs m (bv_unsigned a0) [Z_to_bv 8 90]).
    { apply (bytes_at_transport rsegs [(Sp + -144, Sp)] m0 m); [exact (H0 E0) | exact MU |].
      cbn [disjoint_from length]. rewrite E0 in Hdj. split; [lia | exact I]. }
    assert (HR : ov_read_bytes rsegs m a0 1 = Some [Z_to_bv 8 90]).
    { replace a0 with (wa (bv_unsigned a0 + Z.of_nat 0)) by (apply wa_of_var; lia).
      rewrite (bytes_at_ov_read rsegs m (bv_unsigned a0) [Z_to_bv 8 90] 0 1 Hb) by (cbn; lia). reflexivity. }
    (* lbu a0,0(s0); li a1,0x5a; beq a0,a1 (taken) *)
    step. step. step. br.
    unfold ccsv_saves in FR.
    do 13 step.
    release_frame FR ST Sp.
    finish.
  - zbr.
    pose proof (Hpos ltac:(lia)) as Hb0.
    assert (Hb : bytes_at rsegs m (bv_unsigned a0) (csv_bytes (csv_cut L (bv_unsigned a1) ++ [0]))).
    { apply (bytes_at_transport rsegs [(Sp + -144, Sp)] m0 m); [exact Hb0 | exact MU |].
      cbn [disjoint_from]. rewrite csv_bytes_length, length_app, csv_cut_length by lia. cbn [length].
      split; [lia | exact I]. }
    clear Hb0.
    (* addi a1,a1,-1; bltu s1,a1 *)
    step. step.
    destruct (Z_lt_le_dec (Z.of_nat (length L)) (bv_unsigned a1 + -1)) as [Lt|Ge].
    + zbr.
      eapply (ccsv_cmp BC L); try eassumption; lia.
    + zbr. step.
      eapply (ccsv_cmp BC L); try eassumption; lia.
Qed.

(** From the loop's exit as the passes leave it (hd_mem with prefix P = L) to the return. *)
Lemma ccsv_fin : bcmp_contract ->
  forall (P : list Z) (n' : Z)
         (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a3 x18 x19 x20 x21 x22 x23 x24 x25 : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (lo Sp : Z),
    csv_list (bv_unsigned a3) = P -> n' = Z.of_nat (length P) ->
    bv_unsigned a1 <= 23 ->
    (bv_unsigned a1 = 0 -> bytes_at rsegs m0 (bv_unsigned a0) [Z_to_bv 8 0x5a]) ->
    (0 < bv_unsigned a1 ->
       bytes_at rsegs m0 (bv_unsigned a0) (csv_bytes (csv_cut (csv_list (bv_unsigned a3)) (bv_unsigned a1) ++ [0]))) ->
    (bv_unsigned a0 + Z.max (bv_unsigned a1) 1 <= lo \/ Sp <= bv_unsigned a0) ->
    0 <= lo -> lo + 144 <= Sp -> Sp <= 2^64 ->
    hd_mem Sp lo m0 m P (ccsv_saves ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) ->
    evt rsegs (ccsv_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Sp F fc m0 lo)
      (hd_st 0x14994 3 n' Sp ra gp tp a0 (Z_to_bv 64 (Z.of_nat (length (csv_list (bv_unsigned a3))))) a1 a3
             x18 x19 x20 x21 x22 x23 x24 x25 s10 s11 F fc m).
Proof.
  intros BC P n' ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a3 x18 x19 x20 x21 x22 x23 x24 x25 F fc m0 m
    lo Sp HP Hn' Hn H0 Hpos Hdj Hlo HK Hhi HM.
  destruct HM as (j0 & dj & wj & FR & ST & MU & WM & MI).
  assert (HL : (length (csv_list (bv_unsigned a3)) <= 17)%nat).
  { apply csv_list_length. pose proof (bv_unsigned_in_range 64 a3). lia. }
  rewrite HP in HL. assert (HL40 : (length P <= 40)%nat) by lia.
  destruct (ccsv_cells56 _ _ _ _ _ _ _ HL40 FR) as [[j FR56] HW]. clear HL40.
  replace (Sp + -144 + 16) with (Sp + -128) in HW by lia.
  rewrite <- HP in HW, HL. subst n'. rewrite <- HP.
  eapply (ccsv_tail BC (csv_list (bv_unsigned a3))); eassumption.
Qed.
