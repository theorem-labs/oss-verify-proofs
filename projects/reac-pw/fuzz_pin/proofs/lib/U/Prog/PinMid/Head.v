(** pin_mid_contract (UBSan), the head: from malloc's return at 0x12d50 (`beqz a0`, phi <> 0), memcpy(phi, src, k)
    when k <> 0 (0x12d68), the phi + k check (0x12d70, never taken), phi[k] = 0 (0x12d78), strlen(phi) (0x12d80),
    then [Tail.parse_call] when len = 0 and [Want.scan_loop] from tok = 0 otherwise. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Image.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog Require Import memcpy_c strlen_c fuzz_catalogue_row_c
  reac_box_pin_parse_c check_known_c check_row_c check_label_c LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog.PinMid Require Import Facts Tail Want.
Import ListNotations.
Open Scope Z_scope.

Section Head.
Variables (sp gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
          (s slack junk : list byte) (fl phi K lo src : Z) (can : word).
Hypothesis HK : Z.of_nat (length s) = K.
Hypothesis HPHI : 0 < phi.
Hypothesis HFL : 0 <= fl < 256.
Hypothesis HNUL : ~ In NUL s.
Hypothesis HSLM : (- (phi + K + 1)) mod 8 <= Z.of_nat (length slack).
Hypothesis HPB : phi + K + 1 + Z.of_nat (length slack) <= 2^64.
Hypothesis HLO0 : 0 <= lo.
Hypothesis HLO : lo + 224 <= bv_unsigned sp.
Hypothesis HSP : bv_unsigned sp + 24 <= 2^64.
Hypothesis HSPA : bv_unsigned sp mod 16 = 0.
Hypothesis HSN : forall a, lo <= a < bv_unsigned sp + 24 -> seg_rom rsegs (wa a) = None.
Hypothesis HDJ : phi + K + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp + 24 <= phi.
Hypothesis HRO : rom_out sp phi K.
Hypothesis HSRC : bytes_at rsegs m0 src s.
Hypothesis HRW : rw_cells rsegs m0 phi [CB (S (length s)) junk].
Hypothesis HSLB : bytes_at rsegs m0 (phi + K + 1) slack.
Hypothesis HDJS : src + K <= phi \/ phi + K <= src.
Hypothesis HMI0 : minv sp phi K lo can m0 m0.
Hypothesis MCPY : memcpy_contract.
Hypothesis STRL : strlen_contract.
Hypothesis FCR : fuzz_catalogue_row_contract.
Hypothesis PARSE : reac_box_pin_parse_contract.
Hypothesis CK : check_known_contract.
Hypothesis CR : check_row_contract.
Hypothesis CL : check_label_contract.

Local Abbreviation Q := (Qpost sp gp tp s6 s7 s8 s9 s10 s11 F fc m0 phi K lo).

Ltac refute_trap T := exfalso; zify_cond T; lia.

(** The NUL store at phi + k keeps the carried facts and completes the spec string. *)
Lemma nul_store : forall m1 jl,
  minv sp phi K lo can m0 m1 -> bytes_at rsegs m1 phi s -> rw_cells rsegs m1 (phi + K) [CB 1 jl] ->
  bytes_at rsegs m1 (phi + K + 1) slack ->
  minv sp phi K lo can m0 (write_to_mem m1 (wa (phi + K)) [Z_to_bv 8 0]) /\
  bytes_at rsegs (write_to_mem m1 (wa (phi + K)) [Z_to_bv 8 0]) phi (s ++ NUL :: slack).
Proof.
  intros m1 jl HM HS HC HSL.
  pose proof (rw_cells_store_ok rsegs m1 (phi + K) [CB 1 jl] 0 (CB 1 jl) 1 HC eq_refl eq_refl) as HOK.
  change (Z.of_nat 0) with 0 in HOK. rewrite Z.add_0_r in HOK.
  split.
  - apply minv_store; [exact HRO | exact HM | | lia | cbn [length]; lia | exact HOK].
    unfold mid_fp. cbn [inside length]. right. left. lia.
  - change (NUL :: slack) with ([NUL] ++ slack). rewrite app_assoc.
    apply bytes_at_app. split; [apply bytes_at_app; split|].
    + apply bytes_at_write_other; [exact HS | lia | cbn [length]; lia | rewrite HK; cbn [length]; lia].
    + rewrite HK. apply bytes_at_write_same; cbn [length]; lia.
    + replace (phi + Z.of_nat (length (s ++ [NUL]))) with (phi + K + 1) by (rewrite length_app; cbn [length]; lia).
      apply bytes_at_write_other; [exact HSL | lia | cbn [length]; lia | cbn [length]; lia].
Qed.

(** 0x12d6c, after the copy: the phi + k check, phi[k] = 0, strlen(phi), and the branch on len. *)
Lemma after_copy : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 : word)
    (m1 : word -> option byte) (jl : list byte),
  s0 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 K -> s3 = Z_to_bv 64 fl ->
  minv sp phi K lo can m0 m1 -> bytes_at rsegs m1 phi s -> rw_cells rsegs m1 (phi + K) [CB 1 jl] ->
  bytes_at rsegs m1 (phi + K + 1) slack ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x12d6c) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m1 jl -> -> -> HM HS HC HSL.
  destruct (nul_store m1 jl HM HS HC HSL) as [HM2 HS2].
  pose proof (rw_cells_store_ok rsegs m1 (phi + K) [CB 1 jl] 0 (CB 1 jl) 1 HC eq_refl eq_refl) as HOK.
  change (Z.of_nat 0) with 0 in HOK. rewrite Z.add_0_r in HOK.
  clear HC HS HSL.
  zstep. rewrite ?zb_lxor_ones by lia.
  zstep. if_cases T0; [refute_trap T0|].
  zstep. step.
  lazymatch goal with |- evt _ _ (MS ?R ?F' ?pc ?fc' ?rv (write_to_mem ?mm ?a ?bs) ?ro) =>
    change (write_to_mem mm a bs) with (write_to_mem mm (wa (phi + K)) [Z_to_bv 8 0])
  end.
  remember (write_to_mem m1 (wa (phi + K)) [Z_to_bv 8 0]) as m2 eqn:Em2. clear Em2 HOK HM.
  zstep. zstep.
  eapply evt_cut.
  { eapply STRL with (str := s) (slack := slack).
    - rewrite unsigned_lit by lia. exact HS2.
    - exact HNUL.
    - rewrite unsigned_lit by lia. rewrite HK. exact HSLM.
    - exact (proj1 (proj2 (proj2 HM2))). }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & -> &
              MU3 & WM3 & MI3 & HS3).
  fix_ret.
  rewrite unsigned_lit in HS3 by lia.
  pose proof (stk_transport_disjoint rsegs [] m2 m3 lo (bv_unsigned sp)
                (proj1 (proj2 (proj2 (proj2 HM2)))) MU3 WM3 I) as ST3.
  assert (HM3 : minv sp phi K lo can m0 m3)
    by (eapply minv_call; [exact HRO | exact HM2 | exact MU3 | fp_tac | exact WM3 | exact MI3 | exact ST3]).
  clear HM2 HS2 MU3 WM3 MI3 ST3.
  rewrite HK.
  zstep. if_cases EL.
  - (* len = 0 *)
    zify_cond EL. zstep. zstep.
    assert (Hs0 : length s = 0%nat) by lia.
    destruct (want_len0 FUZZ_CATALOGUE phi fl s Hs0) as [W1 W2].
    eapply (parse_call sp gp tp s6 s7 s8 s9 s10 s11 F fc m0 s slack fl phi K lo can); try eassumption;
      rewrite ?W1, ?W2; reflexivity.
  - (* len <> 0: the scan from tok = 0 *)
    zify_cond EL. zstep. zstep.
    eapply (scan_loop sp gp tp s6 s7 s8 s9 s10 s11 F fc m0 s slack fl phi K lo can) with
      (n := (length s - 1)%nat) (tok := 0%nat); try eassumption; try reflexivity.
    + lia.
    + intros j Hj. lia.
Qed.

(** 0x12d50: phi <> 0, s0 = phi, memcpy(phi, src, k) when k <> 0, then [after_copy]. *)
Lemma mid_entry : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 : word),
  a0 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 K -> s1 = Z_to_bv 64 src -> s3 = Z_to_bv 64 fl ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 PIN_MID) fc None m0 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 -> -> -> ->.
  unfold PIN_MID.
  pose proof (bytes_at_bound rsegs m0 src s HSRC) as BSRC.
  destruct (rw_cells_CB_last m0 phi (length s) junk HRW) as [HC1 HC2].
  rewrite HK in HC2.
  zstep. if_cases E0; [zify_cond E0; lia|].
  zstep. zstep. if_cases EK.
  - (* k = 0: no copy *)
    zify_cond EK.
    assert (Hs0 : s = []) by (apply length_zero_iff_nil; lia).
    eapply after_copy; try eassumption; try reflexivity.
    rewrite Hs0. apply bytes_at_nil. lia.
  - zify_cond EK.
    zstep. zstep. zstep. zstep.
    eapply evt_cut.
    { eapply MCPY with (src := s) (junk := firstn (length s) junk).
      - rewrite unsigned_lit by lia. exact HSRC.
      - rewrite unsigned_lit by lia. lia.
      - rewrite !unsigned_lit by lia. replace (Z.to_nat K) with (length s) by lia. exact HC1.
      - rewrite !unsigned_lit by lia. lia.
      - exact (proj1 (proj2 (proj2 HMI0))). }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> &
                MU1 & WM1 & MI1 & HC1' & _).
    fix_ret.
    rewrite !unsigned_lit in MU1, HC1' by lia.
    pose proof (stk_transport_disjoint rsegs _ m0 m1 lo (bv_unsigned sp)
                  (proj1 (proj2 (proj2 (proj2 HMI0)))) MU1 WM1 ltac:(cbn [disjoint_from]; split; [lia | exact I]))
      as ST1.
    assert (HM1 : minv sp phi K lo can m0 m1)
      by (eapply minv_call; [exact HRO | exact HMI0 | exact MU1 | fp_tac | exact WM1 | exact MI1 | exact ST1]).
    eapply after_copy with (m1 := m1); try eassumption; try reflexivity.
    + exact (rw_cells_CB_bytes _ _ _ _ HC1').
    + apply (rw_cells_transport rsegs _ m0 m1 _ _ HC2 MU1 WM1). cbn [disjoint_from cells_size csize]. split; [lia | exact I].
    + apply (bytes_at_transport rsegs _ m0 m1 _ _ HSLB MU1). cbn [disjoint_from]. split; [lia | exact I].
Qed.

End Head.
