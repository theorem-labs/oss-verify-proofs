(** pin_mid_contract (UBSan), the expectation: the scan for the first ':' (0x12d90 .. 0x12da8), want =
    fuzz_catalogue_row(spec, tok) when flags & 7 = 0 (0x12e68), and want_label (0x12e74 .. 0x12ea8), up to
    [Tail.parse_call] at 0x12dbc. The UBSan checks on the way (0x12d90, 0x12e7c, 0x12e94, 0x12ea0) never fire. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Image.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog Require Import fuzz_catalogue_row_c reac_box_pin_parse_c
  check_known_c check_row_c check_label_c LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog.PinMid Require Import Facts Tail.
Import ListNotations.
Open Scope Z_scope.

Section Want.
Variables (sp gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
          (s slack : list byte) (fl phi K lo : Z) (can : word).
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
Hypothesis FCR : fuzz_catalogue_row_contract.
Hypothesis PARSE : reac_box_pin_parse_contract.
Hypothesis CK : check_known_contract.
Hypothesis CR : check_row_contract.
Hypothesis CL : check_label_contract.

Local Abbreviation Q := (Qpost sp gp tp s6 s7 s8 s9 s10 s11 F fc m0 phi K lo).

Ltac to_parse :=
  eapply (parse_call sp gp tp s6 s7 s8 s9 s10 s11 F fc m0 s slack fl phi K lo can);
  try eassumption; try reflexivity.

Ltac refute_trap T := exfalso; zify_cond T; lia.

(** 0x12dac, after the scan: tok = colon_idx s in s2, the last byte read in s5. *)
Lemma want_block : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 : word)
    (m : word -> option byte) (b : byte),
  s0 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 (Z.of_nat (colon_idx s)) -> s3 = Z_to_bv 64 fl ->
  s4 = Z_to_bv 64 (18446744073709551615 - phi) -> s5 = Z_to_bv 64 (bv_unsigned b) ->
  (bv_unsigned b = COLON <-> (colon_idx s < length s)%nat) -> length s <> 0%nat ->
  minv sp phi K lo can m0 m -> bytes_at rsegs m phi (s ++ NUL :: slack) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x12dac) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m b -> -> -> -> -> Hb Hn HM HS.
  pose proof (colon_idx_le s) as Hci.
  pose proof (bv_unsigned_in_range 8 b) as Rb. change (bv_modulus 8) with 256 in Rb.
  set (tok := colon_idx s) in *.
  zstep. zstep.
  if_cases E7.
  2: { (* flags & 7 <> 0: want = NULL *)
    zify_cond E7. zstep. zstep.
    destruct (want_flags FUZZ_CATALOGUE phi fl s E7) as [W1 W2].
    to_parse; rewrite ?W1, ?W2; reflexivity. }
  zify_cond E7.
  zstep. zstep. zstep.
  pose proof (bytes_at_app rsegs m phi s (NUL :: slack)) as [HSA _]. destruct (HSA HS) as [HSs _]. clear HSA.
  eapply evt_cut.
  { eapply FCR with (sb := firstn tok s) (lo := lo).
    - apply bytes_at_firstn. rewrite unsigned_lit by lia. exact HSs.
    - rewrite unsigned_lit by lia. rewrite firstn_length_le by lia. reflexivity.
    - exact (proj1 (proj2 (proj2 (proj2 HM)))).
    - unfold FCR_STACK. lia.
    - intros a Ha. apply HSN. lia.
    - rewrite firstn_length_le by lia. rewrite unsigned_lit by lia. lia.
    - exact (minv_cat _ _ _ _ _ _ _ HM).
    - exact (proj1 (proj2 (proj2 HM))). }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> &
              MU1 & WM1 & MI1 & ST1).
  fix_ret.
  assert (HM1 : minv sp phi K lo can m0 m1)
    by (eapply minv_call; [exact HRO | exact HM | exact MU1 | fp_tac | exact WM1 | exact MI1 | exact ST1]).
  assert (HS1 : bytes_at rsegs m1 phi (s ++ NUL :: slack)).
  { apply (bytes_at_transport rsegs _ m m1 _ _ HS MU1). cbn [disjoint_from]. rewrite length_app. cbn [length].
    unfold FCR_STACK. split; [lia | exact I]. }
  clear HM HS HSs MU1 WM1 MI1 ST1.
  unfold row_ptr.
  destruct (row_of (firstn tok s)) as [i|] eqn:Er.
  2: { (* no row: want = NULL *)
    zstep. try (if_cases E0; [|zify_cond E0; lia]).
    zstep. zstep.
    destruct (want_none FUZZ_CATALOGUE phi fl s E7 Hn Er) as [W1 W2].
    to_parse; rewrite ?W1, ?W2; reflexivity. }
  pose proof (row_of_lt _ _ Er) as Hi.
  assert (HRA : 0 < row_addr FUZZ_CATALOGUE i < 2^64)
    by (unfold row_addr, CAT_ROW, FUZZ_CATALOGUE, CAT_N in *; lia).
  destruct (want_some FUZZ_CATALOGUE phi fl s i E7 Hn Er) as [W1 W2].
  zstep. if_cases E0; [zify_cond E0; lia|].
  zstep. zstep. zstep.
  (* the display path, shared by both cases where there is no label in the spec *)
  assert (DISP : forall (ra' t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' s2' s4' s5' t3'' t4'' t5'' t6'' : word),
             harness_label_off s = None ->
             evt rsegs Q (MS (mkR ra' sp gp tp t0'' t1'' t2'' (Z_to_bv 64 phi) (Z_to_bv 64 (row_addr FUZZ_CATALOGUE i))
                                  a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' s2' (Z_to_bv 64 fl) s4' s5'
                                  s6 s7 s8 s9 s10 s11 t3'' t4'' t5'' t6'')
                             F (Z_to_bv 64 0x12e9c) fc None m1 (seg_rom rsegs))).
  { intros ra' t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' s2' s4' s5' t3'' t4'' t5'' t6'' HL.
    zstep. zstep.
    if_cases T8.
    { exfalso. zify_cond T8. apply T8. change 7 with (Z.ones 3). rewrite Z.land_ones by lia.
      exact (row_addr_mod8 FUZZ_CATALOGUE i cat_mod8). }
    pose proof (disp_read m1 i (minv_cat _ _ _ _ _ _ _ HM1) Hi) as HRD.
    zstep. zstep.
    to_parse; rewrite ?W1, ?W2, ?HL; reflexivity. }
  if_cases EC.
  - (* s5 <> ':': the scan ran to the end *)
    zify_cond EC. eapply DISP.
    apply label_off_end.
    destruct (Nat.eq_dec tok (length s)) as [Ht|Ht]; [exact Ht|].
    exfalso. apply EC. apply Hb. lia.
  - (* s5 = ':' *)
    zify_cond EC. assert (Hlt : (tok < length s)%nat) by (apply Hb; exact EC).
    zstep. if_cases T1; [refute_trap T1|].
    zstep. zstep.
    assert (HRB : ov_read_bytes rsegs m1 (wa (phi + Z.of_nat tok + 1)) 1
                  = Some [nth (S tok) (s ++ NUL :: slack) NUL]).
    { replace (phi + Z.of_nat tok + 1) with (phi + Z.of_nat (S tok)) by lia.
      apply bytes_at_nth; [exact HS1|]. rewrite length_app. cbn [length]. lia. }
    rewrite (nth_app_slack s slack (S tok)) in HRB by lia.
    pose proof (bv_unsigned_in_range 8 (nth (S tok) (s ++ [NUL]) NUL)) as Rc. change (bv_modulus 8) with 256 in Rc.
    pose proof (label_off_colon s Hlt) as HLC. fold tok in HLC.
    zstep. zstep.
    if_cases EZ.
    + (* the byte after ':' is NUL: no label *)
      zify_cond EZ. eapply DISP. rewrite HLC. rewrite EZ. reflexivity.
    + zify_cond EZ.
      zstep. zstep. if_cases T2; [|refute_trap T2].
      apply Z.eqb_neq in EZ.
      to_parse; rewrite ?W1, ?W2, ?HLC, ?EZ; [reflexivity | cbv beta iota; f_equal; lia].
Qed.

(** The scan 0x12d90 .. 0x12da8 from tok, n bytes before the end of s. *)
Lemma scan_loop : forall (n tok : nat) (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 : word)
    (m : word -> option byte),
  (tok + S n = length s)%nat ->
  s0 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 (Z.of_nat tok) -> a0 = Z_to_bv 64 K -> a1 = Z_to_bv 64 58 ->
  s3 = Z_to_bv 64 fl -> s4 = Z_to_bv 64 (18446744073709551615 - phi) ->
  (forall j, (j < tok)%nat -> bv_unsigned (nth j s NUL) <> COLON) ->
  minv sp phi K lo can m0 m -> bytes_at rsegs m phi (s ++ NUL :: slack) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x12d90) fc None m (seg_rom rsegs)).
Proof.
  induction n as [|n IH];
    intros tok ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m Hn -> -> -> -> -> -> Hpre HM HS.
  all: assert (Hlt : (tok < length s)%nat) by lia.
  all: assert (HRB : ov_read_bytes rsegs m (wa (phi + Z.of_nat tok)) 1 = Some [nth tok s NUL])
         by (rewrite (bytes_at_nth m phi _ tok HS) by (rewrite length_app; cbn [length]; lia);
             rewrite app_nth1 by exact Hlt; reflexivity).
  all: pose proof (bv_unsigned_in_range 8 (nth tok s NUL)) as Rb; change (bv_modulus 8) with 256 in Rb.
  all: zstep; if_cases T0; [refute_trap T0|].
  all: zstep; zstep; zstep.
  all: if_cases EC.
  1, 3: (* s[tok] = ':' *)
    zify_cond EC;
    assert (Hci : colon_idx s = tok) by (apply colon_idx_eq; [lia | exact Hpre | right; exact EC]);
    eapply (want_block ra) with (b := nth tok s NUL); try eassumption; try reflexivity;
    [ rewrite Hci; reflexivity | rewrite Hci; split; [intros _; exact Hlt | intros _; exact EC]
    | lia ].
  - (* n = 0: s[tok] is the last byte, no ':' *)
    zify_cond EC.
    zstep. zstep. if_cases E2; [zify_cond E2; lia|].
    zstep.
    assert (Hci : colon_idx s = length s).
    { apply colon_idx_eq; [lia | | left; reflexivity]. intros j Hj.
      destruct (Nat.eq_dec j tok) as [->|Hne]; [exact EC | apply Hpre; lia]. }
    eapply (want_block ra) with (b := nth tok s NUL); try eassumption; try reflexivity;
    [ f_equal; lia | rewrite Hci; split; [intros H; exfalso; exact (EC H) | intros H; lia] | lia ].
  - (* n > 0: the next byte *)
    zify_cond EC.
    zstep. zstep. if_cases E2; [|zify_cond E2; lia].
    eapply (IH (S tok)); try eassumption; try reflexivity.
    + lia.
    + f_equal. lia.
    + intros j Hj. destruct (Nat.eq_dec j tok) as [->|Hne]; [exact EC | apply Hpre; lia].
Qed.

End Want.
