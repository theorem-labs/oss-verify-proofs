From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge Arr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel pcap_source_next_lib pcap_source_struct
  pcap_source_struct_next.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require Import PSegW.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(* The magic test of 0x12d00-0x12d30 for a magic word M read from a file of n bytes. *)
Definition mgood (n M : Z) : bool := (24 <=? n) && ((M =? 0xA1B2C3D4) || (M =? 0xD4C3B2A1)).
Definition msw (M : Z) : Z := if M =? 0xD4C3B2A1 then 1 else 0.

Lemma lxor_range64 : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> 0 <= Z.lxor x y < 2 ^ 64.
Proof.
  intros x y Hx Hy. assert (N : 0 <= Z.lxor x y) by (apply Z.lxor_nonneg; lia). split; [exact N|].
  destruct (Z.eq_dec (Z.lxor x y) 0) as [E|E]; [lia|].
  apply Z.log2_lt_pow2; [lia|].
  pose proof (Z.log2_lxor x y ltac:(lia) ltac:(lia)) as L.
  assert (Lx : Z.log2 x < 64)
    by (destruct (Z.eq_dec x 0) as [->|]; [cbn; lia | apply Z.log2_lt_pow2; lia]).
  assert (Ly : Z.log2 y < 64)
    by (destruct (Z.eq_dec y 0) as [->|]; [cbn; lia | apply Z.log2_lt_pow2; lia]).
  lia.
Qed.

Lemma swrap_inj : forall M K, 0 <= M < 2 ^ 32 -> 0 <= K < 2 ^ 32 ->
  bv_unsigned (Z_to_bv 64 (bv_swrap 32 M)) = bv_unsigned (Z_to_bv 64 (bv_swrap 32 K)) -> M = K.
Proof.
  intros M K HM HK E. rewrite !swrap_cases in E by lia.
  destruct (Z.ltb_spec M (2 ^ 31)); destruct (Z.ltb_spec K (2 ^ 31)); lia.
Qed.

(* x xor C is zero exactly when the 32-bit words M and K agree (C is K sign-extended). *)
Lemma xor_swrap_eq0 : forall M K C, 0 <= M < 2 ^ 32 -> 0 <= K < 2 ^ 32 ->
  C = bv_unsigned (Z_to_bv 64 (bv_swrap 32 K)) ->
  bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 (bv_swrap 32 M))) C)) = 0 <-> M = K.
Proof.
  intros M K C HM HK ->.
  pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 (bv_swrap 32 M))) as R1.
  pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 (bv_swrap 32 K))) as R2. unfold bv_modulus in R1, R2.
  rewrite unsigned_lit by (apply lxor_range64; lia).
  rewrite Z.lxor_eq_0_iff. split; [apply swrap_inj; lia | intros ->; reflexivity].
Qed.

Lemma snez_xor : forall M K C, 0 <= M < 2 ^ 32 -> 0 <= K < 2 ^ 32 ->
  C = bv_unsigned (Z_to_bv 64 (bv_swrap 32 K)) ->
  v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 (bv_swrap 32 M))) C)) =
  Z_to_bv 64 (Z.b2z (negb (M =? K))).
Proof.
  intros M K C HM HK HC. pose proof (xor_swrap_eq0 M K C HM HK HC) as E.
  unfold v_sltu, c_ltu, bv_ltu. rewrite (unsigned_lit 0) by lia.
  match goal with |- context [bv_unsigned ?w] =>
    lazymatch w with Z_to_bv 64 (Z.lxor _ _) => pose proof (bv_unsigned_in_range 64 w) as R end end.
  unfold bv_modulus in R.
  destruct (Z.eqb_spec M K) as [EK|EK].
  - rewrite (proj2 E EK). reflexivity.
  - rewrite (proj2 (Z.ltb_lt _ _)) by (destruct (Z.eq_dec (bv_unsigned (Z_to_bv 64 (Z.lxor
      (bv_unsigned (Z_to_bv 64 (bv_swrap 32 M))) C))) 0) as [Z0|Z0]; [exfalso; exact (EK (proj1 E Z0)) | lia]).
    reflexivity.
Qed.

Lemma seqz_xor : forall M K C, 0 <= M < 2 ^ 32 -> 0 <= K < 2 ^ 32 ->
  C = bv_unsigned (Z_to_bv 64 (bv_swrap 32 K)) ->
  v_sltiu (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 (bv_swrap 32 M))) C)) 1 = Z_to_bv 64 (Z.b2z (M =? K)).
Proof.
  intros M K C HM HK HC. pose proof (xor_swrap_eq0 M K C HM HK HC) as E.
  unfold v_sltiu. change (bv_wrap 64 1) with 1.
  match goal with |- context [bv_unsigned ?w] =>
    lazymatch w with Z_to_bv 64 (Z.lxor _ _) => pose proof (bv_unsigned_in_range 64 w) as R end end.
  unfold bv_modulus in R.
  destruct (Z.eqb_spec M K) as [EK|EK].
  - rewrite (proj2 E EK). reflexivity.
  - rewrite (proj2 (Z.ltb_ge _ _)) by (destruct (Z.eq_dec (bv_unsigned (Z_to_bv 64 (Z.lxor
      (bv_unsigned (Z_to_bv 64 (bv_swrap 32 M))) C))) 0) as [Z0|Z0]; [exfalso; exact (EK (proj1 E Z0)) | lia]).
    reflexivity.
Qed.

Lemma flag_good : forall n M,
  (n <? 24) || (negb (M =? 0xA1B2C3D4) && negb (M =? 0xD4C3B2A1)) = negb (mgood n M).
Proof.
  intros n M. unfold mgood. rewrite Z.ltb_antisym.
  destruct (24 <=? n), (M =? 0xA1B2C3D4), (M =? 0xD4C3B2A1); reflexivity.
Qed.

Ltac b2z_eq := apply bv_eq; vm_compute; reflexivity.

Lemma pcap_B2 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n M r d b sp_h : Z),
    bv_unsigned sp = sp_h -> a0 = wz r -> a1 = wz (bv_swrap 32 M) -> 0 <= M < 2 ^ 32 -> a2 = wz n ->
    0 <= n < 2 ^ 26 -> s4 = wz b -> s0 = wz d -> 0 <= d < 256 ->
    ((mgood n M = true /\ r = 0 /\ bytes_at rsegs m (sp_h + 40) (le4 (wz (msw M)))) \/
     (mgood n M = false /\ r = -1 /\ bytes_at rsegs m (sp_h + 32) (le8 (wz 0)))) ->
    evt rsegs
      (fun ms' =>
         (mgood n M = true /\ exists a1' a2' a3' a4' : word,
            ms' = MS (mkR (wz (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x170)%Z)) sp gp tp t0 t1 t2 s0 (wz (8 * d)) (wz (if d =? 0 then 1 else 8 * d))
                          a1' a2' a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     FR (Z_to_bv 64 (symaddr Symbols.Plain.s_malloc)) fc None m (seg_rom rsegs)) \/
         (mgood n M = false /\ exists a1' a2' a3' a4' : word,
            ms' = MS (mkR (wz (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x570)%Z)) sp gp tp t0 t1 t2 s0 s1 (wz b) a1' a2' a3' a4' a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     FR (Z_to_bv 64 (symaddr Symbols.Plain.s_free)) fc None m (seg_rom rsegs)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0xfc)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m n M r d b sp_h HSP E0 E1 HM E2 HN E4 ES0 HD HC.
  subst sp_h a0 a1 a2 s4 s0. unfold wz.
  assert (UN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  step.
  rep_reg 12 (Z_to_bv 64 (Z.b2z (n <? 24)))
    ltac:(unfold v_sltiu; rewrite UN; change (bv_wrap 64 24) with 24; destruct (n <? 24); reflexivity).
  do 8 step.
  rep_reg 13 (Z_to_bv 64 (Z.b2z (negb (M =? 0xA1B2C3D4))))
    ltac:(symmetry; apply (snez_xor M 0xA1B2C3D4); [lia | lia | reflexivity]).
  rep_reg 14 (Z_to_bv 64 (Z.b2z (negb (M =? 0xD4C3B2A1))))
    ltac:(symmetry; rewrite alu_sltu; apply (snez_xor M 0xD4C3B2A1); [lia | lia | reflexivity]).
  step.
  rep_reg 13 (Z_to_bv 64 (Z.b2z (negb (M =? 0xA1B2C3D4) && negb (M =? 0xD4C3B2A1))))
    ltac:(destruct (M =? 0xA1B2C3D4), (M =? 0xD4C3B2A1); b2z_eq).
  step.
  rep_reg 12 (Z_to_bv 64 (Z.b2z (negb (mgood n M))))
    ltac:(rewrite <- flag_good; destruct (n <? 24), (M =? 0xA1B2C3D4), (M =? 0xD4C3B2A1); b2z_eq).
  do 2 step.
  rep_reg 12 (Z_to_bv 64 (if mgood n M then 0 else -1)) ltac:(destruct (mgood n M); b2z_eq).
  destruct HC as [(G & -> & HSW) | (G & -> & HF0)]; rewrite G.
  - (* the file is good *)
    pose proof (bytes_at_ov4 _ _ _ HSW) as RSW. clear HSW.
    step. if_false. step. if_true. step.
    rep_reg 10 (Z_to_bv 64 (msw M)) ltac:(unfold msw; destruct (M =? 0xD4C3B2A1); b2z_eq).
    do 4 step.
    rep_reg 11 (Z_to_bv 64 (msw M))
      ltac:(rewrite (seqz_xor M 0xD4C3B2A1) by (lia || reflexivity); unfold msw;
            destruct (M =? 0xD4C3B2A1); reflexivity).
    step. if_false. step.
    rep_reg 9 (Z_to_bv 64 (8 * d))
      ltac:(rewrite unsigned_lit, Z.shiftl_mul_pow2 by lia; f_equal; lia).
    step. step.
    destruct (Z.eq_dec d 0) as [D0|D0].
    + subst d. if_false. do 2 step. apply evt_done. left. split; [reflexivity|]. do 4 eexists. reflexivity.
    + assert (UD : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
      if_true. step. apply evt_done. left. split; [reflexivity|]. do 4 eexists.
      rewrite (proj2 (Z.eqb_neq d 0) D0). reflexivity.
  - (* the file is refused *)
    pose proof (bytes_at_ov8 _ _ _ HF0) as RF0. clear HF0.
    step. if_false. step. if_false. step. step. if_true. do 2 step.
    apply evt_done. right. split; [reflexivity|]. do 4 eexists. reflexivity.
Qed.

(* Segment B, from 0x12cc4 (pcap_source_open answered r) to the call of malloc (0x14158, ra 0x12d74) for a
   good file, or to the call of free(b) (0x14018, ra 0x13174) for a refused one. The inline magic read
   (0x12cd0-0x12cf4) and the two compares equal pcap_magic F and pcap_good F, so no check reaches 0x131c4. *)
Lemma pcap_B_x :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (F : list byte) (sp_h b r d : Z),
    bv_unsigned sp = sp_h -> a0 = wz r -> s4 = wz b -> bytes_at rsegs m b F ->
    s6 = wz (symaddr Symbols.Plain.s_g_file_len) -> bytes_at rsegs m (symaddr Symbols.Plain.s_g_file_len) (le8 (wz (Z.of_nat (length F)))) ->
    Z.of_nat (length F) < 2 ^ 26 -> s0 = wz d -> 0 <= d < 256 ->
    ((pcap_good F = true /\ r = 0 /\ bytes_at rsegs m (sp_h + 40) (le4 (wz (pcap_sw F)))) \/
     (pcap_good F = false /\ r = -1 /\ bytes_at rsegs m (sp_h + 32) (le8 (wz 0)))) ->
    evt rsegs
      (fun ms' =>
         (pcap_good F = true /\ exists a1' a2' a3' a4' a5' : word,
            ms' = MS (mkR (wz (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x170)%Z)) sp gp tp t0 t1 t2 s0 (wz (8 * d)) (wz (if d =? 0 then 1 else 8 * d))
                          a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     FR (Z_to_bv 64 (symaddr Symbols.Plain.s_malloc)) fc None m (seg_rom rsegs)) \/
         (pcap_good F = false /\ exists a1' a2' a3' a4' a5' : word,
            ms' = MS (mkR (wz (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x570)%Z)) sp gp tp t0 t1 t2 s0 s1 (wz b) a1' a2' a3' a4' a5' a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     FR (Z_to_bv 64 (symaddr Symbols.Plain.s_free)) fc None m (seg_rom rsegs)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0xc0)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m F sp_h b r d HSP E0 E4 HF E6 HFL H26 ES0 HD HC.
  subst a0 s4 s6 s0.
  pose proof (bytes_at_ov8 _ _ _ HFL) as RFL. clear HFL.
  set (n := Z.of_nat (length F)) in *. assert (EN : n = Z.of_nat (length F)) by reflexivity. clearbody n.
  assert (UN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  unfold wz in RFL |- *.
  step. step. step.
  destruct (Z_lt_le_dec n 4) as [L4|L4].
  - (* fewer than 4 bytes: the magic word is 0 *)
    if_true. step.
    assert (G : pcap_good F = false)
      by (unfold pcap_good; rewrite <- EN, (proj2 (Z.leb_gt 24 n)) by lia; reflexivity).
    assert (G0 : mgood n 0 = false) by (unfold mgood; rewrite (proj2 (Z.leb_gt 24 n)) by lia; reflexivity).
    destruct HC as [(G' & _) | (_ & Hr & H0)]; [congruence|].
    eapply evt_mono.
    { eapply (pcap_B2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n 0 r d b sp_h);
        try reflexivity; try eassumption; try lia.
      right. exact (conj G0 (conj Hr H0)). }
    intros ms' [(G2 & _) | (_ & a1' & a2' & a3' & a4' & ->)]; [congruence|].
    right. split; [exact G|]. exists a1', a2', a3', a4', a5. reflexivity.
  - (* the magic word: F[0..3] little-endian, sign-extended from 32 bits *)
    if_false.
    destruct F as [|c0 [|c1 [|c2 [|c3 F']]]]; cbn [length] in EN; try lia.
    pose proof (bytes_at_byte m b _ 0 HF ltac:(cbn [length]; lia)) as B0.
    pose proof (bytes_at_byte m b _ 1 HF ltac:(cbn [length]; lia)) as B1.
    pose proof (bytes_at_byte m b _ 2 HF ltac:(cbn [length]; lia)) as B2.
    pose proof (bytes_at_byte m b _ 3 HF ltac:(cbn [length]; lia)) as B3.
    change (nth (Z.to_nat 0) (c0 :: c1 :: c2 :: c3 :: F') (Z_to_bv 8 0)) with c0 in B0.
    change (nth (Z.to_nat 1) (c0 :: c1 :: c2 :: c3 :: F') (Z_to_bv 8 0)) with c1 in B1.
    change (nth (Z.to_nat 2) (c0 :: c1 :: c2 :: c3 :: F') (Z_to_bv 8 0)) with c2 in B2.
    change (nth (Z.to_nat 3) (c0 :: c1 :: c2 :: c3 :: F') (Z_to_bv 8 0)) with c3 in B3.
    do 11 step.
    rep_reg 11 (Z_to_bv 64 (bv_swrap 32 (w32le (bv_unsigned c0) (bv_unsigned c1) (bv_unsigned c2) (bv_unsigned c3))))
      ltac:(rewrite w32le_lor by apply byte_range; bits_eq).
    set (M := w32le (bv_unsigned c0) (bv_unsigned c1) (bv_unsigned c2) (bv_unsigned c3)).
    assert (HM : 0 <= M < 2 ^ 32).
    { unfold M, w32le. pose proof (byte_range c0). pose proof (byte_range c1). pose proof (byte_range c2).
      pose proof (byte_range c3). lia. }
    assert (EG : pcap_good (c0 :: c1 :: c2 :: c3 :: F') = mgood n M) by (rewrite EN; reflexivity).
    assert (ES : pcap_sw (c0 :: c1 :: c2 :: c3 :: F') = msw M) by reflexivity.
    rewrite EG, ES in HC. rewrite EG. clearbody M.
    eapply evt_mono.
    { eapply (pcap_B2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n M r d b sp_h);
        try reflexivity; try eassumption; try lia. }
    intros ms' [(G2 & a1' & a2' & a3' & a4' & ->) | (G2 & a1' & a2' & a3' & a4' & ->)];
      [left | right]; (split; [exact G2|]); do 5 eexists; reflexivity.
Qed.

(* Cuts a slot [a, a + n) out of a stack range. *)
Lemma stk_cut : forall m lo hi a (n : nat), stk rsegs m lo hi -> lo <= a -> a + Z.of_nat n <= hi ->
  stk rsegs m lo a /\ (exists j, rw_cells rsegs m a [CB n j]) /\ stk rsegs m (a + Z.of_nat n) hi.
Proof.
  intros m lo hi a n ST L H.
  destruct (stk_split rsegs m lo (a + Z.of_nat n) hi ST ltac:(lia)) as [S1 S2].
  destruct (stk_carve rsegs m lo (a + Z.of_nat n) n S1 ltac:(lia)) as [S3 [j J]].
  replace (a + Z.of_nat n - Z.of_nat n) with a in S3, J by lia.
  split; [exact S3|]. split; [exists j; exact J | exact S2].
Qed.

(* Puts a slot back into its stack range. *)
Lemma stk_uncut : forall m lo hi a cs, stk rsegs m lo a -> rw_cells rsegs m a cs ->
  stk rsegs m (a + Z.of_nat (cells_size cs)) hi -> lo <= a -> a + Z.of_nat (cells_size cs) <= hi ->
  stk rsegs m lo hi.
Proof.
  intros m lo hi a cs S1 C S2 L H.
  exact (stk_merge rsegs m lo _ hi (stk_release rsegs m lo a cs S1 C L) S2 ltac:(lia)).
Qed.

(* Segment C, from 0x12d74 (malloc answered buf) to the first call of pcap_source_next (0x132a0, ra 0x12d9c). *)
Lemma pcap_C_x :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sp_h buf d lo : Z),
    bv_unsigned sp = sp_h -> a0 = wz buf -> 0 < buf < 2 ^ 64 -> s0 = wz d -> s1 = wz (8 * d) -> 0 <= d < 256 ->
    stk rsegs m lo (sp_h + 160) -> lo <= sp_h -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists m' : word -> option byte,
         ms' = MS (mkR (wz (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x198)%Z)) sp gp tp t0 t1 t2 s0 s1 (wz (sp_h + 32)) (wz buf) (wz (8 * d)) (wz (sp_h + 24))
                       a4 a5 a6 a7 (wz buf) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  FR (Z_to_bv 64 (symaddr Symbols.Plain.s_pcap_source_next)) fc None m' (seg_rom rsegs) /\
         munch [(sp_h + 8, sp_h + 16); (sp_h + 24, sp_h + 32)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo (sp_h + 160) /\
         rw_cells rsegs m' (sp_h + 8) [C8 (wz d)] /\ rw_cells rsegs m' (sp_h + 24) [C8 (wz (-1))])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x170)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m sp_h buf d lo HSP E0 HB ES0 ES1 HD ST LO MI.
  subst sp_h a0 s0 s1.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (munch_refl [(bv_unsigned sp + 8, bv_unsigned sp + 16); (bv_unsigned sp + 24, bv_unsigned sp + 32)] m)
    as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (UB : bv_unsigned (Z_to_bv 64 buf) = buf) by (apply unsigned_lit; lia).
  destruct (stk_cut m lo _ (bv_unsigned sp + 24) 8 ST ltac:(lia) ltac:(cbn; lia)) as (STa & (j24 & C24) & STb).
  destruct (stk_cut m lo _ (bv_unsigned sp + 8) 8 STa ltac:(lia) ltac:(cbn; lia)) as (STc & (j8 & C8a) & STd).
  clear ST STa.
  unfold wz.
  step. if_false.
  do 9 step.
  apply evt_done. eexists. split; [reflexivity|].
  refine (conj MU (conj WM (conj MI (conj _ (conj C8a C24))))).
  assert (S24 : stk rsegs m1 lo (bv_unsigned sp + 24)).
  { apply (stk_uncut _ lo _ (bv_unsigned sp + 8) _ STc C8a); [ exact STd | lia | cbn [cells_size csize Nat.add]; lia ]. }
  apply (stk_uncut _ lo _ (bv_unsigned sp + 24) _ S24 C24); [ exact STb | lia | cbn [cells_size csize Nat.add]; lia ].
Qed.
