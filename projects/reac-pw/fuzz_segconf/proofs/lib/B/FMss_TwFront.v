(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMss_TwFront.v at cold/port-fm-int b6bc009d623, relocated A->B by asan-kit elfmap.py + remap.py over the unstripped twins; every image numeral re-derived by symbol / section (fmb-b4 reloc report). *)
(* lib/A/Prog/TwFront.v (RtStr's port, unchanged from cold/c-asan-rt-fmio-n affce6489c8), re-run over the
   local-shadow TW_ASAN / TW_STATIC / twoway contract (FMss_TwAsan.v, FMss_TwSetup_c.v, FMss_twoway_strstr_c.v);
   only the imports differ. *)
From Stdlib Require Import ZArith NArith Arith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Tac Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Spec Require Import StrStr StrBytes TwoWay TwSearch TwSearchPf.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import twoway_strstr_c TwFrame1 TwFrame2.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import FMss_TwAsan FMss_twoway_strstr_c FMss_TwFrame3 FMss_TwSetup_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.TacDiet2.diet_word_eq_tac.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require StepFast.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Step.zstep ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.StepFast.sf_zstep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.TacDiet2.diet_word_eq_tac ].
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Stor0fe.sb_mem_after_store.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require AndN.
Import ListNotations.
Open Scope Z_scope.

Lemma tf_hzero : forall (hb hs : list byte) l b, ~ In (Z_to_bv 8 0) hb -> (l <= length hb)%nat ->
  nth_error (hb ++ Z_to_bv 8 0 :: hs) l = Some b -> (bv_unsigned b = 0 <-> l = length hb).
Proof.
  intros hb hs l b NZ Hl E. destruct (Nat.eq_dec l (length hb)) as [->|Ne].
  - rewrite nth_error_app2, Nat.sub_diag in E by lia. cbn in E. injection E as <-. split; intros; reflexivity.
  - rewrite nth_error_app1 in E by lia. pose proof (tw_nz_of_nth hb l b NZ E) as H.
    split; intros H'; exfalso; [exact (H H') | exact (Ne H')].
Qed.

Lemma tf_bit_range : forall k, 0 <= k < 64 -> 0 <= Z.shiftl 1 k < 2^64.
Proof. intros k Hk. rewrite Z.shiftl_1_l. split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia]. Qed.

Section Front.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 : word) (F : bvmap 5 word) (fc : bv 32)
          (m0 : word -> option byte) (hb hs nb : list byte) (lo : Z) (g : word).
Hypothesis TS : TW_STATIC sp a0 a1 m0 hb hs nb lo g.
Hypothesis K918 : AT918 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc m0 hb hs nb lo g.

Notation POSTQ := (twoway_strstr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 hb hs nb lo m0).
Notation X := (map bv_unsigned nb).

Definition FOK (m : word -> option byte) (j48 : list byte) (bset tbl : list word) : Prop :=
  rw_cells rsegs m (bv_unsigned sp + -2240) [CB 48 j48] /\
  u64arr rsegs m (bv_unsigned sp + -2192) tbl /\ u64arr rsegs m (bv_unsigned sp + -144) bset /\
  rw_cells rsegs m (bv_unsigned sp + -112)
    [C8 g; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
  stk rsegs m lo (bv_unsigned sp + -2240) /\ mem_inv rsegs m /\
  munch [(bv_unsigned sp - 4560, bv_unsigned sp)] m0 m /\ wmono rsegs m0 m /\
  bytes_at rsegs m (bv_unsigned a0) (hb ++ Z_to_bv 8 0 :: hs) /\
  bytes_at rsegs m (bv_unsigned a1) (nb ++ [Z_to_bv 8 0]) /\
  bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) /\ bytes_at rsegs m GUARD (le8 g).

Notation LT pc r5 r6 r7 r11 r15 r16 r17 r23 r28 r29 r30 r31 m :=
  (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp r5 r6 r7 a1 a0 (Z_to_bv 64 (-1)) r11 (Z_to_bv 64 1)
       (Z_to_bv 64 (bv_unsigned sp + -144)) (Z_to_bv 64 (bv_unsigned sp + -2192)) r15 r16 r17
       s2 (Z_to_bv 64 GUARD) s4 s5 (Z_to_bv 64 (bv_unsigned a1 + 1)) r23 s8 s9 s10 s11 r28 r29 r30 r31)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Ltac tf_facts :=
  pose proof TS as (ST0 & LO & HH0 & NH & PAD & HN0 & NN & NE & MI0 & SH & SN & GG0 & GD0 & GL & GGL & TA);
  pose proof (bytes_at_bound _ _ _ _ HH0) as BH; pose proof (bytes_at_bound _ _ _ _ HN0) as BN;
  rewrite length_app in BH, BN; cbn [length] in BH, BN;
  pose proof ST0 as [LO0 _];
  pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
  clear ST0 HH0 HN0 MI0 GG0 GD0.

Ltac tf_frame :=
  first [ eapply rw_cells_frame; [eassumption | lia | rewrite length_le8; lia | cbn [cells_size csize Nat.add]; rewrite length_le8; lia]
        | eapply u64arr_frame; [eassumption | lia | rewrite length_le8; lia | rewrite length_le8; lia]
        | eapply stk_write; [eassumption | lia | rewrite length_le8; lia]
        | eapply mem_inv_store; [eassumption | rewrite length_le8; eassumption]
        | eapply munch_write; [eassumption | lia | rewrite length_le8; lia | cbn [inside]; rewrite length_le8; lia]
        | eapply wmono_write; eassumption
        | eapply bytes_at_write_other;
            [eassumption | lia | rewrite length_le8; lia | rewrite ?length_app, ?length_le8; cbn [length]; unfold GOT_GUARD, GUARD in *; lia] ].

Lemma tf_st_bset : forall m j48 bset tbl (i : Z) (v : word),
  FOK m j48 bset tbl -> 0 <= i < 4 -> length bset = 4%nat -> length tbl = 256%nat ->
  FOK (write_to_mem m (Z_to_bv 64 (bv_unsigned sp + -144 + 8 * i)) (le8 v)) j48 (upd bset (Z.to_nat i) v) tbl.
Proof.
  intros m j48 bset tbl i v (FL & TBm & BSm & FR & ST & MI & MU & WM & HH & HN & GG & GD) Hi BL TL.
  tf_facts.
  assert (SB : store_ok rsegs m (wa (bv_unsigned sp + -144 + 8 * i)) 8 = true)
    by (apply (u64arr_store_ok rsegs m _ bset i _ BSm); [rewrite BL; lia | reflexivity]).
  change (Z_to_bv 64 (bv_unsigned sp + -144 + 8 * i)) with (wa (bv_unsigned sp + -144 + 8 * i)).
  unfold FOK. OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.AndN.and_splits.
  3: apply u64arr_write; [exact BSm | lia].
  all: tf_frame.
Qed.

Lemma tf_st_tbl : forall m j48 bset tbl (i : Z) (v : word),
  FOK m j48 bset tbl -> 0 <= i < 256 -> length bset = 4%nat -> length tbl = 256%nat ->
  FOK (write_to_mem m (Z_to_bv 64 (bv_unsigned sp + -2192 + 8 * i)) (le8 v)) j48 bset (upd tbl (Z.to_nat i) v).
Proof.
  intros m j48 bset tbl i v (FL & TBm & BSm & FR & ST & MI & MU & WM & HH & HN & GG & GD) Hi BL TL.
  tf_facts.
  assert (SB : store_ok rsegs m (wa (bv_unsigned sp + -2192 + 8 * i)) 8 = true)
    by (apply (u64arr_store_ok rsegs m _ tbl i _ TBm); [rewrite TL; lia | reflexivity]).
  change (Z_to_bv 64 (bv_unsigned sp + -2192 + 8 * i)) with (wa (bv_unsigned sp + -2192 + 8 * i)).
  unfold FOK. OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.AndN.and_splits.
  2: apply u64arr_write; [exact TBm | lia].
  all: tf_frame.
Qed.

Lemma tf_loop : forall (d l : nat) (m : word -> option byte) (j48 : list byte) (bset tbl : list word) (bn : byte)
    (w11 w15 r5 r6 r7 r16 r17 r23 r28 r29 r30 r31 : word),
  (length nb - l = d)%nat -> (l < length nb)%nat -> (l <= length hb)%nat -> nth_error nb l = Some bn ->
  FOK m j48 bset tbl -> BSET (firstn l X) bset -> TBL (firstn l X) tbl ->
  bv_unsigned w11 = bv_unsigned bn -> bv_unsigned w15 = Z.of_nat l ->
  evt rsegs POSTQ (LT 0x9ba34 r5 r6 r7 w11 w15 r16 r17 r23 r28 r29 r30 r31 m).
Proof.
  induction d as [d IH] using lt_wf_ind.
  intros l m j48 bset tbl bn w11 w15 r5 r6 r7 r16 r17 r23 r28 r29 r30 r31 Hd Hl Hh EB FO BS TB E11 E15.
  tf_facts.
  pose proof FO as (FL & TBm & BSm & FR & ST & MI & MU & WM & HH & HN & GG & GD).
  pose proof BS as [BL4 BSV]. pose proof TB as [TL256 TBV].
  apply tw_word_of in E11, E15. subst w11 w15.
  pose proof (sb_byte_range bn) as RBN. pose proof (tw_nz_of_nth nb l bn NN EB) as NZ.
  destruct (tw_nth_ex (hb ++ Z_to_bv 8 0 :: hs) l ltac:(rewrite length_app; cbn [length]; lia)) as [bh EH].
  pose proof (sb_byte_range bh) as RBH. pose proof (tf_hzero hb hs l bh NH Hh EH) as HZ.
  assert (RH : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned a0 + Z.of_nat l)) 1 = Some [bh]).
  { apply (sb_rd1 rsegs m (bv_unsigned a0) _ l bh _ HH EH). rewrite unsigned_lit by lia. lia. }
  zstep. zstep. zstep.
  if_cases K; zify_cond K; rewrite ?sb_u_zxb, ?sb_u_byte, ?Z.mod_small in K by lia; cbv iota.
  - assert (Kl : l = length hb) by (apply HZ; lia).
    pose proof (tw_rd8 _ _ _ _ GD) as RD.
    zstep. zstep. zstep. zstep. zstep. zstep.
    if_cases K2; zify_cond K2; cbv iota; [|exfalso; lia].
    eapply (tw_exit ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc m0 hb hs nb lo g)
      with (m := m) (cs := [CB 48 j48]) (bset := bset) (tbl := tbl); try eassumption; [reflexivity|].
    rewrite tw_sv_none; [reflexivity|].
    apply tw_none_short; rewrite !length_map; lia.
  - assert (Hh' : (l < length hb)%nat)
      by (destruct (Nat.eq_dec l (length hb)) as [E|E]; [exfalso; pose proof (proj2 HZ E); lia | lia]).
    zstep. zstep.
    rewrite (tw_bs_idx8 (bv_unsigned bn) RBN).
    assert (Q4 : 0 <= bv_unsigned bn / 64 < 4) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
    set (wb := nth (Z.to_nat (bv_unsigned bn / 64)) bset (Z_to_bv 64 0)).
    assert (RB : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned sp + -144 + 8 * (bv_unsigned bn / 64))) 8 = Some (le8 wb)).
    { apply (u64arr_read rsegs m (bv_unsigned sp + -144) bset (bv_unsigned bn / 64) wb _ BSm); [|lia|reflexivity].
      apply tw_nth_error_nth. rewrite BL4. lia. }
    destruct (sb_nth_full nb (S l) ltac:(lia)) as [bn1 EB1]. pose proof (sb_byte_range bn1) as RBN1.
    assert (RN1 : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned a1 + 1 + Z.of_nat l)) 1 = Some [bn1]).
    { apply (sb_rd1 rsegs m (bv_unsigned a1) _ (S l) bn1 _ HN EB1). rewrite unsigned_lit by lia. lia. }
    assert (SB : store_ok rsegs m (wa (bv_unsigned sp + -144 + 8 * (bv_unsigned bn / 64))) 8 = true).
    { apply (u64arr_store_ok rsegs m (bv_unsigned sp + -144) bset (bv_unsigned bn / 64) _ BSm); [rewrite BL4; lia | reflexivity]. }
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    rewrite (Z.mod_small (Z.shiftl 1 (bv_unsigned bn mod 64)) 18446744073709551616)
      by (pose proof (tf_bit_range (bv_unsigned bn mod 64) ltac:(apply Z.mod_pos_bound; lia)); lia).
    set (v1 := Z_to_bv 64 (Z.lor (bv_unsigned wb) (Z.shiftl 1 (bv_unsigned bn mod 64)))).
    assert (V1 : bv_unsigned v1 = Z.lor (bv_unsigned wb) (Z.shiftl 1 (bv_unsigned bn mod 64))).
    { pose proof (tf_bit_range (bv_unsigned bn mod 64) ltac:(apply Z.mod_pos_bound; lia)) as BR.
      pose proof (bv_unsigned_in_range 64 wb) as WR. unfold bv_modulus in WR. cbn in WR.
      apply unsigned_lit. apply Z_lor_range; lia. }
    pose proof (tf_st_bset m j48 bset tbl (bv_unsigned bn / 64) v1 FO Q4 BL4 TL256) as FO1.
    set (m1 := write_to_mem m (Z_to_bv 64 (bv_unsigned sp + -144 + 8 * (bv_unsigned bn / 64))) (le8 v1)) in *.
    clearbody m1. clear FL TBm BSm FR ST MI MU WM HH HN GG GD RH RB RN1 SB.
    pose proof FO1 as (FL & TBm & BSm & FR & ST & MI & MU & WM & HH & HN & GG & GD).
    assert (SB2 : store_ok rsegs m1 (wa (bv_unsigned sp + -2192 + 8 * bv_unsigned bn)) 8 = true).
    { apply (u64arr_store_ok rsegs m1 (bv_unsigned sp + -2192) tbl (bv_unsigned bn) _ TBm); [rewrite TL256; lia | reflexivity]. }
    replace (Z.shiftl (bv_unsigned bn) 3) with (8 * bv_unsigned bn) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep.
    pose proof (tf_st_tbl m1 j48 (upd bset (Z.to_nat (bv_unsigned bn / 64)) v1) tbl (bv_unsigned bn)
                  (Z_to_bv 64 (Z.of_nat l + 1)) FO1 ltac:(lia) ltac:(rewrite upd_length; exact BL4) TL256) as FO2.
    set (m2 := write_to_mem m1 (Z_to_bv 64 (bv_unsigned sp + -2192 + 8 * bv_unsigned bn))
                 (le8 (Z_to_bv 64 (Z.of_nat l + 1)))) in *.
    clearbody m2. clear FL TBm BSm FR ST MI MU WM HH HN GG GD SB2.
    assert (XL : (l < length X)%nat) by (rewrite length_map; lia).
    assert (BS' : BSET (firstn (S l) X) (upd bset (Z.to_nat (bv_unsigned bn / 64)) v1)).
    { rewrite (tw_firstn_S X l XL), (tw_at_u nb l bn EB). apply tw_BSET_snoc; [exact BS | lia | exact V1]. }
    assert (TB' : TBL (firstn (S l) X) (upd tbl (Z.to_nat (bv_unsigned bn)) (Z_to_bv 64 (Z.of_nat l + 1)))).
    { rewrite (tw_firstn_S X l XL), (tw_at_u nb l bn EB). apply tw_TBL_snoc; [exact TB | lia |].
      rewrite length_firstn, length_map. rewrite unsigned_lit by lia. lia. }
    zstep. zstep.
    if_cases K2; zify_cond K2; rewrite ?sb_u_zxb, ?sb_u_byte, ?Z.mod_small in K2 by lia; cbv iota.
    + assert (Nl : (S l < length nb)%nat).
      { destruct (Nat.eq_dec (S l) (length nb)) as [E|E]; [|lia].
        exfalso. apply K2. apply (sb_nth_full_zero nb (S l) bn1 NN EB1). exact E. }
      rewrite nth_error_app1 in EB1 by lia.
      eapply (IH (length nb - S l)%nat ltac:(lia) (S l) m2 j48 (upd bset (Z.to_nat (bv_unsigned bn / 64)) v1)
                 (upd tbl (Z.to_nat (bv_unsigned bn)) (Z_to_bv 64 (Z.of_nat l + 1))) bn1).
      all: first [reflexivity | exact EB1 | exact FO2 | exact BS' | exact TB' | apply sb_u_byte
                 | rewrite unsigned_lit by lia; lia | lia].
    + assert (Nl : (S l = length nb)%nat) by (apply (sb_nth_full_zero nb (S l) bn1 NN EB1); lia).
      rewrite firstn_all2 in BS', TB' by (rewrite length_map; lia).
      replace (bv_unsigned bn1) with 0 by lia.
      replace (Z.of_nat l + 1) with (Z.of_nat (length nb)) by lia.
      pose proof K918 as KK. unfold AT918 in KK.
      pose proof FO2 as (FL & TBm & BSm & FR & ST & MI & MU & WM & HH & HN & GG & GD).
      eapply KK; try eassumption; lia.
Qed.

End Front.

Theorem tw_front : TW_FRONT.
Proof.
  unfold TW_FRONT. intros BACK. unfold twoway_strstr_contract, TWOWAY_STRSTR, TWOWAY_STRSTR_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m hb hs nb lo g
         ST LO HH NH PAD NE HN NN MI SH SN GG GD GL GGL LH LN ADH ADN EH EN PH PN HL SPA AC SR RMC RMP GCF CF4 CF5.
  assert (TA : TW_ASAN sp a0 a1 m hb nb lo) by (unfold TW_ASAN; tauto).
  clear LH LN ADH ADN EH EN PH PN HL SPA AC SR RMC RMP GCF CF4 CF5.
  assert (TS : TW_STATIC sp a0 a1 m hb hs nb lo g) by (unfold TW_STATIC; tauto).
  pose proof (BACK ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc m hb hs nb lo g TS) as K918.
  clear BACK.
  pose proof (munch_refl [(bv_unsigned sp - 4560, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ HH) as BH. pose proof (bytes_at_bound _ _ _ _ HN) as BN.
  rewrite length_app in BH, BN. cbn [length] in BH, BN.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (L1 : (1 <= length nb)%nat) by (destruct nb; [congruence | cbn; lia]).
  destruct (tw_nth_ex nb 0 ltac:(lia)) as [b0 EB0].
  pose proof (tw_nz_of_nth nb 0 b0 NN EB0) as NZ0. pose proof (sb_byte_range b0) as RB0.
  carve_frame 112%nat ST. carve_frame 32%nat ST. carve_frame 2048%nat ST. carve_frame 48%nat ST.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  zstep. zstep. zstep. zstep.
  pose proof GG as GG'. unfold GOT_GUARD in GG'. pose proof (tw_rd8 _ _ _ _ GG') as RG. clear GG'.
  pose proof (tw_rd8 _ _ _ _ GD) as RD.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into M2 end.
  assert (RN0 : ov_read_bytes rsegs M2 a1 1 = Some [b0]).
  { apply (sb_rd1 rsegs M2 (bv_unsigned a1) _ 0 b0 _ HN); [rewrite nth_error_app1 by lia; exact EB0 | lia]. }
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  if_cases K; zify_cond K; rewrite ?sb_u_zxb, ?sb_u_byte, ?Z.mod_small in K by lia; cbv iota; [exfalso; lia|].
  zstep. zstep. zstep. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into M3 end.
  pose proof (tw_u64arr_of_C8x4 _ _ _ _ _ _ _ FR0) as BS0.
  change 2048%nat with (8 * 256)%nat in FR1.
  destruct (tw_u64arr_of_CB _ _ _ _ _ FR1) as (tbl0 & TL0 & TB0).
  eapply (tf_loop ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc m hb hs nb lo g TS K918
            (length nb - 0) 0 M3 junk2 _ tbl0 b0).
  - reflexivity.
  - lia.
  - lia.
  - exact EB0.
  - unfold FOK. OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.AndN.and_splits; eassumption.
  - exact tw_BSET_nil.
  - apply tw_TBL_nil. exact TL0.
  - apply sb_u_byte.
  - reflexivity.
Qed.
