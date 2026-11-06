From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge Arr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require MemNorm RoAdapt.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel fread_c fread_ro_c
  pcap_source_struct pcap_source_struct_next pcap_lib pcap_source_next_lib.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Ltac show_st := lazymatch goal with |- evt _ _ ?st => idtac "GOAL:" st end.

Lemma swrap_congr32 : forall x y, x mod 2 ^ 32 = y mod 2 ^ 32 -> bv_swrap 32 x = bv_swrap 32 y.
Proof. intros x y H. rewrite !swrap32_eq. f_equal. rewrite Zplus_mod, H, <- Zplus_mod. reflexivity. Qed.

Lemma subw_swrap : forall L c, 0 <= c < 2 ^ 64 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (bv_swrap 32 L)) - bv_unsigned (Z_to_bv 64 c))) =
  Z_to_bv 64 (bv_swrap 32 (L - c)).
Proof.
  intros L c Hc. f_equal. apply swrap_congr32. rewrite (unsigned_lit c) by lia. rewrite unsigned_lit_wrap.
  rewrite Zminus_mod, mod64_mod32, swrap32_mod, <- Zminus_mod. reflexivity.
Qed.

Lemma shl32_mod : forall v : word, bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned v) 32)) = (bv_unsigned v mod 2 ^ 32) * 2 ^ 32.
Proof.
  intros v. rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2 by lia. change (2 ^ 64) with (2 ^ 32 * 2 ^ 32).
  apply Z.mul_mod_distr_r; lia.
Qed.

Lemma psn_ts :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ts usec sec L : Z) (tsv : word),
    rw_cells rsegs m (bv_unsigned sp) [C8 (wz ts)] ->
    bv_unsigned s4 mod 2 ^ 32 = sec -> bv_unsigned s5 mod 2 ^ 32 = usec -> bv_unsigned s3 mod 2 ^ 32 = L ->
    0 <= ts < 2 ^ 64 -> (ts <> 0 -> ts mod 8 = 0) ->
    (ts <> 0 -> rw_cells rsegs m ts [C8 tsv]) ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' s3' s4' s5' : word) m',
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7 s2 s3' s4' s5' (wz L) s7 s8 s9 s10 s11
                       t3 t4 t5 t6) F (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_pcap_source_next + 0x148)%Z)) fc None m' (seg_rom rsegs) /\
         munch [(ts, ts + 8)] m m' /\ wmono rsegs m m' /\ (ts = 0 -> m' = m) /\
         (ts <> 0 -> rw_cells rsegs m' ts [C8 (wz (sec * 1000000 + usec))]))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_pcap_source_next + 0x238)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m ts usec sec L tsv HFR ES ESU EL RT RAL HTS.
  unfold wz in *.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (rw_cells_bound rsegs _ _ _ HFR) as HFB. cbn [cells_size csize Nat.add] in HFB.
  pose proof (munch_refl [(ts, ts + 8)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  assert (RS : 0 <= sec < 2 ^ 32) by (rewrite <- ES; apply Z.mod_pos_bound; lia).
  assert (RU : 0 <= usec < 2 ^ 32) by (rewrite <- ESU; apply Z.mod_pos_bound; lia).
  destruct (Z.eq_dec ts 0) as [T0|T0].
  - subst ts. do 2 step. if_true. do 3 step.
    rewrite zx32_val, EL.
    apply evt_done. do 6 eexists. exists m. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    split; [reflexivity|]. intros C. exfalso. apply C. reflexivity.
  - specialize (HTS T0). specialize (RAL T0).
    assert (ET : bv_unsigned (Z_to_bv 64 ts) = ts) by (apply unsigned_lit; lia).
    assert (L7 : Z.land ts 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; exact RAL).
    assert (EL7 : bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 ts)) 7)) = 0)
      by (rewrite ET, L7; apply unsigned_lit; lia).
    do 2 step. if_false. do 2 step. if_false. do 7 step.
    rep_reg 10 (Z_to_bv 64 (sec * 1000000 + usec))
      ltac:(f_equal; rewrite !shl32_mod, ES, ESU; rewrite !Z.shiftr_div_pow2 by lia;
            replace (sec * 2 ^ 32 * 4294967296000000) with (sec * 1000000 * 2 ^ 64) by ring;
            rewrite !Z.div_mul by lia; reflexivity).
    step. do 3 step.
    rewrite (zx32_val s3), EL.
    let mm := cur_mem in (apply evt_done; do 6 eexists; exists mm).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [intros C; exfalso; exact (T0 C)|].
    intros _. exact HTS.
Qed.

Lemma psn_skip : fread_ro_contract -> forall (N : nat)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (ps buf cap h b x left lo : Z) (Fc : list byte) (pv nx sw0 l1 l2 l3 : word) (bj pad : list byte),
    left <= Z.of_nat N ->
    s1 = wz buf -> s2 = wz ps -> s7 = wz cap -> s3 = wz (bv_swrap 32 left) -> 1 <= left < 2 ^ 32 -> 1 <= cap < 2 ^ 64 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 112 <= bv_unsigned sp -> (symaddr ImgPages.Ubsan.top) <= lo -> bv_unsigned sp + 128 <= ps ->
    rw_cells rsegs m ps [C8 (wz h); C4 sw0; C4 l1; C4 l2; C2 l3; CB 2 pad] ->
    mstl m h b Fc x pv nx -> img_apart h 1304 -> h + 1304 <= lo -> b + Z.of_nat (length Fc) <= lo ->
    u8arr rsegs m buf bj -> Z.of_nat (length bj) = Z.max cap 1 -> img_apart buf (Z.max cap 1) -> 4096 <= buf ->
    buf + Z.max cap 1 <= lo ->
    (buf + Z.max cap 1 <= h \/ h + 1304 <= buf) -> (buf + Z.max cap 1 <= b \/ b + Z.of_nat (length Fc) <= buf) ->
    MemNorm.ro_agree rsegs m ->
    evt rsegs
      (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' t3' t4' t5' t6' : word) m',
         ((x + left <= Z.of_nat (length Fc) /\
           ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' (wz h) a4' a5' a6' a7'
                         s2 s3' s4' s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_pcap_source_next + 0x74)%Z)) fc None m' (seg_rom rsegs) /\
           mstl m' h b Fc (x + left) pv nx) \/
          (Z.of_nat (length Fc) < x + left /\
           ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                         s2 s3' s4' s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_pcap_source_next + 0x148)%Z)) fc None m' (seg_rom rsegs) /\
           mstl m' h b Fc (Z.of_nat (length Fc)) pv nx)) /\
         rw_cells rsegs m' ps [C8 (wz h); C4 sw0; C4 l1; C4 l2; C2 l3; CB 2 pad] /\
         (exists bj', u8arr rsegs m' buf bj' /\ length bj' = length bj) /\
         munch [(bv_unsigned sp - 112, bv_unsigned sp); (buf, buf + Z.max cap 1); (h, h + 1304)] m m' /\
         wmono rsegs m m' /\ MemNorm.ro_agree rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_pcap_source_next + 0x108)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros HFR. unfold fread_ro_contract, FREAD in HFR.
  induction N as [|N IH];
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m ps buf cap h b x left lo Fc pv nx sw0 l1 l2 l3 bj pad
    HN E1 E2 E7 E3 HL HC ST LO HLO HPS0 HPS HMS HIH HHL HBL HBJ HBN HIB HB4K HBL2 HBH HBB RO.
  { lia. }
  subst s1 s2 s7. unfold wz in *.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (u8arr_len _ _ _ HBJ) as HBR.
  pose proof (rw_cells_bound rsegs _ _ _ HPS) as HPR. cbn [cells_size csize Nat.add] in HPR.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  assert (HQ : 0 <= x <= Z.of_nat (length Fc) /\ 0 < h /\ 0 < b).
  { destruct HMS as (fl & md & q' & rb & (bf & (pd0 & pd1 & pd2 & ung & HC0 & L1 & L2 & H0 & H16) & Hq & Hrb & HFc & Hb0 & Hd)
                     & R1 & R2 & R3 & R4).
    destruct rb as [[i e]|]; cbn [rlen] in R3; lia. }
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (buf, buf + Z.max cap 1); (h, h + 1304)] m) as MUT.
  pose proof (wmono_refl rsegs m) as WMT.
  assert (EL : bv_unsigned (Z_to_bv 64 left) = left) by (apply unsigned_lit; lia).
  assert (EC : bv_unsigned (Z_to_bv 64 cap) = cap) by (apply unsigned_lit; lia).
  subst s3.
  eapply evt_cut with (P := fun ms => ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 buf) (Z_to_bv 64 left)
      a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ps) (Z_to_bv 64 (bv_swrap 32 left)) (Z_to_bv 64 (Z.min cap left))
      s5 s6 (Z_to_bv 64 cap) s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_pcap_source_next + 0x11c)%Z)) fc None m (seg_rom rsegs)).
  { do 4 step. rewrite zx32_val, uns_swrap_mod32_0 by lia.
    destruct (Z_lt_le_dec cap left) as [CL|CL].
    - if_true. apply evt_done. rewrite Z.min_l by lia. reflexivity.
    - if_false. step. apply evt_done. rewrite Z.min_r by lia. reflexivity. }
  intros ms ->.
  do 5 step.
  eapply evt_cut.
  { eapply HFR with (lo := lo) (b := b) (Fc := Fc) (p := x) (pv := pv) (nx := nx)
      (junk := firstn (Z.to_nat (Z.min cap left)) bj).
    - rewrite unsigned_lit by lia. exact HMS.
    - rewrite unsigned_lit by lia. apply not_ro_apart; [lia | lia | exact HIH].
    - reflexivity.
    - rewrite unsigned_lit by lia. lia.
    - rewrite !unsigned_lit by lia. apply u8arr_take; [exact HBJ | lia].
    - rewrite !unsigned_lit by lia. apply not_ro_apart; [lia | lia | unfold img_apart in *; lia].
    - rewrite !unsigned_lit by lia. lia.
    - rewrite !unsigned_lit by lia. lia.
    - rewrite !unsigned_lit by lia. left. lia.
    - exact RO.
    - exact ST.
    - apply not_ro_hi; lia.
    - unfold FREAD_K. lia.
    - rewrite unsigned_lit by lia. lia.
    - exact HBL. }
  intros ms' (t0b & t1b & t2b & a0b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2
    & E & EA & MUf & WMf & RO2 & ST2 & BY2 & MS2).
  subst ms'.
  unfold fread_j, FREAD_K in EA, MUf, BY2, MS2.
  rewrite ?unsigned_lit in EA by lia. rewrite ?unsigned_lit in MUf by lia.
  rewrite ?unsigned_lit in BY2 by lia. rewrite ?unsigned_lit in MS2 by lia.
  unfold wz in EA. subst a0b.
  replace (ret_pc (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_pcap_source_next + 0x130)%Z))) with (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_pcap_source_next + 0x130)%Z)) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  xp_rw HPS MUf WMf.
  pose proof (u8arr_after _ _ _ _ _ _ HBJ MUf WMf BY2 ltac:(rewrite length_firstn; lia)
                ltac:(rewrite length_firstn, length_skipn; out_tac)) as HBJ2.
  match type of HBJ2 with u8arr _ _ _ ?L => remember L as bj2 eqn:Ebj2 end.
  assert (HBN2 : length bj2 = length bj).
  { rewrite Ebj2, length_app; repeat first [rewrite length_firstn | rewrite length_skipn]; lia. }
  pose proof (munch_ext _ _ _ _ _ MUT MUf ltac:(out_tac)) as MUT2. clear MUT.
  pose proof (wmono_trans rsegs _ _ _ WMT WMf) as WMT2. clear WMT.
  clear HBJ BY2 MUf WMf ST RO HMS.
  step.
  destruct (Z_lt_le_dec (Z.of_nat (length Fc) - x) (Z.min cap left)) as [SH|FL].
  - rewrite (Z.min_r (Z.min cap left)) in * by lia.
    assert (EJ : bv_unsigned (Z_to_bv 64 (Z.of_nat (length Fc) - x)) = Z.of_nat (length Fc) - x)
      by (apply unsigned_lit; lia).
    assert (EM : bv_unsigned (Z_to_bv 64 (Z.min cap left)) = Z.min cap left) by (apply unsigned_lit; lia).
    if_true.
    replace (x + (Z.of_nat (length Fc) - x)) with (Z.of_nat (length Fc)) in MS2 by lia.
    apply evt_done. do 18 eexists. exists m2.
    split; [right; split; [lia | split; [reflexivity | exact MS2]]|].
    split; [exact HPS|]. split; [exists bj2; split; [exact HBJ2 | exact HBN2]|].
    split; [exact MUT2|]. split; [exact WMT2|]. split; [exact RO2 | exact ST2].
  - rewrite (Z.min_l (Z.min cap left)) in * by lia.
    if_false.
    step.
    rep_reg 19 (Z_to_bv 64 (bv_swrap 32 (left - Z.min cap left))) ltac:(symmetry; apply subw_swrap; lia).
    step.
    destruct (Z.eq_dec (left - Z.min cap left) 0) as [Z0|Z0].
    + assert (C : bv_eqb (Z_to_bv 64 (bv_swrap 32 (left - Z.min cap left))) (Z_to_bv 64 0) = true)
        by (rewrite eqb_swrap0 by lia; apply Z.eqb_eq; exact Z0).
      rewrite C. cbn [negb].
      do 2 step.
      replace (x + Z.min cap left) with (x + left) in MS2 by lia.
      apply evt_done. do 18 eexists. exists m2.
      split; [left; split; [lia | split; [reflexivity | exact MS2]]|].
      split; [exact HPS|]. split; [exists bj2; split; [exact HBJ2 | exact HBN2]|].
      split; [exact MUT2|]. split; [exact WMT2|]. split; [exact RO2 | exact ST2].
    + assert (C : bv_eqb (Z_to_bv 64 (bv_swrap 32 (left - Z.min cap left))) (Z_to_bv 64 0) = false)
        by (rewrite eqb_swrap0 by lia; apply Z.eqb_neq; exact Z0).
      rewrite C. cbn [negb].
      eapply evt_cut.
      { eapply (IH _ sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ _ _ _ _ s5 s6 _ s8 s9 s10 s11 _ _ _ _ F fc m2
                  ps buf cap h b (x + Z.min cap left) (left - Z.min cap left) lo Fc pv nx sw0 l1 l2 l3 bj2 pad);
          try reflexivity; try eassumption; try lia. }
      intros ms' (ra3 & t03 & t13 & t23 & a03 & a13 & a23 & a33 & a43 & a53 & a63 & a73 & s33 & s43 & t33 & t43 & t53 & t63
        & m3 & DISJ & HPS3 & (bj3 & HBJ3 & HBN3) & MU3 & WM3 & RO3 & ST3).
      replace (x + Z.min cap left + (left - Z.min cap left)) with (x + left) in DISJ by lia.
      apply evt_done. do 18 eexists. exists m3.
      split; [exact DISJ|].
      split; [exact HPS3|]. split; [exists bj3; split; [exact HBJ3 | lia]|].
      split; [exact (munch_trans _ _ _ _ MUT2 MU3)|].
      split; [exact (wmono_trans rsegs _ _ _ WMT2 WM3)|]. split; [exact RO3 | exact ST3].
  Unshelve. all: try exact (Z_to_bv 64 0).
Qed.
