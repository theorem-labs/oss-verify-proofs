From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge Arr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel pcap_source_struct pcap_source_struct_next
  pcap_source_next_lib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require Import PWalkDef PWalk.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(* The 4-byte read of the record's incl field with the optional byte swap (0x1308c-0x130d4). *)
Lemma pcap_W_hw :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (F : list byte) (b e swz : Z) (sw : bool),
    bv_unsigned s8 = b + e -> a1 = wz swz -> (swz = 0 \/ swz = 1) -> sw = (swz =? 1) -> a4 = wz 0xff00 ->
    bytes_at rsegs m b F -> 0 <= e -> e + 12 <= flen F ->
    evt rsegs
      (fun ms' => exists t0' t1' a6' : word,
         ms' = MS (mkR ra sp gp tp t0' t1' t2 s0 s1 a0 a1 a2 a3 a4 a5 a6' (wz (bv_swrap 32 (hw sw F e 8)))
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) FR (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x4d4)%Z)) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x488)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m F b e swz sw ES8 EA1 HSW ESW EA4 HF He HE.
  subst a1 a4. unfold flen in HE.
  assert (HB : forall k, 8 <= k < 12 ->
            ov_read_bytes rsegs m (wa (bv_unsigned s8 + k)) 1 = Some [nth (Z.to_nat (e + k)) F (Z_to_bv 8 0)]).
  { intros k Hk. rewrite ES8. replace (b + e + k) with (b + (e + k)) by lia.
    apply bytes_at_byte; [exact HF | lia]. }
  pose proof (HB 8 ltac:(lia)) as HB8. pose proof (HB 9 ltac:(lia)) as HB9.
  pose proof (HB 10 ltac:(lia)) as HB10. pose proof (HB 11 ltac:(lia)) as HB11. clear HB.
  destruct HSW as [SW|SW]; subst swz; cbn in ESW; subst sw; unfold wz.
  - do 11 step. try if_true.
    rep_reg 17 (Z_to_bv 64 (bv_swrap 32 (hw false F e 8))) ltac:(hw_eq).
    apply evt_done. do 3 eexists. reflexivity.
  - do 11 step. try if_false. do 8 step.
    rep_reg 17 (Z_to_bv 64 (bv_swrap 32 (hw true F e 8))) ltac:(hw_eq).
    apply evt_done. do 3 eexists. reflexivity.
Qed.

Lemma bytes_at_ov8 : forall m a v, bytes_at rsegs m a (le8 v) -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 v).
Proof.
  intros m a v H.
  pose proof (bytes_at_read rsegs m a (le8 v) 0 8 H ltac:(lia) ltac:(rewrite length_le8; lia)) as R.
  rewrite Z.add_0_r in R. rewrite R. f_equal. all: try (apply firstn_all2; rewrite length_le8; lia).
Qed.

Lemma bytes_at_ov4 : forall m a v, bytes_at rsegs m a (le4 v) -> ov_read_bytes rsegs m (wa a) 4 = Some (le4 v).
Proof.
  intros m a v H.
  pose proof (bytes_at_read rsegs m a (le4 v) 0 4 H ltac:(lia) ltac:(rewrite length_le4; lia)) as R.
  rewrite Z.add_0_r in R. rewrite R. f_equal. all: try (apply firstn_all2; rewrite length_le4; lia).
Qed.

Lemma lor_ones64 : forall x, 0 <= x < 2 ^ 64 -> Z.lor (Z.ones 64) x = Z.ones 64.
Proof.
  intros x Hx. apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec.
  destruct (Z.lt_ge_cases i 64) as [L|L].
  - rewrite Z.ones_spec_low by lia. reflexivity.
  - rewrite Z.ones_spec_high by lia. cbn [orb].
    destruct (Z.eq_dec x 0) as [->|NZ]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|].
    pose proof (proj1 (Z.log2_lt_pow2 x 64 ltac:(lia)) ltac:(lia)). lia.
Qed.

Ltac w_done := apply evt_done; do 10 eexists; reflexivity.

(* The end loop 0x13080-0x13100 (with the check at 0x131b4-0x131c0), from a record q of the skips chain
   to the call of pcap_source_close; N bounds the number of records left. *)
Lemma pcap_W_loop : forall (N : nat) (F : list byte) (sw : bool) (q Q d b swz n : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  (Z.to_nat (flen F - q) < N)%nat -> skips sw F (8 * d) q Q ->
  s8 = wz q -> 0 <= q < flen F -> flen F < 2 ^ 26 -> a0 = wz (flen F) -> t2 = wz d -> 0 <= d < 256 ->
  s1 = wz (8 * d) -> a1 = wz swz -> (swz = 0 \/ swz = 1) -> sw = (swz =? 1) -> a4 = wz 0xff00 -> a3 = wz (-1) ->
  s4 = wz b -> bytes_at rsegs m b F -> a2 = wz n -> n = res_of sw F (8 * d) Q -> kind sw F (8 * d) Q <> KFit ->
  evt rsegs
    (fun ms' => exists (t0' t1' t2' a1' a3' a4' a5' a6' a7' s8' : word),
       ms' = MS (mkR (wz (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x508)%Z)) sp gp tp t0' t1' t2' s0 s1 (wz (bv_unsigned sp + 32)) a1' a2 a3' a4' a5' a6' a7'
                     s2 s3 s4 s5 s6 s7 s8' s9 s10 s11 t3 t4 t5 t6) FR (Z_to_bv 64 (symaddr Symbols.Plain.s_pcap_source_close)) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x47c)%Z)) fc None m (seg_rom rsegs)).
Proof.
  induction N as [|N IH];
    intros F sw q Q d b swz n ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      t3 t4 t5 t6 FR fc m HN HS ES8 HQ H26 EA0 ET2 HD ES1 EA1 HSW ESW EA4 EA3 ES4 HF EA2 EN KQ; [lia|].
  subst s8 a0 t2 s1 a1 a4 a3 s4 a2.
  pose proof (bytes_at_bound rsegs _ _ _ HF) as HFB. change (Z.of_nat (length F)) with (flen F) in HFB.
  unfold wz.
  assert (E1 : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (E2 : bv_unsigned (Z_to_bv 64 (flen F)) = flen F) by (apply unsigned_lit; lia).
  assert (E3 : bv_unsigned (Z_to_bv 64 (q + 16)) = q + 16) by (apply unsigned_lit; lia).
  assert (EB : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
  assert (EC : bv_unsigned (Z_to_bv 64 (8 * d)) = 8 * d) by (apply unsigned_lit; lia).
  step. rewrite ?E1. step.
  destruct (Z_lt_le_dec (flen F) (q + 16)) as [C1|C1].
  { (* fewer than 16 bytes left: KCutH *)
    assert (K : kind sw F (8 * d) q = KCutH) by (unfold kind; bool_dec; reflexivity).
    pose proof (skips_exit sw F (8 * d) q Q HS ltac:(rewrite K; discriminate) ltac:(rewrite K; discriminate)) as EQ.
    subst Q. assert (R : res_of sw F (8 * d) q = -1) by (unfold res_of; rewrite K; reflexivity).
    rewrite R in EN. subst n.
    if_true. step. if_false. step. step. w_done. }
  (* at least 16 bytes left: read incl *)
  if_false. step.
  eapply evt_cut.
  { eapply pcap_W_hw with (F := F) (b := b) (e := q) (swz := swz) (sw := sw);
      [rewrite unsigned_lit by lia; reflexivity | reflexivity | exact HSW | exact ESW | reflexivity | exact HF
      | lia | lia]. }
  intros ms' (t0' & t1' & a6' & ->).
  change (hw sw F q 8) with (incl sw F q). unfold wz.
  pose proof (hw_range sw F q 8) as RI. change (hw sw F q 8) with (incl sw F q) in RI.
  step.
  destruct (Z.eq_dec (incl sw F q) 0) as [I0|I0].
  { (* KEmpty: go on at q + 16 *)
    assert (C : bv_eqb (Z_to_bv 64 (bv_swrap 32 (incl sw F q))) (Z_to_bv 64 0) = true)
      by (rewrite eqb_swrap0 by lia; apply Z.eqb_eq; exact I0).
    rewrite C; cbv iota.
    assert (K : kind sw F (8 * d) q = KEmpty) by (unfold kind; bool_dec; reflexivity).
    pose proof (skips_empty_inv sw F (8 * d) q Q HS K) as HS'.
    step. step.
    destruct (Z.eq_dec (q + 16) (flen F)) as [C2|C2].
    - assert (K2 : kind sw F (8 * d) (q + 16) = KEnd) by (unfold kind; rewrite C2, Z.sub_diag; reflexivity).
      pose proof (skips_exit sw F (8 * d) (q + 16) Q HS' ltac:(rewrite K2; discriminate)
                    ltac:(rewrite K2; discriminate)) as EQ.
      subst Q. assert (R : res_of sw F (8 * d) (q + 16) = 0) by (unfold res_of; rewrite K2; reflexivity).
      rewrite R in EN. subst n.
      if_false. step. step. if_false. step. step. w_done.
    - if_true. eapply (IH F sw (q + 16) Q d b swz n); try reflexivity; try eassumption; lia. }
  assert (C : bv_eqb (Z_to_bv 64 (bv_swrap 32 (incl sw F q))) (Z_to_bv 64 0) = false)
    by (rewrite eqb_swrap0 by lia; apply Z.eqb_neq; exact I0).
  rewrite C; cbv iota.
  step. step. rewrite zx32_val, uns_swrap_mod32_0 by lia.
  assert (EI : bv_unsigned (Z_to_bv 64 (incl sw F q)) = incl sw F q) by (apply unsigned_lit; lia).
  assert (E4 : bv_unsigned (Z_to_bv 64 (q + 16 + incl sw F q)) = q + 16 + incl sw F q) by (apply unsigned_lit; lia).
  step. rewrite ?E3, ?EI. step.
  destruct (Z_le_gt_dec (incl sw F q) (8 * d)) as [CI|CI].
  { (* incl <= cap: KFit (excluded) or KCutFit *)
    destruct (Z_le_gt_dec (q + 16 + incl sw F q) (flen F)) as [CF|CF].
    { exfalso. assert (K : kind sw F (8 * d) q = KFit) by (unfold kind; bool_dec; reflexivity).
      pose proof (skips_exit sw F (8 * d) q Q HS ltac:(rewrite K; discriminate) ltac:(rewrite K; discriminate)) as EQ.
      subst Q. exact (KQ K). }
    assert (K : kind sw F (8 * d) q = KCutFit) by (unfold kind; bool_dec; reflexivity).
    pose proof (skips_exit sw F (8 * d) q Q HS ltac:(rewrite K; discriminate) ltac:(rewrite K; discriminate)) as EQ.
    subst Q. assert (R : res_of sw F (8 * d) q = -1) by (unfold res_of; rewrite K; reflexivity).
    rewrite R in EN. subst n.
    if_true. step. step. step.
    assert (SL : v_sltu (Z_to_bv 64 (flen F)) (Z_to_bv 64 (q + 16 + incl sw F q)) = Z_to_bv 64 1)
      by (unfold v_sltu, c_ltu, bv_ltu; rewrite E2, E4; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
    rewrite SL, EI.
    rep_reg 13 (Z_to_bv 64 (-1))
      ltac:(apply Z_to_bv_eqm; change (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 1)))) with (Z.ones 64);
            rewrite lor_ones64 by lia; reflexivity).
    step. if_true. step. step. w_done. }
  (* incl > cap *)
  if_false. step.
  destruct (Z.eq_dec d 0) as [D0|D0].
  { assert (K : kind sw F (8 * d) q = KBig0) by (unfold kind; bool_dec; reflexivity).
    pose proof (skips_exit sw F (8 * d) q Q HS ltac:(rewrite K; discriminate) ltac:(rewrite K; discriminate)) as EQ.
    subst Q. assert (R : res_of sw F (8 * d) q = -1) by (unfold res_of; rewrite K; reflexivity).
    rewrite R in EN. subst n.
    if_true. step. if_false. step. step. w_done. }
  if_false. step.
  destruct (Z_lt_le_dec (flen F) (q + 16 + incl sw F q)) as [CB|CB].
  { assert (K : kind sw F (8 * d) q = KCutBig) by (unfold kind; bool_dec; reflexivity).
    pose proof (skips_exit sw F (8 * d) q Q HS ltac:(rewrite K; discriminate) ltac:(rewrite K; discriminate)) as EQ.
    subst Q. assert (R : res_of sw F (8 * d) q = -1) by (unfold res_of; rewrite K; reflexivity).
    rewrite R in EN. subst n.
    if_true. step. if_false. step. step. w_done. }
  (* KBig: go on after the record *)
  assert (K : kind sw F (8 * d) q = KBig) by (unfold kind; bool_dec; reflexivity).
  pose proof (skips_big_inv sw F (8 * d) q Q HS K) as HS'.
  if_false. step. step.
  destruct (Z.eq_dec (q + 16 + incl sw F q) (flen F)) as [C2|C2].
  { assert (K2 : kind sw F (8 * d) (q + 16 + incl sw F q) = KEnd)
      by (unfold kind; rewrite C2, Z.sub_diag; reflexivity).
    pose proof (skips_exit sw F (8 * d) _ Q HS' ltac:(rewrite K2; discriminate)
                  ltac:(rewrite K2; discriminate)) as EQ.
    subst Q. assert (R : res_of sw F (8 * d) (q + 16 + incl sw F q) = 0) by (unfold res_of; rewrite K2; reflexivity).
    rewrite R in EN. subst n.
    if_false. step. step. if_false. step. step. w_done. }
  if_true. eapply (IH F sw (q + 16 + incl sw F q) Q d b swz n); try reflexivity; try eassumption; lia.
Qed.

(* Segment W, from the walk's end (cut K5, 0x1305c) to the call of pcap_source_close (0x1357c, ra 0x1310c):
   the reader's last answer n = res_of Q at the first record Q of the skips chain from p that is not a fit
   equals the end loop's value want_of Q, so no check branches to the stop path 0x131c4. sp_h is the
   slot's sp; p <= flen F bounds s8 for the comparisons with the file length. *)
Lemma pcap_W_x :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (F : list byte) (sw : bool)
         (sp_h n p Q cap d b swz : Z),
    bv_unsigned sp = sp_h ->
    a2 = wz n -> n = res_of sw F cap Q -> kind sw F cap Q <> KFit ->
    s8 = wz p -> 24 <= p -> p <= flen F -> skips sw F cap p Q ->
    s1 = wz cap -> cap = 8 * d -> 0 <= d < 256 -> bytes_at rsegs m (sp_h + 8) (le8 (wz d)) ->
    s4 = wz b -> bytes_at rsegs m b F ->
    s6 = wz (symaddr Symbols.Plain.s_g_file_len) -> bytes_at rsegs m (symaddr Symbols.Plain.s_g_file_len) (le8 (wz (flen F))) ->
    bytes_at rsegs m (sp_h + 40) (le4 (wz swz)) -> (swz = 0 \/ swz = 1) -> sw = (swz =? 1) ->
    flen F < 2 ^ 26 ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a3' a4' a5' a6' a7' s8' : word),
         ms' = MS (mkR (wz (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x508)%Z)) sp gp tp t0' t1' t2' s0 s1 (wz (sp_h + 32)) a1' a2 a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8' s9 s10 s11 t3 t4 t5 t6) FR (Z_to_bv 64 (symaddr Symbols.Plain.s_pcap_source_close)) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x458)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m F sw sp_h n p Q cap d b swz ESP EA2 EN KQ ES8 P24 PF HS ES1 ECAP HD HDB ES4 HF ES6 HFL HSWB HSW ESW H26.
  subst sp_h a2 s8 s1 cap s4 s6.
  pose proof (bytes_at_ov8 _ _ _ HFL) as RFL. pose proof (bytes_at_ov8 _ _ _ HDB) as RD.
  pose proof (bytes_at_ov4 _ _ _ HSWB) as RSW. clear HFL HDB HSWB.
  unfold wz in *.
  pose proof (bytes_at_bound rsegs _ _ _ HF) as HFB. change (Z.of_nat (length F)) with (flen F) in HFB.
  destruct (kind_nfit sw F (8 * d) Q KQ) as [_ HN]. rewrite <- EN in HN.
  assert (C0 : bv_lts (Z_to_bv 64 n) (Z_to_bv 64 (-1)) = false) by (destruct HN as [-> | ->]; reflexivity).
  step. step. rewrite C0; cbv iota. clear C0.
  step. step.
  assert (EP : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (Z_to_bv 64 (flen F)) = flen F) by (apply unsigned_lit; lia).
  step.
  destruct (Z.eq_dec p (flen F)) as [PE|PE].
  - assert (K : kind sw F (8 * d) p = KEnd) by (unfold kind; rewrite PE, Z.sub_diag; reflexivity).
    pose proof (skips_exit sw F (8 * d) p Q HS ltac:(rewrite K; discriminate) ltac:(rewrite K; discriminate)) as EQ.
    subst Q. assert (R : res_of sw F (8 * d) p = 0) by (unfold res_of; rewrite K; reflexivity).
    rewrite R in EN. subst n.
    if_true. step. step. if_false. step. step. w_done.
  - if_false. step. step. step. step.
    rep_reg 11 (Z_to_bv 64 swz) ltac:(destruct HSW as [-> | ->]; reflexivity).
    eapply (pcap_W_loop (S (Z.to_nat (flen F - p))) F sw p Q d b swz n); try reflexivity; try eassumption; lia.
Qed.
