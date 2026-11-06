(** reac_segconf_parse_file, plain build (image 3776ca44d75c, 0x14cbc): piece P6, the role branch
    (reac_segconf.c:236-246 with reac_role_intent_parse inlined, reac_role.h:110-120). Family F3 of the
    contracts; the piece statement is S_P6 of lib/Prog/reac_segconf_parse_file_pieces_c.v. lib/U/Prog/pf_p6.v is
    the UBSan twin.

    S_P6 = forall n, (H_INTENT n -> H_ROLE n) /\ (H_KREF n -> H_PROV n -> H_INTENT n).

    ROLE 0x15074 -> INTENT 0x151e8: the fold loop at 0x15084 lowercases val into low = sp + 0x50 one byte a pass
    (`addi -0x41; sltiu 0x1a; slli 5; add; sb`: p6_fold_val), stops at the NUL or at li = 63, and stores
    low[li] = 0 at 0x151e4; the 64 bytes of low are then r_low val 0 64 and its NUL, which is INTENT's LB (p6_lowb,
    p6_lb_prefix, p6_rlow).
    INTENT -> KREF or PROV: bcmp(low, "auto" / "master" / "slave", 5 / 7 / 6) at 0x151f4 / 0x1520c / 0x15224
    (bcmp_c.v, O1_bcmp_lit_holds), then the tap / box word compares at 0x15258 / 0x15288 against the frame slots
    sp + 0x18 / sp + 0x10 (p6_word_val, O1_word_lit_holds); a hit stores role = r at 0x15490 and role_set = 1 at
    0x15498 (p6_role_rconf, giving pf_prov_mid (PRole r) rc gi) and falls into PROV with a0 = &seg[gi].role_file
    and a2 = "%s"; no hit goes to KREF with a2 = F_badrole.

    The frame facts are carried by the kit (lib/Prog/pfB_kit.v: pf_mem and its transport lemmas), the
    build-independent facts by lib/Prog/pfB_p6_spine.v. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac Bytes ZBridge FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import StrFun SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_env pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import refuse_c reac_segconf_parse_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import reac_segconf_parse_file_pieces_c bcmp_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pfB_p6_spine pfB_facts pfB_kit.
Import ListNotations.
Open Scope Z_scope.

(** The kit's lemmas (lib/Prog/pfB_facts.v and lib/Prog/pfB_kit.v) under this file's names. *)
Lemma p6s_saved_read : forall m a ws k, saved_at rsegs m a ws -> (k < length ws)%nat ->
  ov_read_bytes rsegs m (wa (a + 8 * Z.of_nat k)) 8 = Some (le8 (nth k ws (Z_to_bv 64 0))).
Proof. exact (pfb_saved_read rsegs). Qed.

Lemma p6s_cstr_at_munch : forall W m m' a s,
  cstr_at rsegs m a s -> munch W m m' -> disjoint_from W a (Z.of_nat (length s) + 8) -> cstr_at rsegs m' a s.
Proof. exact (pfb_cstr_at_munch rsegs). Qed.

Lemma p6s_rconf_at_munch : forall W m m' c rc,
  rconf_at rsegs m c rc -> munch W m m' -> disjoint_from W c SEG_C_SIZE -> rconf_at rsegs m' c rc.
Proof. exact (pfb_rconf_at_munch rsegs). Qed.

(** ** Local facts *)
Lemma p6_not_outside1 : forall a b x, ~ outside [(a, b)] x -> a <= x < b.
Proof.
  intros a b x H. cbn [outside] in H.
  destruct (Z_le_gt_dec a x), (Z_lt_ge_dec x b); try lia; exfalso; apply H; split; try lia; exact I.
Qed.

Lemma p6_outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[l h] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H].
  - destruct (Z_le_gt_dec l x), (Z_lt_ge_dec x h);
      first [ right; intros [H1 _]; lia | left; split; [lia | exact H] ].
  - right. intros [_ H2]. exact (H H2).
Qed.

(** The exits' post, stated at the exit memory, is the entry's: P6 writes only low and seg[gi]'s role fields. *)
Lemma p6_fin_keep : forall W v sp gp tp F m m' lo c st ms,
  munch W m m' -> wmono rsegs m m' ->
  (forall x, ~ outside W x -> (bv_unsigned sp + PF_LOW <= x < bv_unsigned sp + PF_LOW + 64) \/ (c <= x < c + RC_N + 4)) ->
  pf_fin v sp gp tp F m' lo c st ms -> pf_fin v sp gp tp F m lo c st ms.
Proof.
  intros W v sp gp tp F m m' lo c st ms MU WM HW H.
  unfold pf_fin, pf_ret, ret_post_fp in *.
  destruct H as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & F' & fc' & m'' & E & FR & FF
    & MU' & WM' & MI & TM & ST & RC).
  exists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, F', fc', m''.
  split; [exact E|]. split; [exact FR|]. split; [exact FF|].
  split.
  { eapply munch_trans; [|exact MU']. eapply munch_weaken; [|exact MU].
    intros x Ho. destruct (p6_outside_dec W x) as [O|O]; [exact O|]. exfalso.
    unfold PARSE_FILE_STACK, PARSE_FILE_FRAME, REFUSE_STACK, PRINTF_K, RC_PARSE_W, RC_N, RC_REFUSAL, RC_OVERFLOW,
      RC_READING, RC_GEN, PF_LOW in *.
    pose proof (bv_unsigned_in_range 64 sp) as RS. unfold bv_modulus in RS. cbn in RS.
    cbn [outside] in Ho. destruct (HW x O); lia. }
  split; [eapply wmono_trans; [exact WM | exact WM']|].
  split; [exact MI|]. split; [exact TM|]. split; [exact ST|]. exact RC.
Qed.

(** bcmp at a call site: its contract's post, as a continuation. *)
Lemma p6_bcmp : forall (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc m (LB rs : list byte) v,
  bcmp_contract ->
  bytes_at rsegs m (bv_unsigned a0) LB -> bytes_at rsegs m (bv_unsigned a1) rs ->
  memcmp_model LB rs (Z.to_nat (bv_unsigned a2)) = Some v -> mem_inv rsegs m ->
  (forall m' (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
     munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> bytes_at rsegs m' (bv_unsigned a0) LB ->
     evt rsegs Q (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 v) x11 x12 x13 x14 x15 x16 x17
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 BCMP) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m LB rs v BC B0 B1 MM MI K.
  eapply evt_cut; [eapply BC; [exact B0 | exact B1 | exact MM | exact MI]|].
  intros ms' (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m' & -> & MU & WM
    & MI' & B0' & _).
  apply K; assumption.
Qed.

Lemma p6_lit : forall m a w, mem_inv rsegs m -> 0 <= a -> a + Z.of_nat (length (zb (w ++ [0]))) <= 2 ^ 64 ->
  ro_bytes_b rsegs a (zb (w ++ [0])) = true -> bytes_at rsegs m a (zb (w ++ [0])).
Proof.
  intros m a w MI H0 H1 H2. apply ro_bytes_at; [exact MI | exact H0 | exact H1 |].
  apply ro_bytes_b_sound. exact H2.
Qed.

Lemma p6_wfacts : forall w, forallb (fun x => negb (x =? 0) && (0 <=? x) && (x <? 256)) w = true ->
  ~ In 0 w /\ Forall (fun x => 0 <= x < 256) w.
Proof.
  intros w H. rewrite forallb_forall in H. split.
  - intros Hin. specialize (H 0 Hin). cbn in H. discriminate H.
  - apply Forall_forall. intros x Hx. specialize (H x Hx).
    apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [_ H2].
    apply Z.leb_le in H2. apply Z.ltb_lt in H3. lia.
Qed.

Ltac fix_ret :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity])
  end.

(** The tap compare (0x1522c .. 0x15258): `lbu, lbu, lbu, lb; slli, or, slli, slli, or, or` build pf_word4 of the
    four bytes of low, `ld a1, 0x18(sp)` reads the tap slot and `beq` goes to 0x15420 (role = 3) or falls to the
    box compare at 0x1525c. Stepped over abstract bytes, away from the walk's context. *)
Lemma p6_tapcmp : forall (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc m (b0 b1 b2 b3 : byte),
  ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned sp + 80)) 1 = Some [b0] ->
  ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned sp + 81)) 1 = Some [b1] ->
  ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned sp + 82)) 1 = Some [b2] ->
  ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned sp + 83)) 1 = Some [b3] ->
  ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned sp + 24)) 8 = Some (le8 (Z_to_bv 64 PF_TAP_WORD)) ->
  (forall x10 x11 x12 x13 : word, pf_word4 [b0; b1; b2; b3] = PF_TAP_WORD ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                          t3 t4 t5 t6) F (Z_to_bv 64 0x15420) fc None m (seg_rom rsegs))) ->
  (forall x10 x11 x12 x13 : word, pf_word4 [b0; b1; b2; b3] <> PF_TAP_WORD ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                          t3 t4 t5 t6) F (Z_to_bv 64 0x1525c) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6) F (Z_to_bv 64 0x1522c) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m b0 b1 b2 b3 R0 R1 R2 R3 RT KT KF.
  pose proof (p6_word4_range [b0; b1; b2; b3]) as W4R.
  do 12 zstep.
  rewrite (p6_word_val b0 b1 b2 b3).
  if_cases K;
    rewrite (p6_bveq_small (pf_word4 [b0; b1; b2; b3]) PF_TAP_WORD) in K by (unfold PF_TAP_WORD; lia).
  - apply Z.eqb_eq in K. apply KT. exact K.
  - apply Z.eqb_neq in K. apply KF. exact K.
Qed.

(** The box compare (0x1525c .. 0x15288): the same, against the box slot sp + 0x10; `beq` goes to 0x1548c
    (role = 4) or falls to the bad-role refusal at 0x1528c. *)
Lemma p6_boxcmp : forall (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc m (b0 b1 b2 b3 : byte),
  ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned sp + 80)) 1 = Some [b0] ->
  ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned sp + 81)) 1 = Some [b1] ->
  ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned sp + 82)) 1 = Some [b2] ->
  ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned sp + 83)) 1 = Some [b3] ->
  ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned sp + 16)) 8 = Some (le8 (Z_to_bv 64 PF_BOX_WORD)) ->
  (forall x10 x11 x12 x13 : word, pf_word4 [b0; b1; b2; b3] = PF_BOX_WORD ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                          t3 t4 t5 t6) F (Z_to_bv 64 0x1548c) fc None m (seg_rom rsegs))) ->
  (forall x10 x11 x12 x13 : word, pf_word4 [b0; b1; b2; b3] <> PF_BOX_WORD ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                          t3 t4 t5 t6) F (Z_to_bv 64 0x1528c) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6) F (Z_to_bv 64 0x1525c) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m b0 b1 b2 b3 R0 R1 R2 R3 RB KT KF.
  pose proof (p6_word4_range [b0; b1; b2; b3]) as W4R.
  do 12 zstep.
  rewrite (p6_word_val b0 b1 b2 b3).
  if_cases K;
    rewrite (p6_bveq_small (pf_word4 [b0; b1; b2; b3]) PF_BOX_WORD) in K by (unfold PF_BOX_WORD; lia).
  - apply Z.eqb_eq in K. apply KT. exact K.
  - apply Z.eqb_neq in K. apply KF. exact K.
Qed.

(** The piece's frame facts carried across a write list inside pf_Wp (the kit's pf_mem). *)
Lemma p6_keep : forall (W : list ivl) m m' fc sp lo v c t s o ln d n rc nm,
  pf_ctx m fc sp lo v c t s o ln d n -> rconf_at rsegs m c rc -> pf_nm_at m (sp + PF_NAMEBUF) nm ->
  munch W m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  (forall x, ~ outside W x -> (sp + PF_LOW <= x < sp + PF_LOW + 64) \/ (c <= x < c + RC_N + 4)) ->
  pf_ctx m' fc sp lo v c t s o ln d n /\ pf_nm_at m' (sp + PF_NAMEBUF) nm.
Proof.
  intros W m m' fc sp lo v c t s o ln d n rc nm CTX RC NM MU WM MI HW.
  pose proof CTX as (ENV & TXT & SPL & R1 & R2 & R3).
  pose proof ENV as (_ & _ & _ & _ & PE & _). pose proof PE as (FRM & _).
  assert (SUB : sub_fp W (pf_Wp sp c)).
  { intros x Ho. destruct (p6_outside_dec W x) as [O|O]; [exact O|]. exfalso. revert Ho.
    unfold pf_Wp, PF_LO, PF_SCRATCH, PF_NAMEBUF, PF_LOW, RC_PARSE_W, RC_N, RC_REFUSAL, RC_OVERFLOW, RC_READING,
      RC_GEN, PARSE_FILE_STACK, PARSE_FILE_FRAME, REFUSE_STACK, PRINTF_K in *.
    cbn [outside]. intros Ho. repeat match goal with H : _ /\ _ |- _ => destruct H end.
    destruct (HW x O); lia. }
  assert (PM : pf_mem m m' sp lo c)
    by (eapply pf_mem_call; [eapply pf_mem_refl; [exact ENV | exact RC] | exact SUB | exact MU | exact WM | exact MI]).
  split; [|eapply pf_nm_at_mem; [exact NM | exact PM]].
  split; [eapply pf_env_mem; [exact ENV | exact PM | exact FRM]|].
  split; [eapply pf_text_mem; [exact TXT | exact PM]|].
  split; [eapply pf_spill_mem; [exact SPL | exact PM]|].
  split; [exact R1 | split; [exact R2 | exact R3]].
Qed.

(** The c block is writable as far as c->n (the kit's pf_c_wr). *)
Lemma p6_cwr : forall m fc sp lo v c t s o ln d n rc,
  pf_ctx m fc sp lo v c t s o ln d n -> rconf_at rsegs m c rc -> wr_at rsegs m c (RC_N + 4).
Proof.
  intros m fc sp lo v c t s o ln d n rc CTX RC.
  pose proof (pf_c_wr m sp lo c rc (pf_wok_of m fc sp lo c v rc (proj1 CTX) RC) RC) as (H1 & H2 & H3).
  unfold SEG_C_SIZE in *. split; [exact H1|]. split; [unfold RC_N; lia|].
  intros i Hi. apply H3. unfold RC_N in Hi. lia.
Qed.

Lemma p6_role : forall n, H_INTENT n -> H_ROLE n.
Proof.
  intros n HI. unfold H_ROLE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo v c t s rc nm o ln d gi kp vp key val CTX ST RG HS9 HS6 KV HS8 HS7 KEY.
  rewrite (p6_rkey rc gi nm (ln + 1) (pf_tline s o) key val (proj1 KV) KEY).
  destruct KV as (_ & _ & _ & CV & IBV).
  pose proof CTX as ((C0 & C16 & APc & NOI & PE & CAT & SOK & MI & SAV) & _).
  pose proof PE as (FRM & TM & SSP & ILO & SPH).
  pose proof SOK as (STK & DEP & AL & NR).
  pose proof ST as (RCA & CUR & NMA & CNT).
  subst s7.
  assert (DEP' : lo + 6032 <= bv_unsigned sp)
    by (unfold PARSE_FILE_STACK, PARSE_FILE_FRAME, REFUSE_STACK, PRINTF_K in DEP; lia).
  assert (SPH' : bv_unsigned sp + 976 < 2 ^ 63) by (unfold PARSE_FILE_FRAME in SPH; lia).
  assert (LO0 : 0 <= lo) by (destruct STK as [? _]; assumption).
  unfold PARSE_FILE_FRAME in STK. unfold pf_inb, PF_BUF in IBV.
  unfold apart, SEG_C_SIZE in APc.
  destruct (stk_split rsegs m lo (bv_unsigned sp + 80) (bv_unsigned sp + 976) STK ltac:(lia)) as [_ STK1].
  destruct (stk_split rsegs m (bv_unsigned sp + 80) (bv_unsigned sp + 144) (bv_unsigned sp + 976) STK1 ltac:(lia))
    as [STKL _].
  destruct (stk_bytes rsegs m _ _ STKL ltac:(lia)) as (LB0 & LL0 & BL0).
  assert (LL : length LB0 = 64%nat)
    by (rewrite LL0; replace (bv_unsigned sp + 144 - (bv_unsigned sp + 80)) with 64 by lia; reflexivity).
  clear LL0.
  pose proof CV as (bsv & slv & BV & ZV & NZV & SLV).
  assert (LBV : length bsv = length val) by (rewrite <- ZV; unfold zs; symmetry; apply length_map).
  assert (RV : forall i, 0 <= nth i val 0 < 256).
  { intros i. rewrite <- ZV. unfold zs. destruct (Nat.lt_ge_cases i (length bsv)) as [Hi|Hi].
    - rewrite (nth_indep _ 0 (bv_unsigned ZERO)) by (rewrite length_map; exact Hi). rewrite map_nth.
      pose proof (bv_unsigned_in_range 8 (nth i bsv ZERO)) as R. unfold bv_modulus in R.
      change (2 ^ Z.of_N 8) with 256 in R. exact R.
    - rewrite nth_overflow by (rewrite length_map; lia). lia. }
  assert (RVF : Forall (fun x => 0 <= x < 256) val).
  { apply Forall_forall. intros x Hx. destruct (In_nth val x 0 Hx) as (i & Hi & <-). apply RV. }
  assert (BVZ : bytes_at rsegs m vp (bsv ++ [ZERO])).
  { pose proof BV as BV'. replace (bsv ++ ZERO :: slv) with ((bsv ++ [ZERO]) ++ slv) in BV'
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app in BV'. exact (proj1 BV'). }
  assert (HBV : forall i, (i <= length val)%nat -> nth_error (bsv ++ [ZERO]) i = Some (Z_to_bv 8 (nth i val 0))).
  { intros i Hi. rewrite <- ZV. apply p6_byte_at. lia. }
  assert (NZE : forall i, (i <= length val)%nat -> nth i val 0 = 0 -> i = length val).
  { intros i Hi E. destruct (Nat.eq_dec i (length val)) as [->|Ne]; [reflexivity|].
    exfalso. exact (p6_nth_nz val i NZV ltac:(lia) E). }
  set (Wl := [(bv_unsigned sp + 80, bv_unsigned sp + 144)]).
  assert (HWl : forall x, ~ outside Wl x ->
            (bv_unsigned sp + PF_LOW <= x < bv_unsigned sp + PF_LOW + 64) \/ (c <= x < c + RC_N + 4)).
  { intros x Hx. apply p6_not_outside1 in Hx. unfold PF_LOW. left. lia. }
  lazymatch goal with |- evt _ ?QQ _ => set (Q := QQ) end.
  (* 0x151dc: low[li] = 0, then INTENT *)
  assert (EXIT : forall (li : nat) (m1 : word -> option byte) (x10 x11 x12 x13 x14 : word),
    (li = length val \/ li = 63%nat) -> (li <= length val)%nat -> (li <= 63)%nat ->
    x12 = Z_to_bv 64 (Z.of_nat li) ->
    munch Wl m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
    stk rsegs m1 (bv_unsigned sp + 80) (bv_unsigned sp + 144) ->
    bytes_at rsegs m1 (bv_unsigned sp + 80) (p6_lowb val LB0 li) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 x14 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 vp) s8 s9
                         s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x151dc) fc None m1 (seg_rom rsegs))).
  { intros li m1 x10 x11 x12 x13 x14 Eli Hl1 Hl2 -> MU1 WM1 MI1 ST1 BL1.
    assert (SO : store_ok rsegs m1 (wa (bv_unsigned sp + 80 + Z.of_nat li)) 1 = true).
    { apply (wr_at_store_ok rsegs m1 (bv_unsigned sp + 80) (bv_unsigned sp + 144 - (bv_unsigned sp + 80)));
        [apply p6_stk_wr; [exact ST1 | lia] | lia | lia]. }
    zstep. zstep. zstep.
    replace (le1 (Z_to_bv 64 0)) with [ZERO] by reflexivity.
    set (m2 := write_to_mem m1 (Z_to_bv 64 (bv_unsigned sp + 80 + Z.of_nat li)) [ZERO]).
    assert (MU2 : munch Wl m m2).
    { apply (munch_write Wl m m1 (bv_unsigned sp + 80 + Z.of_nat li) [ZERO] MU1); unfold Wl; cbn [length inside];
        lia. }
    assert (WM2 : wmono rsegs m m2) by (apply wmono_write; exact WM1).
    assert (MI2 : mem_inv rsegs m2) by (apply mem_inv_store; [exact MI1 | exact SO]).
    assert (BL2 : bytes_at rsegs m2 (bv_unsigned sp + 80) (zb (map lower (firstn li val)) ++ ZERO :: skipn (S li) LB0)).
    { pose proof (bytes_at_write_inside rsegs m1 (bv_unsigned sp + 80) (p6_lowb val LB0 li) (Z.of_nat li) [ZERO] BL1)
        as NW.
      rewrite Nat2Z.id in NW. rewrite p6_lowb_fin in NW by lia.
      apply NW; [lia | rewrite p6_lowb_len by lia; cbn [length]; lia]. }
    clearbody m2.
    pose proof (p6_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX RCA NMA MU2 WM2 MI2 HWl) as [CTX2 NM2].
    assert (RC2 : rconf_at rsegs m2 c rc).
    { eapply p6s_rconf_at_munch; [exact RCA | exact MU2 |]. unfold Wl, PARSE_FILE_FRAME, SEG_C_SIZE in *.
      cbn [disjoint_from]. split; [lia | exact I]. }
    assert (CV2 : cstr_at rsegs m2 vp val).
    { eapply p6s_cstr_at_munch; [exact CV | exact MU2 |]. unfold Wl. cbn [disjoint_from]. split; [lia | exact I]. }
    eapply evt_mono.
    { eapply HI with (lo := lo) (v := v) (c := c) (t := t) (s := s) (rc := rc) (nm := nm) (o := o) (ln := ln)
        (d := d) (gi := gi) (vp := vp) (val := val).
      - exact CTX2.
      - split; [exact RC2 | split; [exact CUR | split; [exact NM2 | exact CNT]]].
      - exact RG.
      - exact HS9.
      - exact HS6.
      - unfold PF_LOW. reflexivity.
      - reflexivity.
      - exact CV2.
      - unfold pf_inb, PF_BUF. exact IBV.
      - exists (zb (map lower (firstn li val)) ++ ZERO :: skipn (S li) LB0). split; [|split].
        + rewrite length_app. cbn [length]. rewrite p6_zb_len by lia. rewrite length_skipn. lia.
        + unfold PF_LOW. exact BL2.
        + rewrite (p6_rlow_len val li NZV Eli Hl1 Hl2), (p6_rlow val li NZV Eli Hl1 Hl2).
          apply p6_lb_prefix; [exact RVF | exact Hl1]. }
    intros ms' HF. unfold Q. eapply p6_fin_keep; [exact MU2 | exact WM2 | exact HWl | exact HF]. }
  (* the fold loop at 0x15084 *)
  assert (LOOP : forall (k li : nat) (m1 : word -> option byte) (x10 x12 x13 x14 : word),
    (63 - li = k)%nat -> (li < 63)%nat -> (li < length val)%nat ->
    x10 = Z_to_bv 64 (bv_unsigned (Z_to_bv 8 (nth li val 0))) -> x12 = Z_to_bv 64 (Z.of_nat li) ->
    munch Wl m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
    stk rsegs m1 (bv_unsigned sp + 80) (bv_unsigned sp + 144) ->
    bytes_at rsegs m1 (bv_unsigned sp + 80) (p6_lowb val LB0 li) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 (Z_to_bv 64 (vp + 1)) x12 x13 x14 a5 a6 a7
                         s2 s3 s4 s5 s6 (Z_to_bv 64 vp) s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x15084) fc None m1 (seg_rom rsegs))).
  { induction k as [|k IH]; intros li m1 x10 x12 x13 x14 Hk Hli Hlv -> -> MU1 WM1 MI1 ST1 BL1; [lia|].
    pose proof (RV li) as Rc.
    assert (SO : store_ok rsegs m1 (wa (bv_unsigned sp + 80 + Z.of_nat li)) 1 = true).
    { apply (wr_at_store_ok rsegs m1 (bv_unsigned sp + 80) (bv_unsigned sp + 144 - (bv_unsigned sp + 80)));
        [apply p6_stk_wr; [exact ST1 | lia] | lia | lia]. }
    do 7 zstep.
    rewrite (p6_u8 (nth li val 0) Rc). rewrite (p6_fold_le1 (nth li val 0) Rc).
    set (m2 := write_to_mem m1 (Z_to_bv 64 (bv_unsigned sp + 80 + Z.of_nat li)) [Z_to_bv 8 (lower (nth li val 0))]).
    assert (MU2 : munch Wl m m2).
    { apply (munch_write Wl m m1 (bv_unsigned sp + 80 + Z.of_nat li) _ MU1); unfold Wl; cbn [length inside]; lia. }
    assert (WM2 : wmono rsegs m m2) by (apply wmono_write; exact WM1).
    assert (MI2 : mem_inv rsegs m2) by (apply mem_inv_store; [exact MI1 | exact SO]).
    assert (ST2 : stk rsegs m2 (bv_unsigned sp + 80) (bv_unsigned sp + 144))
      by (apply stk_write; [exact ST1 | lia | cbn [length]; lia]).
    assert (BL2 : bytes_at rsegs m2 (bv_unsigned sp + 80) (p6_lowb val LB0 (S li))).
    { pose proof (bytes_at_write_inside rsegs m1 (bv_unsigned sp + 80) (p6_lowb val LB0 li) (Z.of_nat li)
        [Z_to_bv 8 (lower (nth li val 0))] BL1) as NW.
      rewrite Nat2Z.id in NW. rewrite p6_lowb_step in NW by lia.
      apply NW; [lia | rewrite p6_lowb_len by lia; cbn [length]; lia]. }
    clearbody m2. clear MU1 WM1 MI1 ST1 BL1 SO.
    assert (RD : ov_read_bytes rsegs m2 (wa (vp + Z.of_nat (S li))) 1 = Some [Z_to_bv 8 (nth (S li) val 0)]).
    { apply (p6_read1 rsegs m2 vp (bsv ++ [ZERO]) (S li)); [|apply HBV; lia].
      apply (bytes_at_transport rsegs Wl m m2 vp _ BVZ MU2). unfold Wl. cbn [disjoint_from].
      rewrite length_app, LBV. cbn [length]. split; [lia | exact I]. }
    zstep. zstep. zstep. zstep.
    if_cases K; zify_cond K; rewrite ?(p6_u8 (nth (S li) val 0) (RV (S li))) in K.
    - assert (E : S li = length val) by (apply NZE; [lia | exact K]).
      eapply (EXIT (S li)); [left; exact E | lia | lia | f_equal; lia | exact MU2 | exact WM2 | exact MI2
        | exact ST2 | exact BL2].
    - zstep. zstep.
      if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
      + eapply (EXIT (S li)); [right; lia | lia | lia | f_equal; lia | exact MU2 | exact WM2 | exact MI2
          | exact ST2 | exact BL2].
      + zstep.
        assert (Lv : (S li < length val)%nat).
        { destruct (Nat.lt_ge_cases (S li) (length val)) as [L|L]; [exact L|].
          exfalso. apply K. rewrite nth_overflow by lia. reflexivity. }
        eapply (IH (S li)); [lia | lia | exact Lv | reflexivity | f_equal; lia | exact MU2 | exact WM2 | exact MI2
          | exact ST2 | exact BL2]. }
  (* 0x15074: val[0] *)
  assert (R0 : ov_read_bytes rsegs m (wa (vp + Z.of_nat 0)) 1 = Some [Z_to_bv 8 (nth 0 val 0)])
    by (apply (p6_read1 rsegs m vp (bsv ++ [ZERO]) 0); [exact BVZ | apply HBV; lia]).
  unfold PF_PC_ROLE.
  zstep. zstep.
  if_cases K; zify_cond K; rewrite ?(p6_u8 (nth 0 val 0) (RV 0%nat)) in K.
  - assert (E : 0%nat = length val) by (apply NZE; [lia | exact K]).
    zstep. eapply (EXIT 0%nat); [left; exact E | lia | lia | reflexivity | apply munch_refl | apply wmono_refl
      | exact MI | exact STKL | exact BL0].
  - assert (L0 : (0 < length val)%nat).
    { destruct val as [|x val']; [cbn in K; exfalso; apply K; reflexivity | cbn; lia]. }
    zstep. zstep.
    eapply (LOOP 63%nat 0%nat); [lia | lia | exact L0 | reflexivity | reflexivity | apply munch_refl
      | apply wmono_refl | exact MI | exact STKL | exact BL0].
Qed.

Lemma p6_intent : forall n, bcmp_contract -> H_KREF n -> H_PROV n -> H_INTENT n.
Proof.
  intros n BC HK HP. unfold H_INTENT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo v c t s rc nm o ln d gi vp val CTX ST RG HS9 HS6 HA0 HS7 CV IBV (LB & LLB & BLB & PLB).
  change (pf_cur_ptr c (Some gi)) with (rseg_addr c gi) in HS6.
  subst a0 s6 s7 s9.
  unfold PF_LOW in *.
  pose proof CTX as ((C0 & C16 & APc & NOI & PE & CAT & SOK & MI & SAV) & TXT & SPL & _).
  pose proof PE as (FRM & TM & SSP & ILO & SPH).
  pose proof SOK as (STK & DEP & AL & NR).
  pose proof ST as (RCA & CUR & NMA & CNT).
  assert (DEP' : lo + 6032 <= bv_unsigned sp)
    by (unfold PARSE_FILE_STACK, PARSE_FILE_FRAME, REFUSE_STACK, PRINTF_K in DEP; lia).
  assert (SPH' : bv_unsigned sp + 976 < 2 ^ 63) by (unfold PARSE_FILE_FRAME in SPH; lia).
  assert (LO0 : 0 <= lo) by (destruct STK as [? _]; assumption).
  pose proof CV as (bsv & slv & BV & ZV & NZV & SLV).
  set (l := r_low val 0 64) in *.
  assert (NZl : ~ In 0 l) by (apply p6_rlow_nz; exact NZV).
  lazymatch goal with |- evt _ ?QQ _ => set (Q := QQ) end.
  assert (HW0 : forall x, ~ outside [] x ->
            (bv_unsigned sp + PF_LOW <= x < bv_unsigned sp + PF_LOW + 64) \/ (c <= x < c + RC_N + 4)).
  { intros x Hx. exfalso. apply Hx. exact I. }
  (* KREF: the bad-role refusal at 0x1528c *)
  assert (KREFP : forall (mk : word -> option byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    role_intent_parse l = None -> munch [] m mk -> wmono rsegs m mk -> mem_inv rsegs mk ->
    evt rsegs Q (MS (mkR x1 sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5
                         (Z_to_bv 64 (rseg_addr c gi)) (Z_to_bv 64 vp) s8 (Z_to_bv 64 512) s10 s11 x28 x29 x30 x31)
                    F (Z_to_bv 64 0x1528c) fc None mk (seg_rom rsegs))).
  { intros mk x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 RN MUk WMk MIk.
    zstep. zstep. zstep.
    pose proof (p6_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX RCA NMA MUk WMk MIk HW0) as [CTXk NMk].
    assert (RCk : rconf_at rsegs mk c rc) by (eapply p6s_rconf_at_munch; [exact RCA | exact MUk | exact I]).
    assert (CVk : cstr_at rsegs mk vp val) by (eapply p6s_cstr_at_munch; [exact CV | exact MUk | exact I]).
    eapply evt_mono.
    { eapply HK with (lo := lo) (v := v) (c := c) (t := t) (s := s) (rc := rc) (cur := Some gi) (nm := nm)
        (o := o) (ln := ln) (d := d) (f := F_badrole) (fp := PF_STR_BADROLE) (vp := vp) (x := val).
      - exact CTXk.
      - split; [exact RCk | split; [exact CUR | split; [exact NMk | exact CNT]]].
      - exact RG.
      - reflexivity.
      - reflexivity.
      - left. reflexivity.
      - unfold PF_STR_BADROLE. reflexivity.
      - reflexivity.
      - exact CVk.
      - exact IBV. }
    intros ms' HF. unfold Q. rewrite (p6_step_none rc gi nm (ln + 1) val RN).
    eapply p6_fin_keep; [exact MUk | exact WMk | exact HW0 | exact HF]. }
  (* PROV: role = r, role_set = 1 at 0x15490 / 0x15498, then a0 = &seg[gi].role_file, a2 = "%s" *)
  assert (PROVP : forall (r : Z) (mk : word -> option byte)
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    role_intent_parse l = Some r -> 0 <= r <= 4 -> munch [] m mk -> wmono rsegs m mk -> mem_inv rsegs mk ->
    evt rsegs Q (MS (mkR x1 sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5
                         (Z_to_bv 64 (rseg_addr c gi)) (Z_to_bv 64 vp) s8 (Z_to_bv 64 512) s10 s11 x28 x29 x30 x31)
                    F (Z_to_bv 64 0x15490) fc None mk (seg_rom rsegs))).
  { intros r mk x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 RP Hr MUk WMk MIk.
    assert (CTXk : pf_ctx mk fc (bv_unsigned sp) lo v c t s o ln d n)
      by (exact (proj1 (p6_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX RCA NMA MUk WMk MIk HW0))).
    assert (RCk : rconf_at rsegs mk c rc) by (eapply p6s_rconf_at_munch; [exact RCA | exact MUk | exact I]).
    pose proof (p6_cwr _ _ _ _ _ _ _ _ _ _ _ _ _ CTXk RCk) as WR.
    destruct RCk as (bsc & BC0 & EC0).
    pose proof EC0 as (LC & LSEG & _).
    unfold SEG_C_SIZE in LC.
    cbn [pf_cur_ok] in CUR.
    set (Wc := [(rseg_addr c gi + 16, rseg_addr c gi + 24)]).
    assert (HWc : forall x, ~ outside Wc x ->
              (bv_unsigned sp + PF_LOW <= x < bv_unsigned sp + PF_LOW + 64) \/ (c <= x < c + RC_N + 4)).
    { intros x Hx. apply p6_not_outside1 in Hx. right. unfold rseg_addr, RSEG_SIZE, RC_N in *. lia. }
    assert (MUk' : munch Wc m mk) by (eapply munch_weaken; [|exact MUk]; intros x _; exact I).
    assert (SO1 : store_ok rsegs mk (wa (c + (356 * Z.of_nat gi + 16))) 4 = true).
    { apply (wr_at_store_ok rsegs mk c (RC_N + 4)); [exact WR | lia | unfold RC_N; lia]. }
    assert (SO1r : store_ok rsegs mk (wa (rseg_addr c gi + 16)) 4 = true)
      by (replace (rseg_addr c gi + 16) with (c + (356 * Z.of_nat gi + 16)) by (unfold rseg_addr, RSEG_SIZE; lia);
          exact SO1).
    zstep. clear SO1r.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ ?A _) _) =>
      replace A with (wa (c + (356 * Z.of_nat gi + 16))) by (unfold wa, rseg_addr, RSEG_SIZE; f_equal; try lia) end.
    set (m5 := write_to_mem mk (wa (c + (356 * Z.of_nat gi + 16))) (le4 (Z_to_bv 64 r))).
    pose proof (bytes_at_bound _ _ _ _ BC0) as BB. rewrite LC in BB.
    assert (MU5 : munch Wc m m5).
    { apply (munch_write Wc m mk _ _ MUk'); rewrite ?length_le4; [lia | lia |].
      unfold Wc. cbn [inside]. unfold rseg_addr, RSEG_SIZE. lia. }
    assert (WM5 : wmono rsegs m m5) by (apply wmono_write; exact WMk).
    assert (MI5 : mem_inv rsegs m5) by (apply mem_inv_store; [exact MIk | rewrite length_le4; exact SO1]).
    assert (BC5 : bytes_at rsegs m5 c (upd_bytes bsc (356 * gi + 16) (le4 (Z_to_bv 64 r)))).
    { pose proof (bytes_at_write_inside rsegs mk c bsc (356 * Z.of_nat gi + 16) (le4 (Z_to_bv 64 r)) BC0) as NW.
      replace (Z.to_nat (356 * Z.of_nat gi + 16)) with (356 * gi + 16)%nat in NW by lia.
      apply NW; [lia | rewrite length_le4; lia]. }
    assert (WR5 : wr_at rsegs m5 c (RC_N + 4)) by (apply wr_at_write; exact WR).
    clearbody m5.
    zstep.
    assert (SO2 : store_ok rsegs m5 (wa (c + (356 * Z.of_nat gi + 20))) 4 = true).
    { apply (wr_at_store_ok rsegs m5 c (RC_N + 4)); [exact WR5 | lia | unfold RC_N; lia]. }
    assert (SO2r : store_ok rsegs m5 (wa (rseg_addr c gi + 20)) 4 = true)
      by (replace (rseg_addr c gi + 20) with (c + (356 * Z.of_nat gi + 20)) by (unfold rseg_addr, RSEG_SIZE; lia);
          exact SO2).
    zstep. clear SO2r.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ ?A _) _) =>
      replace A with (wa (c + (356 * Z.of_nat gi + 20))) by (unfold wa, rseg_addr, RSEG_SIZE; f_equal; try lia) end.
    set (m6 := write_to_mem m5 (wa (c + (356 * Z.of_nat gi + 20))) (le4 (Z_to_bv 64 1))).
    assert (MU6 : munch Wc m m6).
    { apply (munch_write Wc m m5 _ _ MU5); rewrite ?length_le4; [lia | lia |].
      unfold Wc. cbn [inside]. unfold rseg_addr, RSEG_SIZE. lia. }
    assert (WM6 : wmono rsegs m m6) by (apply wmono_write; exact WM5).
    assert (MI6 : mem_inv rsegs m6) by (apply mem_inv_store; [exact MI5 | rewrite length_le4; exact SO2]).
    assert (BC6 : bytes_at rsegs m6 c
                    (upd_bytes (upd_bytes bsc (356 * gi + 16) (le4 (Z_to_bv 64 r))) (356 * gi + 20)
                       (le4 (Z_to_bv 64 1)))).
    { pose proof (bytes_at_write_inside rsegs m5 c _ (356 * Z.of_nat gi + 20) (le4 (Z_to_bv 64 1)) BC5) as NW.
      replace (Z.to_nat (356 * Z.of_nat gi + 20)) with (356 * gi + 20)%nat in NW by lia.
      apply NW; [lia | rewrite upd_bytes_length; rewrite ?length_le4; lia]. }
    assert (RC6 : rconf_at rsegs m6 c (pf_prov_mid (PRole r) rc gi)).
    { exists (upd_bytes (upd_bytes bsc (356 * gi + 16) (le4 (Z_to_bv 64 r))) (356 * gi + 20) (le4 (Z_to_bv 64 1))).
      split; [exact BC6 | apply p6_role_rconf; [exact EC0 | exact CUR | lia]]. }
    clearbody m6.
    pose proof (p6_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX RCA NMA MU6 WM6 MI6 HWc) as [CTX6 NM6].
    zstep. zstep. zstep.
    eapply evt_mono.
    { eapply HP with (lo := lo) (v := v) (c := c) (t := t) (s := s) (rc := rc) (nm := nm) (o := o) (ln := ln)
        (d := d) (k := PRole r) (gi := gi).
      - exact CTX6.
      - split; [exact RC6 | split; [apply p6_prov_cur_ok; exact CUR | split; [exact NM6 | apply p6_prov_cnt; exact CNT]]].
      - exact RG.
      - reflexivity.
      - reflexivity.
      - cbn [pf_prov_off]. unfold RS_ROLE_FILE. f_equal; try lia.
      - unfold PF_STR_S. reflexivity. }
    intros ms' HF. unfold Q. rewrite (p6_step_some rc gi nm (ln + 1) val r RP).
    eapply p6_fin_keep; [exact MU6 | exact WM6 | exact HWc | exact HF]. }
  (* the literals in .rodata and the three bcmp results *)
  assert (LA : forall mm, mem_inv rsegs mm -> bytes_at rsegs mm 66318 (zb (S_auto ++ [0]))).
  { intros mm MM. apply p6_lit; [exact MM | lia | change (length (zb (S_auto ++ [0]))) with 5%nat; lia |].
    vm_compute. reflexivity. }
  assert (LM : forall mm, mem_inv rsegs mm -> bytes_at rsegs mm 66888 (zb (S_master ++ [0]))).
  { intros mm MM. apply p6_lit; [exact MM | lia | change (length (zb (S_master ++ [0]))) with 7%nat; lia |].
    vm_compute. reflexivity. }
  assert (LS : forall mm, mem_inv rsegs mm -> bytes_at rsegs mm 67420 (zb (S_slave ++ [0]))).
  { intros mm MM. apply p6_lit; [exact MM | lia | change (length (zb (S_slave ++ [0]))) with 6%nat; lia |].
    vm_compute. reflexivity. }
  destruct (p6_wfacts S_auto ltac:(vm_compute; reflexivity)) as [NZA RA].
  destruct (p6_wfacts S_master ltac:(vm_compute; reflexivity)) as [NZM RM].
  destruct (p6_wfacts S_slave ltac:(vm_compute; reflexivity)) as [NZS RS].
  destruct (memcmp_model_total LB (zb (S_auto ++ [0])) 5 ltac:(lia) ltac:(apply Nat.leb_le; reflexivity))
    as [v1 MM1].
  pose proof (O1_bcmp_lit_holds LB l S_auto v1 NZl NZA RA PLB MM1) as O1A.
  pose proof (p6_memcmp_range _ _ _ _ MM1) as RV1.
  unfold PF_PC_INTENT. zstep. zstep. zstep. zstep.
  eapply (p6_bcmp Q) with (LB := LB) (rs := zb (S_auto ++ [0])) (v := v1);
    [exact BC | rewrite unsigned_lit by lia; exact BLB | rewrite unsigned_lit by lia; apply LA; exact MI
    | rewrite unsigned_lit by lia; exact MM1 | exact MI |].
  intros m1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 MU1 WM1 MI1 BL1.
  rewrite unsigned_lit in BL1 by lia.
  fix_ret. zstep.
  destruct (Z.eq_dec v1 0) as [E1|E1].
  { subst v1. try if_true.
    eapply (PROVP 0); [apply p6_rip_auto; apply O1A; reflexivity | lia | exact MU1 | exact WM1 | exact MI1]. }
  assert (C1 : bv_eqb (Z_to_bv 64 v1) (Z_to_bv 64 0) = false)
    by (rewrite p6_bveq_small by lia; apply Z.eqb_neq; exact E1).
  if_cases K; [exfalso; congruence | clear K].
  assert (NA : strcmp l S_auto <> 0) by (intros H; apply E1; apply O1A; exact H).
  destruct (memcmp_model_total LB (zb (S_master ++ [0])) 7 ltac:(lia) ltac:(apply Nat.leb_le; reflexivity))
    as [v2 MM2].
  pose proof (O1_bcmp_lit_holds LB l S_master v2 NZl NZM RM PLB MM2) as O1M.
  pose proof (p6_memcmp_range _ _ _ _ MM2) as RV2.
  zstep. zstep. zstep. zstep. zstep.
  eapply (p6_bcmp Q) with (LB := LB) (rs := zb (S_master ++ [0])) (v := v2);
    [exact BC | rewrite unsigned_lit by lia; exact BL1 | rewrite unsigned_lit by lia; apply LM; exact MI1
    | rewrite unsigned_lit by lia; exact MM2 | exact MI1 |].
  intros m2 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 MU2 WM2 MI2 BL2.
  rewrite unsigned_lit in BL2 by lia.
  assert (MU2' : munch [] m m2) by (eapply munch_trans; [exact MU1 | exact MU2]).
  assert (WM2' : wmono rsegs m m2) by (eapply wmono_trans; [exact WM1 | exact WM2]).
  fix_ret. zstep.
  destruct (Z.eq_dec v2 0) as [E2|E2].
  { subst v2. try if_true. zstep. zstep.
    eapply (PROVP 1); [apply p6_rip_master; [exact NA | apply O1M; reflexivity] | lia | exact MU2' | exact WM2'
      | exact MI2]. }
  assert (C2 : bv_eqb (Z_to_bv 64 v2) (Z_to_bv 64 0) = false)
    by (rewrite p6_bveq_small by lia; apply Z.eqb_neq; exact E2).
  if_cases K; [exfalso; congruence | clear K].
  assert (NM : strcmp l S_master <> 0) by (intros H; apply E2; apply O1M; exact H).
  destruct (memcmp_model_total LB (zb (S_slave ++ [0])) 6 ltac:(lia) ltac:(apply Nat.leb_le; reflexivity))
    as [v3 MM3].
  pose proof (O1_bcmp_lit_holds LB l S_slave v3 NZl NZS RS PLB MM3) as O1S.
  pose proof (p6_memcmp_range _ _ _ _ MM3) as RV3.
  zstep. zstep. zstep. zstep. zstep.
  eapply (p6_bcmp Q) with (LB := LB) (rs := zb (S_slave ++ [0])) (v := v3);
    [exact BC | rewrite unsigned_lit by lia; exact BL2 | rewrite unsigned_lit by lia; apply LS; exact MI2
    | rewrite unsigned_lit by lia; exact MM3 | exact MI2 |].
  intros m3 w5 w6 w7 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 MU3 WM3 MI3 BL3.
  rewrite unsigned_lit in BL3 by lia.
  assert (MU3' : munch [] m m3) by (eapply munch_trans; [exact MU2' | exact MU3]).
  assert (WM3' : wmono rsegs m m3) by (eapply wmono_trans; [exact WM2' | exact WM3]).
  fix_ret. zstep.
  destruct (Z.eq_dec v3 0) as [E3|E3].
  { subst v3. try if_true. zstep. zstep.
    eapply (PROVP 2); [apply p6_rip_slave; [exact NA | exact NM | apply O1S; reflexivity] | lia | exact MU3'
      | exact WM3' | exact MI3]. }
  assert (C3 : bv_eqb (Z_to_bv 64 v3) (Z_to_bv 64 0) = false)
    by (rewrite p6_bveq_small by lia; apply Z.eqb_neq; exact E3).
  if_cases K; [exfalso; congruence | clear K].
  assert (NS : strcmp l S_slave <> 0) by (intros H; apply E3; apply O1S; exact H).
  (* the tap / box words *)
  assert (RDL : forall i : nat, (i < 64)%nat ->
            ov_read_bytes rsegs m3 (Z_to_bv 64 (bv_unsigned sp + 80 + Z.of_nat i)) 1 = Some [nth i LB ZERO]).
  { intros i Hi. apply (p6_read1 rsegs m3 (bv_unsigned sp + 80) LB i); [exact BL3 | apply nth_error_nth'; lia]. }
  unfold pf_spill, saved_at in SPL.
  pose proof (bytes_at_transport rsegs [] m m3 _ _ SPL MU3' I) as SPL3. clear SPL.
  assert (RSL : forall k : nat, (k < 8)%nat ->
            ov_read_bytes rsegs m3 (Z_to_bv 64 (bv_unsigned sp + 8 + 8 * Z.of_nat k)) 8 =
            Some (le8 (nth k [Z_to_bv 64 (c + RC_OVERFLOW); Z_to_bv 64 PF_BOX_WORD; Z_to_bv 64 PF_TAP_WORD;
                              Z_to_bv 64 (c + RC_GEN); Z_to_bv 64 (c + RC_READING); Z_to_bv 64 (c + RC_N);
                              Z_to_bv 64 PF_STR_LONG; Z_to_bv 64 PF_STR_BLANKS] (Z_to_bv 64 0)))).
  { intros k Hk. exact (p6s_saved_read m3 (bv_unsigned sp + 8) _ k SPL3 ltac:(cbn [length]; lia)). }
  clear SPL3.
  destruct (O1_word_lit_holds LB l NZl ltac:(lia) PLB) as [OT OB].
  assert (RD0 : ov_read_bytes rsegs m3 (Z_to_bv 64 (bv_unsigned sp + 80)) 1 = Some [nth 0 LB ZERO]).
  { pose proof (RDL 0%nat ltac:(lia)) as H.
    replace (bv_unsigned sp + 80 + Z.of_nat 0) with (bv_unsigned sp + 80) in H by lia. exact H. }
  assert (RD1 : ov_read_bytes rsegs m3 (Z_to_bv 64 (bv_unsigned sp + 81)) 1 = Some [nth 1 LB ZERO]).
  { pose proof (RDL 1%nat ltac:(lia)) as H.
    replace (bv_unsigned sp + 80 + Z.of_nat 1) with (bv_unsigned sp + 81) in H by lia. exact H. }
  assert (RD2 : ov_read_bytes rsegs m3 (Z_to_bv 64 (bv_unsigned sp + 82)) 1 = Some [nth 2 LB ZERO]).
  { pose proof (RDL 2%nat ltac:(lia)) as H.
    replace (bv_unsigned sp + 80 + Z.of_nat 2) with (bv_unsigned sp + 82) in H by lia. exact H. }
  assert (RD3 : ov_read_bytes rsegs m3 (Z_to_bv 64 (bv_unsigned sp + 83)) 1 = Some [nth 3 LB ZERO]).
  { pose proof (RDL 3%nat ltac:(lia)) as H.
    replace (bv_unsigned sp + 80 + Z.of_nat 3) with (bv_unsigned sp + 83) in H by lia. exact H. }
  assert (RT : ov_read_bytes rsegs m3 (Z_to_bv 64 (bv_unsigned sp + 24)) 8 = Some (le8 (Z_to_bv 64 PF_TAP_WORD))).
  { pose proof (RSL 2%nat ltac:(lia)) as H. cbn [nth] in H.
    replace (bv_unsigned sp + 8 + 8 * Z.of_nat 2) with (bv_unsigned sp + 24) in H by lia. exact H. }
  assert (RB : ov_read_bytes rsegs m3 (Z_to_bv 64 (bv_unsigned sp + 16)) 8 = Some (le8 (Z_to_bv 64 PF_BOX_WORD))).
  { pose proof (RSL 1%nat ltac:(lia)) as H. cbn [nth] in H.
    replace (bv_unsigned sp + 8 + 8 * Z.of_nat 1) with (bv_unsigned sp + 16) in H by lia. exact H. }
  clear RDL RSL.
  assert (W4 : pf_word4 [nth 0 LB ZERO; nth 1 LB ZERO; nth 2 LB ZERO; nth 3 LB ZERO] = pf_word4 LB) by reflexivity.
  (* 0x1522c: the tap compare *)
  eapply p6_tapcmp;
    [exact RD0 | exact RD1 | exact RD2 | exact RD3 | exact RT | | ].
  { intros x10 x11 x12 x13 ET. rewrite W4 in ET. zstep. zstep.
    eapply (PROVP 3); [apply p6_rip_tap; [exact NA | exact NM | exact NS | apply OT; exact ET] | lia | exact MU3'
      | exact WM3' | exact MI3]. }
  intros x10 x11 x12 x13 ET. rewrite W4 in ET.
  assert (NT : strcmp l S_tap <> 0) by (intros H; apply ET; apply OT; exact H).
  (* 0x1525c: the box compare *)
  eapply p6_boxcmp;
    [exact RD0 | exact RD1 | exact RD2 | exact RD3 | exact RB | | ].
  { intros q10 q11 q12 q13 EB. rewrite W4 in EB. zstep.
    eapply (PROVP 4); [apply p6_rip_box; [exact NA | exact NM | exact NS | exact NT | apply OB; exact EB] | lia
      | exact MU3' | exact WM3' | exact MI3]. }
  intros q10 q11 q12 q13 EB. rewrite W4 in EB.
  assert (NB : strcmp l S_box <> 0) by (intros H; apply EB; apply OB; exact H).
  eapply KREFP; [apply p6_rip_none; assumption | exact MU3' | exact WM3' | exact MI3].
Qed.

(** P6: ROLE -> INTENT (the fold), INTENT -> KREF (bad role) or PROV. *)
Theorem pf_p6_holds : bcmp_contract -> S_P6.
Proof.
  intros BC n. split; [apply p6_role | intros HK HP; exact (p6_intent n BC HK HP)].
Qed.
