(* Segment R23 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x13654, 0x136c0] and [0x136d4, 0x136e0],
   U13654 -> U136c4 (strcmp of the round trip's model name with the row's name returned) or U136e4
   (has_identity_record(m) = 0 at 0x136a0, then v1.9's memset(sp+36, 0, 40) of `first` at 0x136d4: FIRST0).
   #24-#29: RID_7's has_fw, fw_milli, has_reac_version, major, minor, patch equal the row's (RTM (g)); T09: the spilled
   m & 7 at sp+24 is 0 (M8); #30: has_model_name(RID_7) = 1 when E(6); 0x136b4: name(m) != 0 for those rows.
   RID_7 is the round trip's id at sp+36 (RIDB).
   The round-trip model facts RTM_fw, RTM_ver, RTM_hid, RTM_name (batch u2 owns RTM; the plain b2_rtm_fw, _ver, _hid,
   _name forms) and the catalogue rows in the image ROWS (batch u1) are Section Hypotheses. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcKindLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel RcDecl RcEmit RcSynth RcParseLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInv strcmp_c memset_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Import Tac_slot Tac_u3.
Import ListNotations.
Open Scope Z_scope.

(* ---- Word and byte facts ---- *)

Lemma r23_neqb_refl : forall x : word, negb (bv_eqb x x) = false.
Proof. intros x. unfold bv_eqb. rewrite Z.eqb_refl. reflexivity. Qed.

(* `bne` on two equal values: not taken. *)
Ltac r23_ne_refl :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false; [cbv iota | symmetry; apply r23_neqb_refl]
  end.

Lemma r23_byte1 : forall b : byte, bv_unsigned b = 1 -> b = Z_to_bv 8 1.
Proof. intros b H. apply bv_eq. rewrite H. reflexivity. Qed.

Lemma r23_sx32_eqb0 : forall h, 0 <= h < 2 ^ 32 -> bv_eqb (sx32 (Z_to_bv 64 h)) (Z_to_bv 64 0) = (h =? 0).
Proof.
  intros h Hh. unfold sx32, bv_eqb. rewrite (MState.unsigned_lit h) by lia.
  rewrite !MState.unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296.
  change (2 ^ 64) with 18446744073709551616.
  destruct (Z.eqb_spec h 0) as [->|Hn]; [reflexivity|]. apply Z.eqb_neq.
  Z.div_mod_to_equations. lia.
Qed.

Lemma r23_bytes_eq : forall l1 l2 : list byte, map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

Lemma r23_first1 : forall (l : list byte) k, (k < length l)%nat -> firstn 1 (skipn k l) = [nth k l (Z_to_bv 8 0)].
Proof.
  induction l as [|x l IH]; intros k Hk; cbn in Hk; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma r23_first2 : forall (l : list byte) k, (k + 2 <= length l)%nat ->
  firstn 2 (skipn k l) = [nth k l (Z_to_bv 8 0); nth (S k) l (Z_to_bv 8 0)].
Proof.
  induction l as [|x l IH]; intros k Hk; cbn in Hk; [lia|].
  destruct k as [|k].
  - destruct l as [|y l]; cbn in Hk; [lia|]. reflexivity.
  - cbn [skipn nth]. apply IH. lia.
Qed.

(* A byte and a u16 (little-endian) read from a byte run. *)
Lemma r23_rd1 : forall m a l k, bytes_at rsegs m a l -> (k < length l)%nat ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat k)) 1 = Some [nth k l (Z_to_bv 8 0)].
Proof.
  intros m a l k H Hk. rewrite (bytes_at_ov_read rsegs m a l k 1 H) by lia. rewrite r23_first1 by lia. reflexivity.
Qed.

Lemma r23_rd2 : forall m a l k, bytes_at rsegs m a l -> (k + 2 <= length l)%nat ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat k)) 2 =
  Some (le2 (Z_to_bv 64 (bv_unsigned (nth k l (Z_to_bv 8 0)) + 256 * bv_unsigned (nth (S k) l (Z_to_bv 8 0))))).
Proof.
  intros m a l k H Hk. rewrite (bytes_at_ov_read rsegs m a l k 2 H) by lia. rewrite r23_first2 by lia.
  rewrite <- RcParseLib.rc_le2_pair.
  replace (bv_unsigned (nth (S k) l (Z_to_bv 8 0)) * 256 + bv_unsigned (nth k l (Z_to_bv 8 0)))
    with (bv_unsigned (nth k l (Z_to_bv 8 0)) + 256 * bv_unsigned (nth (S k) l (Z_to_bv 8 0))) by lia.
  reflexivity.
Qed.

(* A sub-range of a byte run. *)
Lemma r23_sub : forall m a bs k n, bytes_at rsegs m a bs -> (k + n <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m a bs k n H Hk.
  rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn in H. replace (Nat.min k (length bs)) with k in H by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

Lemma r23_RID_len : forall inp b, length (RID inp b) = 38%nat.
Proof.
  intros inp b. unfold RID. induction b as [|b IH]; [reflexivity|].
  cbn [rt_st].
  destruct (rt_n inp (Z.of_nat b) =? 0); [exact IH|].
  destruct ((Z.of_nat b =? 3) || (Z.of_nat b =? 4)); cbn [fst snd].
  - unfold rp_id. destruct (RcReply.ir _ _); [apply RcIdentModel.ING_length; exact IH | exact IH].
  - destruct ((Z.of_nat b =? 5) || (Z.of_nat b =? 6)); cbn [fst snd]; [|exact IH].
    unfold fg_id. destruct (fg_rf _ _ _ =? 1); [apply RcIdentModel.ING_length; exact IH | exact IH].
Qed.

(* ---- The 11 catalogue rows: has_identity_record (u32 at + 56), name (q64 at + 280), by computation ---- *)

Definition r23_rowchk (i : Z) : bool :=
  let r := rowb i in let h := RcSynth.rw32 r 56 in let nm := RcSynth.rname r in
  (0 <=? h) && (h <? 2 ^ 32) && Bool.eqb (RcEmit.em_hid r =? 0) (h =? 0) &&
  ((RcEmit.em_hid r =? 0) || ((0 <? nm) && (nm + 17 <=? 2 ^ 64) && Image.ro_bytes_b rsegs nm (img_cstr nm 16))).

Lemma r23_rowchk_all : forallb r23_rowchk (map Z.of_nat (seq 0 11)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r23_rowchk_i : forall i, 0 <= i < 11 -> r23_rowchk i = true.
Proof.
  intros i Hi. pose proof r23_rowchk_all as H. rewrite forallb_forall in H. apply H.
  apply in_map_iff. exists (Z.to_nat i). split; [lia | apply in_seq; lia].
Qed.

Lemma r23_row_le : forall i, 0 <= i < 11 ->
  firstn 4 (skipn 56 (rowb i)) = le4 (Z_to_bv 64 (RcSynth.rw32 (rowb i) 56)) /\
  firstn 8 (skipn 280 (rowb i)) = le8 (Z_to_bv 64 (RcSynth.rname (rowb i))).
Proof.
  intros i Hi.
  assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]];
    split; apply r23_bytes_eq; vm_compute; reflexivity.
Qed.

Lemma r23_row_facts : forall i, 0 <= i < 11 ->
  0 <= RcSynth.rw32 (rowb i) 56 < 2 ^ 32 /\
  (RcEmit.em_hid (rowb i) = 0 <-> RcSynth.rw32 (rowb i) 56 = 0) /\
  (RcEmit.em_hid (rowb i) <> 0 ->
     0 < RcSynth.rname (rowb i) /\ RcSynth.rname (rowb i) + 17 <= 2 ^ 64 /\
     Image.ro_bytes_b rsegs (RcSynth.rname (rowb i)) (img_cstr (RcSynth.rname (rowb i)) 16) = true).
Proof.
  intros i Hi. pose proof (r23_rowchk_i i Hi) as H. unfold r23_rowchk in H. cbv zeta in H.
  rewrite !andb_true_iff in H. destruct H as [[[H1 H2] H3] H4].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Bool.eqb_prop in H3.
  split; [lia|]. split.
  - destruct (Z.eqb_spec (RcEmit.em_hid (rowb i)) 0) as [E|E];
      destruct (Z.eqb_spec (RcSynth.rw32 (rowb i) 56) 0) as [E'|E']; try discriminate H3; tauto.
  - intros Hn. apply orb_true_iff in H4. destruct H4 as [H4|H4]; [apply Z.eqb_eq in H4; contradiction|].
    rewrite !andb_true_iff in H4. destruct H4 as [[H5 H6] H7].
    apply Z.ltb_lt in H5. apply Z.leb_le in H6. split; [lia|]. split; [lia | exact H7].
Qed.

(* ---- The run ---- *)

(* v1.9's memset(sp+36, 0, 40) of `first` (0x136d4 .. 0x136e0), then U136e4 at 0x136e4. *)
Lemma r23_first : memset_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv : Z) (junk : list byte),
    sp = Z_to_bv 64 spv -> 0 <= spv -> spv + 1936 <= 2 ^ 64 ->
    rw_cells rsegs m (spv + 36) [Cells.CB 40 junk] -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x136e4) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (spv + 36))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x136e4) fc None m' (seg_rom rsegs) /\
         munch [(spv + 36, spv + 76)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (spv + 36) (repeat (Z_to_bv 8 0) 40))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x136d4) fc None m (seg_rom rsegs)).
Proof.
  intros MSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv junk -> Hlo Hsp HC MI.
  do 4 step.
  eapply evt_cut.
  { eapply MSET with (junk := junk); [ | exact MI].
    rewrite !MState.unsigned_lit by lia. exact HC. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MUc & WMc & MIc & Hz).
  subst ms'.
  rewrite !MState.unsigned_lit in MUc, Hz by lia.
  replace (spv + 36 + 40) with (spv + 76) in MUc by lia.
  replace (ret_pc (Z_to_bv 64 0x136e4)) with (Z_to_bv 64 0x136e4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|]. split; [exact MUc|]. split; [exact WMc|].
  exact (sl_rw_bytes _ _ _ _ Hz).
Qed.

Lemma r23_evt : strcmp_contract -> memset_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (spv mr fw maj mnr pat h nm : Z) (sx junk : list byte),
    sp = Z_to_bv 64 spv -> s0 = Z_to_bv 64 mr ->
    0 <= spv -> spv + 1936 <= 2 ^ 63 -> 0 <= mr -> mr + 296 <= 2 ^ 63 -> 0 <= h < 2 ^ 32 ->
    ov_read_bytes rsegs m (wa (spv + 38)) 1 = Some [Z_to_bv 8 1] ->
    ov_read_bytes rsegs m (wa (spv + 24)) 8 = Some (le8 (Z_to_bv 64 0)) ->
    ov_read_bytes rsegs m (wa (spv + 36)) 2 = Some (le2 (Z_to_bv 64 fw)) ->
    ov_read_bytes rsegs m (wa (mr + 266)) 2 = Some (le2 (Z_to_bv 64 fw)) ->
    ov_read_bytes rsegs m (wa (spv + 72)) 1 = Some [Z_to_bv 8 1] ->
    ov_read_bytes rsegs m (wa (spv + 58)) 2 = Some (le2 (Z_to_bv 64 maj)) ->
    ov_read_bytes rsegs m (wa (mr + 268)) 2 = Some (le2 (Z_to_bv 64 maj)) ->
    ov_read_bytes rsegs m (wa (spv + 60)) 2 = Some (le2 (Z_to_bv 64 mnr)) ->
    ov_read_bytes rsegs m (wa (mr + 270)) 2 = Some (le2 (Z_to_bv 64 mnr)) ->
    ov_read_bytes rsegs m (wa (spv + 62)) 2 = Some (le2 (Z_to_bv 64 pat)) ->
    ov_read_bytes rsegs m (wa (mr + 272)) 2 = Some (le2 (Z_to_bv 64 pat)) ->
    ov_read_bytes rsegs m (wa (mr + 56)) 4 = Some (le4 (Z_to_bv 64 h)) ->
    (h <> 0 ->
       ov_read_bytes rsegs m (wa (spv + 56)) 1 = Some [Z_to_bv 8 1] /\
       ov_read_bytes rsegs m (wa (mr + 280)) 8 = Some (le8 (Z_to_bv 64 nm)) /\ 0 < nm < 2 ^ 64 /\
       bytes_at rsegs m (spv + 39) (sx ++ [Z_to_bv 8 0]) /\ bytes_at rsegs m nm (sx ++ [Z_to_bv 8 0]) /\
       ~ In (Z_to_bv 8 0) sx) ->
    (h = 0 -> rw_cells rsegs m (spv + 36) [Cells.CB 40 junk] /\ mem_inv rsegs m) ->
    evt rsegs
      (fun ms' =>
         (h = 0 /\ exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
            ms' = MS (mkR (Z_to_bv 64 0x136e4) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (spv + 36))
                          a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 0x136e4) fc None m' (seg_rom rsegs) /\
            munch [(spv + 36, spv + 76)] m m' /\ wmono rsegs m m' /\
            bytes_at rsegs m' (spv + 36) (repeat (Z_to_bv 8 0) 40)) \/
         (h <> 0 /\ exists a1' a2' a3' : word,
            ms' = MS (mkR (Z_to_bv 64 0x136c4) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x136c4) fc None m (seg_rom rsegs)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13654) fc None m (seg_rom rsegs)).
Proof.
  intros SC MSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv mr fw maj mnr pat h nm sx junk -> -> Hs0 Hs1 Hm0 Hm1 Hh
    R38 R24 R36 R266 R72 R58 R268 R60 R270 R62 R272 R56 HN HZ.
  step. step. if_false.
  step. step. if_false.
  step. step. step. r23_ne_refl.
  step. step. if_false.
  step. step. step. r23_ne_refl.
  step. step. step. r23_ne_refl.
  step. step. step. r23_ne_refl.
  step. step.
  destruct (Z.eq_dec h 0) as [E0 | E0].
  - if_true_by (eq_trans (r23_sx32_eqb0 h Hh) (proj2 (Z.eqb_eq h 0) E0)).
    destruct (HZ E0) as (HC & MI).
    eapply evt_mono; [exact (r23_first MSET _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                               spv junk eq_refl Hs0 ltac:(lia) HC MI)|].
    intros ms' Hms. left. split; [exact E0 | exact Hms].
  - if_false_by (eq_trans (r23_sx32_eqb0 h Hh) (proj2 (Z.eqb_neq h 0) E0)).
    destruct (HN E0) as (R56' & R280 & Hnm & HS1 & HS2 & HS0).
    step. step. if_false.
    step. step. step. if_true_by (f_equal negb (u3_eqb0 nm Hnm)).
    step.
    eapply evt_cut.
    { eapply SC with (sx := sx) (sy := sx).
      - rewrite MState.unsigned_lit by lia. exact HS1.
      - exact HS0.
      - rewrite MState.unsigned_lit by lia. exact HS2.
      - exact HS0. }
    intros ms' (r & x11 & x12 & x13 & E & Hr).
    assert (Er : r = Z_to_bv 64 0) by (apply Hr; reflexivity). subst ms' r.
    rewrite (MState.ret_pc_even 0x136c4) by (first [reflexivity | lia]).
    apply evt_done. right. split; [exact E0|]. do 3 eexists. reflexivity.
Qed.

Section R23.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis SCMP : strcmp_contract.
Hypothesis MSET : memset_contract.
(* Batch u1's image helper (plan-ubsan 8.3): the 11 catalogue rows at CAT in the image. *)
Hypothesis ROWS : forall i, 0 <= i < CAT_N -> Image.image_bytes rsegs (CAT + CAT_ROW * i) 296 = Some (rowb i).
(* Batch u2's round-trip model facts RTM (g) for this build (plain b2_rtm_fw, b2_rtm_ver, b2_rtm_hid, b2_rtm_name). *)
Hypothesis RTM_fw : forall inp, RcIdentModel.has_fw (RID inp 7) = 1 /\
  RcIdentModel.fw_milli (RID inp 7) = RcDecl.rval (rt_mb inp) 266 + 256 * RcDecl.rval (rt_mb inp) 267.
Hypothesis RTM_ver : forall inp, RcIdentModel.has_reac_version (RID inp 7) = 1 /\
  RcIdentModel.major (RID inp 7) = RcDecl.rval (rt_mb inp) 268 + 256 * RcDecl.rval (rt_mb inp) 269 /\
  RcIdentModel.minor (RID inp 7) = RcDecl.rval (rt_mb inp) 270 + 256 * RcDecl.rval (rt_mb inp) 271 /\
  RcIdentModel.patch (RID inp 7) = RcDecl.rval (rt_mb inp) 272 + 256 * RcDecl.rval (rt_mb inp) 273.
Hypothesis RTM_hid : forall inp, rt_n inp 6 <> 0 <-> RcEmit.em_hid (rt_mb inp) <> 0.
Hypothesis RTM_name : forall inp, rt_n inp 6 <> 0 ->
  RcIdentModel.has_model_name (RID inp 7) = 1 /\
  firstn (length (rt_nb inp)) (RcIdentModel.model_name (RID inp 7)) = rt_nb inp /\
  last (rt_nb inp) (RcIdentModel.zb 1) = RcIdentModel.zb 0 /\
  forallb (fun x => negb (RcIdentModel.bz x =? 0)) (removelast (rt_nb inp)) = true /\
  (Nat.leb 2 (length (rt_nb inp)) && Nat.leb (length (rt_nb inp)) 16)%bool = true.

Lemma seg_R23 : Hcut B APIf ra (Inv_U136c4 B APIf ra empty) -> Hcut B APIf ra (Inv_U136e4 B APIf ra empty) ->
  Hcut B APIf ra (Inv_U13654 B APIf ra empty).
Proof.
  intros H1 H2 g c (L & A & regs & mem & md & -> & HFR & HP & (H7 & (Hc & Hpc & Hnc) & HOUR) & H8 & HM8 & HID).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & HREL & _).
  assert (Hi : 0 <= istar (g_in g) < 11) by (unfold istar, CAT_N; apply Z.mod_pos_bound; lia).
  pose proof (ROWS (istar (g_in g)) ltac:(unfold CAT_N; lia)) as HI.
  pose proof (Image.image_bytes_length rsegs 296 _ _ HI) as Hlen.
  pose proof (u3_relro_bytes B APIf ra empty FF mem _ 296 _ HREL HI
                ltac:(unfold CAT, CAT_ROW; lia) ltac:(unfold CAT, CAT_ROW; lia)) as HROW.
  pose proof (mem_rel_normalize rsegs mem HMI) as HN.
  pose proof (proj1 (bytes_at_rel rsegs _ _ _ _ HN) HROW) as NROW.
  pose proof (proj1 (bytes_at_rel rsegs _ _ _ _ HN) HID) as NID. unfold RIDB in NID.
  pose proof (u3_M8_rd g _ (u3_M8_norm g mem HMI HM8)) as R24.
  pose proof (r23_RID_len (g_in g) 7) as Hid38.
  destruct (r23_row_le (istar (g_in g)) Hi) as (L56 & L280).
  destruct (r23_row_facts (istar (g_in g)) Hi) as (Hh & Ehid & Hnm).
  destruct (RTM_fw (g_in g)) as (Ehf & Efw).
  destruct (RTM_ver (g_in g)) as (Ehv & Emaj & Emin & Epat).
  unfold spk in *. unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 36) 40 ST ltac:(lia) ltac:(lia)) as (junk & HC).
  (* RID_7's bytes at sp+36 *)
  pose proof (r23_rd1 _ _ _ 2 NID ltac:(lia)) as R38.
  rewrite (r23_byte1 (nth 2 (RID (g_in g) 7) (Z_to_bv 8 0)) Ehf) in R38.
  replace (g_S g - 1936 + 36 + Z.of_nat 2) with (g_S g - 1936 + 38) in R38 by lia.
  pose proof (r23_rd1 _ _ _ 36 NID ltac:(lia)) as R72.
  rewrite (r23_byte1 (nth 36 (RID (g_in g) 7) (Z_to_bv 8 0)) Ehv) in R72.
  replace (g_S g - 1936 + 36 + Z.of_nat 36) with (g_S g - 1936 + 72) in R72 by lia.
  pose proof (r23_rd2 _ _ _ 0 NID ltac:(lia)) as R36.
  replace (g_S g - 1936 + 36 + Z.of_nat 0) with (g_S g - 1936 + 36) in R36 by lia.
  pose proof (r23_rd2 _ _ _ 22 NID ltac:(lia)) as R58.
  replace (g_S g - 1936 + 36 + Z.of_nat 22) with (g_S g - 1936 + 58) in R58 by lia.
  pose proof (r23_rd2 _ _ _ 24 NID ltac:(lia)) as R60.
  replace (g_S g - 1936 + 36 + Z.of_nat 24) with (g_S g - 1936 + 60) in R60 by lia.
  pose proof (r23_rd2 _ _ _ 26 NID ltac:(lia)) as R62.
  replace (g_S g - 1936 + 36 + Z.of_nat 26) with (g_S g - 1936 + 62) in R62 by lia.
  (* the row's bytes at m *)
  assert (R266 : ov_read_bytes rsegs (normalize rsegs mem) (wa (mrow (g_in g) + 266)) 2 =
                 Some (le2 (Z_to_bv 64 (RcIdentModel.fw_milli (RID (g_in g) 7))))).
  { rewrite Efw. exact (r23_rd2 _ _ _ 266 NROW ltac:(lia)). }
  assert (R268 : ov_read_bytes rsegs (normalize rsegs mem) (wa (mrow (g_in g) + 268)) 2 =
                 Some (le2 (Z_to_bv 64 (RcIdentModel.major (RID (g_in g) 7))))).
  { rewrite Emaj. exact (r23_rd2 _ _ _ 268 NROW ltac:(lia)). }
  assert (R270 : ov_read_bytes rsegs (normalize rsegs mem) (wa (mrow (g_in g) + 270)) 2 =
                 Some (le2 (Z_to_bv 64 (RcIdentModel.minor (RID (g_in g) 7))))).
  { rewrite Emin. exact (r23_rd2 _ _ _ 270 NROW ltac:(lia)). }
  assert (R272 : ov_read_bytes rsegs (normalize rsegs mem) (wa (mrow (g_in g) + 272)) 2 =
                 Some (le2 (Z_to_bv 64 (RcIdentModel.patch (RID (g_in g) 7))))).
  { rewrite Epat. exact (r23_rd2 _ _ _ 272 NROW ltac:(lia)). }
  assert (R56 : ov_read_bytes rsegs (normalize rsegs mem) (wa (mrow (g_in g) + 56)) 4 =
                Some (le4 (Z_to_bv 64 (RcSynth.rw32 (rowb (istar (g_in g))) 56)))).
  { rewrite <- L56. exact (bytes_at_ov_read rsegs _ _ _ 56 4 NROW ltac:(lia)). }
  set (sx := removelast (rt_nb (g_in g))).
  assert (HN' : RcSynth.rw32 (rowb (istar (g_in g))) 56 <> 0 ->
       ov_read_bytes rsegs (normalize rsegs mem) (wa (g_S g - 1936 + 56)) 1 = Some [Z_to_bv 8 1] /\
       ov_read_bytes rsegs (normalize rsegs mem) (wa (mrow (g_in g) + 280)) 8 =
         Some (le8 (Z_to_bv 64 (RcSynth.rname (rowb (istar (g_in g)))))) /\
       0 < RcSynth.rname (rowb (istar (g_in g))) < 2 ^ 64 /\
       bytes_at rsegs (normalize rsegs mem) (g_S g - 1936 + 39) (sx ++ [Z_to_bv 8 0]) /\
       bytes_at rsegs (normalize rsegs mem) (RcSynth.rname (rowb (istar (g_in g)))) (sx ++ [Z_to_bv 8 0]) /\
       ~ In (Z_to_bv 8 0) sx).
  { intros Hh0.
    assert (Hhid : RcEmit.em_hid (rowb (istar (g_in g))) <> 0) by (intros E; apply Hh0; apply Ehid; exact E).
    destruct (Hnm Hhid) as (Hnm0 & Hnm1 & HRO).
    assert (Hn6 : rt_n (g_in g) 6 <> 0) by (apply (proj2 (RTM_hid (g_in g))); exact Hhid).
    destruct (RTM_name (g_in g) Hn6) as (Ehn & Efn & Elast & Hall & Hlen16).
    apply andb_true_iff in Hlen16 as [Hl1 Hl2]. apply Nat.leb_le in Hl1. apply Nat.leb_le in Hl2.
    assert (Enb : rt_nb (g_in g) = sx ++ [Z_to_bv 8 0]).
    { unfold sx. change (Z_to_bv 8 0) with (RcIdentModel.zb 0). rewrite <- Elast.
      apply app_removelast_last. intros E. rewrite E in Hl1. cbn in Hl1. lia. }
    split.
    { pose proof (r23_rd1 _ _ _ 20 NID ltac:(lia)) as RS56.
      rewrite (r23_byte1 (nth 20 (RID (g_in g) 7) (Z_to_bv 8 0)) Ehn) in RS56.
      replace (g_S g - 1936 + 36 + Z.of_nat 20) with (g_S g - 1936 + 56) in RS56 by lia. exact RS56. }
    split.
    { rewrite <- L280. exact (bytes_at_ov_read rsegs _ _ _ 280 8 NROW ltac:(lia)). }
    split; [lia|].
    split.
    { rewrite <- Enb.
      assert (Es : firstn (length (rt_nb (g_in g))) (skipn 3 (RID (g_in g) 7)) = rt_nb (g_in g)).
      { rewrite <- Efn at 2. unfold RcIdentModel.model_name, RcIdentModel.get, RcIdentModel.OFF_NAME,
          RcIdentModel.NAME_CAP. rewrite firstn_firstn. f_equal. lia. }
      pose proof (r23_sub _ _ _ 3 (length (rt_nb (g_in g))) NID ltac:(lia)) as X.
      rewrite Es in X. replace (g_S g - 1936 + 36 + Z.of_nat 3) with (g_S g - 1936 + 39) in X by lia.
      exact X. }
    split.
    { rewrite <- Enb. apply rc_ro_in_image; [exact (mem_inv_normalize rsegs mem)|].
      assert (HRO' : Image.ro_bytes_b rsegs (RcSynth.rname (rowb (istar (g_in g)))) (rt_nb (g_in g)) = true)
        by exact HRO.
      rewrite HRO'. cbn [andb]. apply andb_true_intro. split; apply Z.leb_le; lia. }
    intros Hin. pose proof (proj1 (forallb_forall _ _) Hall (Z_to_bv 8 0) Hin) as X.
    vm_compute in X. discriminate X. }
  set (W := [(g_S g - 1936 + 36, g_S g - 1936 + 76)]).
  eapply (u3_mid B APIf ra empty FF g [] L A regs mem md _ W); [exact HFR | exact HP | | | |].
  - intros x Hx O. apply (sl_fp1 g (g_S g - 1936 + 36) (g_S g - 1936 + 76) x);
      [unfold SLOT_K, SLOT_STACK; lia | lia | exact Hx | exact O].
  - rewrite sl_mkR_of.
    apply (r23_evt SCMP MSET _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             (g_S g - 1936) (mrow (g_in g)) (RcIdentModel.fw_milli (RID (g_in g) 7))
             (RcIdentModel.major (RID (g_in g) 7)) (RcIdentModel.minor (RID (g_in g) 7))
             (RcIdentModel.patch (RID (g_in g) 7)) (RcSynth.rw32 (rowb (istar (g_in g))) 56)
             (RcSynth.rname (rowb (istar (g_in g)))) sx junk);
      [exact Hsp | exact H8 | lia | lia | unfold mrow, CAT, CAT_ROW; lia | unfold mrow, CAT, CAT_ROW; lia
      | exact Hh | exact R38 | exact R24 | exact R36 | exact R266 | exact R72 | exact R58 | exact R268
      | exact R60 | exact R270 | exact R62 | exact R272 | exact R56 | exact HN'
      | intros _; exact (conj HC (mem_inv_normalize rsegs mem))].
  - intros ms [(_ & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & -> & MU & WM & _)
              | (_ & ? & ? & ? & ->)].
    + do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      split; [reflexivity|]. split; reflexivity.
    + do 3 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
      split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    assert (HOUR' : OURb g m').
    { unfold OURb in *. apply (bytes_at_transport rsegs W mem m' _ _ HOUR MU'). rewrite OUR_length.
      unfold W, spk, fsp, SLOT_FRAME. cbn [disjoint_from]. split; [lia | exact I]. }
    destruct HQ as [(E0 & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & _ & _ & HZ)
                   | (E0 & ? & ? & ? & HE)].
    + injection HE; intros; subst.
      apply H2. exists L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      assert (E7 : c0 (g_in g) = 7) by (unfold c0; unfold g_n in H7; lia).
      apply u3_PB_intro; [| exact HOUR' |].
      * rewrite E7. unfold CUR, rg in *. rewrite !(sl_getr_eqv _ _ _ Hx).
        split; [exact Hc|]. split; [exact Hpc | exact Hnc].
      * unfold spk, fsp, SLOT_FRAME. exact (proj2 (bytes_at_rel rsegs _ _ _ _ Hrel) HZ).
    + injection HE; intros; subst.
      apply H1. exists L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      unfold RA, CUR, rg in *. rewrite !(sl_getr_eqv _ _ _ Hx).
      refine (conj (conj H7 (conj (conj Hc (conj Hpc Hnc)) HOUR')) (conj H8 (conj _ (conj _ eq_refl)))).
      * apply (u3_M8_keep g W mem m' HM8 MU'). unfold W, spk, fsp, SLOT_FRAME. cbn [disjoint_from].
        split; [lia | exact I].
      * unfold RIDB, spk, fsp, SLOT_FRAME. exact (proj2 (bytes_at_rel rsegs _ _ _ _ Hrel) NID).
Qed.

End R23.
