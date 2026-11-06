From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import RcModel RcLeaf RcKind RcParse CtrlParsed.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import disco_table_c disco_table.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_classify_c SightModel.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import find_entry_c role_of_c check_table_c check_sighting_c classify_core_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_frame_clean_len_c reac_disco_table_observe_c hunt_c reac_hunt_observe_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import slot_inv slot_lib uslot_frame uslot_observe uslot_known.
Import ListNotations.
Open Scope Z_scope.

Definition cl_word (len : Z) : word := Z_to_bv 64 (Z.add len (Z.land (bv_unsigned (Z_to_bv 64 (Z.sub 0 (bv_unsigned (v_sltiu (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.add (Z.mul (bv_unsigned (Z_to_bv 64 len)) 18446744073709522489) (-6)))) 48))) 50))) (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.add (Z.mul (bv_unsigned (Z_to_bv 64 len)) 18446744073709522489) (-6)))) 14)))))) 65535)) 1821))))) 18446744073709551614)).

Definition cl_z (n : Z) : Z :=
  let a := ((n mod 18446744073709551616) * 18446744073709522489 + -6) mod 18446744073709551616 in
  let b := (Z.shiftr ((Z.shiftl a 48) mod 18446744073709551616) 50) mod 18446744073709551616 in
  let c := (Z.shiftl a 14) mod 18446744073709551616 in
  let d := (Z.land ((Z.lor b c) mod 18446744073709551616) 65535) mod 18446744073709551616 in
  let e := if d <? 1821 then 1 else 0 in
  n + Z.land ((0 - e) mod 18446744073709551616) 18446744073709551614.

Lemma sltiu_u : forall x k, bv_unsigned (v_sltiu x k) = if bv_unsigned x <? bv_wrap 64 k then 1 else 0.
Proof. intros x k. unfold v_sltiu. destruct (_ <? _); reflexivity. Qed.

Lemma cl_word_z : forall n, cl_word n = Z_to_bv 64 (cl_z n).
Proof.
  intros n. unfold cl_word, cl_z. rewrite sltiu_u. rewrite !unsigned_lit_wrap.
  change (bv_wrap 64 1821) with 1821. change (2 ^ 64) with 18446744073709551616. reflexivity.
Qed.

Fixpoint cl_chk (k : nat) (n : Z) : bool :=
  match k with
  | O => true
  | S k' => (cl_z n mod 18446744073709551616 =? reac_frame_clean_len_model n) && cl_chk k' (n + 1)
  end.

Lemma cl_chk_ok : cl_chk 65482 54 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cl_chk_sound : forall k n, cl_chk k n = true -> forall x, n <= x < n + Z.of_nat k ->
  cl_z x mod 18446744073709551616 = reac_frame_clean_len_model x.
Proof.
  induction k as [|k IH]; intros n H x Hx; [lia|].
  cbn [cl_chk] in H. apply andb_prop in H as [H1 H2].
  destruct (Z.eq_dec x n) as [->|Ne]; [apply Z.eqb_eq; exact H1|].
  apply (IH (n + 1) H2). lia.
Qed.

Lemma cl_model_rng : forall n, 0 <= n < 65536 -> 0 <= reac_frame_clean_len_model n <= n.
Proof. intros n Hn. unfold reac_frame_clean_len_model. destruct (_ && _) eqn:E; [|lia].
  apply andb_prop in E as [E _]. apply Z.leb_le in E. lia. Qed.

Lemma cl_eq : forall n, 54 <= n < 65536 -> cl_word n = Z_to_bv 64 (reac_frame_clean_len_model n).
Proof.
  intros n Hn. rewrite cl_word_z. apply Z_to_bv_eqm.
  pose proof (cl_model_rng n ltac:(lia)) as R.
  rewrite (Z.mod_small (reac_frame_clean_len_model n)) by lia.
  change (2 ^ 64) with 18446744073709551616.
  apply (cl_chk_sound 65482 54 cl_chk_ok). change (Z.of_nat 65482) with 65482. lia.
Qed.

From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require GateModel.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require uslot_classify.

Lemma sub_sub0 : forall (H : list byte) k n, 0 <= k -> k + Z.of_nat n <= 400 -> sub (sub H 0 400) k n = sub H k n.
Proof.
  intros H k n Hk Hn. unfold sub. change (Z.to_nat 0) with 0%nat. cbn [skipn].
  rewrite skipn_firstn_comm, firstn_firstn. rewrite Nat.min_l by lia. reflexivity.
Qed.

Lemma fld_firstn : forall (R : list byte) k n, (k + n <= 50)%nat -> fld (firstn 50 R) k n = fld R k n.
Proof. intros R k n H. unfold fld. rewrite skipn_firstn_comm, firstn_firstn, Nat.min_l by lia. reflexivity. Qed.

Lemma fb_firstn : forall (R : list byte) k, (50 <= length R)%nat -> (k < 50)%nat -> fb (firstn 50 R) k = fb R k.
Proof.
  intros R k L Hk. unfold fb. rewrite <- (firstn_skipn 50 R) at 2. rewrite app_nth1; [reflexivity|].
  rewrite length_firstn. lia.
Qed.

Lemma u1_fb : forall (A : list byte) k, (k < length A)%nat -> u_at A (Z.of_nat k) 1 = fb A k.
Proof.
  intros A k Hk. unfold u_at, sub, fb, zb. rewrite Nat2Z.id. rewrite (firstn1_skipn A k (Z_to_bv 8 0) Hk).
  cbn [bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r. reflexivity.
Qed.

Lemma beq_neq : forall a b : list byte, a <> b -> bytes_eqb a b = false.
Proof.
  intros a b N. unfold bytes_eqb. destruct (list_eq_dec Z.eq_dec _ _) as [E|E]; [|reflexivity].
  exfalso. apply N. clear N. revert b E. induction a as [|x a IH]; intros [|y b] E; cbn in E; try discriminate;
    [reflexivity|]. injection E as E1 E2. f_equal; [apply bv_eq; exact E1 | apply IH; exact E2].
Qed.

Lemma beq_refl : forall a, bytes_eqb a a = true.
Proof. intros a. unfold bytes_eqb. destruct (list_eq_dec Z.eq_dec _ _) as [_|N]; [reflexivity | exfalso; apply N; reflexivity]. Qed.

Lemma sf1 : forall (A Rb : list byte), (50 <= length Rb)%nat -> s_mac A = sub Rb 6 6 ->
  bytes_eqb (fld A 0 6) (fld (firstn 50 Rb) 6 6) = true.
Proof.
  intros A Rb LR EM. change (fld A 0 6) with (s_mac A). rewrite fld_firstn by lia. change (fld Rb 6 6) with (sub Rb 6 6).
  rewrite EM. apply beq_refl.
Qed.

Lemma sf2 : forall (A U : list byte), s_mac A <> U -> bytes_eqb (fld A 0 6) U = false.
Proof. intros A U N. change (fld A 0 6) with (s_mac A). apply beq_neq. exact N. Qed.

Lemma sf3 : forall (A : list byte), fu A 20 4 = s_ch A.
Proof. intros A. reflexivity. Qed.

Lemma sf4a : forall (A : list byte), 0 <= s32 (fu A 8 4) <= 2 <-> 0 <= s_role A <= 2.
Proof.
  intros A. pose proof (u4_rng A 8) as R. change (fu A 8 4) with (u_at A 8 4).
  rewrite <- (GateModel.s32_swrap (u_at A 8 4) R). reflexivity.
Qed.

Lemma sf4b : forall (A : list byte), length A = 24%nat -> fb A 12 = s_hd A /\ fb A 13 = s_din A /\ fb A 14 = s_dout A.
Proof.
  intros A LA.
  pose proof (u1_fb A 12 ltac:(lia)) as F12. change (u_at A (Z.of_nat 12) 1) with (s_hd A) in F12.
  pose proof (u1_fb A 13 ltac:(lia)) as F13. change (u_at A (Z.of_nat 13) 1) with (s_din A) in F13.
  pose proof (u1_fb A 14 ltac:(lia)) as F14. change (u_at A (Z.of_nat 14) 1) with (s_dout A) in F14.
  split; [|split]; symmetry; assumption.
Qed.

Lemma fsum_firstn : forall Rb : list byte, fsum (firstn 50 Rb) = fsum Rb.
Proof. intros Rb. exact (f_equal blocksum (fld_firstn Rb 18 32 ltac:(lia))). Qed.

Lemma ho_sf : forall H Rb L T A U, length A = 24%nat -> (50 <= length Rb)%nat -> sub H 412 6 = U ->
  ho_facts H Rb L T A -> sighting_facts A (firstn 50 Rb) U L 1.
Proof.
  intros H Rb L T A U LA LR EU (L50 & EM & NU & HG & HRo & HFB & HHd & HDi & _).
  split; [exact L50|].
  split; [exact (sf1 A Rb LR EM)|].
  split; [apply sf2; rewrite <- EU; exact NU|].
  split; [intros C; lia|].
  split; [intros _; rewrite sf3; exact HG|].
  split.
  - split; [exact LA|]. split; [apply sf4a; lia|].
    destruct (sf4b A LA) as (F12 & F13 & F14). rewrite F12, F13, F14.
    destruct HHd as [E|E]; [left; exact E | right; split; [exact E | apply HDi; lia]].
  - destruct HFB as [[F16 F17]|FS].
    + left. rewrite !fb_firstn by lia. split; assumption.
    + right. rewrite fsum_firstn. exact FS.
Qed.


Lemma sub412 : forall (T' Lk C H : list byte), length T' = 400%nat -> length Lk = 12%nat -> firstn 6 C = sub H 412 6 ->
  sub (T' ++ Lk ++ C) 412 6 = sub H 412 6.
Proof.
  intros T' Lk C H LT LL E. unfold sub at 1. change (Z.to_nat 412) with 412%nat.
  rewrite skipn_app, (skipn_all2 T') by lia. rewrite LT. cbn [app].
  replace (412 - 400)%nat with 12%nat by reflexivity.
  rewrite skipn_app, (skipn_all2 Lk) by lia. rewrite LL. cbn [app]. exact E.
Qed.

Lemma lk_len : forall F len U Lb, length Lb = 12%nat -> (dkind F len <> 0 -> length F = 50%nat) ->
  length (match cm_lock F len U (Some Lb) with Some x => x | None => Lb end) = 12%nat.
Proof.
  intros F len U Lb HL HF. unfold cm_lock, classify_model. cbv zeta.
  destruct (Z.eqb_spec (dkind F len) 0) as [K0|K0]; [exact HL|].
  specialize (HF K0).
  destruct (bytes_eqb (src F) U); [exact HL|].
  destruct (negb (dkind F len =? 1) && negb (fsum F =? 0)); [exact HL|].
  destruct ((dkind F len =? 1) && negb (lv Lb =? 0) && negb (bytes_eqb (lm Lb) (src F))); [exact HL|].
  destruct (negb (dkind F len =? 1) && (lv Lb =? 0)); [|exact HL].
  cbn [snd]. unfold latch, src, fld, le4. rewrite !length_app, length_Z_to_le_bytes, !length_firstn, !length_skipn, HF, HL.
  reflexivity.
Qed.

Lemma obs_len : forall T G ow now T' ret, length T = 400%nat -> length G = 24%nat -> tbl_T1 T ->
  observe_model T G ow now T' ret -> length T' = 400%nat.
Proof.
  intros T G ow now T' ret LT LG T1 (r & FR & [(Hr & E) | [(Hr & HN & E) | (Hr & HN & E)]]).
  - unfold tbl_T1 in T1. destruct FR as [[? _] | (? & _)]; [lia|].
    destruct (ok_facts T G ow now r T' ret LT LG ltac:(lia) E) as (L & _). exact L.
  - destruct (full_facts T T' ret LT E) as (L & _). exact L.
  - unfold tbl_T1 in T1. destruct (new_facts T G ow now T' ret LT LG ltac:(lia) E) as (L & _). exact L.
Qed.

Lemma ho_our : forall H FR O len now out r H' m', length H = 480%nat -> length FR = Z.to_nat len -> 0 <= len < 65536 ->
  tbl_T1 (sub H 0 400) -> ho_post H FR O len now out r H' m' -> sub H' 412 6 = sub H 412 6.
Proof.
  intros H FR O len now out r H' m' LH LF Hl T1 HP. unfold ho_post in HP. cbv zeta in HP. destruct HP as [P1 P2].
  set (FB := firstn 50 FR) in *. set (L := reac_frame_clean_len_model len) in *.
  assert (HFB : dkind FB L <> 0 -> length FB = 50%nat).
  { intros K. pose proof (uslot_classify.sc_dkind_len FB L K) as H50. pose proof (cl_model_rng len Hl) as R.
    unfold FB. rewrite length_firstn. subst L. lia. }
  assert (LLk : length (match cm_lock FB L (sub H 412 6) (Some (sub H 400 12)) with Some x => x | None => sub H 400 12 end) = 12%nat)
    by (apply lk_len; [apply length_sub; lia | exact HFB]).
  assert (L12 : firstn 6 (sub H 412 12) = sub H 412 6).
  { unfold sub. rewrite firstn_firstn. reflexivity. }
  destruct (Z.eq_dec (cm_ret FB L (sub H 412 6) (Some (sub H 400 12))) 0) as [C0|C0].
  - destruct (P2 C0) as (T' & c & OM & _ & EH & _). rewrite EH.
    apply sub412; [| exact LLk |].
    + destruct (uslot_classify.sc_cm_ret0 FB L (sub H 412 6) (Some (sub H 400 12)) [] C0) as (K0 & _).
      pose proof (HFB K0) as LFB.
      destruct (uslot_classify.sc_sight FB L (sub H 412 6) (Some (sub H 400 12)) LFB C0) as (_ & LS & _).
      exact (obs_len (sub H 0 400) (sight FB L) 0 now T' c ltac:(apply length_sub; lia) LS T1 OM).
    + rewrite firstn_app. rewrite length_sub by lia. replace (6 - 12)%nat with 0%nat by reflexivity.
      rewrite firstn_O, app_nil_r. exact L12.
  - destruct (P1 C0) as (_ & EH & _). rewrite EH.
    apply sub412; [apply length_sub; lia | exact LLk | reflexivity].
Qed.



Lemma hadd : forall x c, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + c) = Z_to_bv 64 (x + c).
Proof.
  intros x c. rewrite unsigned_lit_wrap.
  rewrite <- (Z_to_bv_mod64 (x mod 2 ^ 64 + c)), <- (Z_to_bv_mod64 (x + c)).
  f_equal. apply Zplus_mod_idemp_l.
Qed.

Ltac hweq := apply Z_to_bv_eqm; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia.

Definition R18 : Z := 0x13c9c.
Definition R18B : Z := 0x13cbc.
Definition R18C : Z := 0x13cf4.
Definition R18S : Z := 0x13d34.
Definition R18T : Z := 0x13d58.

Lemma uslot_R18_cl :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X len : Z),
  sp = Z_to_bv 64 X -> s3 = Z_to_bv 64 len -> 0 < X -> X + 2624 < 2 ^ 63 -> 0 <= len < 65536 ->
  rw_cells rsegs m (X + 32) [C8 (Z_to_bv 64 65535)] -> rw_cells rsegs m (X + 40) [C8 (Z_to_bv 64 INV9)] ->
  evt rsegs (fun ms' => exists a0' a1' : word,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' (Z_to_bv 64 (reac_frame_clean_len_model len)) a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 R18S) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 R18C) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m X len
    Esp Es3 HX0 HX1 Hl R32 R40.
  subst sp s3. unfold R18C, R18S, INV9 in *.
  step. step. step. rewrite ltu_lit by lia.
  destruct (Z.ltb_spec len 54) as [L54|L54]; cbv iota.
  - apply evt_done. do 2 eexists. unfold reac_frame_clean_len_model.
    replace (54 <=? len) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  - do 13 step. apply evt_done. do 2 eexists. rewrite <- (cl_eq len) by lia. reflexivity.
Qed.

Lemma uslot_R18_tail : check_table_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X lo h : Z) (H' : list byte),
  sp = Z_to_bv 64 X ->
  0 < X -> X + 2624 < 2 ^ 63 -> 0 < h -> h mod 8 = 0 -> h + 480 <= lo ->
  rw_cells rsegs m (X + 168) [C8 (Z_to_bv 64 h)] ->
  rw_cells rsegs m h [CB 480 H'] -> hunt_ok H' -> mem_inv rsegs m -> stk rsegs m lo X -> lo + 80 <= X ->
  evt rsegs
    (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
       ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 R27) fc None m' (seg_rom rsegs) /\
       munch [(X - 80, X)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo X)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 R18T) fc None m (seg_rom rsegs)).
Proof.
  intros CTC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    X lo h H' Esp HX0 HX1 Hh0 Hh8 Hhl R168 RH HOK MI ST HLO.
  subst sp. unfold R18T, R27.
  pose proof (munch_refl [(X - 80, X)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  destruct HOK as (LH & (T1 & T2 & T3 & T4) & _ & _).
  pose proof (rwc_split _ _ _ _ RH) as (_ & HH & _).
  pose proof (bytes_at_sub m h H' 0 400 HH ltac:(lia) ltac:(lia)) as B0. rewrite Z.add_0_r in B0.
  step. step.
  eapply evt_cut.
  { eapply CTC with (lo := lo) (t := h) (T := sub H' 0 400); try reflexivity; try eassumption;
      try (apply length_sub; lia); unfold off_window, CHECK_TABLE_K; rewrite ?(unsigned_lit X) by lia; try eassumption; lia. }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
              Eq & MUc & WMc & MI1 & ST1).
  subst ms'. rewrite (unsigned_lit X) in MUc, ST1 by lia. unfold CHECK_TABLE_K in MUc.
  transport_after_call rsegs m m1 MUc WMc. clear MUc WMc MI.
  rewrite (ret_pc_even 0x13d60) by (first [lia | reflexivity]).
  step. apply evt_done. do 16 eexists. exists m1. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI1 | exact ST1].
Qed.

Lemma uslot_R18_sight : check_sighting_contract -> check_table_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X lo f len h v : Z) (Rb H' A U : list byte),
  sp = Z_to_bv 64 X -> s5 = Z_to_bv 64 v -> s11 = Z_to_bv 64 1 -> s7 = Z_to_bv 64 f ->
  a2 = Z_to_bv 64 (reac_frame_clean_len_model len) ->
  0 < X -> X mod 16 = 0 -> X + 2624 < 2 ^ 63 -> 50 <= len < 65536 -> v = -1 \/ v = 0 \/ v = 1 \/ v = 2 ->
  0 < f -> f + len <= lo -> 0 < h -> h mod 8 = 0 -> h + 480 <= lo -> lo + 80 <= X ->
  bytes_at rsegs m f Rb -> length Rb = Z.to_nat len ->
  rw_cells rsegs m (X + 168) [C8 (Z_to_bv 64 h)] ->
  rw_cells rsegs m (X + 1056) [CB 24 A] -> length U = 6%nat -> bytes_at rsegs m (X + 946) U ->
  rw_cells rsegs m h [CB 480 H'] -> hunt_ok H' ->
  sighting_facts A (firstn 50 Rb) U (reac_frame_clean_len_model len) 1 ->
  (v = 1 -> s_role A <> 2) ->
  mem_inv rsegs m -> stk rsegs m lo X ->
  evt rsegs
    (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
       ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 R27) fc None m' (seg_rom rsegs) /\
       munch [(lo, X)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo X)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 R18S) fc None m (seg_rom rsegs)).
Proof.
  intros CSC CTC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    X lo f len h v Rb H' A U Esp Es5 Es11 Es7 Ea2 HX0 HX16 HX1 Hl Hv Hf0 Hfl Hh0 Hh8 Hhl HLO HRb LRb
    R168 RA LU HU RH HOK SF NR MI ST.
  pose proof (munch_refl [(lo, X)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (cl_model_rng len ltac:(lia)) as RL. pose proof SF as (L50 & _ & _ & _ & _ & (LA & SR & _) & _).
  apply sf4a in SR.
  subst sp s5 s11 s7 a2. unfold R18S.
  step. step. step. step. step.
  pose proof (rwc_bytes _ _ _ _ RA) as HA.
  pose proof (bytes_at_sub m f Rb 0 50 HRb ltac:(lia) ltac:(lia)) as B50. rewrite Z.add_0_r in B50.
  eapply evt_cut.
  { eapply CSC with (lo := lo) (s := X + 1056) (f := f) (len := reac_frame_clean_len_model len) (u := X + 946) (st := 1)
      (S := A) (FB := firstn 50 Rb) (U := U); try reflexivity; try eassumption;
      try (rewrite length_firstn; lia); unfold CHECK_SIGHTING_K; rewrite ?(unsigned_lit X) by lia; try eassumption;
      try (Z.div_mod_to_equations; lia); lia. }
  intros ms' (t0' & t1' & t2' & a0b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3' & t4' & t5' & t6' & m1 &
              Eq & MUc & WMc & MI1 & ST1).
  subst ms'. rewrite (unsigned_lit X) in MUc, ST1 by lia. unfold CHECK_SIGHTING_K in MUc.
  transport_after_call rsegs m m1 MUc WMc. clear MUc WMc MI.
  rewrite (ret_pc_even 0x13d48) by (first [lia | reflexivity]).
  assert (TAIL : forall (m2 : word -> option byte) (rx x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    munch [(lo, X)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 -> stk rsegs m2 lo X ->
    rw_cells rsegs m2 (X + 168) [C8 (Z_to_bv 64 h)] -> rw_cells rsegs m2 h [CB 480 H'] ->
    evt rsegs
      (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' (Z_to_bv 64 X) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 (Z_to_bv 64 v) s6 (Z_to_bv 64 f) s8 s9 s10 (Z_to_bv 64 1) t3' t4' t5' t6')
                  F (Z_to_bv 64 R27) fc None m' (seg_rom rsegs) /\
         munch [(lo, X)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo X)
      (MS (mkR rx (Z_to_bv 64 X) gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17
               s2 s3 s4 (Z_to_bv 64 v) s6 (Z_to_bv 64 f) s8 s9 s10 (Z_to_bv 64 1) x28 x29 x30 x31)
          F (Z_to_bv 64 R18T) fc None m2 (seg_rom rsegs))).
  { intros m2 rx x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 MU2 WM2 MI2 ST2 R1682 RH2.
    eapply evt_mono.
    { eapply (uslot_R18_tail CTC) with (lo := lo) (h := h) (H' := H'); try reflexivity; try eassumption; lia. }
    intros ms' (ra' & t0c & t1c & t2c & a0c & a1c & a2c & a3c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & m3 &
                -> & MU3 & WM3 & MI3 & ST3).
    do 16 eexists. exists m3. split; [reflexivity|].
    split; [eapply munch_trans; [exact MU2 | eapply munch_weaken; [|exact MU3]; unfold sub_fp; cbn [outside]; intros; lia]|].
    split; [eapply wmono_trans; eassumption|]. split; assumption. }
  destruct Hv as [-> | [-> | [-> | ->]]].
  - step. ccl. apply TAIL; assumption.
  - step. ccl. apply TAIL; assumption.
  - step. ccl.
    rdx (X + 1056) A 8 4%nat RB.
    step. rewrite lw_val by lv. rem_lw w Ew.
    assert (Hw : w = s_role A) by (subst w; reflexivity). rewrite Hw. clear Ew Hw RB.
    step. step. rewrite eqb_lit by lia.
    replace (s_role A =? 2) with false by (symmetry; apply Z.eqb_neq; specialize (NR eq_refl); lia).
    cbv iota. apply TAIL; assumption.
  - step. ccl. apply TAIL; assumption.
Qed.


Definition r18_post (ra sp gp tp s1 s2 s3 s4 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (X lo f len h : Z) (Rb U : list byte) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' s0' a0' a1' a2' a3' a4' a5' a6' a7' s5' t3' t4' t5' t6' : word)
                    (m' : word -> option byte) (H' S' : list byte),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5' s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 R27) fc None m' (seg_rom rsegs) /\
    munch [(lo, X); (h, h + 480); (X + 1056, X + 1080)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    stk rsegs m' lo X /\
    rw_cells rsegs m' f [CB (Z.to_nat len) Rb] /\ rw_cells rsegs m' h [CB 480 H'] /\ hunt_ok H' /\ sub H' 412 6 = U /\
    rw_cells rsegs m' (X + 1056) [CB 24 S'] /\ bytes_at rsegs m' (X + 946) U.

Lemma uslot_R18_body : role_of_contract -> reac_hunt_observe_contract -> check_sighting_contract -> check_table_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X lo f len h now p : Z) (Rb H OB U P : list byte),
  sp = Z_to_bv 64 X -> a1 = Z_to_bv 64 p -> s1 = Z_to_bv 64 now -> s3 = Z_to_bv 64 len -> s7 = Z_to_bv 64 f ->
  s11 = Z_to_bv 64 1 ->
  0 < X -> X mod 16 = 0 -> X + 2624 < 2 ^ 63 -> 0 <= len < 65536 -> 0 <= now < 2 ^ 64 ->
  0 < f -> f + len <= lo -> 0 < h -> h mod 8 = 0 -> h + 480 <= lo ->
  (0 < len -> disj f len h 480) ->
  rw_cells rsegs m f [CB (Z.to_nat len) Rb] -> rw_cells rsegs m h [CB 480 H] -> hunt_ok H -> sub H 412 6 = U ->
  length U = 6%nat -> bytes_at rsegs m (X + 946) U ->
  0 < p -> bytes_at rsegs m p P -> length P = 6%nat -> p + 6 <= lo \/ X <= p -> (11 < len -> P = sub Rb 6 6) ->
  rw_cells rsegs m (X + 32) [C8 (Z_to_bv 64 65535)] -> rw_cells rsegs m (X + 40) [C8 (Z_to_bv 64 INV9)] ->
  rw_cells rsegs m (X + 168) [C8 (Z_to_bv 64 h)] ->
  rw_cells rsegs m (X + 1056) [CB 24 OB] ->
  bytes_at rsegs m A_M (le8 (Z_to_bv 64 KM)) -> bytes_at rsegs m A_T (le8 (Z_to_bv 64 KT)) ->
  mem_inv rsegs m -> stk rsegs m lo X -> lo + REAC_HUNT_OBSERVE_K <= X -> 0x52000 <= lo ->
  evt rsegs (r18_post ra sp gp tp s1 s2 s3 s4 s6 s7 s8 s9 s10 s11 F fc m X lo f len h Rb U)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 R18B) fc None m (seg_rom rsegs)).
Proof.
  intros ROC HOC CSC CTC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m X lo f len h now p Rb H OB U P Esp Ea1 Es1 Es3 Es7 Es11 HX0 HX16 HX1 Hl Hnow Hf0 Hfl Hh0
    Hh8 Hhl Hdj RF RH HOK EU LU HU Hp0 HP LP Hpw HP11 R32 R40 R168 RO HAM HAT MI ST HLO HLI.
  subst sp a1 s1 s3 s7 s11. unfold R18B, r18_post. unfold A_M, A_T in HAM, HAT. unfold REAC_HUNT_OBSERVE_K in HLO.
  pose proof (munch_refl [(lo, X); (h, h + 480); (X + 1056, X + 1080)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (rwc_split _ _ _ _ RF) as (LRb & HRb & WRb).
  pose proof (rwc_split _ _ _ _ RH) as (LH & HH & WH).
  pose proof HOK as (LH' & (T1 & T2 & T3 & T4) & _ & _).
  pose proof (bytes_at_sub m h H 0 400 HH ltac:(lia) ltac:(lia)) as B0. rewrite Z.add_0_r in B0.
  step. step. step.
  eapply evt_cut.
  { eapply ROC with (lo := lo) (t := h) (p := p) (T := sub H 0 400) (P := P); try reflexivity;
      try (apply length_sub; lia); try eassumption;
      unfold off_window, ROLE_OF_K, FIND_ENTRY_K; rewrite ?(unsigned_lit X) by lia; try eassumption;
      try (Z.div_mod_to_equations; lia); lia. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & v &
              Eq & MUc & WMc & MI1 & ST1 & (idx & FRi & Ev) & Vr).
  subst ms'. rewrite (unsigned_lit X) in MUc, ST1 by lia. unfold ROLE_OF_K, FIND_ENTRY_K in MUc.
  transport_after_call rsegs m m1 MUc WMc. clear MUc WMc MI.
  rewrite (ret_pc_even 0x13cc8) by (first [lia | reflexivity]).
  step. step. step. step. step. step. step.
  eapply evt_cut.
  { eapply HOC with (lo := lo) (h := h) (f := f) (len := len) (now := now) (out := X + 1056) (H := H) (FR := Rb) (O := OB);
      try reflexivity; try eassumption; try lia.
    all: first
      [ intros Hl0; split; [apply Hdj; exact Hl0 | unfold off_window, REAC_HUNT_OBSERVE_K; rewrite (unsigned_lit X) by lia; lia]
      | intros _; split; [Z.div_mod_to_equations; lia|]; split; [exact RO|]; split; [unfold disj; lia|];
        split; [intros _; unfold disj; lia | unfold off_window, REAC_HUNT_OBSERVE_K; rewrite (unsigned_lit X) by lia; lia]
      | rewrite (unsigned_lit X) by lia; first [exact HX16 | exact ST1 | unfold REAC_HUNT_OBSERVE_K; lia]
      | unfold off_window, REAC_HUNT_OBSERVE_K; rewrite (unsigned_lit X) by lia; lia
      | exact HAM | exact HAT ]. }
  intros ms' (t0c & t1c & t2c & a1c & a2c & a3c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & m2 & r & H' &
              Eq & MUc & WMc & MI2 & ST2 & HRb2 & RH2 & HOK2 & Hr & HPo).
  subst ms'. rewrite (unsigned_lit X) in MUc, ST2 by lia. unfold REAC_HUNT_OBSERVE_K in MUc.
  replace (X + 1056 =? 0) with false in MUc by (symmetry; apply Z.eqb_neq; lia). cbv iota in MUc.
  transport_after_call rsegs m1 m2 MUc WMc. clear MUc WMc MI1.
  rewrite (ret_pc_even 0x13ce4) by (first [lia | reflexivity]).
  pose proof (ho_our H Rb OB len now (X + 1056) r H' m2 LH' LRb Hl T1 HPo) as EH.
  pose proof HPo as HPo'. unfold ho_post in HPo'. cbv zeta in HPo'. destruct HPo' as [P1 P2].
  set (FB := firstn 50 Rb) in *. set (L := reac_frame_clean_len_model len) in *.
  destruct Hr as [-> | Hr01].
  - destruct (Z.eq_dec (cm_ret FB L (sub H 412 6) (Some (sub H 400 12))) 0) as [C0|C0].
    { destruct (P2 C0) as (T' & c & _ & Erc & _). destruct (c =? 0); lia. }
    destruct (P1 C0) as (_ & _ & RO2). specialize (RO2 ltac:(lia)).
    step. step. step. ccl. step. ccl.
    eapply evt_cut.
    { eapply (uslot_R18_tail CTC) with (lo := lo) (h := h) (H' := H'); try reflexivity; try eassumption; lia. }
    intros ms' (ra' & t0d & t1d & t2d & a0d & a1d & a2d & a3d & a4d & a5d & a6d & a7d & t3d & t4d & t5d & t6d & m3 &
                -> & MU3 & WM3 & MI3 & ST3).
    transport_after_call rsegs m2 m3 MU3 WM3. clear MU3 WM3 MI2.
    apply evt_done. do 18 eexists. exists m3, H', OB. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact ST3|].
    split; [apply rwc_mk; assumption|]. split; [assumption|]. split; [assumption|].
    split; [rewrite EH; exact EU|]. split; assumption.
  - destruct (Z.eq_dec (cm_ret FB L (sub H 412 6) (Some (sub H 400 12))) 0) as [C0|C0];
      [| destruct (P1 C0) as (Er & _); lia].
    destruct (P2 C0) as (T' & c & _ & _ & _ & PA).
    destruct (PA ltac:(lia)) as (A & _ & RA & HF).
    pose proof (cl_model_rng len Hl) as RL.
    pose proof HF as (L50 & EM & _).
    assert (L50' : 50 <= len) by (subst L; lia).
    pose proof (rwc_len _ _ _ _ RA) as LA.
    assert (SF : sighting_facts A FB U L 1) by (apply (ho_sf H Rb L (sub H 0 400) A U LA ltac:(lia) EU HF)).
    assert (NR : v = 1 -> s_role A <> 2).
    { intros Hb. rewrite Ev in Hb.
      destruct (Z.ltb_spec idx 0) as [Hn|Hn]; [lia|].
      destruct FRi as [[Em _] | (Hidx & Emac & _)]; [lia|].
      destruct HF as (_ & _ & _ & _ & _ & _ & _ & _ & HB).
      assert (EMA : mac_of (sub H 0 400) idx = s_mac A) by (rewrite Emac, (HP11 ltac:(lia)); symmetry; exact EM).
      rewrite (HB (ex_intro _ idx (conj Hidx (conj EMA Hb)))). lia. }
    destruct Hr01 as [-> | ->].
    + step. step. step. ccl. step. ccl.
      eapply evt_cut.
      { eapply uslot_R18_cl with (X := X) (len := len); try reflexivity; try eassumption; lia. }
      intros ms' (a0e & a1e & ->).
      eapply evt_cut.
      { eapply (uslot_R18_sight CSC CTC) with (lo := lo) (f := f) (len := len) (h := h) (v := v)
          (Rb := Rb) (H' := H') (A := A) (U := U);
          try reflexivity; try eassumption; try lia. }
      intros ms' (ra' & t0d & t1d & t2d & a0d & a1d & a2d & a3d & a4d & a5d & a6d & a7d & t3d & t4d & t5d & t6d & m3 &
                  -> & MU3 & WM3 & MI3 & ST3).
      transport_after_call rsegs m2 m3 MU3 WM3. clear MU3 WM3 MI2.
      apply evt_done. do 18 eexists. exists m3, H', A. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact ST3|].
      split; [apply rwc_mk; assumption|]. split; [assumption|]. split; [assumption|].
      split; [rewrite EH; exact EU|]. split; assumption.
    + step. step. step. ccl. step. ccl.
      eapply evt_cut.
      { eapply uslot_R18_cl with (X := X) (len := len); try reflexivity; try eassumption; lia. }
      intros ms' (a0e & a1e & ->).
      eapply evt_cut.
      { eapply (uslot_R18_sight CSC CTC) with (lo := lo) (f := f) (len := len) (h := h) (v := v)
          (Rb := Rb) (H' := H') (A := A) (U := U);
          try reflexivity; try eassumption; try lia. }
      intros ms' (ra' & t0d & t1d & t2d & a0d & a1d & a2d & a3d & a4d & a5d & a6d & a7d & t3d & t4d & t5d & t6d & m3 &
                  -> & MU3 & WM3 & MI3 & ST3).
      transport_after_call rsegs m2 m3 MU3 WM3. clear MU3 WM3 MI2.
      apply evt_done. do 18 eexists. exists m3, H', A. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact ST3|].
      split; [apply rwc_mk; assumption|]. split; [assumption|]. split; [assumption|].
      split; [rewrite EH; exact EU|]. split; assumption.
Qed.

Lemma uslot_R18 : role_of_contract -> reac_hunt_observe_contract -> check_sighting_contract -> check_table_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X lo f len h now : Z) (Rb H OB U : list byte),
  sp = Z_to_bv 64 X -> s1 = Z_to_bv 64 now -> s3 = Z_to_bv 64 len -> s7 = Z_to_bv 64 f -> s11 = Z_to_bv 64 1 ->
  0 < X -> X mod 16 = 0 -> X + 2624 < 2 ^ 63 -> 0 <= len < 2 ^ 16 -> 0 <= now < 2 ^ 64 ->
  0 < f -> f + len <= lo -> 0 < h -> h mod 8 = 0 -> h + 480 <= lo ->
  (0 < len -> disj f len h 480) ->
  rw_cells rsegs m f [CB (Z.to_nat len) Rb] -> rw_cells rsegs m h [CB 480 H] -> hunt_ok H -> sub H 412 6 = U ->
  length U = 6%nat -> bytes_at rsegs m (X + 946) U ->
  rw_cells rsegs m (X + 32) [C8 (Z_to_bv 64 65535)] -> rw_cells rsegs m (X + 40) [C8 (Z_to_bv 64 INV9)] ->
  rw_cells rsegs m (X + 128) [C8 (Z_to_bv 64 0)] -> rw_cells rsegs m (X + 168) [C8 (Z_to_bv 64 h)] ->
  rw_cells rsegs m (X + 1056) [CB 24 OB] ->
  bytes_at rsegs m A_M (le8 (Z_to_bv 64 KM)) -> bytes_at rsegs m A_T (le8 (Z_to_bv 64 KT)) ->
  mem_inv rsegs m -> stk rsegs m lo X -> lo + REAC_HUNT_OBSERVE_K <= X -> 0x52000 <= lo ->
  evt rsegs (r18_post ra sp gp tp s1 s2 s3 s4 s6 s7 s8 s9 s10 s11 F fc m X lo f len h Rb U)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 R18) fc None m (seg_rom rsegs)).
Proof.
  intros ROC HOC CSC CTC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m X lo f len h now Rb H OB U Esp Es1 Es3 Es7 Es11 HX0 HX16 HX1 Hl Hnow Hf0 Hfl Hh0 Hh8 Hhl
    Hdj RF RH HOK EU LU HU R32 R40 R128 R168 RO HAM HAT MI ST HLO HLI.
  pose proof (rwc_split _ _ _ _ RF) as (LRb & HRb & _).
  subst sp s1 s3 s7 s11. unfold R18.
  pose proof HLO as HLO'. unfold REAC_HUNT_OBSERVE_K in HLO'.
  step. step. ccl.
  step. step. step. rewrite ?hadd. rewrite ltu_lit by lia.
  destruct (Z.ltb_spec len 12) as [L12|L12]; cbv iota.
  - eapply (uslot_R18_body ROC HOC CSC CTC) with (lo := lo) (f := f) (len := len) (h := h) (now := now)
        (p := X + 946) (P := U) (Rb := Rb) (H := H) (OB := OB) (U := U);
        try reflexivity; try eassumption; try lia; try hweq; try (intros; exfalso; lia).
  - step. step. step. rewrite ?hadd. rewrite ltu_lit by lia.
    replace (f + 6 <? 7) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    eapply (uslot_R18_body ROC HOC CSC CTC) with (lo := lo) (f := f) (len := len) (h := h) (now := now)
        (p := f + 6) (P := sub Rb 6 6) (Rb := Rb) (H := H) (OB := OB) (U := U);
        try reflexivity; try eassumption; try lia; try hweq; try (intros; reflexivity);
        try (apply bytes_at_sub; [exact HRb | lia | lia]);
        try (apply length_sub; lia).
Qed.
