From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_text.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells codec_img
  diginet_personality_of_c text_arg_c check_text_seg7_c check_text_counter_c owed_counter_text_c
  codec_main_inv codec_main_lib codec_main_rd12.
Import ListNotations.
Open Scope Z_scope.

(** Segment RD13 of the walk of LLVMFuzzerTestOneInput in the UBSan image: COUNTER_TEXT
    (fuzz_codec.c:632-647), 0x13994-0x139f8. A NULL k.p takes the personality and desk of index 1
    (as SCRIBBLE_TEXT does); then text_arg(&in, text), check_text_seg7(), check_text_counter(text,
    k.bytes, &dots) and owed_counter_text(text, k.bytes, &dots). A non-zero code continues to the
    latch; code 0 sets k.kind = COUNTER and k.b = dots and jumps to run()'s COUNTER arm. *)

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** The record of a text operation: kind, p and desk of index i, b, the 24 bytes; the rest as the
    head left it. *)
Definition kt (kind i b : Z) (bs : list byte) : kcall :=
  mkKcall kind (repeat (b8 0) 4) (pers_of i) (sdesk i) 0 b 0 0 bs 0 0
          (repeat (b8 0xa5) 32) (repeat (b8 0xa5) 32) 0 (repeat (b8 0) 24) 0 0 0.

(** ---- the model ---- *)

Lemma ct2_go_rc : forall k n s dot i seg d,
  fst (fst (ct2_go n s dot i k seg d)) = 0 \/ fst (fst (ct2_go n s dot i k seg d)) = E_RANGE.
Proof.
  induction k as [|k IH]; intros n s dot i seg d; cbn [ct2_go].
  - left. reflexivity.
  - repeat match goal with |- context [if ?b then _ else _] => destruct b end;
      first [ left; reflexivity | right; reflexivity | apply IH ].
Qed.

(** owed_counter_text returns 0 or E_RANGE. *)
Lemma oct_rc : forall t,
  fst (fst (owed_counter_text_spec t)) = 0 \/ fst (fst (owed_counter_text_spec t)) = E_RANGE.
Proof.
  intros t. unfold owed_counter_text_spec.
  destruct (ct1_owe t 0 [] (repeat 0 8)) as [[[n s] dot] |].
  - unfold ct2. apply ct2_go_rc.
  - right. reflexivity.
Qed.

Lemma zb_app : forall a b, zb (a ++ b) = zb a ++ zb b.
Proof. intros a b. unfold zb. apply map_app. Qed.

(** The record of a counter text whose owed code is 0: what run() may be handed. *)
Lemma rec_wf_k10 : forall i t sg d, (i = 1 \/ i = 2) -> owed_counter_text_spec t = (0, sg, d) ->
  rec_wf (kt 10 i d (bz sg ++ repeat (b8 0xa5) 16)).
Proof.
  intros i t sg d Hi H. destruct (owed_counter_ok t 0 sg d H eq_refl) as (L & F & D).
  assert (F' : Forall (fun x => 0 <= x < 256) sg)
    by (rewrite Forall_forall in F |- *; intros x Hx; specialize (F x Hx); lia).
  unfold rec_wf, kt.
  cbn [k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc k_before k_out k_want_rc k_want
       k_want_len k_want_key k_want_display].
  split; [lia |].
  split.
  { unfold desk_at. cbn [k_p k_desk].
    destruct Hi as [-> | ->]; [right; left | right; right]; split; reflexivity. }
  do 7 (split; [reflexivity |]).
  rewrite zb_app, (zb_bz_id sg F').
  exact (reader_ok_13 t sg d H).
Qed.

(** ---- k.bytes and the dots slot as the callees take them ---- *)

Lemma cb_8_16 : forall m A x y, rw_cells rsegs m A [CB 8 x] -> rw_cells rsegs m (A + 8) [CB 16 y] ->
  rw_cells rsegs m A [CB 24 (x ++ y)].
Proof.
  intros m A x y H1 H2.
  pose proof (proj2 (cb_bytes _ _ _ _ H1)) as L1. pose proof (proj2 (cb_bytes _ _ _ _ H2)) as L2.
  apply (rw_cells_same_bytes m A ([CB 8 x] ++ [CB 16 y]) [CB 24 (x ++ y)]);
    [ cbn; rewrite length_app; repeat split; lia | cbn; rewrite ?app_nil_r; reflexivity | reflexivity | ].
  apply rw_cells_app_join; [exact H1 | exact H2].
Qed.

Lemma cb10_split : forall m A d0 pl9, rw_cells rsegs m A [CB 10 (d0 :: pl9)] ->
  rw_cells rsegs m A [C1 d0] /\ rw_cells rsegs m (A + 1) [CB 9 pl9].
Proof.
  intros m A d0 pl9 H. pose proof (proj2 (cb_bytes _ _ _ _ H)) as L. cbn [length] in L.
  apply (rw_cells_same_bytes m A [CB 10 (d0 :: pl9)] ([C1 d0] ++ [CB 9 pl9])) in H;
    [ | cbn; repeat split; lia | cbn; rewrite ?app_nil_r; reflexivity | reflexivity ].
  apply rw_cells_app_split in H. exact H.
Qed.

Lemma cb10_join : forall m A d0 pl9, rw_cells rsegs m A [C1 d0] -> rw_cells rsegs m (A + 1) [CB 9 pl9] ->
  rw_cells rsegs m A [CB 10 (d0 :: pl9)].
Proof.
  intros m A d0 pl9 H1 H2. pose proof (proj2 (cb_bytes _ _ _ _ H2)) as L.
  apply (rw_cells_same_bytes m A ([C1 d0] ++ [CB 9 pl9]) [CB 10 (d0 :: pl9)]);
    [ cbn; repeat split; lia | cbn; rewrite ?app_nil_r; reflexivity | reflexivity | ].
  apply rw_cells_app_join; [exact H1 | exact H2].
Qed.

(** ---- 0x139b0-0x139f8: the four text calls and the two exits ---- *)

Lemma rd13_body : forall E n, env_ok E -> text_arg_contract -> check_text_seg7_contract ->
  check_text_counter_contract -> owed_counter_text_contract -> rd_run_arm E n -> latch_ok E n 0x14a54 ->
  forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' : word)
         (cur rem : word) (i c ops : Z) (u0 pj tj plj : list byte) (m1 : word -> option byte),
  (i = 1 \/ i = 2) ->
  256 - ops <= Z.of_nat n -> 0 <= ops <= 255 ->
  bv_unsigned cur = bv_unsigned (c_p E) + c -> 1 <= c ->
  c + bv_unsigned rem = Z.of_nat (length (c_data E)) ->
  fr E m1 (kcall_cells (k_head 13 i)) cur rem u0 pj tj plj ->
  stk rsegs m1 (c_lo E) (bv_unsigned (c_sp E) + -416) ->
  munch [(bv_unsigned (c_sp E) - 640, bv_unsigned (c_sp E))] (c_m E) m1 ->
  wmono rsegs (c_m E) m1 ->
  mem_inv rsegs m1 ->
  evt rsegs (Qk E) (st12 E ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7'
                     t3' t4' t5' t6' ops 0x139b0 m1).
Proof.
  intros E n ENV CTA CSG CTC OCT RUN LATCH ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7'
         t3' t4' t5' t6' cur rem i c ops u0 pj tj plj m1 Hi HN HOPS HCUR HC1 HCN FR ST MU WM HMI.
  unfold st12.
  pose proof ENV as (HD & _ & _ & HLO & SPA & DJ & HPB & HPNZ & _ & DJR).
  pose proof (bv_unsigned_in_range 64 (c_sp E)) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 (c_p E)) as Rp. unfold bv_modulus in Rp.
  pose proof (bv_unsigned_in_range 64 cur) as Rcur. unfold bv_modulus in Rcur.
  pose proof (bv_unsigned_in_range 64 rem) as Rrem. unfold bv_modulus in Rrem.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp, Rp, Rcur, Rrem.
  assert (HL : 0 < Z.of_nat (length (c_data E))) by lia.
  specialize (HPNZ HL).
  pose proof ST as (Hlo0 & _).
  unfold fr in FR. destruct FR as (_ & F0 & F8 & FK & FIN & FPD & FTX & FPL & FSV).
  rewrite <- (Z_to_bv_bv_unsigned cur), <- (Z_to_bv_bv_unsigned rem), HCUR in FIN.
  replace (bv_unsigned rem) with (Z.of_nat (length (c_data E)) - c) in FIN by lia.
  pose proof (data_at E m1 ENV MU) as HDAT.
  assert (DATA : bytes_at rsegs m1 (bv_unsigned (c_p E) + c) (skipn (Z.to_nat c) (c_data E)))
    by (apply bytes_at_skipn; [exact HDAT | lia]).
  assert (LD : Z.of_nat (length (skipn (Z.to_nat c) (c_data E))) = Z.of_nat (length (c_data E)) - c)
    by (rewrite length_skipn; lia).
  rewrite <- LD in FIN.
  pose proof (used_le (skipn (Z.to_nat c) (c_data E))) as TU.
  remember (skipn (Z.to_nat c) (c_data E)) as dd eqn:Edd. clear Edd HDAT HD.
  clear Rcur Rrem HCUR HCN.
  destruct (krec_split _ _ _ FK) as (K1 & K2 & K3). clear FK.
  unfold kpre in K1. cbn [k_head k_kind k_pad k_p k_desk k_a k_b k_c k_delta] in K1.
  cbn [k_head k_bytes] in K2.
  unfold kpost in K3.
  cbn [k_head k_n k_rc k_before k_out k_want_rc k_want k_want_len k_want_key k_want_display] in K3.
  unfold saved in FSV.
  destruct (cb_bytes _ _ _ _ FPL) as [_ LPL].
  destruct plj as [|d0 pl9]; [discriminate LPL |].
  destruct (cb10_split _ _ _ _ FPL) as [FDT FP9]. clear FPL LPL.
  assert (U416 : bv_unsigned (Z_to_bv 64 (bv_unsigned (c_sp E) + -416)) = bv_unsigned (c_sp E) + -416)
    by (apply u_frame; lia).
  assert (U200 : bv_unsigned (Z_to_bv 64 (bv_unsigned (c_sp E) + -200)) = bv_unsigned (c_sp E) + -200)
    by (apply unsigned_lit; lia).
  assert (U179 : bv_unsigned (Z_to_bv 64 (bv_unsigned (c_sp E) + -179)) = bv_unsigned (c_sp E) + -179)
    by (apply unsigned_lit; lia).
  assert (U344 : bv_unsigned (Z_to_bv 64 (bv_unsigned (c_sp E) + -344)) = bv_unsigned (c_sp E) + -344)
    by (apply unsigned_lit; lia).
  assert (U114 : bv_unsigned (Z_to_bv 64 (bv_unsigned (c_sp E) + -114)) = bv_unsigned (c_sp E) + -114)
    by (apply unsigned_lit; lia).
  (* 0x139b0-0x139b8: text_arg(&in, text) *)
  zstep. zstep. zstep.
  unfold text_arg_contract, TEXT_ARG, TEXT_ARG_DEPTH in CTA.
  eapply evt_cut;
    [ eapply CTA with (lo := c_lo E) (p := bv_unsigned (c_p E) + c) (data := dd) (tj := tj)
    | intros ms' (t0x & t1x & t2x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x
                  & mT & -> & MU2 & WM2 & MI2 & ST2 & FIN2 & FTX2) ].
  { unfold text_arg_pre, TEXT_ARG_DEPTH. rewrite ?U416, ?U200, ?U179.
    split; [exact FIN |]. split; [exact DATA |]. split; [exact FTX |].
    split; [unfold disj; lia |]. split; [unfold disj; lia |]. split; [unfold disj; lia |].
    split; [lia |]. split; [lia |]. split; [lia |].
    split; [apply mod8_200; exact SPA |].
    split; [lia |]. split; [lia |].
    split; [assumption |]. split; [assumption | lia]. }
  fix_ret.
  rewrite U416 in ST2. rewrite U200 in FIN2. rewrite U179 in FTX2.
  clear FIN FTX DATA DJ.
  tr MU2 WM2 F0. tr MU2 WM2 F8. tr MU2 WM2 K1. tr MU2 WM2 K2. tr MU2 WM2 K3.
  tr MU2 WM2 FPD. tr MU2 WM2 FDT. tr MU2 WM2 FP9. tr MU2 WM2 FSV.
  assert (MU2' : munch [(bv_unsigned (c_sp E) - 640, bv_unsigned (c_sp E))] (c_m E) mT)
    by (apply (munch_trans _ _ _ _ MU); refine (munch_weaken _ _ _ _ _ MU2);
        intros x Hx; cbn [outside] in Hx |- *; destruct Hx as [Hx _]; repeat split; lia).
  pose proof (wmono_trans rsegs _ _ _ WM WM2) as WM2'.
  clear MU WM MU2 WM2.
  (* 0x139bc: check_text_seg7() *)
  zstep.
  unfold check_text_seg7_contract, CHECK_TEXT_SEG7, CHECK_TEXT_SEG7_DEPTH in CSG.
  eapply evt_cut;
    [ eapply CSG with (lo := c_lo E)
    | intros ms' (t0g & a0g & a1g & a2g & a3g & a4g & a5g & a6g & a7g & mG & -> & MU4 & WM4 & MI4 & ST4) ].
  { unfold check_text_seg7_pre, CHECK_TEXT_SEG7_DEPTH. rewrite ?U416.
    split; [exact (relro_at E mT ENV MU2') |].
    split; [unfold disj in DJR |- *; lia |].
    split; [assumption |]. split; [assumption |]. split; [lia |].
    exact seg7_agree. }
  fix_ret.
  rewrite U416 in ST4.
  tr MU4 WM4 F0. tr MU4 WM4 F8. tr MU4 WM4 K1. tr MU4 WM4 K2. tr MU4 WM4 K3.
  tr MU4 WM4 FIN2. tr MU4 WM4 FTX2.
  tr MU4 WM4 FPD. tr MU4 WM4 FDT. tr MU4 WM4 FP9. tr MU4 WM4 FSV.
  assert (MU4' : munch [(bv_unsigned (c_sp E) - 640, bv_unsigned (c_sp E))] (c_m E) mG)
    by (apply (munch_trans _ _ _ _ MU2'); refine (munch_weaken _ _ _ _ _ MU4);
        intros x Hx; cbn [outside] in Hx |- *; destruct Hx as [Hx _]; repeat split; lia).
  pose proof (wmono_trans rsegs _ _ _ WM2' WM4) as WM4'.
  clear MU2' WM2' MU4 WM4.
  (* 0x139c0-0x139d0: check_text_counter(text, k.bytes, &dots) *)
  zstep. zstep. zstep. zstep. zstep.
  unfold check_text_counter_contract, CHECK_TEXT_COUNTER, CHECK_TEXT_COUNTER_DEPTH in CTC.
  destruct (cb_bytes _ _ _ _ FTX2) as [TBB LTB].
  assert (TB0 : In (b8 0) (text_taken dd ++ [b8 0] ++ skipn (S (text_len dd)) tj))
    by (apply in_or_app; right; left; reflexivity).
  remember (text_taken dd ++ [b8 0] ++ skipn (S (text_len dd)) tj) as tb eqn:Etb. clear Etb.
  eapply evt_cut;
    [ eapply CTC with (lo := c_lo E) (tb := tb) (sj := repeat (b8 0) 24) (dj := d0)
    | intros ms' (t0c & t1c & t2c & a0c & a1c & a2c & a3c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c
                  & mC & -> & MU5 & WM5 & MI5 & ST5 & sg0 & dv0 & KB5 & DT5) ].
  { unfold check_text_counter_pre, CHECK_TEXT_COUNTER_DEPTH. rewrite ?U416, ?U179, ?U344, ?U114.
    split; [lia |]. split; [split; [exact TBB | exact TB0] |].
    split; [lia |]. split; [exact K2 |].
    split; [lia |]. split; [exact FDT |].
    split; [unfold disj; lia |].
    split; [unfold disj; rewrite LTB; lia |].
    split; [unfold disj; rewrite LTB; lia |].
    split; [exact (relro_at E mG ENV MU4') |].
    split; [unfold disj in DJR |- *; lia |].
    split; [lia |]. split; [lia |]. split; [lia |].
    split; [assumption |]. split; [assumption |]. split; [lia |].
    rewrite counter_text_agree by exact (bytes_ok_map tb).
    destruct (owed_counter_text_spec (zb tb)) as [[r s] d].
    cbv beta iota. split; [reflexivity | intros _; split; reflexivity]. }
  fix_ret.
  rewrite U416 in ST5. rewrite U344 in KB5. rewrite U114 in DT5.
  clear K2 FDT TBB.
  tr MU5 WM5 F0. tr MU5 WM5 F8. tr MU5 WM5 K1. tr MU5 WM5 K3.
  tr MU5 WM5 FIN2. tr MU5 WM5 FTX2.
  tr MU5 WM5 FPD. tr MU5 WM5 FP9. tr MU5 WM5 FSV.
  assert (MU5' : munch [(bv_unsigned (c_sp E) - 640, bv_unsigned (c_sp E))] (c_m E) mC)
    by (apply (munch_trans _ _ _ _ MU4'); refine (munch_weaken _ _ _ _ _ MU5);
        intros x Hx; cbn [outside] in Hx |- *; destruct Hx as [Hx _]; repeat split; lia).
  pose proof (wmono_trans rsegs _ _ _ WM4' WM5) as WM5'.
  clear MU4' WM4' MU5 WM5.
  (* 0x139d4-0x139e0: owed_counter_text(text, k.bytes, &dots) on the first 8 bytes *)
  apply rw_cells_app_split with (cs1 := [CB 8 sg0]) in KB5. destruct KB5 as [KB8 KB16].
  change (Z.of_nat (cells_size [CB 8 sg0])) with 8 in KB16.
  zstep. zstep. zstep. zstep.
  unfold owed_counter_text_contract, OWED_COUNTER_TEXT, OWED_COUNTER_TEXT_DEPTH in OCT.
  pose proof (proj1 (cb_bytes _ _ _ _ FTX2)) as TBC.
  eapply evt_cut;
    [ eapply OCT with (lo := c_lo E) (tb := tb) (sj := sg0) (dj := dv0)
    | intros ms' (t0o & a0o & a1o & a2o & a3o & a4o & a5o & a6o & a7o & mO & -> & MU6 & WM6 & MI6 & ST6 & PO) ].
  { unfold owed_counter_text_pre, OWED_COUNTER_TEXT_DEPTH. rewrite ?U416, ?U179, ?U344, ?U114.
    split; [lia |]. split; [split; [exact TBC | exact TB0] |].
    split; [lia |]. split; [exact KB8 |].
    split; [lia |]. split; [exact DT5 |].
    split; [unfold disj; lia |].
    split; [exact (relro_at E mC ENV MU5') |].
    split; [unfold disj in DJR |- *; lia |].
    split; [lia |]. split; [lia |]. split; [lia |].
    split; [assumption |]. split; [assumption | lia]. }
  fix_ret.
  rewrite U416 in ST6.
  clear KB8 DT5 TBC.
  tr MU6 WM6 F0. tr MU6 WM6 F8. tr MU6 WM6 K1. tr MU6 WM6 KB16. tr MU6 WM6 K3.
  tr MU6 WM6 FIN2. tr MU6 WM6 FTX2.
  tr MU6 WM6 FPD. tr MU6 WM6 FP9. tr MU6 WM6 FSV.
  assert (MU6' : munch [(bv_unsigned (c_sp E) - 640, bv_unsigned (c_sp E))] (c_m E) mO)
    by (apply (munch_trans _ _ _ _ MU5'); refine (munch_weaken _ _ _ _ _ MU6);
        intros x Hx; cbn [outside] in Hx |- *; destruct Hx as [Hx _]; repeat split; lia).
  pose proof (wmono_trans rsegs _ _ _ WM5' WM6) as WM6'.
  clear MU5' WM5' MU6 WM6.
  pose proof (oct_rc (zb tb)) as RC.
  revert PO. destruct (owed_counter_text_spec (zb tb)) as [[rc sg] d] eqn:OCS. intros PO.
  cbn [fst] in RC.
  destruct PO as (-> & P0 & P1).
  rewrite U344, U114 in P0. rewrite U344, U114 in P1.
  destruct RC as [R0 | R1]; subst rc.
  - (* code 0: 0x139ec-0x139f8, kind = COUNTER, k.b = dots, run()'s COUNTER arm *)
    destruct (P0 eq_refl) as [KB6 DT6]. clear P0 P1.
    destruct (owed_counter_ok (zb tb) 0 sg d OCS eq_refl) as (LSG & FSG & DR).
    step. dec_closed.
    zstep. zstep. zstep. zstep.
    rewrite (b8_val d) in K1 by lia.
    pose proof (cb_8_16 _ _ _ _ KB6 KB16) as KB.
    pose proof (krec_join _ _ (kt 10 i d (bz sg ++ repeat (b8 0xa5) 16)) K1 KB K3) as KF.
    pose proof (rec_wf_k10 i (zb tb) sg d Hi OCS) as WFK.
    pose proof (RUN _ WFK) as RK. unfold rec_ok in RK.
    change (pc_run (k_kind (kt 10 i d (bz sg ++ repeat (b8 0xa5) 16)))) with 0x143e4 in RK.
    eapply RK with (cur := Z_to_bv 64 (bv_unsigned (c_p E) + c + Z.of_nat (text_used dd)))
                   (rem := Z_to_bv 64 (Z.of_nat (length dd - text_used dd)))
                   (c := c + Z.of_nat (text_used dd)) (u0 := u0) (pj := pj) (tj := tb)
                   (plj := b8 d :: pl9).
    + exact WFK.
    + exact HN.
    + exact HOPS.
    + rewrite unsigned_lit by lia. lia.
    + lia.
    + rewrite unsigned_lit by lia. lia.
    + unfold fr. exact (conj (kcall_cells_size _) (conj F0 (conj F8 (conj KF (conj FIN2 (conj FPD
                         (conj FTX2 (conj (cb10_join _ _ _ _ DT6 FP9) FSV)))))))).
    + assumption.
    + assumption.
    + assumption.
    + assumption.
  - (* E_RANGE: 0x139e8, continue to the latch *)
    destruct (P1 ltac:(unfold E_RANGE; lia)) as (sg' & dv & KB6 & DT6). clear P0 P1.
    step. dec_closed.
    zstep.
    pose proof (cb_8_16 _ _ _ _ KB6 KB16) as KB.
    pose proof (krec_join _ _ (kt 13 i 0 (sg' ++ repeat (b8 0xa5) 16)) K1 KB K3) as KF.
    unfold latch_ok in LATCH.
    eapply LATCH with (kc := kcall_cells (kt 13 i 0 (sg' ++ repeat (b8 0xa5) 16)))
                      (cur := Z_to_bv 64 (bv_unsigned (c_p E) + c + Z.of_nat (text_used dd)))
                      (rem := Z_to_bv 64 (Z.of_nat (length dd - text_used dd)))
                      (c := c + Z.of_nat (text_used dd)) (u0 := u0) (pj := pj) (tj := tb)
                      (plj := dv :: pl9).
    + exact HN.
    + exact HOPS.
    + rewrite unsigned_lit by lia. lia.
    + lia.
    + rewrite unsigned_lit by lia. lia.
    + unfold fr. exact (conj (kcall_cells_size _) (conj F0 (conj F8 (conj KF (conj FIN2 (conj FPD
                         (conj FTX2 (conj (cb10_join _ _ _ _ DT6 FP9) FSV)))))))).
    + assumption.
    + assumption.
    + assumption.
    + assumption.
Qed.

(** ---- 0x13994-0x139ac: a NULL k.p takes the personality and desk of index 1 ---- *)

Lemma codec_main_rd13 : seg_rd13_stmt.
Proof.
  unfold seg_rd13_stmt.
  intros E n ENV PERSOF CTA CSG CTC OCT RUN LATCH i Hi0.
  pose proof (rd13_body E n ENV CTA CSG CTC OCT RUN LATCH) as K. unfold st12 in K.
  unfold rd_ok.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' cur rem u0 pj tj plj c ops m1
         _ HN HOPS HCUR HC1 HCN FR ST MU WM HMI.
  change (pc_rd 13) with 0x13994.
  assert (i = 0 \/ i = 1 \/ i = 2) as [-> | [-> | ->]] by lia.
  - pose proof ENV as (_ & _ & _ & HLO & _).
    pose proof (bv_unsigned_in_range 64 (c_sp E)) as Rsp. unfold bv_modulus in Rsp.
    change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
    pose proof ST as (Hlo0 & _).
    unfold fr in FR. destruct FR as (_ & F0 & F8 & FK & FIN & FPD & FTX & FPL & FSV).
    unfold kcall_cells, k_head in FK.
    cbn [k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc k_before k_out k_want_rc k_want
         k_want_len k_want_key k_want_display] in FK.
    (* 0x13994 bnez s5 (k.p = pers_of 0 = NULL) falls through *)
    step. dec_closed.
    (* 0x13998-0x1399c: diginet_personality_of(DIGINET_DESK_CONTROL24) *)
    zstep. zstep.
    eapply evt_cut; [ apply PERSOF | ]. intros ms' [a1p ->]. fix_ret.
    match goal with |- context [pers_of ?x] => replace (pers_of x) with (pers_of 1) by reflexivity end.
    (* 0x139a0-0x139ac: k.desk = &SPEC_C24, k.p = the personality *)
    zstep. zstep. zstep. zstep.
    eapply K with (i := 1) (c := c).
    all: first [ eassumption | lia
               | (unfold fr; exact (conj (kcall_cells_size _) (conj F0 (conj F8 (conj FK (conj FIN (conj FPD
                                      (conj FTX (conj FPL FSV)))))))))].
  - step. dec_closed.
    eapply K with (i := 1) (c := c).
    all: first [ eassumption | lia ].
  - step. dec_closed.
    eapply K with (i := 2) (c := c).
    all: first [ eassumption | lia ].
Qed.
