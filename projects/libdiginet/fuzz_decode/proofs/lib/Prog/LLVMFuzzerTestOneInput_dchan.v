(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: dchan_stmt of LLVMFuzzerTestOneInput_seg.v, the inlined spec_event_of of a
   channel message in LLVMFuzzerTestOneInput (plain image, 0x133d0 .. 0x13180), and the fader's LSB lookahead.
   The paths: kind OTHER first (0x133d8); status & 0xf0 = 0x90 a note (0x133ec) -- a zone key (0x1340c) or a
   touch / strip button (0x135b8); 0xb0 a control change (0x1341c) -- d1 < 0x20 a fader (value = d2 << 3) whose
   LSB the lookahead 0x13434-0x13484 / 0x13614-0x13674 reads (value |= lsb.d2 >> 4 & 7, o.next, o.status_out)
   or leaves owed (lsb_missing = 1, 0x13484), d1 = 0x5c a jog (0x135d8), 0x40 <= d1 < 0x58 a V-Pot (0x135fc),
   else OTHER; any other family OTHER. The lookahead is the third inlining of spec_msg_step: its tests, and its
   own data-byte loop 0x1361c-0x1362c, are matched to DgnSpec.spec_msg_step of (o.next, o.status_out). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib DgnDecHarness.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import memset_c memcpy_c DgnLayout.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import LLVMFuzzerTestOneInput_seg.
Import ListNotations.
Open Scope Z_scope.

(* ---- bytes and words ---- *)

Lemma dchan_le1 : forall z, le1 (Z_to_bv 64 z) = [b8 z].
Proof.
  intros z. unfold le1. cbn [Z_to_le_bytes]. f_equal. rewrite unsigned_lit_wrap.
  apply (b8_mod_w z 64). lia.
Qed.

Lemma dchan_byte_all : forall P : Z -> bool, forallb P (zseq 256) = true -> forall x, 0 <= x < 256 -> P x = true.
Proof.
  intros P H x Hx. rewrite forallb_forall in H. apply H. unfold zseq. apply in_map_iff.
  exists (Z.to_nat x). split; [lia|]. apply in_seq. lia.
Qed.

Ltac dchan_brute :=
  lazymatch goal with
  | |- forall x, _ -> @eq Z (@?l x) (@?r x) =>
      let H := fresh in
      assert (H : forallb (fun x => Z.eqb (l x) (r x)) (zseq 256) = true) by (vm_compute; reflexivity);
      let y := fresh "x" in let Hy := fresh "Hx" in
      intros y Hy; apply Z.eqb_eq; exact (dchan_byte_all _ H y Hy)
  | |- forall x, _ -> @eq bool (@?l x) (@?r x) =>
      let H := fresh in
      assert (H : forallb (fun x => Bool.eqb (l x) (r x)) (zseq 256) = true) by (vm_compute; reflexivity);
      let y := fresh "x" in let Hy := fresh "Hx" in
      intros y Hy; apply Bool.eqb_prop; exact (dchan_byte_all _ H y Hy)
  end.

Lemma dchan_onb : forall x, 0 <= x < 256 -> Z.shiftr (Z.shiftl x 57 mod 2 ^ 64) 63 = Z.land (Z.shiftr x 6) 1.
Proof. dchan_brute. Qed.

Lemma dchan_b456 : forall x, 0 <= x < 256 -> Z.shiftr (Z.shiftl x 57 mod 2 ^ 64) 61 = Z.land (Z.shiftr x 4) 7.
Proof. dchan_brute. Qed.

Lemma dchan_n1 : forall x, 0 <= x < 256 ->
  ((Z.land x 240 =? 192) || (Z.land x 240 =? 208)) = (Z.land x 224 =? 192).
Proof. dchan_brute. Qed.

Lemma dchan_sh7 : forall x, 0 <= x < 256 -> Z.shiftr x 7 = (if 128 <=? x then 1 else 0).
Proof. dchan_brute. Qed.

Lemma dchan_sl56 : forall x, 0 <= x < 256 -> (2 ^ 63 <=? Z.shiftl x 56 mod 2 ^ 64) = (128 <=? x).
Proof. dchan_brute. Qed.

Lemma dchan_tid : forall x, 0 <= x < 256 ->
  (5 <? (Z.land x 63 + -24) mod 2 ^ 64) = negb ((24 <=? Z.land x 63) && (Z.land x 63 <=? 29)).
Proof. dchan_brute. Qed.

Lemma dchan_vpot : forall x, 0 <= x < 256 ->
  (23 <? Z.land ((x + -64) mod 2 ^ 64) 255) = negb ((64 <=? x) && (x <? 64 + SPEC_VPOTS)).
Proof. dchan_brute. Qed.

Lemma dchan_sx_aux : forall u, 0 <= u < 256 -> (2 ^ 63 <=? ((u + 128) mod 256 - 128) mod 2 ^ 64) = (128 <=? u).
Proof. dchan_brute. Qed.

Lemma dchan_tid_ltu : forall x, 0 <= x < 256 ->
  bv_ltu (Z_to_bv 64 5) (Z_to_bv 64 (Z.land x 63 + -24)) =
  negb ((SPEC_ZONE_FIRST <=? Z.land x 63) && (Z.land x 63 <=? SPEC_ZONE_LAST)).
Proof.
  intros x Hx. unfold bv_ltu. rewrite !unsigned_lit_wrap. change (5 mod 2 ^ 64) with 5. apply dchan_tid. exact Hx.
Qed.

Lemma dchan_seqz : forall x, 0 <= x < 256 ->
  Z.lxor (if (x + -9) mod 2 ^ 64 <? 1 then 1 else 0) 3 = (if x =? SPEC_BTN_TOUCH then SPEC_EV_TOUCH else SPEC_EV_STRIP_BUTTON).
Proof. dchan_brute. Qed.

Lemma dchan_kind : forall x, 0 <= x < 256 ->
  Z.lxor (bv_unsigned (v_sltiu (Z_to_bv 64 (x + -9)) 1)) 3 =
  (if x =? SPEC_BTN_TOUCH then SPEC_EV_TOUCH else SPEC_EV_STRIP_BUTTON).
Proof.
  intros x Hx. rewrite <- (dchan_seqz x Hx). f_equal. unfold v_sltiu. rewrite unsigned_lit_wrap.
  change (bv_wrap 64 1) with 1. destruct (_ <? 1); reflexivity.
Qed.

Lemma dchan_vpot_ltu : forall x, 0 <= x < 256 ->
  bv_ltu (Z_to_bv 64 23) (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (x + -64))) 255)) =
  negb ((64 <=? x) && (x <? 64 + SPEC_VPOTS)).
Proof.
  intros x Hx. unfold bv_ltu. rewrite (unsigned_lit_wrap (x + -64)).
  rewrite (unsigned_lit (Z.land ((x + -64) mod 2 ^ 64) 255))
    by (apply Z_land_range; [apply Z.mod_pos_bound; lia | lia]).
  rewrite (unsigned_lit 23) by lia. apply dchan_vpot. exact Hx.
Qed.

Lemma dchan_all2 : forall P : Z -> Z -> bool,
  forallb (fun x => forallb (P x) (zseq 8)) (zseq 128) = true ->
  forall x y, 0 <= x < 128 -> 0 <= y < 8 -> P x y = true.
Proof.
  intros P H x y Hx Hy. rewrite forallb_forall in H.
  assert (Ix : In x (zseq 128)) by (unfold zseq; apply in_map_iff; exists (Z.to_nat x); split; [lia | apply in_seq; lia]).
  specialize (H x Ix). rewrite forallb_forall in H. apply H.
  unfold zseq; apply in_map_iff; exists (Z.to_nat y); split; [lia | apply in_seq; lia].
Qed.

Lemma dchan_val : forall d t, 0 <= d < 128 -> 0 <= t < 8 ->
  Z.lor (u16 (Z.shiftl d 3)) t = u16 (Z.lor (u16 (Z.shiftl d 3)) (u16 t)).
Proof.
  intros d t Hd Ht. apply Z.eqb_eq.
  exact (dchan_all2 (fun d t => Z.lor (u16 (Z.shiftl d 3)) t =? u16 (Z.lor (u16 (Z.shiftl d 3)) (u16 t)))
           ltac:(vm_compute; reflexivity) d t Hd Ht).
Qed.

Lemma dchan_v : forall x, 0 <= x < 128 -> u16 (Z.shiftl x 3) = 8 * x.
Proof.
  intros x Hx. unfold u16. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. rewrite Z.mod_small; lia.
Qed.

Lemma dchan_sl3 : forall x, 0 <= x < 256 -> Z.shiftl x 3 = u16 (Z.shiftl x 3).
Proof. dchan_brute. Qed.

Lemma dchan_t : forall x, 0 <= x < 256 -> (0 <=? Z.land (Z.shiftr x 4) 7) && (Z.land (Z.shiftr x 4) 7 <? 8) = true.
Proof. dchan_brute. Qed.

Lemma dchan_or32 : forall x, 0 <= x < 32 -> Z.lor x 32 = 32 + x.
Proof.
  intros x Hx. assert (H : forallb (fun x => implb (x <? 32) (Z.lor x 32 =? 32 + x)) (zseq 256) = true)
    by (vm_compute; reflexivity).
  pose proof (dchan_byte_all _ H x ltac:(lia)) as E. cbv beta in E.
  rewrite (proj2 (Z.ltb_lt x 32) ltac:(lia)) in E. cbn [implb] in E. apply Z.eqb_eq. exact E.
Qed.

Lemma dchan_snez : forall z, -2 ^ 64 < z < 2 ^ 64 ->
  v_sltu (Z_to_bv 64 0) (Z_to_bv 64 z) = Z_to_bv 64 (if z =? 0 then 0 else 1).
Proof.
  intros z Hz. unfold v_sltu, c_ltu, bv_ltu. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec z 0) as [->|Hne]; [reflexivity|].
  replace (0 mod 2 ^ 64 <? z mod 2 ^ 64) with true; [reflexivity|].
  symmetry. apply Z.ltb_lt. change (0 mod 2 ^ 64) with 0.
  destruct (Z_lt_le_dec z 0).
  - rewrite <- (Z.mod_add z 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
  - rewrite Z.mod_small by lia. lia.
Qed.

Lemma dchan_sl56_lts : forall x, 0 <= x < 256 -> bv_lts (Z_to_bv 64 (Z.shiftl x 56)) (Z_to_bv 64 0) = (128 <=? x).
Proof. intros x Hx. rewrite bv_lts_zero_r, unsigned_lit_wrap. apply dchan_sl56. exact Hx. Qed.

Lemma dchan_n1_fam : forall x, 0 <= x < 256 -> Z.land x 224 = 192 -> Z.land x 240 <> 176.
Proof.
  intros x Hx H. assert (E : forallb (fun x => implb (Z.land x 224 =? 192) (negb (Z.land x 240 =? 176))) (zseq 256) = true)
    by (vm_compute; reflexivity).
  pose proof (dchan_byte_all _ E x Hx) as E2. cbv beta in E2.
  rewrite (proj2 (Z.eqb_eq _ 192) H) in E2. cbn [implb] in E2.
  apply Bool.negb_true_iff, Z.eqb_neq in E2. exact E2.
Qed.

Lemma dchan_t_rng : forall y, 0 <= Z.land y 7 < 8.
Proof.
  intros y. replace 7 with (2 ^ 3 - 1) by reflexivity. rewrite (zb_land_mask y 3 ltac:(lia)).
  apply Z.mod_pos_bound. lia.
Qed.

(* ---- the body bytes ---- *)

Lemma dchan_nth_bz : forall bb n, nth n (map bz bb) 0 = bz (nth n bb (Z_to_bv 8 0)).
Proof. induction bb as [|x bb IH]; intros [|n]; cbn; try reflexivity. apply IH. Qed.

Lemma dchan_bz : forall bb i, 0 <= byte_at (bzl bb) i < 256.
Proof. intros bb i. unfold byte_at, bzl. rewrite dchan_nth_bz. pose proof (bz_range (nth (Z.to_nat i) bb (Z_to_bv 8 0))). lia. Qed.

Lemma dchan_zxb : forall bb i, zxb (nth (Z.to_nat i) bb (Z_to_bv 8 0)) = Z_to_bv 64 (byte_at (bzl bb) i).
Proof. intros bb i. unfold zxb, byte_at, bzl. rewrite dchan_nth_bz. reflexivity. Qed.

Lemma dchan_sxb : forall bb i, bv_lts (sxb (nth (Z.to_nat i) bb (Z_to_bv 8 0))) (Z_to_bv 64 0) = (128 <=? byte_at (bzl bb) i).
Proof.
  intros bb i. unfold sxb. rewrite bv_lts_zero_r, unsigned_lit_wrap. unfold byte_at, bzl. rewrite dchan_nth_bz.
  set (b := nth (Z.to_nat i) bb (Z_to_bv 8 0)). pose proof (bz_range b) as R. unfold bz in *.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 8) with 256. change (256 / 2) with 128.
  apply dchan_sx_aux. lia.
Qed.

Lemma dchan_rd_nat : forall m a bs i, bytes_at rsegs m a bs -> (i < length bs)%nat ->
  ov_read_bytes rsegs m (Z_to_bv 64 (a + Z.of_nat i)) 1 = Some [nth i bs (Z_to_bv 8 0)].
Proof.
  intros m a bs i H Hi.
  change (Z_to_bv 64 (a + Z.of_nat i)) with (wa (a + Z.of_nat i)).
  rewrite (bytes_at_ov_read rsegs m a bs i 1 H ltac:(lia)).
  f_equal. clear H. revert i Hi. induction bs as [|x bs IH]; intros [|i] Hi; cbn [length] in Hi.
  - lia.
  - lia.
  - reflexivity.
  - cbn [skipn nth]. apply IH. lia.
Qed.

Lemma dchan_rd : forall m body bb i, bytes_at rsegs m body bb -> 0 <= i < Z.of_nat (length bb) ->
  ov_read_bytes rsegs m (Z_to_bv 64 (body + i)) 1 = Some [nth (Z.to_nat i) bb (Z_to_bv 8 0)].
Proof.
  intros m body bb i H Hi. pose proof (dchan_rd_nat m body bb (Z.to_nat i) H ltac:(lia)) as R.
  rewrite Z2Nat.id in R by lia. exact R.
Qed.

(* ---- the model: a channel message ---- *)

Lemma dchan_M : forall b len pos status,
  (forall i, 0 <= byte_at b i < 256) -> 0 <= status < 256 ->
  sm_code (spec_msg_step b len pos status) = 1 ->
  (sm_status (spec_msg_step b len pos status) =? 240) = false ->
  0 <= sm_status (spec_msg_step b len pos status) < 256 /\
  0 <= sm_d1 (spec_msg_step b len pos status) < 128 /\
  0 <= sm_d2 (spec_msg_step b len pos status) < 128 /\
  pos < sm_next (spec_msg_step b len pos status) <= len /\
  sm_status_out (spec_msg_step b len pos status) = sm_status (spec_msg_step b len pos status).
Proof.
  intros b len pos status Hb Hs Hc H240. unfold spec_msg_step in *. cbv zeta in *.
  unfold SPEC_E_TRUNCATED, SPEC_E_STATUS, SPEC_E_NO_STATUS in *.
  repeat (match type of Hc with context [if ?c then _ else _] => let E := fresh "E" in destruct c eqn:E end;
          cbn [sm_code sm_status] in Hc, H240; try discriminate).
  cbn [sm_status sm_d1 sm_d2 sm_next sm_status_out].
  pose proof (Hb pos). pose proof (Hb (pos + 1)). pose proof (Hb (pos + 1 + 1)).
  repeat match goal with |- context [if ?c then _ else _] => let E := fresh "E" in destruct c eqn:E end;
  cbn [Z.eqb Pos.eqb andb orb] in *;
  repeat match goal with
  | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
  | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
  | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
  | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
  end;
  repeat split; lia.
Qed.

(* ---- the walk ---- *)

Ltac usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end.
Ltac solve_c := unfold bv_eqb, bv_ltu, bv_leu, bv_lts; cbn [negb]; usub; fold_lit_ux; solve_cond_rec.
Ltac take b := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; solve_c]
  end.
Ltac take_by b tac := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; tac]
  end.
Ltac sbstep := step; rewrite ?dchan_le1; mem_after_store_opt.

Ltac dch_cells H :=
  unfold fr_head, owed_cells, owed0, spec_msg_cells, spec_event_cells, arr_cells, se_zero in H;
  cbn [app map seq nth repeat ow_m ow_e ow_lsb_missing ow_next ow_status_out se_kind se_strip se_button
       se_zone se_on se_right se_addr se_device se_len se_dots se_value se_mask se_delta se_segments se_text
       se_seg] in H.

Ltac dch_close K :=
  unfold dend in K; eapply K; [eassumption | eassumption | eassumption | eassumption | ];
  unfold fr_head, owed_cells, spec_msg_cells, spec_event_cells, arr_cells, se_other, se_with_value;
  cbn [app map seq nth repeat ow_m ow_e ow_lsb_missing ow_next ow_status_out se_kind se_strip se_button
       se_zone se_on se_right se_addr se_device se_len se_dots se_value se_mask se_delta se_segments se_text
       se_seg].

(* the state at the hand-off pc 0x133d0 *)
Definition dch_pre (Q : machine_state -> Prop)
    (r1 x3 x4 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 x22 r28 r29 r30 r31 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (Sp body pos : Z) (bb : list byte) (M : spec_msg) : Prop :=
  evt rsegs Q
    (MS (mkR r1 (Z_to_bv 64 Sp) x3 x4 r5 r6 r7 (Z_to_bv 64 pos) (Z_to_bv 64 (sm_status M))
           r10 r11 r12 r13 r14 r15 r16 r17
           (Z_to_bv 64 (Z.of_nat (length bb))) (Z_to_bv 64 (Sp + 88)) (Z_to_bv 64 (sm_next M))
           (Z_to_bv 64 body) x22 (Z_to_bv 64 (sm_d2 M)) (Z_to_bv 64 (- Z.of_nat (length bb)))
           (Z_to_bv 64 (sm_d1 M)) (Z_to_bv 64 247) (Z_to_bv 64 1) r28 r29 r30 r31)
        F (Z_to_bv 64 0x133d0) fc None m (seg_rom rsegs)).

(* what the walk knows about a channel message M *)
Definition dch_ok (Sp body : Z) (bb : list byte) (M : spec_msg) : Prop :=
  seg_ok Sp body bb /\ 0 <= sm_status M < 256 /\ 0 <= sm_d1 M < 128 /\ 0 <= sm_d2 M < 128 /\
  0 <= sm_next M <= Z.of_nat (length bb) /\ sm_status_out M = sm_status M.

(* status & 0xf0 is neither 0x90 nor 0xb0: kind OTHER (0x133e8) *)
Lemma dchan_other :
  forall (r1 x3 x4 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 x22 r28 r29 r30 r31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (Sp body pos : Z) (bb j0 oj : list byte) (w10 : word) (rest : list cell)
    (Q : machine_state -> Prop) (M : spec_msg),
  dch_ok Sp body bb M -> (sm_status M =? 240) = false ->
  Z.land (sm_status M) 240 <> 176 -> Z.land (sm_status M) 240 <> 144 ->
  bytes_at rsegs m body bb ->
  rw_cells rsegs m Sp (fr_head j0 (Z_to_bv 64 0x103a4) w10 body ++ owed_cells (ow_p1 oj) (ow_p2 oj) (owed0 M) ++ rest) ->
  mem_inv rsegs m ->
  dend Q x3 x4 x22 F fc m Sp body bb j0 oj w10 rest
    (Owed M (spec_event_of (bzl bb) M) 0 (sm_next M) (sm_status_out M)) ->
  dch_pre Q r1 x3 x4 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 x22 r28 r29 r30 r31 F fc m Sp body pos bb M.
Proof.
  intros r1 x3 x4 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 x22 r28 r29 r30 r31 F fc m Sp body pos bb j0 oj w10
    rest Q M [[H0 [H1 [H2 [H3 H4]]]] [Hst [Hd1 [Hd2 [Hnx Hso]]]]] H240 Hf1 Hf2 HB HC MI K.
  unfold spec_event_of in K. cbv zeta in K.
  rewrite (proj2 (Z.eqb_neq _ 144) Hf2), (proj2 (Z.eqb_neq _ 176) Hf1), H240 in K. cbv iota in K.
  unfold dch_pre. dch_cells HC.
  pose proof (munch_refl [(Sp + 32, Sp + 152)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (Z_land_range (sm_status M) 240 ltac:(lia) ltac:(lia)) as Hfam.
  do 5 step. take false. step. step. take true.
  dch_close K. exact HC.
Qed.

(* status & 0xf0 = 0x90, a note (0x133ec): zone key (0x1340c), touch or strip button (0x135b8) *)
Lemma dchan_note :
  forall (r1 x3 x4 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 x22 r28 r29 r30 r31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (Sp body pos : Z) (bb j0 oj : list byte) (w10 : word) (rest : list cell)
    (Q : machine_state -> Prop) (M : spec_msg),
  dch_ok Sp body bb M ->
  Z.land (sm_status M) 240 = 144 ->
  bytes_at rsegs m body bb ->
  rw_cells rsegs m Sp (fr_head j0 (Z_to_bv 64 0x103a4) w10 body ++ owed_cells (ow_p1 oj) (ow_p2 oj) (owed0 M) ++ rest) ->
  mem_inv rsegs m ->
  dend Q x3 x4 x22 F fc m Sp body bb j0 oj w10 rest
    (Owed M (spec_event_of (bzl bb) M) 0 (sm_next M) (sm_status_out M)) ->
  dch_pre Q r1 x3 x4 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 x22 r28 r29 r30 r31 F fc m Sp body pos bb M.
Proof.
  intros r1 x3 x4 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 x22 r28 r29 r30 r31 F fc m Sp body pos bb j0 oj w10
    rest Q M [[H0 [H1 [H2 [H3 H4]]]] [Hst [Hd1 [Hd2 [Hnx Hso]]]]] Hf HB HC MI K.
  unfold spec_event_of in K. cbv zeta in K.
  rewrite Hf in K. cbv iota in K. cbn [Z.eqb Pos.eqb] in K.
  unfold dch_pre. dch_cells HC.
  pose proof (munch_refl [(Sp + 32, Sp + 152)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (Z_land_range (sm_status M) 240 ltac:(lia) ltac:(lia)) as Hfam.
  pose proof (Z_land_range (sm_d2 M) 63 ltac:(lia) ltac:(lia)) as Htid.
  do 5 step. take false. step. step. take false.
  step. usub. step. usub. step. usub.
  rewrite (unsigned_lit_wrap (Z.shiftl (sm_d2 M) 57)), (dchan_onb (sm_d2 M)) by lia.
  step. usub. sbstep. sbstep. step. step.
  destruct ((SPEC_ZONE_FIRST <=? Z.land (sm_d2 M) 63) && (Z.land (sm_d2 M) 63 <=? SPEC_ZONE_LAST)) eqn:Hz;
    cbv iota in K.
  - take_by false ltac:(rewrite dchan_tid_ltu by lia; rewrite Hz; reflexivity).
    step. step. sbstep. step.
    dch_close K. exact HC.
  - take_by true ltac:(rewrite dchan_tid_ltu by lia; rewrite Hz; reflexivity).
    step. usub. step. step.
    rewrite (dchan_kind (sm_d1 M)) by lia.
    step. sbstep. step.
    dch_close K. exact HC.
Qed.

(* status & 0xf0 = 0xb0 and d1 >= 0x20 (0x135d0): jog (0x135d8), V-Pot (0x135fc) or OTHER *)
Lemma dchan_cc_hi :
  forall (r1 x3 x4 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 x22 r28 r29 r30 r31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (Sp body pos : Z) (bb j0 oj : list byte) (w10 : word) (rest : list cell)
    (Q : machine_state -> Prop) (M : spec_msg),
  dch_ok Sp body bb M ->
  Z.land (sm_status M) 240 = 176 -> 32 <= sm_d1 M ->
  bytes_at rsegs m body bb ->
  rw_cells rsegs m Sp (fr_head j0 (Z_to_bv 64 0x103a4) w10 body ++ owed_cells (ow_p1 oj) (ow_p2 oj) (owed0 M) ++ rest) ->
  mem_inv rsegs m ->
  dend Q x3 x4 x22 F fc m Sp body bb j0 oj w10 rest
    (Owed M (spec_event_of (bzl bb) M) 0 (sm_next M) (sm_status_out M)) ->
  dch_pre Q r1 x3 x4 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 x22 r28 r29 r30 r31 F fc m Sp body pos bb M.
Proof.
  intros r1 x3 x4 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 x22 r28 r29 r30 r31 F fc m Sp body pos bb j0 oj w10
    rest Q M [[H0 [H1 [H2 [H3 H4]]]] [Hst [Hd1 [Hd2 [Hnx Hso]]]]] Hf H32 HB HC MI K.
  unfold spec_event_of in K. cbv zeta in K.
  rewrite Hf in K. cbn [Z.eqb Pos.eqb] in K.
  rewrite (proj2 (Z.ltb_ge (sm_d1 M) 32) H32) in K. cbv iota in K.
  unfold dch_pre. dch_cells HC.
  pose proof (munch_refl [(Sp + 32, Sp + 152)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (Z_land_range (sm_status M) 240 ltac:(lia) ltac:(lia)) as Hfam.
  do 5 step. take true. step. step. take true. step. step.
  destruct (sm_d1 M =? SPEC_JOG_CC) eqn:Hj; cbv iota in K.
  - apply Z.eqb_eq in Hj. unfold SPEC_JOG_CC in Hj.
    take false. step. usub. step. step. step. step.
    dch_close K.
    replace (s16 (sm_d2 M - 64)) with (sm_d2 M + -64) by (unfold s16; rewrite Z.mod_small by lia; lia).
    exact HC.
  - apply Z.eqb_neq in Hj. unfold SPEC_JOG_CC in Hj.
    take true. step. usub. step. step. step.
    destruct ((64 <=? sm_d1 M) && (sm_d1 M <? 64 + SPEC_VPOTS)) eqn:Hv; cbv iota in K.
    + take_by false ltac:(rewrite dchan_vpot_ltu by lia; rewrite Hv; reflexivity).
      apply andb_true_iff in Hv. destruct Hv as [Hv1 Hv2]. apply Z.leb_le in Hv1. apply Z.ltb_lt in Hv2.
      unfold SPEC_VPOTS in Hv2.
      step. usub. step. step. sbstep. step. step.
      dch_close K.
      replace (s16 (sm_d2 M - 64)) with (sm_d2 M + -64) by (unfold s16; rewrite Z.mod_small by lia; lia).
      replace (u8 (sm_d1 M - 64)) with (sm_d1 M + -64) by (unfold u8; rewrite Z.mod_small by lia; lia).
      exact HC.
    + take_by true ltac:(rewrite dchan_vpot_ltu by lia; rewrite Hv; reflexivity).
      dch_close K. exact HC.
Qed.

(* ---- the model: the fader's LSB step ---- *)

Lemma dchan_mstep : forall b len nx st s2 data n,
  0 < st -> 0 <= nx < len -> byte_at b nx < 240 ->
  ((128 <= byte_at b nx /\ s2 = byte_at b nx /\ data = nx + 1) \/ (byte_at b nx < 128 /\ s2 = st /\ data = nx)) ->
  n = (if (Z.land s2 240 =? 192) || (Z.land s2 240 =? 208) then 1 else 2) ->
  spec_msg_step b len nx st =
    if len <? data + n then
      {| sm_code := SPEC_E_TRUNCATED; sm_at := nx; sm_len := 0; sm_next := len; sm_status := 0; sm_running := 0;
         sm_d1 := 0; sm_d2 := 0; sm_status_out := st; sm_sysex_at := 0; sm_sysex_len := 0 |}
    else if 128 <=? byte_at b data then
      {| sm_code := SPEC_E_TRUNCATED; sm_at := nx; sm_len := 0; sm_next := data; sm_status := 0; sm_running := 0;
         sm_d1 := 0; sm_d2 := 0; sm_status_out := 0; sm_sysex_at := 0; sm_sysex_len := 0 |}
    else if (n =? 2) && (128 <=? byte_at b (data + 1)) then
      {| sm_code := SPEC_E_TRUNCATED; sm_at := nx; sm_len := 0; sm_next := data + 1; sm_status := 0;
         sm_running := 0; sm_d1 := 0; sm_d2 := 0; sm_status_out := 0; sm_sysex_at := 0; sm_sysex_len := 0 |}
    else
      {| sm_code := 1; sm_at := nx; sm_len := data + n - nx; sm_next := data + n; sm_status := s2;
         sm_running := if byte_at b nx <? 128 then 1 else 0; sm_d1 := byte_at b data;
         sm_d2 := if n =? 2 then byte_at b (data + 1) else 0; sm_status_out := s2; sm_sysex_at := 0;
         sm_sysex_len := 0 |}.
Proof.
  intros b len nx st s2 data n Hst Hnx Hl Hc Hn. unfold spec_msg_step. cbv zeta.
  rewrite (proj2 (Z.leb_gt len nx)) by lia.
  rewrite (proj2 (Z.eqb_neq (byte_at b nx) 240)) by lia.
  rewrite (proj2 (Z.ltb_ge 240 (byte_at b nx))) by lia.
  destruct Hc as [[Hl1 [-> ->]] | [Hl1 [-> ->]]].
  - rewrite (proj2 (Z.ltb_ge (byte_at b nx) 128)) by lia. rewrite (proj2 (Z.leb_le 128 (byte_at b nx))) by lia.
    cbn [andb]. subst n. reflexivity.
  - subst n. rewrite (proj2 (Z.ltb_lt (byte_at b nx) 128)) by lia. rewrite (proj2 (Z.eqb_neq st 0)) by lia.
    rewrite (proj2 (Z.leb_gt 128 (byte_at b nx))) by lia. cbn [andb].
    rewrite (proj2 (Z.leb_gt 128 (byte_at b nx))) by lia. cbn [andb]. reflexivity.
Qed.

(* the fader event before its LSB (spec.h:414-418) *)
Definition dch_ef (M : spec_msg) : spec_event :=
  {| se_kind := SPEC_EV_FADER; se_strip := sm_d1 M; se_button := 0; se_zone := 0; se_on := 0;
     se_right := 0; se_addr := 0; se_device := 0; se_len := 0; se_dots := 0;
     se_value := u16 (Z.shiftl (sm_d2 M) 3);
     se_mask := 0; se_delta := 0; se_segments := 0; se_text := repeat 0 8;
     se_seg := repeat 0 8 |}.

(* owed_at of a fader message (fuzz_decode.c:140-148) *)
Definition dch_lo (b : list Z) (len : Z) (M : spec_msg) : owed :=
  let lsb := spec_msg_step b len (sm_next M) (sm_status_out M) in
  if (sm_code lsb =? 1) && (Z.land (sm_status lsb) 240 =? 176) && (sm_d1 lsb =? 32 + sm_d1 M) then
    Owed M (se_with_value (dch_ef M) (u16 (Z.lor (u16 (Z.shiftl (sm_d2 M) 3)) (u16 (Z.land (Z.shiftr (sm_d2 lsb) 4) 7)))))
      0 (sm_next lsb) (sm_status_out lsb)
  else Owed M (dch_ef M) 1 (sm_next M) (sm_status_out M).

Ltac dch_unfold_goal :=
  unfold fr_head, owed_cells, spec_msg_cells, spec_event_cells, arr_cells, se_other, se_with_value, dch_ef;
  cbn [app map seq nth repeat ow_m ow_e ow_lsb_missing ow_next ow_status_out se_kind se_strip se_button
       se_zone se_on se_right se_addr se_device se_len se_dots se_value se_mask se_delta se_segments se_text
       se_seg].

Ltac dch_cells_f H :=
  unfold fr_head, owed_cells, spec_msg_cells, spec_event_cells, arr_cells, dch_ef in H;
  cbn [app map seq nth repeat ow_m ow_e ow_lsb_missing ow_next ow_status_out se_kind se_strip se_button
       se_zone se_on se_right se_addr se_device se_len se_dots se_value se_mask se_delta se_segments se_text
       se_seg] in H.

(* no LSB: lsb_missing = 1 (0x13484) *)
Lemma dchan_miss :
  forall (r1 x3 x4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r20 x22 r23 r25 r28 r29 r30 r31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
    (Sp body : Z) (bb j0 oj : list byte) (w10 : word) (rest : list cell)
    (Q : machine_state -> Prop) (M : spec_msg),
  seg_ok Sp body bb -> bytes_at rsegs m body bb ->
  rw_cells rsegs m Sp (fr_head j0 (Z_to_bv 64 0x103a4) w10 body ++
    owed_cells (ow_p1 oj) (ow_p2 oj) (Owed M (dch_ef M) 0 (sm_next M) (sm_status_out M)) ++ rest) ->
  mem_inv rsegs m -> munch [(Sp + 32, Sp + 152)] m0 m -> wmono rsegs m0 m ->
  dend Q x3 x4 x22 F fc m0 Sp body bb j0 oj w10 rest (Owed M (dch_ef M) 1 (sm_next M) (sm_status_out M)) ->
  evt rsegs Q
    (MS (mkR r1 (Z_to_bv 64 Sp) x3 x4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17
           (Z_to_bv 64 (Z.of_nat (length bb))) (Z_to_bv 64 (Sp + 88)) r20 (Z_to_bv 64 body) x22 r23
           (Z_to_bv 64 (- Z.of_nat (length bb))) r25 (Z_to_bv 64 247) (Z_to_bv 64 1) r28 r29 r30 r31)
        F (Z_to_bv 64 0x13484) fc None m (seg_rom rsegs)).
Proof.
  intros r1 x3 x4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r20 x22 r23 r25 r28 r29 r30 r31 F fc m0 m Sp body
    bb j0 oj w10 rest Q M [H0 [H1 [H2 [H3 H4]]]] HB HC MI MU WM K.
  dch_cells_f HC.
  step. step.
  dch_close K. exact HC.
Qed.

Definition dch_test (b : list Z) (len : Z) (M : spec_msg) : bool :=
  let lsb := spec_msg_step b len (sm_next M) (sm_status_out M) in
  (sm_code lsb =? 1) && (Z.land (sm_status lsb) 240 =? 176) && (sm_d1 lsb =? 32 + sm_d1 M).

Lemma dchan_lo_miss : forall b len M, dch_test b len M = false ->
  dch_lo b len M = Owed M (dch_ef M) 1 (sm_next M) (sm_status_out M).
Proof. intros b len M H. unfold dch_lo, dch_test in *. cbv zeta in *. rewrite H. reflexivity. Qed.

Lemma dchan_test_code : forall b len M,
  sm_code (spec_msg_step b len (sm_next M) (sm_status_out M)) <> 1 -> dch_test b len M = false.
Proof. intros b len M H. unfold dch_test. cbv zeta. rewrite (proj2 (Z.eqb_neq _ 1) H). reflexivity. Qed.

Lemma dchan_test_fam : forall b len M,
  Z.land (sm_status (spec_msg_step b len (sm_next M) (sm_status_out M))) 240 <> 176 -> dch_test b len M = false.
Proof.
  intros b len M H. unfold dch_test. cbv zeta. rewrite (proj2 (Z.eqb_neq _ 176) H).
  rewrite andb_false_r. reflexivity.
Qed.

Lemma dchan_test_d1 : forall b len M,
  sm_d1 (spec_msg_step b len (sm_next M) (sm_status_out M)) <> 32 + sm_d1 M -> dch_test b len M = false.
Proof.
  intros b len M H. unfold dch_test. cbv zeta. rewrite (proj2 (Z.eqb_neq _ (32 + sm_d1 M)) H).
  rewrite andb_false_r. reflexivity.
Qed.

(* the step is over, or its lead byte is 0xf0..0xff: no LSB either way *)
Lemma dchan_test_end : forall b len M, len <= sm_next M -> dch_test b len M = false.
Proof.
  intros b len M H. apply dchan_test_code. unfold spec_msg_step. cbv zeta.
  rewrite (proj2 (Z.leb_le len (sm_next M)) H). cbn [sm_code]. lia.
Qed.

Lemma dchan_test_hi : forall b len M, sm_next M < len -> 240 <= byte_at b (sm_next M) -> dch_test b len M = false.
Proof.
  intros b len M Hl Hb. unfold dch_test. cbv zeta. unfold spec_msg_step. cbv zeta.
  rewrite (proj2 (Z.leb_gt len (sm_next M))) by lia.
  destruct (Z.eqb_spec (byte_at b (sm_next M)) 240) as [E|E].
  - destruct (Z.eqb_spec (scan_f7 b len (sm_next M + 1) (Z.to_nat (len - (sm_next M + 1)))) len) as [E2|E2];
      cbn [sm_code sm_status]; [reflexivity|].
    change (Z.land 240 240) with 240. reflexivity.
  - rewrite (proj2 (Z.ltb_lt 240 (byte_at b (sm_next M))) ltac:(lia)). cbn [sm_code]. reflexivity.
Qed.

(* the three truncations of the LSB step *)
Lemma dchan_test_t1 : forall b len M s2v data n,
  0 < sm_status_out M -> 0 <= sm_next M < len -> byte_at b (sm_next M) < 240 ->
  ((128 <= byte_at b (sm_next M) /\ s2v = byte_at b (sm_next M) /\ data = sm_next M + 1) \/
   (byte_at b (sm_next M) < 128 /\ s2v = sm_status_out M /\ data = sm_next M)) ->
  n = (if (Z.land s2v 240 =? 192) || (Z.land s2v 240 =? 208) then 1 else 2) ->
  len < data + n -> dch_test b len M = false.
Proof.
  intros b len M s2v data n H1 H2 H3 H4 H5 H6. apply dchan_test_code.
  rewrite (dchan_mstep b len (sm_next M) (sm_status_out M) s2v data n) by assumption.
  rewrite (proj2 (Z.ltb_lt len (data + n)) H6). cbn [sm_code]. unfold SPEC_E_TRUNCATED. lia.
Qed.

Lemma dchan_test_t2 : forall b len M s2v data n,
  0 < sm_status_out M -> 0 <= sm_next M < len -> byte_at b (sm_next M) < 240 ->
  ((128 <= byte_at b (sm_next M) /\ s2v = byte_at b (sm_next M) /\ data = sm_next M + 1) \/
   (byte_at b (sm_next M) < 128 /\ s2v = sm_status_out M /\ data = sm_next M)) ->
  n = (if (Z.land s2v 240 =? 192) || (Z.land s2v 240 =? 208) then 1 else 2) ->
  data + n <= len -> 128 <= byte_at b data -> dch_test b len M = false.
Proof.
  intros b len M s2v data n H1 H2 H3 H4 H5 H6 H7. apply dchan_test_code.
  rewrite (dchan_mstep b len (sm_next M) (sm_status_out M) s2v data n) by assumption.
  rewrite (proj2 (Z.ltb_ge len (data + n))) by lia.
  rewrite (proj2 (Z.leb_le 128 (byte_at b data)) H7). cbn [sm_code]. unfold SPEC_E_TRUNCATED. lia.
Qed.

Lemma dchan_test_t3 : forall b len M s2v data n,
  0 < sm_status_out M -> 0 <= sm_next M < len -> byte_at b (sm_next M) < 240 ->
  ((128 <= byte_at b (sm_next M) /\ s2v = byte_at b (sm_next M) /\ data = sm_next M + 1) \/
   (byte_at b (sm_next M) < 128 /\ s2v = sm_status_out M /\ data = sm_next M)) ->
  n = (if (Z.land s2v 240 =? 192) || (Z.land s2v 240 =? 208) then 1 else 2) ->
  data + n <= len -> byte_at b data < 128 -> n = 2 -> 128 <= byte_at b (data + 1) ->
  dch_test b len M = false.
Proof.
  intros b len M s2v data n H1 H2 H3 H4 H5 H6 H7 H8 H9. apply dchan_test_code.
  rewrite (dchan_mstep b len (sm_next M) (sm_status_out M) s2v data n) by assumption.
  rewrite (proj2 (Z.ltb_ge len (data + n))) by lia.
  rewrite (proj2 (Z.leb_gt 128 (byte_at b data))) by lia.
  rewrite (proj2 (Z.leb_le 128 (byte_at b (data + 1))) H9), H8. cbn [andb Z.eqb Pos.eqb sm_code].
  unfold SPEC_E_TRUNCATED. lia.
Qed.

(* the LSB step is a message *)
Lemma dchan_step_good : forall b len M s2v data n,
  0 < sm_status_out M -> 0 <= sm_next M < len -> byte_at b (sm_next M) < 240 ->
  ((128 <= byte_at b (sm_next M) /\ s2v = byte_at b (sm_next M) /\ data = sm_next M + 1) \/
   (byte_at b (sm_next M) < 128 /\ s2v = sm_status_out M /\ data = sm_next M)) ->
  n = (if (Z.land s2v 240 =? 192) || (Z.land s2v 240 =? 208) then 1 else 2) ->
  data + n <= len -> byte_at b data < 128 -> (n = 2 -> byte_at b (data + 1) < 128) ->
  spec_msg_step b len (sm_next M) (sm_status_out M) =
    {| sm_code := 1; sm_at := sm_next M; sm_len := data + n - sm_next M; sm_next := data + n;
       sm_status := s2v; sm_running := if byte_at b (sm_next M) <? 128 then 1 else 0;
       sm_d1 := byte_at b data; sm_d2 := if n =? 2 then byte_at b (data + 1) else 0;
       sm_status_out := s2v; sm_sysex_at := 0; sm_sysex_len := 0 |}.
Proof.
  intros b len M s2v data n H1 H2 H3 H4 H5 H6 H7 H8.
  rewrite (dchan_mstep b len (sm_next M) (sm_status_out M) s2v data n) by assumption.
  rewrite (proj2 (Z.ltb_ge len (data + n))) by lia.
  rewrite (proj2 (Z.leb_gt 128 (byte_at b data))) by lia.
  destruct (Z.eqb_spec n 2) as [E|E].
  - pose proof (H8 E) as H8'. rewrite E.
    rewrite (proj2 (Z.leb_gt 128 (byte_at b (data + 1)))) by lia.
    cbn [andb Z.eqb Pos.eqb]. reflexivity.
  - cbn [andb]. reflexivity.
Qed.

Lemma dchan_lo_hit : forall b len M s2v data,
  0 < sm_status_out M -> 0 <= sm_next M < len -> byte_at b (sm_next M) < 240 ->
  ((128 <= byte_at b (sm_next M) /\ s2v = byte_at b (sm_next M) /\ data = sm_next M + 1) \/
   (byte_at b (sm_next M) < 128 /\ s2v = sm_status_out M /\ data = sm_next M)) ->
  2 = (if (Z.land s2v 240 =? 192) || (Z.land s2v 240 =? 208) then 1 else 2) ->
  data + 2 <= len -> byte_at b data < 128 -> byte_at b (data + 1) < 128 ->
  Z.land s2v 240 = 176 -> byte_at b data = 32 + sm_d1 M ->
  dch_lo b len M =
    Owed M (se_with_value (dch_ef M)
              (u16 (Z.lor (u16 (Z.shiftl (sm_d2 M) 3)) (u16 (Z.land (Z.shiftr (byte_at b (data + 1)) 4) 7)))))
      0 (data + 2) s2v.
Proof.
  intros b len M s2v data H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
  unfold dch_lo. cbv zeta.
  rewrite (dchan_step_good b len M s2v data 2 H1 H2 H3 H4 H5 H6 H7 (fun _ => H8)).
  cbn [sm_code sm_status sm_d1 sm_d2 sm_next sm_status_out].
  rewrite H9, H10. cbn [Z.eqb Pos.eqb andb]. rewrite Z.eqb_refl. cbn [andb].
  unfold dch_ef. cbn [se_value]. reflexivity.
Qed.

(* the LSB lookahead from 0x13464 (the lead byte is read, a1 = the LSB step's status) *)
Lemma dchan_lsb_tail :
  forall (r1 x3 x4 r5 r6 r7 r8 r9 r13 r14 r15 r16 r17 x22 r23 r28 r29 r30 r31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
    (Sp body s2v data lead : Z) (bb j0 oj : list byte) (w10 : word) (rest : list cell)
    (Q : machine_state -> Prop) (M : spec_msg),
  seg_ok Sp body bb ->
  0 <= sm_d1 M < 32 -> 0 <= sm_d2 M < 128 -> 0 < sm_status_out M < 256 ->
  0 <= sm_next M < Z.of_nat (length bb) ->
  lead = byte_at (bzl bb) (sm_next M) -> lead < 240 ->
  ((128 <= lead /\ s2v = lead /\ data = sm_next M + 1) \/ (lead < 128 /\ s2v = sm_status_out M /\ data = sm_next M)) ->
  bytes_at rsegs m body bb ->
  rw_cells rsegs m Sp (fr_head j0 (Z_to_bv 64 0x103a4) w10 body ++
    owed_cells (ow_p1 oj) (ow_p2 oj) (Owed M (dch_ef M) 0 (sm_next M) (sm_status_out M)) ++ rest) ->
  mem_inv rsegs m -> munch [(Sp + 32, Sp + 152)] m0 m -> wmono rsegs m0 m ->
  dend Q x3 x4 x22 F fc m0 Sp body bb j0 oj w10 rest (dch_lo (bzl bb) (Z.of_nat (length bb)) M) ->
  evt rsegs Q
    (MS (mkR r1 (Z_to_bv 64 Sp) x3 x4 r5 r6 r7 r8 r9
           (Z_to_bv 64 (u16 (Z.shiftl (sm_d2 M) 3))) (Z_to_bv 64 s2v) (Z_to_bv 64 lead)
           r13 r14 r15 r16 r17
           (Z_to_bv 64 (Z.of_nat (length bb))) (Z_to_bv 64 (Sp + 88)) (Z_to_bv 64 (sm_next M))
           (Z_to_bv 64 body) x22 r23 (Z_to_bv 64 (- Z.of_nat (length bb))) (Z_to_bv 64 (sm_d1 M))
           (Z_to_bv 64 247) (Z_to_bv 64 1) r28 r29 r30 r31)
        F (Z_to_bv 64 0x13464) fc None m (seg_rom rsegs)).
Proof.
  intros r1 x3 x4 r5 r6 r7 r8 r9 r13 r14 r15 r16 r17 x22 r23 r28 r29 r30 r31 F fc m0 m Sp body s2v data lead
    bb j0 oj w10 rest Q M HOK Hd1 Hd2 Hst Hnx Hlead Hhi Hc HB HC MI MU WM K.
  pose proof HOK as [H0 [H1 [H2 [H3 H4]]]].
  pose proof (dchan_bz bb (sm_next M)) as Bnx.
  pose proof (dchan_bz bb data) as Bd.
  pose proof (dchan_bz bb (data + 1)) as Bd1.
  assert (Hs2v : 0 <= s2v < 256) by (destruct Hc as [[?[??]]|[?[??]]]; lia).
  assert (Hdata : sm_next M <= data <= sm_next M + 1) by (destruct Hc as [[?[??]]|[?[??]]]; lia).
  assert (Hsh : Z.shiftr lead 7 = data - sm_next M)
    by (rewrite dchan_sh7 by lia; destruct Hc as [[?[??]]|[?[??]]];
        [rewrite (proj2 (Z.leb_le 128 lead)) by lia | rewrite (proj2 (Z.leb_gt 128 lead)) by lia]; lia).
  pose proof (Z_land_range s2v 224 ltac:(lia) ltac:(lia)) as Hland.
  pose proof (Z_land_range s2v 240 ltac:(lia) ltac:(lia)) as Hland2.
  pose proof (dchan_t_rng (Z.shiftr (byte_at (bzl bb) (data + 1)) 4)) as Htr.
  assert (Hvr : 0 <= u16 (Z.shiftl (sm_d2 M) 3) < 2 ^ 64)
    by (unfold u16; pose proof (Z.mod_pos_bound (Z.shiftl (sm_d2 M) 3) 65536 ltac:(lia)); lia).
  (* 0x13464 srli a2, a2, 7 *)
  step. usub. rewrite Hsh.
  (* 0x13468 andi a4, a1, 0xe0 *)
  step. usub.
  (* 0x1346c add a3, s4, a2 *)
  step. replace (sm_next M + (data - sm_next M)) with data by lia.
  (* 0x13470 addi a2, a4, -0xc0 ; 0x13474 snez a5, a2 *)
  step. step. rewrite (dchan_snez (Z.land s2v 224 + -192)) by lia.
  destruct (Z.eq_dec (Z.land s2v 224) 192) as [H192|H192].
  - (* n = 1: the LSB step wants one data byte, so its family is C0 or D0, never B0 *)
    pose proof (dchan_n1_fam s2v ltac:(lia) H192) as Hnf.
    assert (Hn1 : (1:Z) = if (Z.land s2v 240 =? 192) || (Z.land s2v 240 =? 208) then 1 else 2)
      by (rewrite (dchan_n1 s2v ltac:(lia)), (proj2 (Z.eqb_eq _ 192) H192); reflexivity).
    replace ((Z.land s2v 224 + -192) =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbv iota.
    (* 0x13478 addi a5, a5, 1 ; 0x1347c add a2, a5, a3 ; 0x13480 bgeu s2, a2 *)
    do 3 step.
    destruct (Z_lt_le_dec (Z.of_nat (length bb)) (data + 1)) as [Hlen|Hlen].
    + take false.
      rewrite (dchan_lo_miss (bzl bb) (Z.of_nat (length bb)) M
                 (dchan_test_t1 (bzl bb) (Z.of_nat (length bb)) M s2v data 1 ltac:(lia) ltac:(lia)
                    ltac:(lia) ltac:(subst lead; exact Hc) Hn1 ltac:(lia))) in K.
      eapply dchan_miss; [exact HOK | exact HB | exact HC | exact MI | exact MU | exact WM | exact K].
    + take true.
      (* 0x13614 add a3, s5, a3 ; 0x13618 mv a6, a3 *)
      do 2 step.
      pose proof (dchan_rd m body bb data HB ltac:(lia)) as R0.
      (* 0x1361c lb a7, 0(a6) ; 0x13620 bltz a7 *)
      do 2 step. rewrite (dchan_sxb bb data).
      destruct (Z_lt_le_dec (byte_at (bzl bb) data) 128) as [Hb0|Hb0].
      * take false.
        (* 0x13624 addi a5, a5, -1 ; 0x13628 addi a6, a6, 1 ; 0x1362c bnez a5 *)
        do 3 step. take false.
        (* 0x13630 addi a5, zero, 0xc0 ; 0x13634 bne a4, a5 *)
        do 2 step. take false.
        assert (Hgood : spec_msg_step (bzl bb) (Z.of_nat (length bb)) (sm_next M) (sm_status_out M) =
          {| sm_code := 1; sm_at := sm_next M; sm_len := data + 1 - sm_next M; sm_next := data + 1;
             sm_status := s2v; sm_running := if lead <? 128 then 1 else 0; sm_d1 := byte_at (bzl bb) data;
             sm_d2 := if 1 =? 2 then byte_at (bzl bb) (data + 1) else 0;
             sm_status_out := s2v; sm_sysex_at := 0; sm_sysex_len := 0 |})
          by (subst lead; apply (dchan_step_good (bzl bb) (Z.of_nat (length bb)) M s2v data 1);
              solve [lia | exact Hc | exact Hn1 | intros; lia]).
        (* 0x13638 mv a4, zero ; 0x1363c j ; 0x1364c andi a5, a1, 0xf0 *)
        do 3 step. usub.
        (* 0x13650 addi a6, zero, 0xb0 ; 0x13654 bne a5, a6 *)
        do 2 step. take true.
        rewrite (dchan_lo_miss (bzl bb) (Z.of_nat (length bb)) M
                   (dchan_test_fam (bzl bb) (Z.of_nat (length bb)) M
                      ltac:(rewrite Hgood; cbn [sm_status]; exact Hnf))) in K.
        eapply dchan_miss; [exact HOK | exact HB | exact HC | exact MI | exact MU | exact WM | exact K].
      * take true.
        rewrite (dchan_lo_miss (bzl bb) (Z.of_nat (length bb)) M
                   (dchan_test_t2 (bzl bb) (Z.of_nat (length bb)) M s2v data 1 ltac:(lia) ltac:(lia)
                      ltac:(lia) ltac:(subst lead; exact Hc) Hn1 ltac:(lia) ltac:(lia))) in K.
        eapply dchan_miss; [exact HOK | exact HB | exact HC | exact MI | exact MU | exact WM | exact K].
  - (* n = 2 *)
    assert (Hn2 : (2:Z) = if (Z.land s2v 240 =? 192) || (Z.land s2v 240 =? 208) then 1 else 2)
      by (rewrite (dchan_n1 s2v ltac:(lia)), (proj2 (Z.eqb_neq _ 192) H192); reflexivity).
    replace ((Z.land s2v 224 + -192) =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
    do 3 step.
    destruct (Z_lt_le_dec (Z.of_nat (length bb)) (data + 2)) as [Hlen|Hlen].
    + take false.
      rewrite (dchan_lo_miss (bzl bb) (Z.of_nat (length bb)) M
                 (dchan_test_t1 (bzl bb) (Z.of_nat (length bb)) M s2v data 2 ltac:(lia) ltac:(lia)
                    ltac:(lia) ltac:(subst lead; exact Hc) Hn2 ltac:(lia))) in K.
      eapply dchan_miss; [exact HOK | exact HB | exact HC | exact MI | exact MU | exact WM | exact K].
    + take true.
      do 2 step.
      pose proof (dchan_rd m body bb data HB ltac:(lia)) as R0.
      do 2 step. rewrite (dchan_sxb bb data).
      destruct (Z_lt_le_dec (byte_at (bzl bb) data) 128) as [Hb0|Hb0]; swap 1 2.
      { take true.
        rewrite (dchan_lo_miss (bzl bb) (Z.of_nat (length bb)) M
                   (dchan_test_t2 (bzl bb) (Z.of_nat (length bb)) M s2v data 2 ltac:(lia) ltac:(lia)
                      ltac:(lia) ltac:(subst lead; exact Hc) Hn2 ltac:(lia) ltac:(lia))) in K.
        eapply dchan_miss; [exact HOK | exact HB | exact HC | exact MI | exact MU | exact WM | exact K]. }
      take false.
      (* the loop's second pass *)
      do 3 step. take true.
      pose proof (dchan_rd m body bb (data + 1) HB ltac:(lia)) as R1.
      do 2 step. rewrite (dchan_sxb bb (data + 1)).
      destruct (Z_lt_le_dec (byte_at (bzl bb) (data + 1)) 128) as [Hb1|Hb1]; swap 1 2.
      { take true.
        rewrite (dchan_lo_miss (bzl bb) (Z.of_nat (length bb)) M
                   (dchan_test_t3 (bzl bb) (Z.of_nat (length bb)) M s2v data 2 ltac:(lia) ltac:(lia)
                      ltac:(lia) ltac:(subst lead; exact Hc) Hn2 ltac:(lia) ltac:(lia) eq_refl ltac:(lia))) in K.
        eapply dchan_miss; [exact HOK | exact HB | exact HC | exact MI | exact MU | exact WM | exact K]. }
      take false.
      assert (Hgood : spec_msg_step (bzl bb) (Z.of_nat (length bb)) (sm_next M) (sm_status_out M) =
        {| sm_code := 1; sm_at := sm_next M; sm_len := data + 2 - sm_next M; sm_next := data + 2;
           sm_status := s2v; sm_running := if lead <? 128 then 1 else 0; sm_d1 := byte_at (bzl bb) data;
           sm_d2 := if 2 =? 2 then byte_at (bzl bb) (data + 1) else 0;
           sm_status_out := s2v; sm_sysex_at := 0; sm_sysex_len := 0 |})
        by (subst lead; apply (dchan_step_good (bzl bb) (Z.of_nat (length bb)) M s2v data 2);
            solve [lia | exact Hc | exact Hn2 | intros; lia]).
      do 3 step. take false.
      do 2 step. take true.
      (* 0x13640 lbu a4, 1(a3) ; 0x13644 slli ; 0x13648 srli: the LSB's bits 6..4 *)
      step. rewrite (dchan_zxb bb (data + 1)).
      step. usub.
      step.
      rewrite (unsigned_lit_wrap (Z.shiftl (byte_at (bzl bb) (data + 1)) 57)),
              (dchan_b456 (byte_at (bzl bb) (data + 1))) by lia.
      (* 0x1364c andi a5, a1, 0xf0 ; 0x13650 addi a6, zero, 0xb0 ; 0x13654 bne a5, a6 *)
      step. usub. do 2 step.
      destruct (Z.eq_dec (Z.land s2v 240) 176) as [H176|H176]; swap 1 2.
      { take true.
        rewrite (dchan_lo_miss (bzl bb) (Z.of_nat (length bb)) M
                   (dchan_test_fam (bzl bb) (Z.of_nat (length bb)) M
                      ltac:(rewrite Hgood; cbn [sm_status]; exact H176))) in K.
        eapply dchan_miss; [exact HOK | exact HB | exact HC | exact MI | exact MU | exact WM | exact K]. }
      take false.
      (* 0x13658 lbu a3, 0(a3) ; 0x1365c ori a5, s9, 0x20 ; 0x13660 bne a5, a3 *)
      step. rewrite (dchan_zxb bb data).
      step. usub. rewrite (dchan_or32 (sm_d1 M) ltac:(lia)).
      step.
      destruct (Z.eq_dec (byte_at (bzl bb) data) (32 + sm_d1 M)) as [Hdd|Hdd]; swap 1 2.
      { take true.
        rewrite (dchan_lo_miss (bzl bb) (Z.of_nat (length bb)) M
                   (dchan_test_d1 (bzl bb) (Z.of_nat (length bb)) M
                      ltac:(rewrite Hgood; cbn [sm_d1]; exact Hdd))) in K.
        eapply dchan_miss; [exact HOK | exact HB | exact HC | exact MI | exact MU | exact WM | exact K]. }
      take false.
      rewrite (dchan_lo_hit (bzl bb) (Z.of_nat (length bb)) M s2v data ltac:(lia) ltac:(lia) ltac:(lia)
                 ltac:(subst lead; exact Hc) Hn2 ltac:(lia) ltac:(lia) ltac:(lia) H176 Hdd) in K.
      dch_cells_f HC.
      (* 0x13664 or a0, a0, a4 ; 0x13668 sh ; 0x1366c sd ; 0x13670 sb ; 0x13674 j *)
      step. usub. sbstep. sbstep. sbstep. step.
      dch_close K.
      replace (2 + data) with (data + 2) in HC by lia.
      rewrite (dchan_val (sm_d2 M) (Z.land (Z.shiftr (byte_at (bzl bb) (data + 1)) 4) 7)
                 ltac:(lia) (dchan_t_rng _)) in HC.
      exact HC.
Qed.

(* the LSB lookahead's entry, 0x13434: is there a next step, and what is its status byte? *)
Lemma dchan_lsb :
  forall (r1 x3 x4 r5 r6 r7 r8 r11 r12 r13 r14 r15 r16 r17 x22 r23 r28 r29 r30 r31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
    (Sp body : Z) (bb j0 oj : list byte) (w10 : word) (rest : list cell)
    (Q : machine_state -> Prop) (M : spec_msg),
  seg_ok Sp body bb ->
  0 <= sm_d1 M < 32 -> 0 <= sm_d2 M < 128 -> 0 < sm_status_out M < 256 ->
  0 <= sm_next M <= Z.of_nat (length bb) -> sm_status_out M = sm_status M ->
  bytes_at rsegs m body bb ->
  rw_cells rsegs m Sp (fr_head j0 (Z_to_bv 64 0x103a4) w10 body ++
    owed_cells (ow_p1 oj) (ow_p2 oj) (Owed M (dch_ef M) 0 (sm_next M) (sm_status_out M)) ++ rest) ->
  mem_inv rsegs m -> munch [(Sp + 32, Sp + 152)] m0 m -> wmono rsegs m0 m ->
  dend Q x3 x4 x22 F fc m0 Sp body bb j0 oj w10 rest (dch_lo (bzl bb) (Z.of_nat (length bb)) M) ->
  evt rsegs Q
    (MS (mkR r1 (Z_to_bv 64 Sp) x3 x4 r5 r6 r7 r8 (Z_to_bv 64 (sm_status M))
           (Z_to_bv 64 (u16 (Z.shiftl (sm_d2 M) 3))) r11 r12 r13 r14 r15 r16 r17
           (Z_to_bv 64 (Z.of_nat (length bb))) (Z_to_bv 64 (Sp + 88)) (Z_to_bv 64 (sm_next M))
           (Z_to_bv 64 body) x22 r23 (Z_to_bv 64 (- Z.of_nat (length bb))) (Z_to_bv 64 (sm_d1 M))
           (Z_to_bv 64 247) (Z_to_bv 64 1) r28 r29 r30 r31)
        F (Z_to_bv 64 0x13434) fc None m (seg_rom rsegs)).
Proof.
  intros r1 x3 x4 r5 r6 r7 r8 r11 r12 r13 r14 r15 r16 r17 x22 r23 r28 r29 r30 r31 F fc m0 m Sp body
    bb j0 oj w10 rest Q M HOK Hd1 Hd2 Hst Hnx Hso HB HC MI MU WM K.
  pose proof HOK as [H0 [H1 [H2 [H3 H4]]]].
  pose proof (dchan_bz bb (sm_next M)) as Bnx.
  rewrite <- Hso.
  (* 0x13434 bgeu s4, s2 *)
  step.
  destruct (Z_lt_le_dec (sm_next M) (Z.of_nat (length bb))) as [Hend|Hend]; swap 1 2.
  { take true.
    rewrite (dchan_lo_miss (bzl bb) (Z.of_nat (length bb)) M
               (dchan_test_end (bzl bb) (Z.of_nat (length bb)) M Hend)) in K.
    eapply dchan_miss; [exact HOK | exact HB | exact HC | exact MI | exact MU | exact WM | exact K]. }
  take false.
  (* 0x13438 add a1, s5, s4 ; 0x1343c lbu a2, 0(a1) *)
  step.
  pose proof (dchan_rd m body bb (sm_next M) HB ltac:(lia)) as R0.
  step. rewrite (dchan_zxb bb (sm_next M)).
  (* 0x13440 addi a1, zero, 0xef ; 0x13444 bltu a1, a2 *)
  do 2 step.
  destruct (Z_lt_le_dec (byte_at (bzl bb) (sm_next M)) 240) as [Hlo|Hhi].
  2: { take true.
       rewrite (dchan_lo_miss (bzl bb) (Z.of_nat (length bb)) M
                  (dchan_test_hi (bzl bb) (Z.of_nat (length bb)) M ltac:(lia) ltac:(lia))) in K.
       eapply dchan_miss; [exact HOK | exact HB | exact HC | exact MI | exact MU | exact WM | exact K]. }
  take false.
  (* 0x13448 slli a3, a2, 0x38 ; 0x1344c bnez s1 *)
  step. usub. step. take true.
  (* 0x13458 mv a1, a2 ; 0x1345c bltz a3 *)
  step. step. rewrite (dchan_sl56_lts (byte_at (bzl bb) (sm_next M)) ltac:(lia)).
  destruct (Z_lt_le_dec (byte_at (bzl bb) (sm_next M)) 128) as [Hd|Hd].
  - take false.
    (* 0x13460 mv a1, s1: the running status *)
    step.
    eapply (dchan_lsb_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m0 m Sp body
              (sm_status_out M) (sm_next M) (byte_at (bzl bb) (sm_next M)) bb j0 oj w10 rest Q M);
      try solve [ exact HOK | lia | reflexivity | exact HB | exact HC | exact MI | exact MU | exact WM | exact K ].
  - take true.
    eapply (dchan_lsb_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m0 m Sp body
              (byte_at (bzl bb) (sm_next M)) (sm_next M + 1) (byte_at (bzl bb) (sm_next M)) bb j0 oj w10 rest Q M);
      try solve [ exact HOK | lia | reflexivity | exact HB | exact HC | exact MI | exact MU | exact WM | exact K ].
Qed.

(* status & 0xf0 = 0xb0 and d1 < 0x20 (0x13424): a fader, then the LSB lookahead *)
Lemma dchan_fader :
  forall (r1 x3 x4 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 x22 r28 r29 r30 r31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (Sp body pos : Z) (bb j0 oj : list byte) (w10 : word) (rest : list cell)
    (Q : machine_state -> Prop) (M : spec_msg),
  dch_ok Sp body bb M ->
  Z.land (sm_status M) 240 = 176 -> sm_d1 M < 32 ->
  bytes_at rsegs m body bb ->
  rw_cells rsegs m Sp (fr_head j0 (Z_to_bv 64 0x103a4) w10 body ++ owed_cells (ow_p1 oj) (ow_p2 oj) (owed0 M) ++ rest) ->
  mem_inv rsegs m ->
  dend Q x3 x4 x22 F fc m Sp body bb j0 oj w10 rest (dch_lo (bzl bb) (Z.of_nat (length bb)) M) ->
  dch_pre Q r1 x3 x4 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 x22 r28 r29 r30 r31 F fc m Sp body pos bb M.
Proof.
  intros r1 x3 x4 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 x22 r28 r29 r30 r31 F fc m Sp body pos bb j0 oj w10
    rest Q M HOK Hf H32 HB HC MI K.
  pose proof HOK as [HS [Hst [Hd1 [Hd2 [Hnx Hso]]]]].
  pose proof HS as [H0 [H1 [H2 [H3 H4]]]].
  assert (Hst0 : 0 < sm_status M)
    by (destruct (Z.eq_dec (sm_status M) 0) as [E|E];
        [rewrite E, Z.land_0_l in Hf; lia | lia]).
  unfold dch_pre. dch_cells HC.
  pose proof (munch_refl [(Sp + 32, Sp + 152)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (Z_land_range (sm_status M) 240 ltac:(lia) ltac:(lia)) as Hfam.
  (* 0x133d0 .. 0x133e0: kind OTHER, then the 0xb0 family *)
  do 5 step. take true.
  (* 0x1341c addi a0, zero, 0x20 ; 0x13420 bgeu s9, a0 *)
  do 2 step. take false.
  (* 0x13424 slli a0, s7, 3 *)
  step. usub. rewrite (dchan_sl3 (sm_d2 M) ltac:(lia)).
  (* 0x13428 sw s11 (kind FADER) ; 0x1342c sb s9 (strip) ; 0x13430 sh a0 (value) *)
  sbstep. sbstep. sbstep.
  eapply (dchan_lsb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m _ Sp body bb j0 oj w10 rest Q M);
    try solve [ exact HS | lia | exact Hso | eassumption ].
Qed.

(* ---- owed_at of a channel message, by family ---- *)

Lemma dchan_ef_eq : forall b M, Z.land (sm_status M) 240 = 176 -> sm_d1 M < 32 ->
  spec_event_of b M = dch_ef M.
Proof.
  intros b M Hf Hd. unfold spec_event_of, dch_ef. cbv zeta. rewrite Hf. cbn [Z.eqb Pos.eqb].
  rewrite (proj2 (Z.ltb_lt (sm_d1 M) 32) Hd). reflexivity.
Qed.

Lemma dchan_owed_fader : forall b len pos status M, M = spec_msg_step b len pos status ->
  sm_code M = 1 -> Z.land (sm_status M) 240 = 176 -> sm_d1 M < 32 ->
  owed_at b len pos status = dch_lo b len M.
Proof.
  intros b len pos status M HM Hc Hf Hd. subst M. unfold owed_at. cbv zeta.
  rewrite (proj2 (Z.eqb_eq _ 1) Hc). cbn [negb].
  rewrite (dchan_ef_eq b (spec_msg_step b len pos status) Hf Hd).
  replace (se_kind (dch_ef (spec_msg_step b len pos status)) =? SPEC_EV_FADER) with true
    by (symmetry; apply Z.eqb_eq; reflexivity).
  cbn [negb]. reflexivity.
Qed.

Lemma dchan_owed_other : forall b len pos status M, M = spec_msg_step b len pos status ->
  sm_code M = 1 -> se_kind (spec_event_of b M) <> SPEC_EV_FADER ->
  owed_at b len pos status = Owed M (spec_event_of b M) 0 (sm_next M) (sm_status_out M).
Proof.
  intros b len pos status M HM Hc Hk. subst M. unfold owed_at. cbv zeta.
  rewrite (proj2 (Z.eqb_eq _ 1) Hc). cbn [negb].
  rewrite (proj2 (Z.eqb_neq _ SPEC_EV_FADER) Hk). cbn [negb]. reflexivity.
Qed.

Lemma dchan_kind_note : forall b M, Z.land (sm_status M) 240 = 144 ->
  se_kind (spec_event_of b M) <> SPEC_EV_FADER.
Proof.
  intros b M Hf. unfold spec_event_of. cbv zeta. rewrite Hf. cbn [Z.eqb Pos.eqb].
  destruct ((SPEC_ZONE_FIRST <=? Z.land (sm_d2 M) 63) && (Z.land (sm_d2 M) 63 <=? SPEC_ZONE_LAST));
    cbn [se_kind]; unfold SPEC_EV_SECTION_BUTTON, SPEC_EV_FADER, SPEC_EV_TOUCH, SPEC_EV_STRIP_BUTTON.
  - lia.
  - destruct (sm_d1 M =? SPEC_BTN_TOUCH); lia.
Qed.

Lemma dchan_kind_cc_hi : forall b M, Z.land (sm_status M) 240 = 176 -> 32 <= sm_d1 M ->
  se_kind (spec_event_of b M) <> SPEC_EV_FADER.
Proof.
  intros b M Hf Hd. unfold spec_event_of. cbv zeta. rewrite Hf. cbn [Z.eqb Pos.eqb].
  rewrite (proj2 (Z.ltb_ge (sm_d1 M) 32) Hd).
  destruct (sm_d1 M =? SPEC_JOG_CC); [cbn [se_kind]; unfold SPEC_EV_JOG, SPEC_EV_FADER; lia|].
  destruct ((64 <=? sm_d1 M) && (sm_d1 M <? 64 + SPEC_VPOTS));
    [cbn [se_kind]; unfold SPEC_EV_VPOT, SPEC_EV_FADER; lia|].
  unfold se_other. cbn [se_kind]. unfold SPEC_EV_OTHER, SPEC_EV_FADER. lia.
Qed.

Lemma dchan_kind_other : forall b M, Z.land (sm_status M) 240 <> 144 -> Z.land (sm_status M) 240 <> 176 ->
  (sm_status M =? 240) = false -> se_kind (spec_event_of b M) <> SPEC_EV_FADER.
Proof.
  intros b M H1 H2 H3. unfold spec_event_of. cbv zeta.
  rewrite (proj2 (Z.eqb_neq _ 144) H1), (proj2 (Z.eqb_neq _ 176) H2), H3. cbn [negb].
  unfold se_other. cbn [se_kind]. unfold SPEC_EV_OTHER, SPEC_EV_FADER. lia.
Qed.

Theorem dchan_holds : dchan_stmt.
Proof.
  unfold dchan_stmt, devent_stmt.
  intros MSC MCC r1 x3 x4 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 x22 r25 r28 r29 r30 r31 F fc m Sp body pos
    status bb j0 oj w10 rest Q HOK Hpos Hstat Hcode Hsys Hoj HB Hr25 HC MI K.
  cbv iota in *. specialize (Hr25 eq_refl). subst r25.
  pose proof (dchan_M (bzl bb) (Z.of_nat (length bb)) pos status (dchan_bz bb) ltac:(lia) Hcode Hsys) as HF.
  set (M := spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos status) in *.
  assert (HM : M = spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos status) by reflexivity.
  destruct HF as (Hst & Hd1 & Hd2 & Hnx & Hso).
  pose proof HOK as [S0 [S1 [S2 [S3 S4]]]].
  assert (Hok : dch_ok Sp body bb M) by (unfold dch_ok; repeat split; lia).
  destruct (Z.eq_dec (Z.land (sm_status M) 240) 144) as [F144|F144].
  - rewrite (dchan_owed_other (bzl bb) (Z.of_nat (length bb)) pos status M HM Hcode
               (dchan_kind_note (bzl bb) M F144)) in K.
    exact (dchan_note r1 x3 x4 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 x22 r28 r29 r30 r31 F fc m Sp body pos
             bb j0 oj w10 rest Q M Hok F144 HB HC MI K).
  - destruct (Z.eq_dec (Z.land (sm_status M) 240) 176) as [F176|F176].
    + destruct (Z_lt_le_dec (sm_d1 M) 32) as [Hlt|Hge].
      * rewrite (dchan_owed_fader (bzl bb) (Z.of_nat (length bb)) pos status M HM Hcode F176 Hlt) in K.
        exact (dchan_fader r1 x3 x4 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 x22 r28 r29 r30 r31 F fc m Sp body
                 pos bb j0 oj w10 rest Q M Hok F176 Hlt HB HC MI K).
      * rewrite (dchan_owed_other (bzl bb) (Z.of_nat (length bb)) pos status M HM Hcode
                   (dchan_kind_cc_hi (bzl bb) M F176 Hge)) in K.
        exact (dchan_cc_hi r1 x3 x4 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 x22 r28 r29 r30 r31 F fc m Sp body
                 pos bb j0 oj w10 rest Q M Hok F176 Hge HB HC MI K).
    + rewrite (dchan_owed_other (bzl bb) (Z.of_nat (length bb)) pos status M HM Hcode
                 (dchan_kind_other (bzl bb) M F144 F176 Hsys)) in K.
      exact (dchan_other r1 x3 x4 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 x22 r28 r29 r30 r31 F fc m Sp body pos
               bb j0 oj w10 rest Q M Hok Hsys F176 F144 HB HC MI K).
Qed.
