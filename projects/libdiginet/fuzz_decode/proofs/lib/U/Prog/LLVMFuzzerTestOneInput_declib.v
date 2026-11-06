(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the facts the walk of the decoder loop of LLVMFuzzerTestOneInput on the UBSan
   image (fuzz_decode.ubsan, 0x12e8c to 0x13384; lib/U/Prog/LLVMFuzzerTestOneInput_decoder.v) takes from the model
   and from the kit's cells. No pc of the image is named here.
   - The model of one pass (fuzz_decode.c:327-339): for a cursor at pos <= len with a running status st_ok, the step
     spec_msg_step and owed_at have fields in the ranges the callees' contracts ask for (a code -8..1, a status byte,
     an F0 payload offset inside the body, a payload length at most len, an event kind 0..13, lsb_missing 0 or 1, a
     scribble length at most 8), the next step starts at a place pos < next <= len unless the code is 0, and the
     running status it leaves is st_ok again; diginet_decoder_next (DgnAgreeDecoder.decoder_step_ok) returns that
     step's code, passes both checks and moves its cursor to owed_at's next place and status.
   - The cells: a CB region split in two and joined again, a byte list read through bz, and the 80 zero bytes of
     the memset of ev (0x131d8) as event_cells of dgn_event_zero (the event check_events_step reads when
     diginet_decoder_next does not return 1).
   - The set-up's arithmetic: (x & 0xff) * 0xab >> 9 is (x & 0xff) / 3 for every x, so the `subw` leaves
     (x & 0xff) mod 3 in the low byte. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import
  DgnSpec DgnLib DgnDecHarness DgnAgreeCursor DgnAgreeDecoder.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import DgnLayout DgnCellsU
  diginet_decoder_next_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- the model ---- *)

Lemma Forall_bz : forall bb : list byte, Forall (fun x => 0 <= x < 256) (map bz bb).
Proof.
  intros bb. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as [y [<- _]]. unfold bz.
  pose proof (bv_unsigned_in_range 8 y) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  lia.
Qed.

Lemma scan_f7_ge : forall b len fuel i, i <= scan_f7 b len i fuel.
Proof.
  intros b len fuel; induction fuel as [|f IH]; intros i; cbn [scan_f7]; [lia|].
  destruct ((i <? len) && negb (byte_at b i =? 247)); [specialize (IH (i + 1)); lia | lia].
Qed.

Lemma scan_f7_le : forall b len fuel i, i <= len -> scan_f7 b len i fuel <= len.
Proof.
  intros b len fuel; induction fuel as [|f IH]; intros i Hi; cbn [scan_f7]; [lia|].
  destruct ((i <? len) && negb (byte_at b i =? 247)) eqn:E; [|lia].
  apply andb_true_iff in E as [E _]. apply Z.ltb_lt in E. apply IH. lia.
Qed.

Local Ltac dif := match goal with |- context [if ?c then _ else _] => let E := fresh "E" in destruct c eqn:E end.

Local Ltac b2p := repeat match goal with
  | H : (_ || _) = false |- _ => apply orb_false_iff in H; destruct H
  | H : (_ && _) = true |- _ => apply andb_true_iff in H; destruct H
  | H : negb _ = true |- _ => apply negb_true_iff in H
  | H : negb _ = false |- _ => apply negb_false_iff in H
  | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
  | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
  | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
  | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
  | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
  | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
  end.

(* the fields of one step of spec.h's grammar (spec.h:298-363) that the callees' contracts bound *)
Lemma sms_facts : forall b len pos st,
  Forall (fun x => 0 <= x < 256) b -> 0 <= pos -> 0 <= len -> st_ok st ->
  -8 <= sm_code (spec_msg_step b len pos st) <= 1 /\
  0 <= sm_status (spec_msg_step b len pos st) < 256 /\
  (sm_status (spec_msg_step b len pos st) = 240 -> 1 <= sm_sysex_at (spec_msg_step b len pos st) < len) /\
  0 <= sm_sysex_len (spec_msg_step b len pos st) <= len /\
  st_ok (sm_status_out (spec_msg_step b len pos st)).
Proof.
  intros b len pos st Hb Hp Hl Hs.
  pose proof (byte_at_range b pos Hb) as Hlead.
  pose proof (scan_f7_ge b len (Z.to_nat (len - (pos + 1))) (pos + 1)) as G1.
  pose proof (scan_f7_le b len (Z.to_nat (len - (pos + 1))) (pos + 1)) as G2.
  unfold st_ok in *. unfold spec_msg_step. cbv zeta.
  repeat dif; cbn [sm_code sm_status sm_sysex_at sm_sysex_len sm_status_out]; b2p;
    unfold SPEC_E_TRUNCATED, SPEC_E_STATUS, SPEC_E_NO_STATUS in *; lia.
Qed.

(* the kind and the length of spec.h's event (spec.h:392-499) *)
Lemma spec_event_facts : forall b m,
  0 <= se_kind (spec_event_of b m) <= 13 /\ 0 <= se_len (spec_event_of b m) <= 8.
Proof.
  intros b m. unfold spec_event_of, se_other. cbv zeta.
  repeat dif; cbn [se_kind se_len]; b2p;
    unfold SPEC_EV_FADER, SPEC_EV_TOUCH, SPEC_EV_STRIP_BUTTON, SPEC_EV_SECTION_BUTTON, SPEC_EV_VPOT,
      SPEC_EV_JOG, SPEC_EV_RING, SPEC_EV_METER, SPEC_EV_STRIP_LEDS, SPEC_EV_SCRIBBLE, SPEC_EV_COUNTER,
      SPEC_EV_SYSTEM, SPEC_EV_OTHER, SPEC_CHARS_MAX, u8 in *; lia.
Qed.

(* what the decoder owes after one step (fuzz_decode.c:127-150) *)
Lemma owed_facts : forall b len pos st,
  Forall (fun x => 0 <= x < 256) b -> 0 <= pos -> 0 <= len -> st_ok st ->
  ow_m (owed_at b len pos st) = spec_msg_step b len pos st /\
  0 <= se_kind (ow_e (owed_at b len pos st)) <= 13 /\
  0 <= ow_lsb_missing (owed_at b len pos st) <= 1 /\
  0 <= se_len (ow_e (owed_at b len pos st)) <= 8 /\
  st_ok (ow_status_out (owed_at b len pos st)) /\
  (sm_code (ow_m (owed_at b len pos st)) <> 0 ->
     pos < ow_next (owed_at b len pos st) <= len).
Proof.
  intros b len pos st Hb Hp Hl Hs.
  pose proof (sms_facts b len pos st Hb Hp Hl Hs) as (C & S & X & L & SO).
  pose proof (spec_msg_step_progress b len pos st) as PR.
  unfold owed_at. cbv zeta.
  destruct (sm_code (spec_msg_step b len pos st) =? 1) eqn:E1; cbn [negb].
  2: { cbn [ow_m ow_e ow_lsb_missing ow_next ow_status_out se_kind se_len se_zero].
       split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact SO | exact PR]. }
  apply Z.eqb_eq in E1.
  pose proof (spec_event_facts b (spec_msg_step b len pos st)) as (K & EL).
  destruct (se_kind (spec_event_of b (spec_msg_step b len pos st)) =? SPEC_EV_FADER) eqn:E2; cbn [negb].
  2: { cbn [ow_m ow_e ow_lsb_missing ow_next ow_status_out].
       split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact SO | exact PR]. }
  assert (N1 : pos < sm_next (spec_msg_step b len pos st) <= len) by (apply PR; lia).
  pose proof (sms_facts b len (sm_next (spec_msg_step b len pos st)) (sm_status_out (spec_msg_step b len pos st))
    Hb ltac:(lia) Hl SO) as (_ & _ & _ & _ & SO2).
  pose proof (spec_msg_step_progress b len (sm_next (spec_msg_step b len pos st))
    (sm_status_out (spec_msg_step b len pos st))) as PR2.
  destruct ((sm_code (spec_msg_step b len (sm_next (spec_msg_step b len pos st))
               (sm_status_out (spec_msg_step b len pos st))) =? 1) &&
            (Z.land (sm_status (spec_msg_step b len (sm_next (spec_msg_step b len pos st))
               (sm_status_out (spec_msg_step b len pos st)))) 240 =? 176) &&
            (sm_d1 (spec_msg_step b len (sm_next (spec_msg_step b len pos st))
               (sm_status_out (spec_msg_step b len pos st))) =?
             32 + sm_d1 (spec_msg_step b len pos st))) eqn:E3.
  - cbn [ow_m ow_e ow_lsb_missing ow_next ow_status_out se_kind se_len se_with_value].
    apply andb_true_iff in E3 as [E3 _]. apply andb_true_iff in E3 as [E3 _]. apply Z.eqb_eq in E3.
    split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact SO2|].
    intros _. specialize (PR2 ltac:(lia)). lia.
  - cbn [ow_m ow_e ow_lsb_missing ow_next ow_status_out].
    split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact SO | exact PR].
Qed.

(* one call of diginet_decoder_next from a decoder at pos, st (DgnAgreeDecoder.decoder_step_ok): the code of
   owed_at's step, both checks of the pass, and the cursor at owed_at's next place and status *)
Lemma dec_pass_model : forall (bb : list byte) (d : dgn_decoder) (pos st : Z),
  dd_c d = DgnCursor (Z.of_nat (length bb)) pos st ->
  dn_r bb d = sm_code (ow_m (owed_at (map bz bb) (Z.of_nat (length bb)) pos st)) /\
  events_step_ok (map bz bb)
    (EventsStep (owed_at (map bz bb) (Z.of_nat (length bb)) pos st) (dn_r bb d) (dn_e bb d)) = true /\
  dd_c (dn_d bb d) = DgnCursor (Z.of_nat (length bb)) (ow_next (owed_at (map bz bb) (Z.of_nat (length bb)) pos st))
                       (ow_status_out (owed_at (map bz bb) (Z.of_nat (length bb)) pos st)).
Proof.
  intros bb d pos st Hd. unfold dn_r, dn_e, dn_d, dn_step.
  change (map bv_unsigned bb) with (map bz bb).
  destruct (diginet_decoder_next (map bz bb) d dgn_event_zero) as [[rd ev] d'] eqn:E. cbn [fst snd].
  destruct (decoder_step_ok (map bz bb) d _ pos st rd ev d' (Forall_bz bb) Hd E) as (H1 & H2 & H3 & _).
  split; [exact H1|]. split; [exact H2 | exact H3].
Qed.

(* ---- the cells ---- *)

Lemma cb_split2 : forall m A (n1 n2 : nat) j,
  rw_cells rsegs m A [CB (n1 + n2) j] ->
  exists j1 j2, rw_cells rsegs m A [CB n1 j1] /\ rw_cells rsegs m (A + Z.of_nat n1) [CB n2 j2].
Proof.
  intros m A n1 n2 j H.
  pose proof (rw_cells_split_CB rsegs m A [] (n1 + n2) j [] [n1; n2] H ltac:(cbn; lia)) as P.
  cbn [app mk_CB_cells] in P.
  destruct (rw_cells_split m A [CB n1 (firstn n1 j)] [CB n2 (firstn n2 (skipn n1 j))] P) as [P1 P2].
  cbn [cells_size csize] in P2. rewrite Nat.add_0_r in P2.
  exists (firstn n1 j), (firstn n2 (skipn n1 j)). split; [exact P1 | exact P2].
Qed.

Lemma cb_join : forall m A (n1 n2 : nat) j1 j2,
  rw_cells rsegs m A [CB n1 j1] -> rw_cells rsegs m (A + Z.of_nat n1) [CB n2 j2] ->
  rw_cells rsegs m A [CB (n1 + n2) (j1 ++ j2)].
Proof.
  intros m A n1 n2 j1 j2 H1 H2.
  assert (H2' : rw_cells rsegs m (A + Z.of_nat (cells_size [CB n1 j1])) [CB n2 j2])
    by (cbn [cells_size csize]; rewrite Nat.add_0_r; exact H2).
  pose proof (rw_cells_join m A [CB n1 j1] [CB n2 j2] H1 H2') as J.
  pose proof (rw_cells_merge rsegs m A [] [CB n1 j1; CB n2 j2] [] J) as M.
  cbn [app cells_size csize cells_bytes cbytes] in M. rewrite Nat.add_0_r, app_nil_r in M. exact M.
Qed.

Lemma bytes_eq_of_bz : forall l1 l2 : list byte, map bz l1 = map bz l2 -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

(* the 80 bytes the memset of 0x131d8 leaves, read as the event check_events_step is given when
   diginet_decoder_next does not return 1: the model's dgn_event_zero, its message dgn_msg_zero (payload NULL) *)
Lemma event_zero_cells : forall m e body,
  rw_cells rsegs m e [CB 80 (repeat (Z_to_bv 8 0) 80)] ->
  ro_cells rsegs m e (event_cells body (repeat (Z_to_bv 8 0) 4) dgn_event_zero).
Proof.
  intros m e body [[_ Hb] _]. split.
  - cbn. repeat split.
  - replace (cells_bytes (event_cells body (repeat (Z_to_bv 8 0) 4) dgn_event_zero))
      with (repeat (Z_to_bv 8 0) 80).
    + cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
    + apply bytes_eq_of_bz. vm_compute. reflexivity.
Qed.

(* ---- the set-up's arithmetic (0x12e8c-0x12eb4) ---- *)

(* (x * 0xab) >> 9 = x / 3 for a byte x, checked over the 256 bytes *)
Lemma div3_byte_chk : forallb (fun x => Z.shiftr (x * 171) 9 =? x / 3) (zseq 256) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma div3_byte : forall x, 0 <= x < 256 -> Z.shiftr (x * 171) 9 = x / 3.
Proof.
  intros x Hx. apply Z.eqb_eq.
  exact (byte_forall (fun x => Z.shiftr (x * 171) 9 =? x / 3) div3_byte_chk x Hx).
Qed.

(* 0x12eac-0x12eb0: with X = x & 0xff, `subw s0, s0, a1` (a1 = 3 (X / 3)) and `andi a1, s0, 0xff` leave X mod 3 *)
Lemma desk_sub : forall u X, X = Z.land u 255 -> 0 <= u < 2 ^ 64 ->
  Z.land (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (u - bv_unsigned (Z_to_bv 64 (Z.shiftl (X / 3) 1 + X / 3))))))
    255 = X mod 3.
Proof.
  intros u X HX Hu. subst X.
  assert (L : Z.land u 255 = u mod 256) by (change 255 with (Z.ones 8); apply Z.land_ones; lia).
  rewrite L. clear L.
  assert (B : 0 <= u mod 256 < 256) by (apply Z.mod_pos_bound; lia).
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
  rewrite (unsigned_lit (u mod 256 / 3 * 2 + u mod 256 / 3)) by lia.
  rewrite unsigned_lit_wrap. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 `div` 2) with 2147483648.
  change (2 ^ 64) with 18446744073709551616. change (2 ^ 8) with 256.
  clear Hu B. Z.div_mod_to_equations. lia.
Qed.

(* the three values diginet_personality_of returns (DgnLib.v) *)
Lemma pers_cases : forall z,
  diginet_personality_of z = None \/ diginet_personality_of z = Some 0 \/ diginet_personality_of z = Some 1.
Proof.
  intros z. unfold diginet_personality_of. cbn [personality_find personalities dp_desk].
  destruct (DIGINET_DESK_CONTROL24 =? z); [right; left; reflexivity|].
  destruct (DIGINET_DESK_PROCONTROL =? z); [right; right; reflexivity | left; reflexivity].
Qed.

(* check_events_step when diginet_decoder_next does not return 1: only the code is compared (fuzz_decode.c:161) *)
Lemma ces_nomsg : forall o r ev, r = sm_code (ow_m o) -> r <> 1 -> check_events_step_ok o r ev = true.
Proof.
  intros o r ev H1 H2. unfold check_events_step_ok. rewrite <- H1, Z.eqb_refl.
  replace (r =? 1) with false by (symmetry; apply Z.eqb_neq; exact H2). reflexivity.
Qed.

(* ---- registers ---- *)

(* lw of a cell C4 (Z_to_bv 64 z) whose z is a C int *)
Lemma dl_sx32 : forall z, -2 ^ 31 <= z < 2 ^ 31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  replace (2 ^ 64) with 18446744073709551616 by reflexivity.
  replace (2 ^ 32) with 4294967296 by reflexivity. replace (2 ^ 31) with 2147483648 by reflexivity.
  replace (2 ^ 31) with 2147483648 in Hz by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

(* beq / bne of two signed 64-bit integers *)
Lemma dl_eqb64 : forall x y, -2 ^ 63 <= x < 2 ^ 63 -> -2 ^ 63 <= y < 2 ^ 63 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof.
  intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec x y) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E. apply N.
  replace (2 ^ 64) with 18446744073709551616 in E by reflexivity.
  replace (2 ^ 63) with 9223372036854775808 in Hx, Hy by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

(* lbu of a cell C1 (b8 z) whose z is a byte *)
Lemma dl_zxb8 : forall z, 0 <= z < 256 -> zxb (b8 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold zxb, b8. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  unfold bv_modulus. change (2 ^ Z.of_N 8) with 256. exact Hz.
Qed.

(* snez of a pointer that is not NULL *)
Lemma dl_snez : forall z, 0 < z < 2 ^ 63 -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 z) = Z_to_bv 64 1.
Proof.
  intros z Hz. rewrite v_sltu_b2z. rewrite (unsigned_lit z) by lia.
  change (bv_unsigned (Z_to_bv 64 0)) with 0. destruct (Z.ltb_spec 0 z); [reflexivity | lia].
Qed.

(* `addi s4, zero, -1` *)
Lemma dl_m1 : Z_to_bv 64 (-1) = Z_to_bv 64 (2 ^ 64 - 1).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* bltu / bgeu of two sizes *)
Lemma dl_ltu : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

(* the alignment of sp, kept from lia *)
Definition dl_al16 (x : Z) : Prop := x mod 16 = 0.

Lemma dl_al16_8 : forall x k, dl_al16 x -> k mod 8 = 0 -> (x + k) mod 8 = 0.
Proof. unfold dl_al16. intros x k H1 H2. Z.div_mod_to_equations. lia. Qed.

(* ---- the 376 bytes at sp + 0x10 that the cuts hand over, in the decoder loop's pieces: (body != 0) 8 bytes at
   sp + 0x10, struct owed o 120 at sp + 0x18, struct diginet_event ev 80 at sp + 0x90, struct diginet_msg msg 40 at
   sp + 0xe0 (not used by the decoder loop), struct diginet_decoder d 40 at sp + 0x108, struct diginet_cursor c 32
   at sp + 0x130 (not used), struct spec_msg lsb 56 at sp + 0x150 ---- *)

Lemma carve376 : forall m S j,
  rw_cells rsegs m (S + 16) [CB 376 j] ->
  exists j10 j18 j90 je0 j108 j130 j150,
    rw_cells rsegs m (S + 16) [CB 8 j10] /\ rw_cells rsegs m (S + 24) [CB 120 j18] /\
    rw_cells rsegs m (S + 144) [CB 80 j90] /\ rw_cells rsegs m (S + 224) [CB 40 je0] /\
    rw_cells rsegs m (S + 264) [CB 40 j108] /\ rw_cells rsegs m (S + 304) [CB 32 j130] /\
    rw_cells rsegs m (S + 336) [CB 56 j150].
Proof.
  intros m S j H.
  destruct (cb_split2 m (S + 16) 8 368 j H) as (j10 & r1 & H10 & R1). change (Z.of_nat 8) with 8 in R1.
  replace (S + 16 + 8) with (S + 24) in R1 by lia.
  destruct (cb_split2 m (S + 24) 120 248 r1 R1) as (j18 & r2 & H18 & R2). change (Z.of_nat 120) with 120 in R2.
  replace (S + 24 + 120) with (S + 144) in R2 by lia.
  destruct (cb_split2 m (S + 144) 80 168 r2 R2) as (j90 & r3 & H90 & R3). change (Z.of_nat 80) with 80 in R3.
  replace (S + 144 + 80) with (S + 224) in R3 by lia.
  destruct (cb_split2 m (S + 224) 40 128 r3 R3) as (je0 & r4 & He0 & R4). change (Z.of_nat 40) with 40 in R4.
  replace (S + 224 + 40) with (S + 264) in R4 by lia.
  destruct (cb_split2 m (S + 264) 40 88 r4 R4) as (j108 & r5 & H108 & R5). change (Z.of_nat 40) with 40 in R5.
  replace (S + 264 + 40) with (S + 304) in R5 by lia.
  destruct (cb_split2 m (S + 304) 32 56 r5 R5) as (j130 & j150 & H130 & H150).
  change (Z.of_nat 32) with 32 in H150. replace (S + 304 + 32) with (S + 336) in H150 by lia.
  exists j10, j18, j90, je0, j108, j130, j150. tauto.
Qed.

Lemma join376 : forall m S j10 j18 j90 je0 j108 j130 j150,
  rw_cells rsegs m (S + 16) [CB 8 j10] -> rw_cells rsegs m (S + 24) [CB 120 j18] ->
  rw_cells rsegs m (S + 144) [CB 80 j90] -> rw_cells rsegs m (S + 224) [CB 40 je0] ->
  rw_cells rsegs m (S + 264) [CB 40 j108] -> rw_cells rsegs m (S + 304) [CB 32 j130] ->
  rw_cells rsegs m (S + 336) [CB 56 j150] ->
  exists j, rw_cells rsegs m (S + 16) [CB 376 j].
Proof.
  intros m S j10 j18 j90 je0 j108 j130 j150 H10 H18 H90 He0 H108 H130 H150.
  assert (A1 : rw_cells rsegs m (S + 16 + Z.of_nat 8) [CB 120 j18])
    by (change (Z.of_nat 8) with 8; replace (S + 16 + 8) with (S + 24) by lia; exact H18).
  pose proof (cb_join m (S + 16) 8 120 j10 j18 H10 A1) as J1. change (8 + 120)%nat with 128%nat in J1.
  assert (A2 : rw_cells rsegs m (S + 16 + Z.of_nat 128) [CB 80 j90])
    by (change (Z.of_nat 128) with 128; replace (S + 16 + 128) with (S + 144) by lia; exact H90).
  pose proof (cb_join m (S + 16) 128 80 _ j90 J1 A2) as J2. change (128 + 80)%nat with 208%nat in J2.
  assert (A3 : rw_cells rsegs m (S + 16 + Z.of_nat 208) [CB 40 je0])
    by (change (Z.of_nat 208) with 208; replace (S + 16 + 208) with (S + 224) by lia; exact He0).
  pose proof (cb_join m (S + 16) 208 40 _ je0 J2 A3) as J3. change (208 + 40)%nat with 248%nat in J3.
  assert (A4 : rw_cells rsegs m (S + 16 + Z.of_nat 248) [CB 40 j108])
    by (change (Z.of_nat 248) with 248; replace (S + 16 + 248) with (S + 264) by lia; exact H108).
  pose proof (cb_join m (S + 16) 248 40 _ j108 J3 A4) as J4. change (248 + 40)%nat with 288%nat in J4.
  assert (A5 : rw_cells rsegs m (S + 16 + Z.of_nat 288) [CB 32 j130])
    by (change (Z.of_nat 288) with 288; replace (S + 16 + 288) with (S + 304) by lia; exact H130).
  pose proof (cb_join m (S + 16) 288 32 _ j130 J4 A5) as J5. change (288 + 32)%nat with 320%nat in J5.
  assert (A6 : rw_cells rsegs m (S + 16 + Z.of_nat 320) [CB 56 j150])
    by (change (Z.of_nat 320) with 320; replace (S + 16 + 320) with (S + 336) by lia; exact H150).
  pose proof (cb_join m (S + 16) 320 56 _ j150 J5 A6) as J6. change (320 + 56)%nat with 376%nat in J6.
  eexists. exact J6.
Qed.
