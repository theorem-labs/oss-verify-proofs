(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the walk of spec_msg_step (fuzz/spec.h:298-363) on the UBSan image, out of line
   at 0x13464 (138 words), against lib/U/Prog/spec_msg_step_c.v. 137 words are walked; the one left is the unimp
   at 0x13688, the target of every UBSan check, and no check branches to it:
   - 0x134a8 `bnez (m & 7)`: m mod 8 = 0;
   - 0x134bc `bltu b + at, b`, 0x134f8 `bltu ~b, i`, 0x135f8 `bltu ~b, data + k`, 0x13630 `bltu ~b, data`,
     0x13664 `bltu ~b, data + 1`: each index is below len, len <= length bs and b + length bs <= 2^64;
   - 0x134cc `beqz ((b != 0) ^ (b + at == 0))` and 0x134d0 `beqz b`: b <> 0.
   The parts:
   - the main theorem: the 48-byte frame (0x13464-0x1347c), memset (m, 0, 56) (0x134a0, memset_holds), whose 56
     zero bytes are read as spec_msg_cells of the zero message, the alignment check, m->at and m->status_out
     (0x134ac / 0x134b0), then `body`;
   - `body` (0x134b4-0x134dc): at >= len ends at 0x13590 (code 0, next = at); else lead = b[at];
   - `f0_path` (lead 0xf0, 0x134e0-0x13570) with `f7_loop`, the F7 scan 0x134f8-0x1350c by induction on the fuel
     of DgnSpec.v's scan_f7;
   - `other_path` (0x13518-0x135a0): lead > 0xf0 (0x13520, SPEC_E_STATUS), a data byte with no running status
     (0x13584, SPEC_E_NO_STATUS), else the status for `data_path`;
   - `data_path` (0x135a4-0x135c0): data = at + (lead >> 7), n = (status & 0xe0) == 0xc0 ? 1 : 2 (n_cond: the
     model's test of status & 0xf0), the length check; `data_n1` / `data_n2` (0x135f0-0x13684) check each data
     byte (0x13604 `bltz` of the `lb`) and write the message;
   - the shared tails `tail_trunc` (0x135c4, next = len), `tail_bad` (0x13650 / 0x13530, next = the byte at or
     above 0x80) and `fin` (0x135d0, the epilogue).
   Byte-valued register forms (sign56, sign56s, shr7, snez1 / snez2, lb_neg, run_bit) are checked over all 256
   values by byte_cases. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import DgnLayout FrameBytes memset_c memset
  spec_msg_step_c.
Import ListNotations.
Open Scope Z_scope.

Lemma le1_lit : forall e, le1 (Z_to_bv 64 e) = [Z_to_bv 8 e].
Proof.
  intros e. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 8 * 2 ^ 56). change (2 ^ Z.of_N 8) with (2 ^ 8).
  rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.

Lemma map_unsigned_inj : forall l1 l2 : list byte, map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as Hxy Hl. f_equal; [apply bv_eq; exact Hxy | apply IH; exact Hl].
Qed.

(* a cell list over the same bytes *)
Lemma rw_cells_conv : forall m A cs1 cs2, rw_cells rsegs m A cs1 -> cells_wf cs2 ->
  map bv_unsigned (cells_bytes cs2) = map bv_unsigned (cells_bytes cs1) -> rw_cells rsegs m A cs2.
Proof.
  intros m A cs1 cs2 [[W1 B1] Wr] W2 E. apply map_unsigned_inj in E.
  split; [split; [exact W2 | rewrite E; exact B1]|].
  rewrite <- (cells_bytes_length cs2 W2), E, (cells_bytes_length cs1 W1). exact Wr.
Qed.

(* the stack below the frame after a callee wrote the cells at A *)
Lemma stk_fill : forall m1 m2 lo hi A cs,
  rw_cells rsegs m2 A cs ->
  stk rsegs m1 lo hi -> munch [(A, A + Z.of_nat (cells_size cs))] m1 m2 -> wmono rsegs m1 m2 ->
  stk rsegs m2 lo hi.
Proof.
  intros m1 m2 lo hi A cs [[Hwf (Ha & Hl & Hb)] _] (H1 & H2 & H) MU WM.
  rewrite cells_bytes_length in Hl, Hb by assumption.
  split; [lia|]. split; [lia|]. intros a Hr.
  destruct (H a Hr) as [Hw (b0 & Hb0)]. split; [apply WM; exact Hw|].
  destruct (Z_lt_le_dec a A) as [L|L]; [|destruct (Z_lt_le_dec a (A + Z.of_nat (cells_size cs))) as [L2|L2]].
  - exists b0. unfold mrd in *. rewrite MU; [exact Hb0|]. cbn [outside]. rewrite wa_unsigned by lia. split; [lia | exact I].
  - replace a with (A + Z.of_nat (Z.to_nat (a - A))) by lia. rewrite Hb by lia.
    destruct (nth_error (cells_bytes cs) (Z.to_nat (a - A))) eqn:E; [eexists; reflexivity|].
    apply nth_error_None in E. rewrite cells_bytes_length in E by assumption. lia.
  - exists b0. unfold mrd in *. rewrite MU; [exact Hb0|]. cbn [outside]. rewrite wa_unsigned by lia. split; [lia | exact I].
Qed.

Lemma byte_at_map : forall (bs : list byte) i,
  byte_at (map bv_unsigned bs) i = bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)).
Proof. intros bs i. unfold byte_at. exact (map_nth bv_unsigned bs (Z_to_bv 8 0) (Z.to_nat i)). Qed.

(* ---- the model's step on each path ---- *)

Lemma model_end : forall bl len pos st, len <= pos ->
  spec_msg_step bl len pos st = SpecMsg 0 pos 0 pos 0 0 0 0 st 0 0.
Proof. intros bl len pos st H. unfold spec_msg_step. rewrite (proj2 (Z.leb_le _ _) H). reflexivity. Qed.

Lemma model_f0 : forall bl len pos st i, pos < len -> byte_at bl pos = 240 ->
  scan_f7 bl len (pos + 1) (Z.to_nat (len - (pos + 1))) = i ->
  spec_msg_step bl len pos st =
  if i =? len then SpecMsg (-6) pos 0 len 0 0 0 0 0 0 0
  else SpecMsg 1 pos (i + 1 - pos) (i + 1) 240 0 0 0 0 (pos + 1) (i - pos - 1).
Proof.
  intros bl len pos st i H1 H2 H3. unfold spec_msg_step. rewrite (proj2 (Z.leb_gt _ _) H1), H2. cbv zeta.
  rewrite H3. reflexivity.
Qed.

Lemma model_f0_trunc : forall bl len pos st, pos < len -> byte_at bl pos = 240 ->
  scan_f7 bl len (pos + 1) (Z.to_nat (len - (pos + 1))) = len ->
  spec_msg_step bl len pos st = SpecMsg (-6) pos 0 len 0 0 0 0 0 0 0.
Proof. intros bl len pos st H1 H2 H3. rewrite (model_f0 _ _ _ _ len H1 H2 H3), Z.eqb_refl. reflexivity. Qed.

Lemma model_f0_ok : forall bl len pos st i, pos < len -> byte_at bl pos = 240 ->
  scan_f7 bl len (pos + 1) (Z.to_nat (len - (pos + 1))) = i -> i <> len ->
  spec_msg_step bl len pos st = SpecMsg 1 pos (i + 1 - pos) (i + 1) 240 0 0 0 0 (pos + 1) (i - pos - 1).
Proof.
  intros bl len pos st i H1 H2 H3 H4. rewrite (model_f0 _ _ _ _ i H1 H2 H3), (proj2 (Z.eqb_neq _ _) H4).
  reflexivity.
Qed.

Lemma scan_range : forall bl len f i, i <= len -> Z.of_nat f = len - i -> i <= scan_f7 bl len i f <= len.
Proof.
  intros bl len f; induction f as [|f IH]; intros i H1 H2; cbn [scan_f7]; [lia|].
  destruct ((i <? len) && negb (byte_at bl i =? 247)) eqn:E; [|lia].
  apply andb_true_iff in E as [E1 _]. apply Z.ltb_lt in E1.
  specialize (IH (i + 1) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma model_status : forall bl len pos st l, pos < len -> byte_at bl pos = l -> 240 < l ->
  spec_msg_step bl len pos st = SpecMsg (-8) pos 0 (pos + 1) 0 0 0 0 0 0 0.
Proof.
  intros bl len pos st l H1 H2 H3. unfold spec_msg_step. rewrite (proj2 (Z.leb_gt _ _) H1), H2. cbv zeta.
  rewrite (proj2 (Z.eqb_neq l 240)) by lia. rewrite (proj2 (Z.ltb_lt 240 l)) by lia. reflexivity.
Qed.

Lemma model_nostatus : forall bl len pos st l, pos < len -> byte_at bl pos = l -> l < 128 -> st = 0 ->
  spec_msg_step bl len pos st = SpecMsg (-7) pos 0 (pos + 1) 0 0 0 0 st 0 0.
Proof.
  intros bl len pos st l H1 H2 H3 H4. subst st. unfold spec_msg_step. rewrite (proj2 (Z.leb_gt _ _) H1), H2.
  cbv zeta. rewrite (proj2 (Z.eqb_neq l 240)) by lia. rewrite (proj2 (Z.ltb_ge 240 l)) by lia.
  rewrite (proj2 (Z.ltb_lt l 128)) by lia. reflexivity.
Qed.

(* ---- byte facts, checked over all 256 values ---- *)

Lemma byte_cases : forall (P : Z -> bool), forallb P (map Z.of_nat (seq 0 256)) = true ->
  forall z, 0 <= z < 256 -> P z = true.
Proof.
  intros P H z Hz. rewrite forallb_forall in H. replace z with (Z.of_nat (Z.to_nat z)) by lia.
  apply H. apply in_map. apply in_seq. lia.
Qed.

(* 0x13574 `slli a1, a2, 0x38` then 0x1359c `bltz a1`: the sign bit of the lead *)
Lemma sign56 : forall x : byte,
  bv_lts (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb x)) 56)) (Z_to_bv 64 0) = (128 <=? bv_unsigned x).
Proof.
  intros x. unfold zxb. rewrite zxb_u. apply Bool.eqb_prop.
  exact (byte_cases (fun z => Bool.eqb (bv_lts (Z_to_bv 64 (Z.shiftl z 56)) (Z_to_bv 64 0)) (128 <=? z))
           ltac:(vm_compute; reflexivity) _ (byte_range x)).
Qed.

(* 0x1357c `srai a0, a1, 0x38` then 0x13580 `bltz a0` *)
Lemma sign56s : forall x : byte,
  bv_lts (Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb x)) 56))) 56)) (Z_to_bv 64 0)
  = (128 <=? bv_unsigned x).
Proof.
  intros x. unfold zxb. rewrite zxb_u. apply Bool.eqb_prop.
  exact (byte_cases (fun z => Bool.eqb (bv_lts (Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl z 56))) 56))
                                               (Z_to_bv 64 0)) (128 <=? z))
           ltac:(vm_compute; reflexivity) _ (byte_range x)).
Qed.

(* 0x135a4 `srli a3, a2, 7`: data = at + (lead >> 7) *)
Lemma shr7 : forall x : byte, Z.shiftr (bv_unsigned (zxb x)) 7 = (if 128 <=? bv_unsigned x then 1 else 0).
Proof.
  intros x. unfold zxb. rewrite zxb_u. apply Z.eqb_eq.
  exact (byte_cases (fun z => Z.shiftr z 7 =? (if 128 <=? z then 1 else 0)) ltac:(vm_compute; reflexivity) _
           (byte_range x)).
Qed.

(* 0x135b0-0x135b8: n = (status & 0xe0) == 0xc0 ? 1 : 2 *)
Lemma snez1 : forall sv, Z.land sv 224 = 192 ->
  bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.land sv 224 + -192))) + 1 = 1.
Proof. intros sv H. rewrite H. vm_compute. reflexivity. Qed.

Lemma snez2 : forall sv, 0 <= sv < 256 -> Z.land sv 224 <> 192 ->
  bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.land sv 224 + -192))) + 1 = 2.
Proof.
  intros sv H1 H2. apply Z.eqb_eq.
  pose proof (byte_cases (fun z => (Z.land z 224 =? 192) ||
    (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.land z 224 + -192))) + 1 =? 2))
    ltac:(vm_compute; reflexivity) _ H1) as E.
  apply orb_true_iff in E. destruct E as [E|E]; [apply Z.eqb_eq in E; contradiction | exact E].
Qed.

(* spec.h:341 as the binary tests it: (status & 0xf0) is 0xc0 or 0xd0 exactly when (status & 0xe0) is 0xc0 *)
Lemma n_cond : forall sv, 0 <= sv < 256 ->
  ((Z.land sv 240 =? 192) || (Z.land sv 240 =? 208)) = (Z.land sv 224 =? 192).
Proof.
  intros sv H. apply Bool.eqb_prop.
  exact (byte_cases (fun z => Bool.eqb ((Z.land z 240 =? 192) || (Z.land z 240 =? 208)) (Z.land z 224 =? 192))
           ltac:(vm_compute; reflexivity) _ H).
Qed.

(* 0x13600 `lb` then 0x13604 `bltz`: the data byte is at or above 0x80 *)
Lemma lb_neg : forall y : byte, bv_lts (sxb y) (Z_to_bv 64 0) = (128 <=? bv_unsigned y).
Proof.
  intros y.
  assert (E : y = Z_to_bv 8 (bv_unsigned y)).
  { apply bv_eq. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range. }
  rewrite E at 1. apply Bool.eqb_prop.
  exact (byte_cases (fun z => Bool.eqb (bv_lts (sxb (Z_to_bv 8 z)) (Z_to_bv 64 0)) (128 <=? z))
           ltac:(vm_compute; reflexivity) _ (byte_range y)).
Qed.

Lemma b8_unsigned : forall y : byte, b8 (bv_unsigned y) = y.
Proof. intros y. unfold b8. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(* 0x13618-0x13620 `not`, `slli 0x38`, `srli 0x3f` then 0x1362c `sb`: running = lead < 0x80 *)
Lemma run_bit : forall x : byte,
  le1 (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64
    (Z.lxor (bv_unsigned (zxb x)) 18446744073709551615))) 56))) 63))
  = [b8 (if bv_unsigned x <? 128 then 1 else 0)].
Proof.
  intros x. rewrite le1_lit. unfold b8, zxb. rewrite zxb_u. do 2 f_equal. apply Z.eqb_eq.
  exact (byte_cases (fun z => Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64
    (Z.lxor z 18446744073709551615))) 56))) 63 =? (if z <? 128 then 1 else 0))
    ltac:(vm_compute; reflexivity) _ (byte_range x)).
Qed.

Lemma model_data : forall bl len pos st l sv dt n, pos < len -> byte_at bl pos = l -> l < 240 ->
  (128 <= l \/ st <> 0) -> sv = (if 128 <=? l then l else st) -> dt = (if 128 <=? l then pos + 1 else pos) ->
  0 <= sv < 256 -> n = (if Z.land sv 224 =? 192 then 1 else 2) ->
  spec_msg_step bl len pos st =
    if len <? dt + n then SpecMsg (-6) pos 0 len 0 0 0 0 st 0 0
    else if 128 <=? byte_at bl dt then SpecMsg (-6) pos 0 dt 0 0 0 0 0 0 0
    else if (n =? 2) && (128 <=? byte_at bl (dt + 1)) then SpecMsg (-6) pos 0 (dt + 1) 0 0 0 0 0 0 0
    else SpecMsg 1 pos (dt + n - pos) (dt + n) sv (if l <? 128 then 1 else 0) (byte_at bl dt)
           (if n =? 2 then byte_at bl (dt + 1) else 0) sv 0 0.
Proof.
  intros bl len pos st l sv dt n H1 H2 H3 H4 H5 H6 H7 H8. unfold spec_msg_step.
  rewrite (proj2 (Z.leb_gt _ _) H1), H2. cbv zeta.
  rewrite (proj2 (Z.eqb_neq l 240)) by lia. rewrite (proj2 (Z.ltb_ge 240 l)) by lia.
  replace ((l <? 128) && (st =? 0)) with false
    by (destruct (Z.ltb_spec l 128); destruct (Z.eqb_spec st 0); cbn; first [reflexivity | exfalso; lia]).
  rewrite <- H5, <- H6, (n_cond sv H7), <- H8. reflexivity.
Qed.

Section Walk.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (b len pos st mp lo : Z) (bs : list byte).

Definition POST (M : spec_msg) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(mp, mp + 56); (bv_unsigned sp + -48, bv_unsigned sp)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
    rw_cells rsegs m' mp (spec_msg_cells M).

(* 0x135d0-0x135ec: reload ra and s0..s4 from the frame, pop it, return *)
Lemma fin : forall (M : spec_msg) (ra' s0' s1' s2' s3' s4' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m2,
  48 <= bv_unsigned sp -> lo <= bv_unsigned sp + -48 ->
  rw_cells rsegs m2 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells rsegs m2 mp (spec_msg_cells M) ->
  stk rsegs m2 lo (bv_unsigned sp + -48) ->
  munch [(mp, mp + 56); (bv_unsigned sp + -48, bv_unsigned sp)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
  evt rsegs (POST M)
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7
             s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x135d0) fc None m2 (seg_rom rsegs)).
Proof.
  intros M ra' s0' s1' s2' s3' s4' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2 HSP HLO FR MC ST MU WM MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  do 8 step.
  apply evt_done. unfold POST. do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [|exact MC].
  release_frame FR ST (bv_unsigned sp). exact ST.
Qed.

Definition FACTS : Prop :=
  0 < b /\ b + Z.of_nat (length bs) <= 2 ^ 64 /\ 0 <= len <= Z.of_nat (length bs) /\ 0 <= pos < 2 ^ 64 /\
  0 <= st < 256 /\ 0 <= mp /\ mp + 56 <= 2 ^ 64 /\ (mp + 56 <= b \/ b + Z.of_nat (length bs) <= mp) /\
  0 <= lo /\ lo + 48 <= bv_unsigned sp /\ bv_unsigned sp < 2 ^ 64 /\
  (mp + 56 <= bv_unsigned sp + -48 \/ bv_unsigned sp <= mp) /\
  (b + Z.of_nat (length bs) <= bv_unsigned sp + -48 \/ bv_unsigned sp <= b).

Definition INV (m2 : word -> option byte) (cs : list cell) : Prop :=
  rw_cells rsegs m2 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
  rw_cells rsegs m2 mp cs /\ bytes_at rsegs m2 b bs /\ stk rsegs m2 lo (bv_unsigned sp + -48) /\
  munch [(mp, mp + 56); (bv_unsigned sp + -48, bv_unsigned sp)] m m2 /\ wmono rsegs m m2 /\ mem_inv rsegs m2.

Local Ltac facts H := destruct H as (Fb & Fbs & Flen & Fpos & Fst & Fmp & Fmp2 & DMB & Flo & HLO & Fsp & DMS & DBS).
Local Ltac unpack H := destruct H as (FR & MC & HB & ST & MU & WM & MI);
  lazymatch goal with Hc : rw_cells _ _ mp _ |- _ =>
    cbv beta iota delta [spec_msg_cells sm_code sm_at sm_len sm_next sm_status sm_running sm_d1 sm_d2 sm_status_out
      sm_sysex_at sm_sysex_len] in Hc end.
Local Ltac fin_ok := eapply fin; [lia | lia | assumption | assumption | assumption | assumption | assumption | assumption].

(* the state of the body: ra = the return address of the memset call, s0 = m, s2 = b, s3 = len, s4 = status_in *)
Local Abbreviation STB pc s1v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2 :=
  (MS (mkR (Z_to_bv 64 79012) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 mp) s1v
           a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 b) (Z_to_bv 64 len) (Z_to_bv 64 st) s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6) F (Z_to_bv 64 pc) fc None m2 (seg_rom rsegs)).

(* 0x135c4-0x135cc: code = SPEC_E_TRUNCATED, next = len *)
Lemma tail_trunc : forall so (s1v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m2,
  FACTS -> INV m2 (spec_msg_cells (SpecMsg 0 pos 0 0 0 0 0 0 so 0 0)) ->
  evt rsegs (POST (SpecMsg (-6) pos 0 len 0 0 0 0 so 0 0))
    (STB 0x135c4 s1v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2).
Proof.
  intros so s1v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2 HF HI. facts HF. unpack HI.
  do 3 step. fin_ok.
Qed.

(* 0x13650-0x13658 and 0x13530: code = SPEC_E_TRUNCATED, next = the data byte at or above 0x80, status_out = 0 *)
Lemma tail_bad : forall nx (s1v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 : word) m2,
  FACTS -> INV m2 (spec_msg_cells (SpecMsg 0 pos 0 0 0 0 0 0 st 0 0)) ->
  evt rsegs (POST (SpecMsg (-6) pos 0 nx 0 0 0 0 0 0 0))
    (STB 0x13650 s1v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 nx) t3 t4 t5 t6 m2).
Proof.
  intros nx s1v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 m2 HF HI. facts HF. unpack HI.
  do 5 step. rewrite le1_lit. mem_after_store. step. fin_ok.
Qed.

Local Ltac inv_ok := unfold INV; repeat (split; [assumption|]); assumption.

(* ~b, the bound of the UBSan check of b + i in the F7 scan (0x134ec `not a2, s2`) *)
Local Abbreviation NB := (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 b)) 18446744073709551615)).

(* the F7 scan 0x134f8-0x1350c from i to the first F7 below len (0x13538) or to len (0x13510), by induction on
   scan_f7's fuel *)
Lemma f7_loop : forall (Q : machine_state -> Prop) f i (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) m2,
  FACTS -> bytes_at rsegs m2 b bs -> pos < i < len -> Z.of_nat f = len - i ->
  (forall a4' : word, scan_f7 (map bv_unsigned bs) len i f < len ->
     evt rsegs Q (STB 0x13538 (Z_to_bv 64 pos) t0 t1 t2 (Z_to_bv 64 (pos + 1))
                   (Z_to_bv 64 (scan_f7 (map bv_unsigned bs) len i f)) NB (Z_to_bv 64 247) a4' a5 a6 a7
                   t3 t4 t5 t6 m2)) ->
  (forall a4' : word, scan_f7 (map bv_unsigned bs) len i f = len ->
     evt rsegs Q (STB 0x13510 (Z_to_bv 64 pos) t0 t1 t2 (Z_to_bv 64 (pos + 1)) (Z_to_bv 64 len) NB
                   (Z_to_bv 64 247) a4' a5 a6 a7 t3 t4 t5 t6 m2)) ->
  evt rsegs Q (STB 0x134f8 (Z_to_bv 64 pos) t0 t1 t2 (Z_to_bv 64 (pos + 1)) (Z_to_bv 64 i) NB (Z_to_bv 64 247)
                 a4 a5 a6 a7 t3 t4 t5 t6 m2).
Proof.
  intros Q f; induction f as [|f IH]; intros i t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m2 HF HB Hi Hf K1 K2; [lia|].
  pose proof HF as HF0. facts HF.
  (* 0x134f8 bltu ~b, i: b + i does not wrap *)
  step. if_cases J1; zify_cond J1; [rewrite zb_lxor_ones in J1 by lia; lia|].
  (* 0x134fc / 0x13500: b[i]; 0x13504 beq b[i], 0xf7 *)
  pose proof (rd1 _ _ _ (Z.to_nat i) HB ltac:(lia)) as RD. rewrite Z2Nat.id in RD by lia.
  pose proof (byte_at_map bs i) as BL.
  do 3 step. if_cases J2; zify_cond J2; rewrite ?zxb_u in J2.
  - assert (E : scan_f7 (map bv_unsigned bs) len i (S f) = i).
    { cbn [scan_f7]. rewrite BL, J2, (proj2 (Z.ltb_lt i len)) by lia. reflexivity. }
    rewrite E in K1. apply K1. lia.
  - assert (E : scan_f7 (map bv_unsigned bs) len i (S f) = scan_f7 (map bv_unsigned bs) len (i + 1) f).
    { cbn [scan_f7]. rewrite BL, (proj2 (Z.eqb_neq _ 247) J2), (proj2 (Z.ltb_lt i len)) by lia. reflexivity. }
    rewrite E in K1, K2.
    (* 0x13508 i++; 0x1350c bne len, i *)
    do 2 step. if_cases J3; zify_cond J3.
    + apply (IH (i + 1)); [exact HF0 | exact HB | lia | lia | exact K1 | exact K2].
    + destruct f as [|f]; [|lia]. replace (i + 1) with len by lia.
      apply K2. cbn [scan_f7]. lia.
Qed.

(* 0x134e0-: the lead byte is 0xf0 *)
Lemma f0_path : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m2,
  FACTS -> INV m2 (spec_msg_cells (SpecMsg 0 pos 0 0 0 0 0 0 st 0 0)) ->
  pos < len -> byte_at (map bv_unsigned bs) pos = 240 ->
  evt rsegs (POST (spec_msg_step (map bv_unsigned bs) len pos st))
    (STB 0x134e0 (Z_to_bv 64 pos) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2).
Proof.
  intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2 HF HI HP HL. pose proof HF as HF0. facts HF. unpack HI.
  (* 0x134e0 i = at + 1; 0x134e8 bgeu i, len *)
  do 3 step. if_cases B1; zify_cond B1.
  - (* 0x13538: status_out = 0; 0x1353c beq i, len: i = at + 1 = len *)
    step. rewrite le1_lit. mem_after_store.
    step. if_cases B2; zify_cond B2; [|lia].
    assert (S0 : scan_f7 (map bv_unsigned bs) len (pos + 1) (Z.to_nat (len - (pos + 1))) = len).
    { replace (Z.to_nat (len - (pos + 1))) with O by lia. cbn [scan_f7]. lia. }
    rewrite (model_f0_trunc _ len pos st HP HL S0).
    eapply tail_trunc; [exact HF0 | inv_ok].
  - (* 0x134ec-0x134f4, then the scan *)
    do 3 step.
    pose proof (scan_range (map bv_unsigned bs) len (Z.to_nat (len - (pos + 1))) (pos + 1) ltac:(lia)
      ltac:(lia)) as SR.
    eapply (f7_loop _ (Z.to_nat (len - (pos + 1))) (pos + 1)); [exact HF0 | exact HB | lia | lia | |].
    + (* an F7 at i < len: 0x13538 status_out = 0; 0x1353c beq i, len not taken; 0x13540-0x13570 *)
      intros a4' HR. set (r := scan_f7 (map bv_unsigned bs) len (pos + 1) (Z.to_nat (len - (pos + 1)))) in *.
      step. rewrite le1_lit. mem_after_store.
      step. if_cases B2; zify_cond B2; [lia|].
      do 10 step. rewrite le1_lit. mem_after_store.
      do 3 step.
      rewrite (model_f0_ok _ len pos st r HP HL eq_refl) by lia.
      rewrite (unsigned_lit (r + 1)), (unsigned_lit pos), zb_lxor_ones in MC by lia.
      replace (Z_to_bv 64 (r + (18446744073709551615 - pos))) with (Z_to_bv 64 (r - pos - 1)) in MC
        by (apply Z_to_bv_eqm; replace (r + (18446744073709551615 - pos)) with (r - pos - 1 + 1 * 2 ^ 64) by lia;
            rewrite Z.mod_add by lia; reflexivity).
      replace (Z_to_bv 8 (-16)) with (b8 240) in MC by (apply bv_eq; vm_compute; reflexivity).
      fin_ok.
    + (* no F7 below len: 0x13510 status_out = 0; 0x13514 j 0x135c4 *)
      intros a4' HR.
      step. rewrite le1_lit. mem_after_store. step.
      rewrite (model_f0_trunc _ len pos st HP HL HR).
      eapply tail_trunc; [exact HF0 | inv_ok].
Qed.

(* the state at 0x135f0, after the length check of a channel message: a0 = status, a1 = data + n, a2 = lead,
   a3 = data, a4 = status & 0xe0, a6 = n *)
Local Abbreviation STD x sv dt n t0 t1 t2 a5 a7 t3 t4 t5 t6 m2 :=
  (STB 0x135f0 (Z_to_bv 64 pos) t0 t1 t2 (Z_to_bv 64 sv) (Z_to_bv 64 (n + dt)) (zxb x) (Z_to_bv 64 dt)
       (Z_to_bv 64 (Z.land sv 224)) a5 (Z_to_bv 64 n) a7 t3 t4 t5 t6 m2).

(* one data byte: 0x135f0-0x13614 *)
Lemma data_n1 : forall (x : byte) sv dt (t0 t1 t2 a5 a7 t3 t4 t5 t6 : word) m2,
  FACTS -> INV m2 (spec_msg_cells (SpecMsg 0 pos 0 0 0 0 0 0 st 0 0)) ->
  pos < len -> byte_at (map bv_unsigned bs) pos = bv_unsigned x -> bv_unsigned x < 240 ->
  (128 <= bv_unsigned x \/ st <> 0) -> sv = (if 128 <=? bv_unsigned x then bv_unsigned x else st) ->
  dt = (if 128 <=? bv_unsigned x then pos + 1 else pos) -> 0 <= sv < 256 ->
  Z.land sv 224 = 192 -> dt + 1 <= len ->
  evt rsegs (POST (spec_msg_step (map bv_unsigned bs) len pos st)) (STD x sv dt 1 t0 t1 t2 a5 a7 t3 t4 t5 t6 m2).
Proof.
  intros x sv dt t0 t1 t2 a5 a7 t3 t4 t5 t6 m2 HF HI HP HL HX HS Esv Edt RS HN HD.
  pose proof HF as HF0. facts HF. unpack HI.
  pose proof (byte_range x) as RX.
  assert (RDT : pos <= dt <= pos + 1) by (rewrite Edt; destruct (128 <=? bv_unsigned x); lia).
  rewrite (model_data _ len pos st (bv_unsigned x) sv dt 1 HP HL HX HS Esv Edt RS)
    by (rewrite HN; reflexivity).
  rewrite (proj2 (Z.ltb_ge len (dt + 1))) by lia.
  (* 0x135f0 ~b; 0x135f4 k = data; 0x135f8 bltu ~b, data: no wrap *)
  do 3 step. if_cases J1; zify_cond J1; [rewrite zb_lxor_ones in J1 by lia; lia|].
  (* 0x135fc / 0x13600 lb b[data]; 0x13604 bltz *)
  pose proof (rd1 _ _ _ (Z.to_nat dt) HB ltac:(lia)) as RD. rewrite Z2Nat.id in RD by lia.
  pose proof (byte_at_map bs dt) as BL1.
  do 3 step. if_cases J2; rewrite lb_neg in J2; zify_bool J2.
  { rewrite BL1, (proj2 (Z.leb_le _ _) J2). eapply tail_bad; [exact HF0 | inv_ok]. }
  rewrite BL1, (proj2 (Z.leb_gt _ _) J2).
  (* 0x13608-0x13610: n - 1 = 0 *)
  do 3 step. if_false.
  (* 0x13614-0x1362c: code = 1, status, running *)
  do 6 step. rewrite le1_lit. mem_after_store.
  step. rewrite run_bit. mem_after_store.
  (* 0x13630 bltu ~b, data; 0x13634-0x13640 d1 = b[data]; 0x13644 bne status & 0xe0, 0xc0 *)
  step. if_cases J3; zify_cond J3; [rewrite zb_lxor_ones in J3 by lia; lia|].
  pose proof (rd1 _ _ _ (Z.to_nat dt) HB ltac:(lia)) as RD2. rewrite Z2Nat.id in RD2 by lia.
  do 4 step. rewrite le1_zxb. mem_after_store.
  step. if_cases J4; zify_cond J4; [lia|].
  (* 0x13648 d2 = 0; 0x13670-0x13680: len, next, d2, status_out *)
  do 6 step. rewrite le1_lit. mem_after_store.
  step. rewrite le1_lit. mem_after_store.
  step.
  rewrite (unsigned_lit (1 + dt)), (unsigned_lit pos) in MC by lia.
  replace (1 + dt) with (dt + 1) in MC by lia.
  rewrite <- (b8_unsigned (nth (Z.to_nat dt) bs (Z_to_bv 8 0))) in MC.
  fin_ok.
Qed.

(* two data bytes: 0x135f0-0x13614 twice, then 0x13660-0x13668 *)
Lemma data_n2 : forall (x : byte) sv dt (t0 t1 t2 a5 a7 t3 t4 t5 t6 : word) m2,
  FACTS -> INV m2 (spec_msg_cells (SpecMsg 0 pos 0 0 0 0 0 0 st 0 0)) ->
  pos < len -> byte_at (map bv_unsigned bs) pos = bv_unsigned x -> bv_unsigned x < 240 ->
  (128 <= bv_unsigned x \/ st <> 0) -> sv = (if 128 <=? bv_unsigned x then bv_unsigned x else st) ->
  dt = (if 128 <=? bv_unsigned x then pos + 1 else pos) -> 0 <= sv < 256 ->
  Z.land sv 224 <> 192 -> dt + 2 <= len ->
  evt rsegs (POST (spec_msg_step (map bv_unsigned bs) len pos st)) (STD x sv dt 2 t0 t1 t2 a5 a7 t3 t4 t5 t6 m2).
Proof.
  intros x sv dt t0 t1 t2 a5 a7 t3 t4 t5 t6 m2 HF HI HP HL HX HS Esv Edt RS HN HD.
  pose proof HF as HF0. facts HF. unpack HI.
  pose proof (byte_range x) as RX.
  assert (RDT : pos <= dt <= pos + 1) by (rewrite Edt; destruct (128 <=? bv_unsigned x); lia).
  rewrite (model_data _ len pos st (bv_unsigned x) sv dt 2 HP HL HX HS Esv Edt RS)
    by (rewrite (proj2 (Z.eqb_neq _ _) HN); reflexivity).
  rewrite (proj2 (Z.ltb_ge len (dt + 2))) by lia.
  (* 0x135f0 ~b; 0x135f4 k = data; 0x135f8 bltu ~b, data: no wrap *)
  do 3 step. if_cases J1; zify_cond J1; [rewrite zb_lxor_ones in J1 by lia; lia|].
  (* 0x135fc / 0x13600 lb b[data]; 0x13604 bltz *)
  pose proof (rd1 _ _ _ (Z.to_nat dt) HB ltac:(lia)) as RD. rewrite Z2Nat.id in RD by lia.
  pose proof (byte_at_map bs dt) as BL1.
  do 3 step. if_cases J2; rewrite lb_neg in J2; zify_bool J2.
  { rewrite BL1, (proj2 (Z.leb_le _ _) J2). eapply tail_bad; [exact HF0 | inv_ok]. }
  rewrite BL1, (proj2 (Z.leb_gt _ _) J2).
  (* 0x13608-0x13610: n - 1 = 1, k = data + 1, back to 0x135f8 *)
  do 3 step. if_true.
  step. if_cases J3; zify_cond J3; [rewrite zb_lxor_ones in J3 by lia; lia|].
  pose proof (rd1 _ _ _ (Z.to_nat (dt + 1)) HB ltac:(lia)) as RD1. rewrite Z2Nat.id in RD1 by lia.
  pose proof (byte_at_map bs (dt + 1)) as BL2.
  do 3 step. if_cases J4; rewrite lb_neg in J4; zify_bool J4.
  { rewrite BL2, (proj2 (Z.leb_le _ _) J4). eapply tail_bad; [exact HF0 | inv_ok]. }
  rewrite BL2, (proj2 (Z.leb_gt _ _) J4).
  do 3 step. if_false.
  (* 0x13614-0x1362c: code = 1, status, running *)
  do 6 step. rewrite le1_lit. mem_after_store.
  step. rewrite run_bit. mem_after_store.
  (* 0x13630 bltu ~b, data; 0x13634-0x13640 d1 = b[data]; 0x13644 bne status & 0xe0, 0xc0 *)
  step. if_cases J5; zify_cond J5; [rewrite zb_lxor_ones in J5 by lia; lia|].
  pose proof (rd1 _ _ _ (Z.to_nat dt) HB ltac:(lia)) as RD2. rewrite Z2Nat.id in RD2 by lia.
  do 4 step. rewrite le1_zxb. mem_after_store.
  step. if_cases J6; zify_cond J6; [|lia].
  (* 0x13660 / 0x13664 bltu ~b, data + 1; 0x13668 / 0x1366c d2 = b[data + 1]; 0x13670-0x13680 *)
  do 2 step. if_cases J7; zify_cond J7; [rewrite zb_lxor_ones in J7 by lia; lia|].
  pose proof (rd1 _ _ _ (Z.to_nat (dt + 1)) HB ltac:(lia)) as RD3. rewrite Z2Nat.id in RD3 by lia.
  do 6 step. rewrite le1_zxb. mem_after_store.
  step. rewrite le1_lit. mem_after_store.
  step.
  rewrite (unsigned_lit (2 + dt)), (unsigned_lit pos) in MC by lia.
  replace (2 + dt) with (dt + 2) in MC by lia.
  rewrite <- (b8_unsigned (nth (Z.to_nat dt) bs (Z_to_bv 8 0))) in MC.
  rewrite <- (b8_unsigned (nth (Z.to_nat (dt + 1)) bs (Z_to_bv 8 0))) in MC.
  fin_ok.
Qed.

(* 0x135a4-0x135c0: data, n and the length check of a channel message; sv is its status (the lead byte, or
   status_in for running status) *)
Lemma data_path : forall (x : byte) sv (t0 t1 t2 a1 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m2,
  FACTS -> INV m2 (spec_msg_cells (SpecMsg 0 pos 0 0 0 0 0 0 st 0 0)) ->
  pos < len -> byte_at (map bv_unsigned bs) pos = bv_unsigned x -> bv_unsigned x < 240 ->
  (128 <= bv_unsigned x \/ st <> 0) -> sv = (if 128 <=? bv_unsigned x then bv_unsigned x else st) ->
  evt rsegs (POST (spec_msg_step (map bv_unsigned bs) len pos st))
    (STB 0x135a4 (Z_to_bv 64 pos) t0 t1 t2 (Z_to_bv 64 sv) a1 (zxb x) a3 a4 a5 a6 a7 t3 t4 t5 t6 m2).
Proof.
  intros x sv t0 t1 t2 a1 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2 HF HI HP HL HX HS Esv.
  pose proof HF as HF0. facts HF. pose proof HI as HI0. unpack HI.
  pose proof (byte_range x) as RX.
  assert (RS : 0 <= sv < 256) by (rewrite Esv; destruct (128 <=? bv_unsigned x); lia).
  remember (if 128 <=? bv_unsigned x then pos + 1 else pos) as dt eqn:Edt.
  assert (DT : pos + Z.shiftr (bv_unsigned (zxb x)) 7 = dt)
    by (rewrite Edt, shr7; destruct (128 <=? bv_unsigned x); lia).
  assert (RDT : pos <= dt <= pos + 1) by (rewrite Edt; destruct (128 <=? bv_unsigned x); lia).
  do 8 step. rewrite DT, (unsigned_lit sv) by lia.
  destruct (Z.eqb_spec (Z.land sv 224) 192) as [HN|HN].
  - rewrite (snez1 sv HN).
    if_cases J; zify_cond J.
    + eapply data_n1; eassumption || lia.
    + rewrite (model_data _ len pos st (bv_unsigned x) sv dt 1 HP HL HX HS Esv Edt RS)
        by (rewrite HN; reflexivity).
      rewrite (proj2 (Z.ltb_lt len (dt + 1))) by lia.
      eapply tail_trunc; [exact HF0 | exact HI0].
  - rewrite (snez2 sv RS HN).
    if_cases J; zify_cond J.
    + eapply data_n2; eassumption || lia.
    + rewrite (model_data _ len pos st (bv_unsigned x) sv dt 2 HP HL HX HS Esv Edt RS)
        by (rewrite (proj2 (Z.eqb_neq _ _) HN); reflexivity).
      rewrite (proj2 (Z.ltb_lt len (dt + 2))) by lia.
      eapply tail_trunc; [exact HF0 | exact HI0].
Qed.

(* 0x13518-: the lead byte x is not 0xf0 *)
Lemma other_path : forall (x : byte) (t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m2,
  FACTS -> INV m2 (spec_msg_cells (SpecMsg 0 pos 0 0 0 0 0 0 st 0 0)) ->
  pos < len -> byte_at (map bv_unsigned bs) pos = bv_unsigned x -> bv_unsigned x <> 240 ->
  evt rsegs (POST (spec_msg_step (map bv_unsigned bs) len pos st))
    (STB 0x13518 (Z_to_bv 64 pos) t0 t1 t2 a0 a1 (zxb x) a3 a4 a5 a6 a7 t3 t4 t5 t6 m2).
Proof.
  intros x t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2 HF HI HP HL HX. pose proof HF as HF0. facts HF. unpack HI.
  pose proof (byte_range x) as RX.
  (* 0x13518 / 0x1351c bltu lead, 0xf1 *)
  do 2 step. if_cases B1; zify_cond B1; rewrite ?zxb_u in B1.
  - (* 0x13574 the lead's sign bit at bit 63; 0x13578 bnez status_in *)
    do 2 step. if_cases B2; zify_cond B2.
    + (* 0x13598 status = lead; 0x1359c bltz: lead >= 0x80 keeps it, else 0x135a0 status = status_in *)
      do 2 step. if_cases B3; rewrite sign56 in B3; zify_bool B3.
      * eapply data_path; [exact HF0 | inv_ok | exact HP | exact HL | lia | lia |].
        rewrite (proj2 (Z.leb_le _ _) B3). reflexivity.
      * step. eapply data_path; [exact HF0 | inv_ok | exact HP | exact HL | lia | lia |].
        rewrite (proj2 (Z.leb_gt _ _) B3). reflexivity.
    + (* 0x1357c srai / 0x13580 bltz: lead >= 0x80 goes to 0x13598 *)
      do 2 step. if_cases B3; rewrite sign56s in B3; zify_bool B3.
      * do 2 step. if_cases B4; rewrite sign56 in B4; zify_bool B4; [|lia].
        eapply data_path; [exact HF0 | inv_ok | exact HP | exact HL | lia | lia |].
        rewrite (proj2 (Z.leb_le _ _) B3). reflexivity.
      * (* 0x13584-0x13594: code = SPEC_E_NO_STATUS, next = at + 1 *)
        do 5 step. rewrite (model_nostatus _ len pos st (bv_unsigned x) HP HL) by lia. fin_ok.
  - (* 0x13520-0x13534: code = SPEC_E_STATUS, next = at + 1, status_out = 0 *)
    do 5 step. rewrite le1_lit. mem_after_store. step.
    rewrite (model_status _ len pos st (bv_unsigned x) HP HL) by lia. fin_ok.
Qed.

Lemma body : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m2,
  FACTS -> INV m2 (spec_msg_cells (SpecMsg 0 pos 0 0 0 0 0 0 st 0 0)) ->
  evt rsegs (POST (spec_msg_step (map bv_unsigned bs) len pos st))
    (STB 0x134b4 (Z_to_bv 64 pos) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2).
Proof.
  intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2 HF HI. pose proof HF as HF0. facts HF. unpack HI.
  (* 0x134b4 bgeu s1, s3: at >= len *)
  step. if_cases B1; zify_cond B1.
  - (* 0x13590: next = at; 0x13594 j *)
    do 2 step. rewrite (model_end _ len pos st B1). fin_ok.
  - (* 0x134b8 / 0x134bc: b + at does not wrap *)
    do 2 step. if_cases B2; zify_cond B2; [lia|].
    (* 0x134c0-0x134cc: exactly one of b, b + at NULL: neither is *)
    do 4 step. if_cases B3; zify_cond B3.
    { rewrite (proj2 (Z.ltb_lt 0 b)), (proj2 (Z.ltb_ge (b + pos) 1)) in B3 by lia. cbn in B3. discriminate B3. }
    (* 0x134d0 beqz s2: b is not NULL *)
    step. if_cases B4; zify_cond B4; [lia|].
    (* 0x134d4 lbu a2, 0(a0): lead = b[at]; 0x134dc bne lead, 0xf0 *)
    pose proof (rd1 _ _ _ (Z.to_nat pos) HB ltac:(lia)) as RD. rewrite Z2Nat.id in RD by lia.
    pose proof (byte_at_map bs pos) as BL.
    do 3 step. if_cases B5; zify_cond B5; rewrite ?zxb_u in B5.
    + eapply other_path; [exact HF0 | inv_ok | exact B1 | exact BL | exact B5].
    + eapply f0_path; [exact HF0 | inv_ok | exact B1 | rewrite BL; exact B5].
Qed.

End Walk.

Theorem spec_msg_step_holds : spec_msg_step_contract.
Proof.
  unfold spec_msg_step_contract, SPEC_MSG_STEP, SPEC_MSG_STEP_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    b len pos st mp lo bs junk HB0 HLEN HPOS HST HB HAL HMC DMB ST HLO DMS DBS MI.
  pose proof (rw_cells_bound _ _ _ _ HMC) as RMC. cbn [cells_size csize Nat.add] in RMC.
  pose proof (bytes_at_bound _ _ _ _ HB) as RB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. change (2 ^ Z.of_N 64) with (2 ^ 64) in RSP.
  pose proof ST as (Hlo0 & _ & _).
  pose proof (munch_refl [(mp, mp + 56); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  do 16 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    eapply evt_cut; [eapply memset_holds | ];
    [ rewrite (unsigned_lit mp) by lia; exact HMC
    | exact MI
    | intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> &
                  MUc & WMc & MIc & CHc);
      rewrite (unsigned_lit mp) in MUc, CHc by lia;
      replace (bv_unsigned (Z_to_bv 64 56)) with 56 in MUc, CHc by (vm_compute; reflexivity);
      pose proof (stk_fill _ _ _ _ _ _ CHc ST MUc WMc) as ST2; clear ST; rename ST2 into ST;
      clear HMC; transport_after_call rsegs m1 m2 MUc WMc; clear MUc WMc;
      repeat match goal with H : mem_inv rsegs m1 |- _ => clear H end ]
  end.
  replace (ret_pc (Z_to_bv 64 79012)) with (Z_to_bv 64 79012) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  change (Z.to_nat 56) with 56%nat in CHc.
  apply (rw_cells_conv _ _ _ (spec_msg_cells (SpecMsg 0 0 0 0 0 0 0 0 0 0 0))) in CHc;
    [ | cbn; repeat split; reflexivity | vm_compute; reflexivity ].
  cbv beta iota delta [spec_msg_cells sm_code sm_at sm_len sm_next sm_status sm_running sm_d1 sm_d2 sm_status_out
    sm_sysex_at sm_sysex_len] in CHc.
  assert (L7 : Z.land mp 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; exact HAL).
  (* 0x134a4 / 0x134a8: the alignment check of m->at, not taken by mp mod 8 = 0 *)
  step. step. rewrite (unsigned_lit mp), L7 by lia. if_false.
  (* 0x134ac: m->at = at; 0x134b0: m->status_out = status_in *)
  step. step. rewrite le1_lit. mem_after_store.
  eapply (body ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m b len pos st mp lo bs).
  - unfold FACTS. repeat split; lia.
  - exact (conj FR (conj CHc (conj HB (conj ST (conj MU (conj WM MIc)))))).
Qed.
