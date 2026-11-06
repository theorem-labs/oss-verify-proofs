(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 552 of its 576 lines of code are new or changed and 120 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/U/Prog/diginet_sysex_encode.v, with its addresses and numbers changed; 210 of its 285 lines of code are new or changed and 501 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells diginet_sysex_encode_c
  diginet_counter_encode_c.
Import ListNotations.
Open Scope Z_scope.

(** diginet_counter_encode of the UBSan image (0x16174, 48 instructions, frame 0x30), walked with the tactics of
    libreac/fuzz_knock's walks (Lib/Tac.v, Lib/Step.v). Paths: seg, p and out NULL tests (p NULL returns E_ARG;
    seg and out are not NULL by the premises), the UBSan alignment test of p (p is 8-aligned), pl[0] = p->counter_addr
    and pl[1] = dots stored in the frame at sp' + 14 (the pointer test of pl + 1 is not taken), the copy of seg[7..0]
    to pl[2..10) (eight iterations, unrolled; the pointer test of seg + 7 is not taken), the call of
    diginet_sysex_encode (device, 0x30, pl, 10, out) under its contract, and on its success the alignment test of
    out and the key store p->counter_addr | 0x60000 at out + 28. The personality bytes are read from p + 16, outside
    the frame and outside out (the premises), so the frame stores and the callee keep them. *)

#[local] Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

#[local] Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(* The callee's footprint has two intervals: prove each piece of a nested conjunction. *)
#[local] Ltac slia ::= first [ exact I | lia | split; [ lia | slia ] ].

(* ---- facts ---- *)

Lemma cx_b8 : forall x, 0 <= x < 256 -> bv_unsigned (b8 x) = x.
Proof. intros x Hx. unfold b8. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

Lemma cx_bb : forall b : byte, bv_unsigned (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (bv_unsigned b)))) = bv_unsigned b.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  rewrite unsigned_lit by lia. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia.
Qed.

Lemma cx_zz : forall x, 0 <= x < 256 -> bv_unsigned (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 x))) = x.
Proof.
  intros x Hx. rewrite unsigned_lit by lia. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia.
Qed.

Lemma cx_land_mod : forall x k, 0 <= k -> Z.land x (Z.ones k) = x mod 2 ^ k.
Proof. intros. apply Z.land_ones. lia. Qed.

Lemma cx_key6 : forall c, 0 <= c < 256 -> Z.lor c 393216 = KEY 6 c.
Proof.
  intros c Hc.
  assert (C : forallb (fun x => Z.lor x 393216 =? KEY 6 x) (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in C.
  assert (Hin : In c (map Z.of_nat (seq 0 256))).
  { apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia. }
  apply Z.eqb_eq. exact (C c Hin).
Qed.

(** sysex_encode either fails without a command or succeeds with key 0 and at most 24 bytes. *)
Lemma cx_sysex_shape : forall dev fn pl,
  (exists rc, sysex_spec dev fn pl = (rc, None) /\ -11 <= rc <= -1) \/
  (exists bs dp, sysex_spec dev fn pl = (0, Some (bs, 0, dp)) /\ (length bs <= 24)%nat).
Proof.
  intros dev fn pl. unfold sysex_spec.
  destruct (0x7f <? dev); [left; eexists; split; [reflexivity | unfold E_ARG; lia] |].
  destruct (fn =? 0x70); [left; eexists; split; [reflexivity | unfold E_REFUSED; lia] |].
  destruct (0x7f <? fn); [left; eexists; split; [reflexivity | unfold E_RANGE; lia] |].
  destruct (24 <? Z.of_nat (length pl) + 5) eqn:E4; [left; eexists; split; [reflexivity | unfold E_SPACE; lia] |].
  destruct (existsb (fun x => Z.testbit x 7) pl); [left; eexists; split; [reflexivity | unfold E_RANGE; lia] |].
  right. do 2 eexists. split; [reflexivity|].
  apply Z.ltb_ge in E4. rewrite !length_app. cbn [length]. lia.
Qed.

Lemma cx_with_key_none : forall rc k, with_key (rc, None) k = (rc, None).
Proof. intros [|q|q] k; reflexivity. Qed.

(** The command bytes with the key of a successful command replaced. *)
Lemma cx_cmd_out_key : forall before bs dp k0 k v,
  length before = 32%nat -> (length bs <= 24)%nat -> v = Z_to_bv 64 k ->
  firstn 28 (cmd_out before (Some (bs, k0, dp))) ++ le4 v = cmd_out before (Some (bs, k, dp)).
Proof.
  intros before bs dp k0 k v Lb Ls ->.
  assert (HP : forall P Q R : list byte, length P = 28%nat -> firstn 28 (P ++ Q) ++ R = P ++ R).
  { intros P Q R HL. rewrite firstn_app, HL, Nat.sub_diag. cbn [firstn app].
    rewrite app_nil_r, firstn_all2 by lia. reflexivity. }
  unfold cmd_out. rewrite !app_assoc. apply HP.
  unfold bz. rewrite ?length_app, ?length_map, ?length_skipn, ?length_firstn, ?length_skipn.
  rewrite Lb. cbn [length]. lia.
Qed.

Lemma cx_rw_cells_eq : forall m A A' cs cs', rw_cells rsegs m A cs -> A = A' -> cs = cs' -> rw_cells rsegs m A' cs'.
Proof. intros; subst; assumption. Qed.

Lemma cx_rw_cells_to_CB : forall m A cs n bs,
  rw_cells rsegs m A cs -> cells_size cs = n -> cells_bytes cs = bs -> rw_cells rsegs m A [CB n bs].
Proof.
  intros m A cs n bs H Hn Hb. subst n bs.
  pose proof (rw_cells_merge rsegs m A [] cs []) as M. rewrite app_nil_r in M. cbn [app] in M. apply M. exact H.
Qed.

(* The bytes of the middle cells of a frame (behind its first cell). *)
Lemma cx_mid_bytes : forall m A x c2 c3,
  rw_cells rsegs m A (x :: c2 ++ c3) -> bytes_at rsegs m (A + Z.of_nat (csize x)) (cells_bytes c2).
Proof.
  intros m A x c2 c3 [[Hwf Hb] _]. cbn [cells_bytes] in Hb. rewrite cells_bytes_app in Hb.
  apply bytes_at_app in Hb. destruct Hb as [_ Hb]. apply bytes_at_app in Hb. destruct Hb as [Hb _].
  destruct Hwf as [Wx _]. rewrite cbytes_length in Hb by exact Wx. exact Hb.
Qed.

(* ---- the walk ---- *)

Section CX.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
          (m : word -> option byte) (lo : Z) (pd : option desk) (dots : Z) (sg before : list byte) (p sga out : word).

Definition Qx (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 96, bv_unsigned sp); (bv_unsigned out, bv_unsigned out + 32)] m m' /\
    wmono rsegs m m' /\
    mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp) /\
    let '(rc, o) := counter_spec pd (zb sg) dots in
    a0' = Z_to_bv 64 rc /\ rw_cells rsegs m' (bv_unsigned out) [CB 32 (cmd_out before o)].

Hypothesis LO : lo + 96 <= bv_unsigned sp.
Hypothesis LO0 : 0 <= lo.
Hypothesis RDOTS : 0 <= dots < 256.
Hypothesis HSG : bv_unsigned sga <> 0.
Hypothesis HOUT : bv_unsigned out <> 0.
Hypothesis OUT4 : bv_unsigned out mod 4 = 0.
Hypothesis SPS : bv_unsigned sp <= bv_unsigned sga.
Hypothesis SPO : bv_unsigned sp <= bv_unsigned out.
Hypothesis OUTB : bv_unsigned out + 32 <= 2 ^ 64.
Hypothesis BLEN : length before = 32%nat.
Hypothesis SYSEX : diginet_sysex_encode_contract.

Lemma cx_exit : forall (j : list byte) (ra' t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                       (m1 : word -> option byte) (rc : Z) (o : option cmd),
  counter_spec pd (zb sg) dots = (rc, o) ->
  a0' = Z_to_bv 64 rc ->
  rw_cells rsegs m1 (bv_unsigned sp + -48) [CB 24 j; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m1 lo (bv_unsigned sp + -48) ->
  rw_cells rsegs m1 (bv_unsigned out) [CB 32 (cmd_out before o)] ->
  munch [(bv_unsigned sp - 96, bv_unsigned sp); (bv_unsigned out, bv_unsigned out + 32)] m m1 ->
  wmono rsegs m m1 -> mem_inv rsegs m1 ->
  evt rsegs Qx
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7'
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x1621c) fc None m1 (seg_rom rsegs)).
Proof.
  intros j ra' t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m1 rc o
    E HA0 FR ST OUT MU WM HMI.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  do 4 zstep.
  eapply stk_release in FR; [ | exact ST | lia ].
  cbn [cells_size csize Nat.add] in FR.
  replace (bv_unsigned sp + -48 + Z.of_nat 48) with (bv_unsigned sp) in FR by lia.
  clear ST.
  zstep.
  finish.
  all: try (rewrite E; split; assumption).
Qed.

Lemma cx_none : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  pd = None -> p = Z_to_bv 64 0 ->
  rw_cells rsegs m (bv_unsigned out) [CB 32 before] ->
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) ->
  evt rsegs Qx
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 p sga (Z_to_bv 64 dots) out a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16174) fc None m (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 Hpd Hp OUT HMI ST. subst p.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 out) as Rout. unfold bv_modulus in Rout.
  carve_frame 48%nat ST.
  assert (MU : munch [(bv_unsigned sp - 96, bv_unsigned sp); (bv_unsigned out, bv_unsigned out + 32)] m m)
    by apply munch_refl.
  assert (WM : wmono rsegs m m) by apply wmono_refl.
  (* addi sp; sd ra; sd s0; sd s1; mv s1, a0; addi a0, zero, -1; beqz a1 *)
  do 6 zstep. zstep.
  if_cases K1. { zify_cond K1. exfalso. lia. }
  (* beqz s1: p = 0 *)
  zstep.
  if_cases K2.
  - eapply cx_exit with (rc := E_ARG) (o := None);
      [ rewrite Hpd; reflexivity | reflexivity | exact FR | exact ST | exact OUT | exact MU | exact WM | exact HMI ].
  - zify_cond K2. exfalso. cbn in K2. lia.
Qed.

Lemma cx_some : forall (d : desk) (g0 g1 g2 g3 g4 g5 g6 g7 : byte) (rest : list byte)
                       (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  pd = Some d -> sg = g0 :: g1 :: g2 :: g3 :: g4 :: g5 :: g6 :: g7 :: rest ->
  desk_ok d -> bv_unsigned p <> 0 -> bv_unsigned p mod 8 = 0 ->
  bv_unsigned p + 16 + 4 <= bv_unsigned sp - 96 \/ bv_unsigned sp - 96 + 96 <= bv_unsigned p + 16 ->
  bv_unsigned p + 16 + 4 <= bv_unsigned out \/ bv_unsigned out + 32 <= bv_unsigned p + 16 ->
  ro_cells rsegs m (bv_unsigned p + 16) [C1 (b8 (d_dev d)); C1 (b8 (d_strips d)); C1 (b8 (d_chars d)); C1 (b8 (d_counter d))] ->
  ro_cells rsegs m (bv_unsigned sga) [C1 g0; C1 g1; C1 g2; C1 g3; C1 g4; C1 g5; C1 g6; C1 g7] ->
  rw_cells rsegs m (bv_unsigned out) [CB 32 before] ->
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) ->
  evt rsegs Qx
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 p sga (Z_to_bv 64 dots) out a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16174) fc None m (seg_rom rsegs)).
Proof.
  intros d g0 g1 g2 g3 g4 g5 g6 g7 rest t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 Hpd Hsg DOK HP0 HP8 D1 D2 PR SGC OUT HMI ST.
  unfold desk_ok in DOK.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 out) as Rout. unfold bv_modulus in Rout.
  pose proof (bv_unsigned_in_range 64 p) as Rp. unfold bv_modulus in Rp.
  pose proof (ro_cells_bound rsegs m _ _ SGC) as BSG. cbn [cells_size csize] in BSG.
  carve_frame 48%nat ST.
  assert (MU : munch [(bv_unsigned sp - 96, bv_unsigned sp); (bv_unsigned out, bv_unsigned out + 32)] m m)
    by apply munch_refl.
  assert (WM : wmono rsegs m m) by apply wmono_refl.
  (* addi sp; sd ra; sd s0; sd s1; mv s1, a0; addi a0, zero, -1; beqz a1 *)
  do 6 zstep. zstep.
  if_cases K1. { zify_cond K1. exfalso. lia. }
  (* beqz s1 *)
  zstep.
  if_cases K2. { zify_cond K2. exfalso. lia. }
  (* mv s0, a3; beqz a3 *)
  zstep. zstep.
  if_cases K3. { zify_cond K3. exfalso. lia. }
  (* andi a0, s1, 7; bnez a0 (UBSan alignment of p) *)
  zstep. zstep.
  if_cases K4.
  { zify_cond K4. exfalso. change 7 with (Z.ones 3) in K4. rewrite cx_land_mod in K4 by lia. apply K4. exact HP8. }
  (* lbu a0, 0x13(s1); addi a3, zero, -1; addi a4, sp, 0xe; sb a0, 0xe(sp); beq a4, a3 (UBSan pl + 1) *)
  do 5 zstep.
  if_cases K5. { zify_cond K5. exfalso. lia. }
  (* sb a2, 0xf(sp); addi a0, sp, 0x10; addi a2, a1, 7; addi a3, zero, 8; addi a4, zero, -8 *)
  do 5 zstep.
  (* the copy loop, eight iterations: bltu a4, a1 (UBSan seg + 7); lbu; addi; sb; addi; addi; bnez *)
  do 7 (zstep; if_false; do 5 zstep; zstep; if_true).
  zstep; if_false; do 5 zstep; zstep; if_false.
  (* the payload, then the frame as one cell before its saved registers *)
  match type of FR with
  | rw_cells ?sg' ?mm ?A (?x :: ?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?post) =>
      pose proof (cx_mid_bytes mm A x [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9] post FR) as PB;
      pose proof (rw_cells_merge sg' mm A [] (x :: [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9]) post FR) as FR';
      clear FR
  end.
  cbn [cells_size csize Nat.add app] in FR'. cbn [cells_bytes cbytes app] in PB.
  replace (bv_unsigned sp + -48 + Z.of_nat (csize (CB 14 _))) with (bv_unsigned sp + -34) in PB
    by (cbn [csize]; lia).
  (* lbu a0, 0x10(s1); addi a1, zero, 0x30; addi a2, sp, 0xe; addi a3, zero, 0xa; mv a4, s0; jal diginet_sysex_encode *)
  do 6 zstep.
  assert (Esp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  unfold diginet_sysex_encode_contract, DIGINET_SYSEX_ENCODE, DIGINET_SYSEX_ENCODE_DEPTH in SYSEX.
  lazymatch goal with
  | PB : bytes_at _ _ _ ?pl10 |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply SYSEX with (lo := lo) (dev := d_dev d) (fn := 48) (pl := pl10) (before := before);
      unfold diginet_sysex_encode_pre, DIGINET_SYSEX_ENCODE_DEPTH, arg_zx, disj;
      repeat (match goal with |- _ /\ _ => split end);
      rewrite ?unsigned_lit by lia;
      first [ assumption | lia | reflexivity | (rewrite cx_b8 by lia; reflexivity) | (rewrite Esp; exact ST)
            | (cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia) ]
    | post_call rsegs mm ]
  end.
  match goal with H : stk rsegs _ lo (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48))) |- _ => rewrite Esp in H end.
  match goal with H : context [sysex_spec] |- _ => rename H into SXP end.
  (* the payload as the model's list *)
  lazymatch type of SXP with context [sysex_spec _ _ (zb ?pl10)] =>
    assert (CS : counter_spec pd (zb sg) dots = with_key (sysex_spec (d_dev d) 48 (zb pl10)) (KEY 6 (d_counter d)))
  end.
  { rewrite Hpd, Hsg. unfold counter_spec. f_equal. f_equal.
    unfold zb. cbn [map firstn rev app].
    rewrite !cx_bb, !cx_zz by lia. rewrite !cx_b8 by lia. reflexivity. }
  lazymatch type of SXP with context [sysex_spec ?dv ?fv ?plz] =>
    destruct (cx_sysex_shape dv fv plz) as [(rc & ESX & RC) | (bs & dp & ESX & LBS)];
    rewrite ESX in SXP, CS; destruct SXP as [HA0 OUT2]; subst
  end.
  - (* sysex_encode failed: bnez a0 is taken *)
    zstep.
    if_cases K.
    + eapply cx_exit with (rc := rc) (o := None);
        [ rewrite CS; apply cx_with_key_none | reflexivity | eassumption | eassumption | exact OUT2
        | eassumption | eassumption | eassumption ].
    + zify_cond K. exfalso. lia.
  - (* success: andi a1, s0, 3; bnez a1 (UBSan alignment of out); lbu a1, 0x13(s1); lui; or; sw a1, 0x1c(s0) *)
    zstep.
    if_cases K. { zify_cond K. exfalso. lia. }
    zstep. zstep.
    if_cases K'.
    { zify_cond K'. exfalso. change 3 with (Z.ones 2) in K'. rewrite cx_land_mod in K' by lia. apply K'. exact OUT4. }
    do 4 zstep.
    eapply cx_exit with (rc := 0) (o := Some (bs, KEY 6 (d_counter d), dp));
      [ rewrite CS; reflexivity | reflexivity | eassumption | eassumption | | eassumption | eassumption | eassumption ].
    eapply cx_rw_cells_to_CB; [ exact OUT2 | reflexivity | ].
    cbn [cells_bytes cbytes]. rewrite app_nil_r.
    apply cx_cmd_out_key; [ exact BLEN | exact LBS | ].
    rewrite cx_b8 by lia. f_equal. apply cx_key6. lia.
Qed.

End CX.

Theorem diginet_counter_encode_holds : diginet_sysex_encode_contract -> diginet_counter_encode_contract.
Proof.
  intros SYSEX. unfold diginet_counter_encode_contract, DIGINET_COUNTER_ENCODE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo pd dots sg before PRE.
  unfold diginet_counter_encode_pre, DIGINET_COUNTER_ENCODE_DEPTH in *.
  destruct PRE as (PA & D1 & D2 & HA1 & HSGB & HL8 & HDOTS & HA3 & OUT & O4 & SPA1 & SPA3 & HMI & ST & LO).
  destruct HDOTS as [RDOTS ->]. change (2 ^ 8) with 256 in RDOTS.
  pose proof (rw_cells_bound rsegs m _ _ OUT) as OB. cbn [cells_size csize] in OB.
  pose proof OUT as [[[BL _] _] _]. cbn in BL.
  pose proof ST as [LO0 _].
  change (evt rsegs (Qx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo pd dots sg before a3)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 dots) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16174) fc None m (seg_rom rsegs))).
  destruct pd as [d|].
  - destruct PA as (HP0 & HP8 & DOK & HPB).
    specialize (D1 d eq_refl). specialize (D2 d eq_refl). unfold disj in D1, D2.
    destruct sg as [|g0 [|g1 [|g2 [|g3 [|g4 [|g5 [|g6 [|g7 rest]]]]]]]]; try (cbn in HL8; lia).
    change (g0 :: g1 :: g2 :: g3 :: g4 :: g5 :: g6 :: g7 :: rest)
      with ([g0; g1; g2; g3; g4; g5; g6; g7] ++ rest) in HSGB.
    apply bytes_at_app in HSGB. destruct HSGB as [HSG8 _].
    eapply (cx_some ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo (Some d) dots _ before a0 a1 a3)
      with (d := d); try reflexivity; try assumption; try lia.
    + split; [ repeat split | exact HPB ].
    + split; [ repeat split | exact HSG8 ].
  - eapply (cx_none ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo None dots sg before a0 a1 a3);
      try reflexivity; try assumption; lia.
Qed.
