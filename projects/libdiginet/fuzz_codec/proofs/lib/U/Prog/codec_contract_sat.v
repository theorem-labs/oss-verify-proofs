From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells codec_img.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import
  check_bytes_c check_personality_c check_range_c check_refusal_c check_text_counter_c check_text_masks_c check_text_scribble_c check_text_seg7_c diginet_button_encode_c diginet_counter_encode_c diginet_counter_leds_encode_c diginet_counter_text_c diginet_fader_encode_c diginet_jog_encode_c diginet_meter_encode_c diginet_meter_mask_c diginet_meter_segments_c diginet_personality_from_name_c diginet_ring_dot_c diginet_ring_encode_c diginet_ring_fill_c diginet_scribble_encode_c diginet_scribble_text_c diginet_seg7_c diginet_strip_leds_encode_c diginet_sysex_encode_c diginet_touch_encode_c diginet_vpot_encode_c leds_encode_c owe_sysex_c owed_counter_text_c owed_seg7_c text_arg_c LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

(** Satisfiability of the contracts of fuzz_codec's own functions in the UBSan image: for each call site of
    each contract, a closed lemma that its premises hold in one concrete state of the real image (rsegs) with
    the registers the caller sets there. The witness memory is a 64 KiB stack window [SAT_LO, SAT_HI) above
    the image, zero except for the bytes listed per site; below it every read is the image's.
    LLVMFuzzerTestOneInput's frame in the witness: entry sp SAT_SP, sp after the prologue MSP, k at SK. *)

(** ---- the witness memory ---- *)

Definition SAT_LO : Z := 0x7ff0000.
Definition SAT_HI : Z := 0x8000000.

Fixpoint fill (l : list (Z * list byte)) (x : Z) : byte :=
  match l with
  | [] => b8 0
  | (a, bs) :: l' =>
      if (a <=? x) && (x <? a + Z.of_nat (length bs)) then nth (Z.to_nat (x - a)) bs (b8 0) else fill l' x
  end.

Definition smem (l : list (Z * list byte)) : word -> option byte :=
  fun w => if (SAT_LO <=? bv_unsigned w) && (bv_unsigned w <? SAT_HI) then Some (fill l (bv_unsigned w)) else None.

Lemma segs_below : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? SAT_LO) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma find_segment_above : forall segs x, forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? x) segs = true ->
  forall y, x <= y -> find_segment segs y 1 = None.
Proof.
  induction segs as [|s segs IH]; intros x H y Hy; [reflexivity|].
  cbn [forallb] in H. apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1.
  cbn [find_segment].
  match goal with |- (if ?c then _ else _) = _ => destruct c eqn:E end.
  - apply andb_prop in E. destruct E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH x H2 y Hy).
Qed.

Lemma smem_inv : forall l, mem_inv rsegs (smem l).
Proof.
  intros l a b H. unfold smem in H.
  destruct ((SAT_LO <=? bv_unsigned a) && (bv_unsigned a <? SAT_HI)) eqn:E; [|discriminate].
  apply andb_prop in E. destruct E as [E _]. apply Z.leb_le in E.
  unfold ro_addr. rewrite (find_segment_above rsegs SAT_LO segs_below (bv_unsigned a) E). reflexivity.
Qed.

Lemma smem_in : forall l x, SAT_LO <= x < SAT_HI -> smem l (wa x) = Some (fill l x).
Proof.
  intros l x Hx. unfold smem. rewrite wa_unsigned by (unfold SAT_LO, SAT_HI in Hx; lia).
  assert (E : (SAT_LO <=? x) && (x <? SAT_HI) = true) by (apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  rewrite E. reflexivity.
Qed.

Lemma smem_out : forall l x, 0 <= x < SAT_LO -> smem l (wa x) = None.
Proof.
  intros l x Hx. unfold smem. rewrite wa_unsigned by (unfold SAT_LO in Hx; lia).
  assert (E : (SAT_LO <=? x) && (x <? SAT_HI) = false) by (apply andb_false_iff; left; apply Z.leb_gt; lia).
  rewrite E. reflexivity.
Qed.

Lemma smem_relro : forall l, relro_img (smem l).
Proof.
  intros l i Hi. unfold mrd. rewrite smem_out by (unfold RELRO_BASE, RELRO_LEN, SAT_LO in *; lia). reflexivity.
Qed.

Lemma smem_stk : forall l lo hi, SAT_LO <= lo -> hi <= SAT_HI -> stk rsegs (smem l) lo hi.
Proof.
  intros l lo hi H1 H2. split; [unfold SAT_LO in H1; lia|]. split; [unfold SAT_HI in H2; lia|].
  intros a Ha. assert (Hin : SAT_LO <= a < SAT_HI) by lia.
  unfold wview, mrd. rewrite (smem_in l a Hin). split; [discriminate | eexists; reflexivity].
Qed.

(** ---- deciding memory facts of a concrete memory ---- *)

Fixpoint mem_bytes_b (m : word -> option byte) (A : Z) (bs : list byte) : bool :=
  match bs with
  | [] => true
  | b :: bs' =>
      match mrd rsegs m (wa A) with
      | Some b' => bv_eqb b b' && mem_bytes_b m (A + 1) bs'
      | None => false
      end
  end.

Lemma mem_bytes_b_nth : forall m bs A (i : nat), mem_bytes_b m A bs = true -> (i < length bs)%nat ->
  mrd rsegs m (wa (A + Z.of_nat i)) = nth_error bs i.
Proof.
  intros m. induction bs as [|b bs IH]; intros A i H Hi; cbn in Hi; [lia|].
  cbn [mem_bytes_b] in H. destruct (mrd rsegs m (wa A)) as [b'|] eqn:E; [|discriminate].
  apply andb_prop in H. destruct H as [H1 H2].
  unfold bv_eqb in H1. apply Z.eqb_eq in H1. apply bv_eq in H1. subst b'.
  destruct i as [|i].
  - cbn [nth_error]. change (Z.of_nat 0) with 0. rewrite Z.add_0_r. exact E.
  - cbn [nth_error]. rewrite <- (IH (A + 1) i H2) by lia.
    replace (A + 1 + Z.of_nat i) with (A + Z.of_nat (S i)) by lia. reflexivity.
Qed.

Lemma mem_bytes_b_sound : forall m A bs, 0 <= A -> A + Z.of_nat (length bs) <= 2 ^ 64 ->
  mem_bytes_b m A bs = true -> bytes_at rsegs m A bs.
Proof.
  intros m A bs H1 H2 H. split; [exact H1|]. split; [exact H2|]. intros i Hi. apply mem_bytes_b_nth; assumption.
Qed.

Fixpoint wr_b (m : word -> option byte) (A : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => match wview rsegs m (wa A) with Some _ => wr_b m (A + 1) n' | None => false end
  end.

Lemma wr_b_sound : forall m n A, 0 <= A -> A + Z.of_nat n <= 2 ^ 64 -> wr_b m A n = true ->
  wr_at rsegs m A (Z.of_nat n).
Proof.
  intros m n. induction n as [|n IH]; intros A H1 H2 H.
  - split; [exact H1|]. split; [lia|]. intros i Hi. lia.
  - cbn [wr_b] in H. destruct (wview rsegs m (wa A)) as [b|] eqn:E; [|discriminate].
    destruct (IH (A + 1) ltac:(lia) ltac:(lia) H) as (_ & _ & IHi).
    split; [exact H1|]. split; [lia|]. intros i Hi.
    destruct (Z.eq_dec i 0) as [->|Hne].
    + rewrite Z.add_0_r, E. discriminate.
    + replace (A + i) with (A + 1 + (i - 1)) by lia. apply IHi. lia.
Qed.

Fixpoint cells_wf_b (cs : list cell) : bool :=
  match cs with
  | [] => true
  | CB n bs :: cs' => Nat.eqb (length bs) n && cells_wf_b cs'
  | _ :: cs' => cells_wf_b cs'
  end.

Lemma cells_wf_b_sound : forall cs, cells_wf_b cs = true -> cells_wf cs.
Proof.
  induction cs as [|c cs IH]; intros H; [exact I|].
  destruct c as [v|v|v|b|n bs]; cbn [cells_wf_b] in H; cbn [cells_wf cell_wf];
    try (split; [exact I | exact (IH H)]).
  apply andb_prop in H. destruct H as [H1 H2]. split; [apply Nat.eqb_eq; exact H1 | exact (IH H2)].
Qed.

Lemma rw_cells_b : forall m A cs, cells_wf_b cs = true -> 0 <= A -> A + Z.of_nat (cells_size cs) <= 2 ^ 64 ->
  mem_bytes_b m A (cells_bytes cs) = true -> wr_b m A (cells_size cs) = true -> rw_cells rsegs m A cs.
Proof.
  intros m A cs W H1 H2 HB HW. pose proof (cells_wf_b_sound cs W) as W'. split.
  - split; [exact W'|]. apply mem_bytes_b_sound; [exact H1 | rewrite cells_bytes_length by exact W'; exact H2 | exact HB].
  - apply wr_b_sound; assumption.
Qed.

Lemma cells_at_b : forall m A cs, cells_wf_b cs = true -> 0 <= A -> A + Z.of_nat (cells_size cs) <= 2 ^ 64 ->
  mem_bytes_b m A (cells_bytes cs) = true -> cells_at rsegs m A cs.
Proof.
  intros m A cs W H1 H2 HB. pose proof (cells_wf_b_sound cs W) as W'. split; [exact W'|].
  apply mem_bytes_b_sound; [exact H1 | rewrite cells_bytes_length by exact W'; exact H2 | exact HB].
Qed.

Lemma in_nul_b : forall tb : list byte, existsb (fun b => bv_eqb b (b8 0)) tb = true -> In (b8 0) tb.
Proof.
  intros tb H. apply existsb_exists in H. destruct H as (x & Hx & E).
  unfold bv_eqb in E. apply Z.eqb_eq in E. apply bv_eq in E. subst x. exact Hx.
Qed.

(** seg7_spec and owed_seg7_spec agree on every char (check_text_seg7's condition), by computation. *)
Lemma sat_seg7_agree : forall c, 0 <= c < 256 -> seg7_spec c = owed_seg7_spec c.
Proof.
  intros c Hc. apply Z.eqb_eq.
  apply (zall_range (fun c => seg7_spec c =? owed_seg7_spec c) 0 256); [vm_compute; reflexivity | exact Hc].
Qed.

(** ---- tactics: every premise of a site is closed ---- *)

Ltac zc :=
  match goal with
  | |- Z.le _ _ /\ _ => split; zc
  | |- Z.le _ _ => apply Z.leb_le; vm_compute; reflexivity
  | |- Z.lt _ _ => apply Z.ltb_lt; vm_compute; reflexivity
  | |- le _ _ => apply Nat.leb_le; vm_compute; reflexivity
  | |- not (@eq Z _ _) => apply Z.eqb_neq; vm_compute; reflexivity
  | |- @eq Z _ _ => vm_compute; reflexivity
  | |- _ \/ _ => first [left; zc | right; zc]
  end.

Ltac sat1 :=
  match goal with
  | |- mem_inv rsegs _ => apply smem_inv
  | |- relro_img _ => apply smem_relro
  | |- stk rsegs _ _ _ => apply smem_stk; zc
  | |- rw_cells rsegs _ _ _ =>
      apply rw_cells_b; [vm_compute; reflexivity | zc | zc | vm_compute; reflexivity | vm_compute; reflexivity]
  | |- cells_at rsegs _ _ _ => apply cells_at_b; [vm_compute; reflexivity | zc | zc | vm_compute; reflexivity]
  | |- bytes_at rsegs _ _ _ => apply mem_bytes_b_sound; [zc | zc | vm_compute; reflexivity]
  | |- In (b8 0) _ => apply in_nul_b; vm_compute; reflexivity
  | |- @eq Z _ _ => zc
  | |- @eq _ _ _ => first [reflexivity | vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity]
  | |- forall d, Some _ = Some d -> _ => intros ? Hd; injection Hd as <-; repeat split; zc
  | |- forall c, 0 <= c < 256 -> seg7_spec c = owed_seg7_spec c => exact sat_seg7_agree
  | |- ~ _ => vm_compute; intuition discriminate
  | |- _ -> _ => intros; first [reflexivity | vm_compute; reflexivity]
  | |- _ => first [zc | vm_compute; repeat split; intros; reflexivity]
  end.

Ltac sat := repeat match goal with |- _ /\ _ => split end; sat1.

Ltac unfold_pre := cbv [cstr pers_arg pers_ok desk_ok arg_u32 arg_s32 arg_zx disj kcall_wf].

(** ---- LLVMFuzzerTestOneInput's frame in the witness ---- *)

Definition SAT_SP : Z := 0x7ffff00.
Definition MSP : Z := SAT_SP - 0x1a0.
Definition SK : Z := MSP + 0x20.
Definition SOUT : Z := SK + 108.
Definition SBEF : Z := SK + 76.
Definition SBYTES : Z := SK + 40.
Definition STEXT : Z := MSP + 0xed.
Definition SDOTS : Z := MSP + 0x12e.
Definition SIN : Z := MSP + 0xd8.
Definition SDATA : Z := SAT_SP + 0x10.
(** &SPEC_C24 (the k.desk of a Control|24 call) *)
Definition SSPEC_C24 : Z := 0x1f690.

Definition sat_a5 (n : nat) : list byte := repeat (b8 0xa5) n.
Definition sat_z0 (n : nat) : list byte := repeat (b8 0) n.


(** ---- call records of the witnesses ---- *)

(** A SYSEX call of function 0x70 the library refused: rc = want_rc = E_REFUSED, out = before. *)
Definition sat_k_refused : kcall :=
  mkKcall 11 (sat_z0 4) 0 0 5 0x70 0 0 (sat_z0 24) 0 E_REFUSED (sat_a5 32) (sat_a5 32) E_REFUSED (sat_z0 24) 0 0 0.

(** A FADER call on Control|24 that succeeded, owe() having filled the want fields. *)
Definition sat_k_fader : kcall :=
  mkKcall 0 (sat_z0 4) PERS SSPEC_C24 3 600 0 0 (sat_z0 24) 0 0 (sat_a5 32)
          (cmd_out (sat_a5 32) (snd (fader_spec (Some c24) 3 600))) 0
          (bz [0xb0; 3; 75; 0x23; 0] ++ sat_z0 19) 5 (KEY 1 3) 0.

(** A SCRIBBLE call on Control|24 and a SYSEX call, as owe() finds them before owe_sysex. *)
Definition sat_k_scribble : kcall :=
  mkKcall 9 (sat_z0 4) PERS SSPEC_C24 5 0 0 0 (bz [0x41; 0x42; 0x43; 0x44] ++ sat_z0 20) 0 0 (sat_a5 32)
          (cmd_out (sat_a5 32) (snd (scribble_spec (Some c24) 5 [0x41; 0x42; 0x43; 0x44]))) 0 (sat_z0 24) 0 0 0.
Definition sat_k_sysex : kcall :=
  mkKcall 11 (sat_z0 4) 0 0 5 0x41 0 0 (bz [1; 2; 3] ++ sat_z0 21) 3 0 (sat_a5 32) (cmd_out (sat_a5 32) (snd (sysex_spec 5 0x41 [1; 2; 3]))) 0 (sat_z0 24) 0 0 0.


(** ---- diginet_personality_from_name ---- *)

Lemma sat_diginet_personality_from_name_check_personality_14c90 :
  diginet_personality_from_name_pre (Z_to_bv 64 (MSP - 0x20)) (Z_to_bv 64 (0x103a1))
    (smem [])
    SAT_LO (bz [0x43; 0x4e; 0x54; 0x52; 0x4c; 0x7c; 0x32; 0x34; 0x0]).
Proof. cbv [diginet_personality_from_name_pre]. unfold_pre. sat. Qed.

Lemma sat_diginet_personality_from_name_check_personality_14ca0 :
  diginet_personality_from_name_pre (Z_to_bv 64 (MSP - 0x20)) (Z_to_bv 64 (0x10381))
    (smem [])
    SAT_LO (bz [0x4d; 0x41; 0x49; 0x4e; 0x55; 0x4e; 0x49; 0x54; 0x0]).
Proof. cbv [diginet_personality_from_name_pre]. unfold_pre. sat. Qed.

Lemma sat_diginet_personality_from_name_check_personality_14cb0 :
  diginet_personality_from_name_pre (Z_to_bv 64 (MSP - 0x20)) (Z_to_bv 64 (0x1031d))
    (smem [])
    SAT_LO (bz [0x43; 0x4e; 0x54; 0x52; 0x4c; 0x7c; 0x32; 0x0]).
Proof. cbv [diginet_personality_from_name_pre]. unfold_pre. sat. Qed.

Lemma sat_diginet_personality_from_name_check_personality_14cc0 :
  diginet_personality_from_name_pre (Z_to_bv 64 (MSP - 0x20)) (Z_to_bv 64 (0x10333))
    (smem [])
    SAT_LO (bz [0x4d; 0x41; 0x49; 0x4e; 0x55; 0x4e; 0x49; 0x54; 0x53; 0x0]).
Proof. cbv [diginet_personality_from_name_pre]. unfold_pre. sat. Qed.

Lemma sat_diginet_personality_from_name_check_personality_14cd0 :
  diginet_personality_from_name_pre (Z_to_bv 64 (MSP - 0x20)) (Z_to_bv 64 (0x102de))
    (smem [])
    SAT_LO (bz [0x0]).
Proof. cbv [diginet_personality_from_name_pre]. unfold_pre. sat. Qed.


(** ---- diginet_sysex_encode ---- *)

Lemma sat_diginet_sysex_encode_main_144c8 :
  diginet_sysex_encode_pre (Z_to_bv 64 (MSP)) (Z_to_bv 64 (5)) (Z_to_bv 64 (0x41)) (Z_to_bv 64 (SBYTES)) (Z_to_bv 64 (3)) (Z_to_bv 64 (SOUT))
    (smem [(SBYTES, bz [1; 2; 3]); (SBEF, sat_a5 64)])
    SAT_LO 5 0x41 (bz [1; 2; 3]) (sat_a5 32).
Proof. cbv [diginet_sysex_encode_pre]. unfold_pre. sat. Qed.

Lemma sat_diginet_sysex_encode_scribble_encode_15ee0 :
  diginet_sysex_encode_pre (Z_to_bv 64 (MSP - 0x40)) (Z_to_bv 64 (1)) (Z_to_bv 64 (0x40)) (Z_to_bv 64 (MSP - 0x40 + 0xe)) (Z_to_bv 64 (6)) (Z_to_bv 64 (SOUT))
    (smem [(MSP - 0x40 + 0xe, (bz [0x5; 0x0; 0x41; 0x42; 0x43; 0x44])); (SBEF, sat_a5 64)])
    SAT_LO 1 0x40 (bz [0x5; 0x0; 0x41; 0x42; 0x43; 0x44]) (sat_a5 32).
Proof. cbv [diginet_sysex_encode_pre]. unfold_pre. sat. Qed.

Lemma sat_diginet_sysex_encode_ring_encode_15b44 :
  diginet_sysex_encode_pre (Z_to_bv 64 (MSP - 0x20)) (Z_to_bv 64 (1)) (Z_to_bv 64 (0x00)) (Z_to_bv 64 (MSP - 0x20 + 5)) (Z_to_bv 64 (3)) (Z_to_bv 64 (SOUT))
    (smem [(MSP - 0x20 + 5, (bz [0x44; 0x12; 0x34])); (SBEF, sat_a5 64)])
    SAT_LO 1 0x00 (bz [0x44; 0x12; 0x34]) (sat_a5 32).
Proof. cbv [diginet_sysex_encode_pre]. unfold_pre. sat. Qed.

Lemma sat_diginet_sysex_encode_meter_encode_15c58 :
  diginet_sysex_encode_pre (Z_to_bv 64 (MSP - 0x20)) (Z_to_bv 64 (1)) (Z_to_bv 64 (0x10)) (Z_to_bv 64 (MSP - 0x20 + 5)) (Z_to_bv 64 (3)) (Z_to_bv 64 (SOUT))
    (smem [(MSP - 0x20 + 5, (bz [0x23; 0x0; 0x7f])); (SBEF, sat_a5 64)])
    SAT_LO 1 0x10 (bz [0x23; 0x0; 0x7f]) (sat_a5 32).
Proof. cbv [diginet_sysex_encode_pre]. unfold_pre. sat. Qed.

Lemma sat_diginet_sysex_encode_leds_encode_15d10 :
  diginet_sysex_encode_pre (Z_to_bv 64 (MSP - 0x20)) (Z_to_bv 64 (1)) (Z_to_bv 64 (0x20)) (Z_to_bv 64 (MSP - 0x20 + 6)) (Z_to_bv 64 (2)) (Z_to_bv 64 (SOUT))
    (smem [(MSP - 0x20 + 6, (bz [0x2; 0x11])); (SBEF, sat_a5 64)])
    SAT_LO 1 0x20 (bz [0x2; 0x11]) (sat_a5 32).
Proof. cbv [diginet_sysex_encode_pre]. unfold_pre. sat. Qed.

Lemma sat_diginet_sysex_encode_counter_encode_161fc :
  diginet_sysex_encode_pre (Z_to_bv 64 (MSP - 0x30)) (Z_to_bv 64 (1)) (Z_to_bv 64 (0x30)) (Z_to_bv 64 (MSP - 0x30 + 0xe)) (Z_to_bv 64 (10)) (Z_to_bv 64 (SOUT))
    (smem [(MSP - 0x30 + 0xe, (bz [0x19; 0x12; 0x7e; 0x30; 0x6d; 0x79; 0x33; 0x5b; 0x5f; 0x70])); (SBEF, sat_a5 64)])
    SAT_LO 1 0x30 (bz [0x19; 0x12; 0x7e; 0x30; 0x6d; 0x79; 0x33; 0x5b; 0x5f; 0x70]) (sat_a5 32).
Proof. cbv [diginet_sysex_encode_pre]. unfold_pre. sat. Qed.


(** ---- diginet_fader_encode ---- *)

Lemma sat_diginet_fader_encode_main_143c4 :
  diginet_fader_encode_pre (Z_to_bv 64 (PERS)) (Z_to_bv 64 (s32 3)) (Z_to_bv 64 (s32 600)) (Z_to_bv 64 (SOUT))
    (smem [(SBEF, sat_a5 64)])
    (Some c24) 3 600 (sat_a5 32).
Proof. cbv [diginet_fader_encode_pre]. unfold_pre. sat. Qed.


(** ---- diginet_button_encode ---- *)

Lemma sat_diginet_button_encode_main_14464 :
  diginet_button_encode_pre (Z_to_bv 64 (s32 0x10)) (Z_to_bv 64 (s32 5)) (Z_to_bv 64 (1)) (Z_to_bv 64 (SOUT))
    (smem [(SBEF, sat_a5 64)])
    0x10 5 1 (sat_a5 32).
Proof. cbv [diginet_button_encode_pre]. unfold_pre. sat. Qed.


(** ---- diginet_touch_encode ---- *)

Lemma sat_diginet_touch_encode_main_1441c :
  diginet_touch_encode_pre (Z_to_bv 64 (PERS)) (Z_to_bv 64 (s32 2)) (Z_to_bv 64 (1)) (Z_to_bv 64 (SOUT))
    (smem [(SBEF, sat_a5 64)])
    (Some c24) 2 1 (sat_a5 32).
Proof. cbv [diginet_touch_encode_pre]. unfold_pre. sat. Qed.


(** ---- diginet_vpot_encode ---- *)

Lemma sat_diginet_vpot_encode_main_14434 :
  diginet_vpot_encode_pre (Z_to_bv 64 (PERS + 24)) (Z_to_bv 64 (s32 1)) (Z_to_bv 64 (-5)) (Z_to_bv 64 (SOUT))
    (smem [(SBEF, sat_a5 64)])
    (Some pc) 1 (-5) (sat_a5 32).
Proof. cbv [diginet_vpot_encode_pre]. unfold_pre. sat. Qed.


(** ---- diginet_jog_encode ---- *)

Lemma sat_diginet_jog_encode_main_14404 :
  diginet_jog_encode_pre (Z_to_bv 64 (7)) (Z_to_bv 64 (SOUT))
    (smem [(SBEF, sat_a5 64)])
    7 (sat_a5 32).
Proof. cbv [diginet_jog_encode_pre]. unfold_pre. sat. Qed.


(** ---- diginet_ring_encode ---- *)

Lemma sat_diginet_ring_encode_main_1447c :
  diginet_ring_encode_pre (Z_to_bv 64 (MSP)) (Z_to_bv 64 (PERS)) (Z_to_bv 64 (s32 4)) (Z_to_bv 64 (0x1235)) (Z_to_bv 64 (SOUT))
    (smem [(SBEF, sat_a5 64)])
    SAT_LO (Some c24) 4 0x1235 (sat_a5 32).
Proof. cbv [diginet_ring_encode_pre]. unfold_pre. sat. Qed.


(** ---- diginet_meter_encode ---- *)

Lemma sat_diginet_meter_encode_main_14498 :
  diginet_meter_encode_pre (Z_to_bv 64 (MSP)) (Z_to_bv 64 (PERS)) (Z_to_bv 64 (s32 3)) (Z_to_bv 64 (1)) (Z_to_bv 64 (s32 7)) (Z_to_bv 64 (SOUT))
    (smem [(SBEF, sat_a5 64)])
    SAT_LO (Some c24) 3 1 7 (sat_a5 32).
Proof. cbv [diginet_meter_encode_pre]. unfold_pre. sat. Qed.


(** ---- diginet_strip_leds_encode ---- *)

Lemma sat_diginet_strip_leds_encode_main_1444c :
  diginet_strip_leds_encode_pre (Z_to_bv 64 (MSP)) (Z_to_bv 64 (PERS)) (Z_to_bv 64 (s32 2)) (Z_to_bv 64 (s32 0x11)) (Z_to_bv 64 (SOUT))
    (smem [(SBEF, sat_a5 64)])
    SAT_LO (Some c24) 2 0x11 (sat_a5 32).
Proof. cbv [diginet_strip_leds_encode_pre]. unfold_pre. sat. Qed.


(** ---- diginet_counter_leds_encode ---- *)

Lemma sat_diginet_counter_leds_encode_main_144ac :
  diginet_counter_leds_encode_pre (Z_to_bv 64 (MSP)) (Z_to_bv 64 (PERS)) (Z_to_bv 64 (s32 0x22)) (Z_to_bv 64 (SOUT))
    (smem [(SBEF, sat_a5 64)])
    SAT_LO (Some c24) 0x22 (sat_a5 32).
Proof. cbv [diginet_counter_leds_encode_pre]. unfold_pre. sat. Qed.


(** ---- diginet_scribble_encode ---- *)

Lemma sat_diginet_scribble_encode_main_143dc :
  diginet_scribble_encode_pre (Z_to_bv 64 (MSP)) (Z_to_bv 64 (PERS)) (Z_to_bv 64 (s32 5)) (Z_to_bv 64 (SBYTES)) (Z_to_bv 64 (SOUT))
    (smem [(SBYTES, (bz [0x41; 0x42; 0x43; 0x44] ++ sat_a5 20)); (SBEF, sat_a5 64)])
    SAT_LO (Some c24) 5 (bz [0x41; 0x42; 0x43; 0x44] ++ sat_a5 20) (sat_a5 32).
Proof. cbv [diginet_scribble_encode_pre]. unfold_pre. sat. Qed.


(** ---- diginet_counter_encode ---- *)

Lemma sat_diginet_counter_encode_main_143f4 :
  diginet_counter_encode_pre (Z_to_bv 64 (MSP)) (Z_to_bv 64 (PERS)) (Z_to_bv 64 (SBYTES)) (Z_to_bv 64 (0x12)) (Z_to_bv 64 (SOUT))
    (smem [(SBYTES, (bz [0x7e; 0x30; 0x6d; 0x79; 0x33; 0x5b; 0x5f; 0x70] ++ sat_a5 16)); (SBEF, sat_a5 64)])
    SAT_LO (Some c24) 0x12 (bz [0x7e; 0x30; 0x6d; 0x79; 0x33; 0x5b; 0x5f; 0x70] ++ sat_a5 16) (sat_a5 32).
Proof. cbv [diginet_counter_encode_pre]. unfold_pre. sat. Qed.


(** ---- leds_encode ---- *)

Lemma sat_leds_encode_strip_leds_encode_15cb0 :
  leds_encode_pre (Z_to_bv 64 (MSP)) (Z_to_bv 64 (PERS)) (Z_to_bv 64 (s32 2)) (Z_to_bv 64 (s32 0x11)) (Z_to_bv 64 (SOUT))
    (smem [(SBEF, sat_a5 64)])
    SAT_LO c24 2 0x11 (sat_a5 32).
Proof. cbv [leds_encode_pre]. unfold_pre. sat. Qed.

Lemma sat_leds_encode_counter_leds_encode_15d60 :
  leds_encode_pre (Z_to_bv 64 (MSP)) (Z_to_bv 64 (PERS)) (Z_to_bv 64 (0x19)) (Z_to_bv 64 (s32 0x11)) (Z_to_bv 64 (SOUT))
    (smem [(SBEF, sat_a5 64)])
    SAT_LO c24 0x19 0x11 (sat_a5 32).
Proof. cbv [leds_encode_pre]. unfold_pre. sat. Qed.


(** ---- diginet_ring_dot ---- *)

Lemma sat_diginet_ring_dot_check_text_masks_15338 :
  diginet_ring_dot_pre (Z_to_bv 64 (s32 0x80000005))
    (smem [])
    0x80000005.
Proof. cbv [diginet_ring_dot_pre]. unfold_pre. sat. Qed.


(** ---- diginet_ring_fill ---- *)

Lemma sat_diginet_ring_fill_check_text_masks_15358 :
  diginet_ring_fill_pre (Z_to_bv 64 (s32 0x80000005))
    (smem [])
    0x80000005.
Proof. cbv [diginet_ring_fill_pre]. unfold_pre. sat. Qed.


(** ---- diginet_meter_mask ---- *)

Lemma sat_diginet_meter_mask_check_text_masks_152e4 :
  diginet_meter_mask_pre (Z_to_bv 64 (s32 0x80000005))
    (smem [])
    0x80000005.
Proof. cbv [diginet_meter_mask_pre]. unfold_pre. sat. Qed.


(** ---- diginet_meter_segments ---- *)

Lemma sat_diginet_meter_segments_check_text_masks_1530c :
  diginet_meter_segments_pre (Z_to_bv 64 (0x3fff))
    (smem [])
    0x3fff.
Proof. cbv [diginet_meter_segments_pre]. unfold_pre. sat. Qed.


(** ---- diginet_seg7 ---- *)

Lemma sat_diginet_seg7_check_text_seg7_14f94 :
  diginet_seg7_pre (Z_to_bv 64 (0x41))
    (smem []).
Proof. cbv [diginet_seg7_pre]. unfold_pre. sat. Qed.

Lemma sat_diginet_seg7_counter_text_16014 :
  diginet_seg7_pre (Z_to_bv 64 (0x38))
    (smem []).
Proof. cbv [diginet_seg7_pre]. unfold_pre. sat. Qed.


(** ---- diginet_scribble_text ---- *)

Lemma sat_diginet_scribble_text_check_text_scribble_14ef0 :
  diginet_scribble_text_pre (Z_to_bv 64 (STEXT)) (Z_to_bv 64 (SBYTES)) (Z_to_bv 64 (4))
    (smem [(STEXT, (bz [0x48; 0x69; 0x2e; 0x35; 0xe9; 0x78; 0x0] ++ sat_z0 58)); (SBYTES, sat_a5 24)])
    4 (bz [0x48; 0x69; 0x2e; 0x35; 0xe9; 0x78; 0x0] ++ sat_z0 58) (sat_a5 4).
Proof. cbv [diginet_scribble_text_pre]. unfold_pre. sat. Qed.


(** ---- diginet_counter_text ---- *)

Lemma sat_diginet_counter_text_check_text_counter_15044 :
  diginet_counter_text_pre (Z_to_bv 64 (MSP - 0x40)) (Z_to_bv 64 (STEXT)) (Z_to_bv 64 (SBYTES)) (Z_to_bv 64 (SDOTS))
    (smem [(STEXT, (bz [0x31; 0x32; 0x2e; 0x35; 0x0] ++ sat_z0 60)); (SBYTES, sat_a5 24); (SDOTS, sat_a5 1)])
    SAT_LO (bz [0x31; 0x32; 0x2e; 0x35; 0x0] ++ sat_z0 60) (sat_a5 8) (b8 0xa5).
Proof. cbv [diginet_counter_text_pre]. unfold_pre. sat. Qed.


(** ---- check_personality ---- *)

Lemma sat_check_personality_main_13304 :
  check_personality_pre (Z_to_bv 64 (MSP))
    (smem [])
    SAT_LO.
Proof. cbv [check_personality_pre]. unfold_pre. sat. Qed.


(** ---- text_arg ---- *)

Lemma sat_text_arg_main_13d50 :
  text_arg_pre (Z_to_bv 64 (MSP)) (Z_to_bv 64 (SIN)) (Z_to_bv 64 (STEXT))
    (smem [(SIN, (le8 (Z_to_bv 64 (SDATA + 2)) ++ le8 (Z_to_bv 64 8))); (SDATA, (bz [0xc; 0x5; 0x6; 0x0; 0x48; 0x69; 0x2e; 0x35; 0xe9; 0x78])); (STEXT, sat_z0 65)])
    SAT_LO (SDATA + 2) (bz [0x6; 0x0; 0x48; 0x69; 0x2e; 0x35; 0xe9; 0x78]) (sat_z0 65).
Proof. cbv [text_arg_pre]. unfold_pre. sat. Qed.

Lemma sat_text_arg_main_139b8 :
  text_arg_pre (Z_to_bv 64 (MSP)) (Z_to_bv 64 (SIN)) (Z_to_bv 64 (STEXT))
    (smem [(SIN, (le8 (Z_to_bv 64 (SDATA + 1)) ++ le8 (Z_to_bv 64 9))); (SDATA, (bz [0xc; 0x5; 0x6; 0x0; 0x48; 0x69; 0x2e; 0x35; 0xe9; 0x78])); (STEXT, sat_z0 65)])
    SAT_LO (SDATA + 1) (bz [0x5; 0x6; 0x0; 0x48; 0x69; 0x2e; 0x35; 0xe9; 0x78]) (sat_z0 65).
Proof. cbv [text_arg_pre]. unfold_pre. sat. Qed.


(** ---- check_text_scribble ---- *)

Lemma sat_check_text_scribble_main_13d70 :
  check_text_scribble_pre (Z_to_bv 64 (MSP)) (Z_to_bv 64 (STEXT)) (Z_to_bv 64 (SBYTES)) (Z_to_bv 64 (4))
    (smem [(STEXT, (bz [0x48; 0x69; 0x2e; 0x35; 0xe9; 0x78; 0x0] ++ sat_z0 58)); (SBYTES, sat_z0 24)])
    SAT_LO 4 (bz [0x48; 0x69; 0x2e; 0x35; 0xe9; 0x78; 0x0] ++ sat_z0 58) (sat_z0 24).
Proof. cbv [check_text_scribble_pre]. unfold_pre. sat. Qed.


(** ---- check_text_seg7 ---- *)

Lemma sat_check_text_seg7_main_139bc :
  check_text_seg7_pre (Z_to_bv 64 (MSP))
    (smem [])
    SAT_LO.
Proof. cbv [check_text_seg7_pre]. unfold_pre. sat. Qed.


(** ---- check_text_counter ---- *)

Lemma sat_check_text_counter_main_139d0 :
  check_text_counter_pre (Z_to_bv 64 (MSP)) (Z_to_bv 64 (STEXT)) (Z_to_bv 64 (SBYTES)) (Z_to_bv 64 (SDOTS))
    (smem [(STEXT, (bz [0x31; 0x32; 0x2e; 0x35; 0x0] ++ sat_z0 60))])
    SAT_LO (bz [0x31; 0x32; 0x2e; 0x35; 0x0] ++ sat_z0 60) (sat_z0 24) (b8 0).
Proof. cbv [check_text_counter_pre]. unfold_pre. sat. Qed.


(** ---- owed_counter_text ---- *)

Lemma sat_owed_counter_text_main_139e0 :
  owed_counter_text_pre (Z_to_bv 64 (MSP)) (Z_to_bv 64 (STEXT)) (Z_to_bv 64 (SBYTES)) (Z_to_bv 64 (SDOTS))
    (smem [(STEXT, (bz [0x31; 0x32; 0x2e; 0x35; 0x0] ++ sat_z0 60)); (SBYTES, (bz [0; 0; 0; 0; 0; 0x30; 0x6d; 0x5b] ++ sat_a5 16)); (SDOTS, bz [0x40])])
    SAT_LO (bz [0x31; 0x32; 0x2e; 0x35; 0x0] ++ sat_z0 60) (bz [0; 0; 0; 0; 0; 0x30; 0x6d; 0x5b]) (b8 0x40).
Proof. cbv [owed_counter_text_pre]. unfold_pre. sat. Qed.

Lemma sat_owed_counter_text_check_text_counter_15018 :
  owed_counter_text_pre (Z_to_bv 64 (MSP - 0x40)) (Z_to_bv 64 (STEXT)) (Z_to_bv 64 (MSP - 0x40 + 8)) (Z_to_bv 64 (MSP - 0x40 + 7))
    (smem [(STEXT, (bz [0x31; 0x32; 0x2e; 0x35; 0x0] ++ sat_z0 60))])
    SAT_LO (bz [0x31; 0x32; 0x2e; 0x35; 0x0] ++ sat_z0 60) (sat_z0 8) (b8 0).
Proof. cbv [owed_counter_text_pre]. unfold_pre. sat. Qed.


(** ---- check_text_masks ---- *)

Lemma sat_check_text_masks_main_14b18 :
  check_text_masks_pre (Z_to_bv 64 (MSP)) (Z_to_bv 64 (s32 0x80000005)) (Z_to_bv 64 (0x3fff))
    (smem [])
    SAT_LO 0x80000005 0x3fff.
Proof. cbv [check_text_masks_pre]. unfold_pre. sat. Qed.


(** ---- owed_seg7 ---- *)

Lemma sat_owed_seg7_check_text_seg7_14fa0 :
  owed_seg7_pre (Z_to_bv 64 (0x41))
    (smem [])
    0x41.
Proof. cbv [owed_seg7_pre]. unfold_pre. sat. Qed.

Lemma sat_owed_seg7_owed_counter_text_15184 :
  owed_seg7_pre (Z_to_bv 64 (0x32))
    (smem [])
    0x32.
Proof. cbv [owed_seg7_pre]. unfold_pre. sat. Qed.


(** ---- check_refusal ---- *)

Lemma sat_check_refusal_main_14a38 :
  check_refusal_pre (Z_to_bv 64 (SK))
    (smem [(SK, cells_bytes (kcall_cells sat_k_refused))])
    sat_k_refused.
Proof. cbv [check_refusal_pre]. unfold_pre. sat. Qed.


(** ---- check_range ---- *)

Lemma sat_check_range_main_14a40 :
  check_range_pre (Z_to_bv 64 (MSP)) (Z_to_bv 64 (SK))
    (smem [(SK, cells_bytes (kcall_cells sat_k_refused))])
    SAT_LO sat_k_refused.
Proof. cbv [check_range_pre]. unfold_pre. sat. Qed.


(** ---- check_bytes ---- *)

Lemma sat_check_bytes_main_14a50 :
  check_bytes_pre (Z_to_bv 64 (MSP)) (Z_to_bv 64 (SK))
    (smem [(SK, cells_bytes (kcall_cells sat_k_fader))])
    SAT_LO sat_k_fader.
Proof. cbv [check_bytes_pre]. unfold_pre. sat. Qed.


(** ---- owe_sysex ---- *)

Lemma sat_owe_sysex_main_14670 :
  owe_sysex_pre (Z_to_bv 64 (MSP)) (Z_to_bv 64 (SK)) (Z_to_bv 64 (1)) (Z_to_bv 64 (0x40)) (Z_to_bv 64 (SDOTS)) (Z_to_bv 64 (6))
    (smem [(SK, cells_bytes (kcall_cells sat_k_scribble)); (SDOTS, bz [5; 0; 0x41; 0x42; 0x43; 0x44])])
    SAT_LO 1 0x40 sat_k_scribble (bz [5; 0; 0x41; 0x42; 0x43; 0x44]).
Proof. cbv [owe_sysex_pre]. unfold_pre. sat. Qed.

Lemma sat_owe_sysex_main_14b70 :
  owe_sysex_pre (Z_to_bv 64 (MSP)) (Z_to_bv 64 (SK)) (Z_to_bv 64 (5)) (Z_to_bv 64 (0x41)) (Z_to_bv 64 (SBYTES)) (Z_to_bv 64 (3))
    (smem [(SK, cells_bytes (kcall_cells sat_k_sysex))])
    SAT_LO 5 0x41 sat_k_sysex (bz [1; 2; 3]).
Proof. cbv [owe_sysex_pre]. unfold_pre. sat. Qed.


(** ---- LLVMFuzzerTestOneInput: the premises of codec_main_contract at the driver's call (a0 = the input,
    a1 = its length; sp 16-aligned with the whole stack below it) ---- *)
Definition sat_input : list byte := bz [0x0c; 0x05; 0x06; 0x00; 0x48; 0x69; 0x2e; 0x35; 0xe9; 0x78].

Lemma sat_LLVMFuzzerTestOneInput_driver :
  bytes_at rsegs (smem [(SDATA, sat_input)]) (bv_unsigned (Z_to_bv 64 SDATA)) sat_input /\
  bv_unsigned (Z_to_bv 64 10) = Z.of_nat (length sat_input) /\
  mem_inv rsegs (smem [(SDATA, sat_input)]) /\
  stk rsegs (smem [(SDATA, sat_input)]) SAT_LO (bv_unsigned (Z_to_bv 64 SAT_SP)) /\
  SAT_LO + LLVM_CODEC_STACK <= bv_unsigned (Z_to_bv 64 SAT_SP) /\
  bv_unsigned (Z_to_bv 64 SAT_SP) mod 16 = 0 /\
  (bv_unsigned (Z_to_bv 64 SDATA) + Z.of_nat (length sat_input) <= SAT_LO \/
   bv_unsigned (Z_to_bv 64 SAT_SP) <= bv_unsigned (Z_to_bv 64 SDATA)) /\
  bv_unsigned (Z_to_bv 64 SDATA) + Z.of_nat (length sat_input) < 2 ^ 63 /\
  (0 < Z.of_nat (length sat_input) -> 0 < bv_unsigned (Z_to_bv 64 SDATA)) /\
  relro_img (smem [(SDATA, sat_input)]) /\
  disj SAT_LO (bv_unsigned (Z_to_bv 64 SAT_SP) - SAT_LO) RELRO_BASE RELRO_LEN.
Proof. cbv [disj]. sat. Qed.
