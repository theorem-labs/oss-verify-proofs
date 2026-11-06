From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells codec_img
  diginet_personality_of_c strcmp_c diginet_personality_from_name_c check_personality_c.
Import ListNotations.
Open Scope Z_scope.

(** check_personality saves ra, s0, s1 in a 32-byte frame, then: s1 = personality_of(1) = &personalities[0],
    s0 = personality_of(2) = &personalities[1]; both are not NULL; strcmp(s1->announce_name, "CNTRL|24") = 0
    (the same pointer); s1's four fields are 1, 0x18, 4, 0x19; strcmp(s0->announce_name, "MAINUNIT") = 0;
    s0's fields are 0, 8, 8, 9; personality_of(0) = NULL; from_name("CNTRL|24") = s1, from_name("MAINUNIT") = s0,
    from_name of "CNTRL|2", "MAINUNITS" and "" is NULL. Every compared value is image data (personalities[] in
    RELRO, the strings in .rodata), so each branch to the abort call at 0x14b0c has a constant condition that
    is false, and the function returns. The RELRO block is carried through the frame stores and the calls as a
    [bytes_at] fact: the premise [disj] keeps the stack window, and so every store and callee frame, off it. *)

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** ---- the RELRO block as bytes ---- *)

Lemma cp_relro_len : Z.of_nat (length codec_relro_bytes) = 568.
Proof. vm_compute. reflexivity. Qed.

Lemma cp_relro_bytes : forall m, relro_img m -> bytes_at rsegs m codec_relro_base codec_relro_bytes.
Proof. intros m H. apply codec_relro_at. exact H. Qed.

Lemma cp_relro_img : forall m, bytes_at rsegs m codec_relro_base codec_relro_bytes -> relro_img m.
Proof.
  intros m (_ & _ & H) i Hi.
  change RELRO_BASE with codec_relro_base. change RELRO_LEN with 568 in Hi.
  assert (Hl : length codec_relro_bytes = 568%nat) by (vm_compute; reflexivity).
  replace i with (Z.of_nat (Z.to_nat i)) by lia.
  rewrite (H (Z.to_nat i)) by lia.
  rewrite (img_bytes_b_nth rsegs codec_relro_bytes codec_relro_base (Z.to_nat i) codec_relro_image_b) by lia.
  reflexivity.
Qed.

(** ---- a read-only object lies outside the stack window ---- *)

Lemma cp_ro_addr : forall A bs, ro_bytes_b rsegs A bs = true ->
  forall i, 0 <= i < Z.of_nat (length bs) -> ro_addr rsegs (wa (A + i)) = true.
Proof.
  intros A bs H i Hi. apply ro_bytes_b_sound in H.
  destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E.
  - pose proof (ro_bytes_nth rsegs bs A (Z.to_nat i) b H E) as [_ R].
    rewrite Z2Nat.id in R by lia. exact R.
  - apply nth_error_None in E. lia.
Qed.

Lemma cp_ro_apart : forall m lo hi A n,
  stk rsegs m lo hi -> mem_inv rsegs m -> lo < hi -> 0 < n ->
  (forall i, 0 <= i < n -> ro_addr rsegs (wa (A + i)) = true) ->
  A + n <= lo \/ hi <= A.
Proof.
  intros m lo hi A n (H0 & H1 & HS) HI Hlt Hn HR.
  destruct (Z.le_gt_cases (A + n) lo) as [L|L]; [left; exact L|].
  destruct (Z.le_gt_cases hi A) as [R|R]; [right; exact R|].
  exfalso.
  assert (Hx : exists x, lo <= x < hi /\ 0 <= x - A < n).
  { destruct (Z.le_gt_cases lo A) as [E|E].
    - exists A. split; lia.
    - exists lo. split; lia. }
  destruct Hx as [x [Hx Hxa]].
  destruct (HS x Hx) as [W _].
  specialize (HR (x - A) Hxa). replace (A + (x - A)) with x in HR by lia.
  destruct (m (wa x)) as [b|] eqn:E.
  - specialize (HI _ _ E). congruence.
  - pose proof (wview_not_ro rsegs m (wa x) W E). congruence.
Qed.

(** ---- the premise of diginet_personality_from_name for a .rodata string ---- *)

Lemma cp_fn_pre : forall spz A m lo tb,
  ro_bytes_b rsegs A tb = true -> In (b8 0) tb -> 0 < A -> A + Z.of_nat (length tb) <= 2^64 ->
  0 <= spz < 2^64 ->
  bytes_at rsegs m codec_relro_base codec_relro_bytes ->
  disj lo (spz - lo) RELRO_BASE RELRO_LEN ->
  mem_inv rsegs m -> stk rsegs m lo spz -> lo + 0x30 <= spz ->
  diginet_personality_from_name_pre (Z_to_bv 64 spz) (Z_to_bv 64 A) m lo tb.
Proof.
  intros spz A m lo tb HRO HIn HA HAl Hsp HRB DJ HMI ST LO.
  assert (Hn : 0 < Z.of_nat (length tb)) by (destruct tb; [contradiction | cbn [length]; lia]).
  assert (UA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  assert (US : bv_unsigned (Z_to_bv 64 spz) = spz) by (apply unsigned_lit; lia).
  unfold diginet_personality_from_name_pre, DIGINET_PERSONALITY_FROM_NAME_DEPTH. rewrite UA, US.
  split; [lia|].
  split; [split; [apply img_ro_bytes_at; first [exact HMI | lia | exact HRO] | exact HIn]|].
  split; [eapply cp_ro_apart; [exact ST | exact HMI | lia | exact Hn | apply cp_ro_addr; exact HRO]|].
  split; [apply cp_relro_img; exact HRB|].
  split; [exact DJ|].
  split; [exact HMI|].
  split; [exact ST|].
  exact LO.
Qed.

(** ---- the walk ---- *)

Ltac cp_res :=
  repeat match goal with
  | |- context [pers_of ?x] => let v := eval vm_compute in (pers_of x) in change (pers_of x) with v
  | |- context [from_name_res ?t] => let v := eval vm_compute in (from_name_res t) in change (from_name_res t) with v
  end.

Ltac cp_br := first [ if_false | if_true ].

Ltac cp_ret :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.

(* diginet_personality_of: no premise; a0 := pers_of a0, computed. *)
Ltac cp_of POF :=
  eapply evt_cut; [ apply POF | ];
  let ms' := fresh "ms'" in intros ms' [? [? ->]]; cp_ret; cp_res.

(* strcmp of a .rodata string with itself: returns 0. *)
Ltac cp_str :=
  first [ (rewrite unsigned_lit by lia; first [ apply codec_str_c24_at | apply codec_str_pc_at ]; assumption)
        | apply codec_str_c24_nz | apply codec_str_pc_nz ].
Ltac cp_strcmp SC s :=
  eapply evt_cut; [ eapply SC with (sx := s) (sy := s); cp_str | ];
  let ms' := fresh "ms'" in let r := fresh "r" in let HRr := fresh "HRr" in
  intros ms' [r [? [? [? [-> HRr]]]]];
  assert (r = Z_to_bv 64 0) by (apply HRr; reflexivity); subst r; clear HRr; cp_ret.

(* diginet_personality_from_name of the .rodata string held by tb. *)
Ltac cp_side :=
  first [ assumption | lia | (unfold disj, RELRO_BASE, RELRO_LEN; lia)
        | (apply in_or_app; right; left; reflexivity)
        | (apply Z.leb_le; vm_compute; reflexivity)
        | lazymatch goal with |- ro_bytes_b _ _ _ = true => vm_compute; reflexivity end ].
Ltac cp_fn FN lov tbv U32 :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
      eapply evt_cut; [ eapply FN with (lo := lov) (tb := tbv); apply cp_fn_pre; cp_side | post_call segs m ]
  end;
  try rewrite U32 in *; cp_res.

Theorem check_personality_holds :
  diginet_personality_of_contract -> strcmp_contract -> diginet_personality_from_name_contract ->
  check_personality_contract.
Proof.
  intros POF SC FN.
  unfold diginet_personality_of_contract, DIGINET_PERSONALITY_OF in POF.
  unfold strcmp_contract, STRCMP in SC.
  unfold diginet_personality_from_name_contract, DIGINET_PERSONALITY_FROM_NAME,
    DIGINET_PERSONALITY_FROM_NAME_DEPTH in FN.
  unfold check_personality_contract, check_personality_pre, CHECK_PERSONALITY, CHECK_PERSONALITY_DEPTH.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo [HR [DJ [HMI [ST LO]]]].
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as [Hlo _].
  pose proof (codec_pers_at m HR) as HP. unfold codec_pers_cells in HP.
  pose proof (cp_relro_bytes m HR) as HRB. clear HR. change codec_relro_base with 127472 in HRB.
  pose proof cp_relro_len as LRB.
  pose proof DJ as DJz. unfold disj, RELRO_BASE, RELRO_LEN in DJz.
  carve_frame 32%nat ST.
  assert (MU : munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m) by apply munch_refl.
  assert (WM : wmono rsegs m m) by apply wmono_refl.
  assert (U32 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32)
    by (apply unsigned_lit; lia).
  (* addi sp; sd ra, s0, s1; addi a0, zero, 1; jal personality_of *)
  do 6 zstep.
  cp_of POF.
  (* mv s1, a0; addi a0, zero, 2; jal personality_of *)
  do 3 zstep.
  cp_of POF.
  (* beqz s1; mv s0, a0; beqz a0 *)
  zstep. cp_br. zstep. zstep. cp_br.
  (* ld a0, 8(s1); auipc; addi; jal strcmp *)
  do 4 zstep.
  cp_strcmp SC codec_str_c24.
  (* bnez a0; four field tests of s1 *)
  zstep. cp_br.
  do 3 zstep. cp_br. do 3 zstep. cp_br. do 3 zstep. cp_br. do 3 zstep. cp_br.
  (* ld a0, 8(s0); auipc; addi; jal strcmp *)
  do 4 zstep.
  cp_strcmp SC codec_str_pc.
  zstep. cp_br.
  (* four field tests of s0 *)
  do 2 zstep. cp_br. do 3 zstep. cp_br. do 2 zstep. cp_br. do 3 zstep. cp_br.
  (* mv a0, zero; jal personality_of; bnez a0 *)
  do 2 zstep.
  cp_of POF.
  zstep. cp_br.
  (* the five from_name calls: auipc; addi; jal; bne/bnez *)
  do 3 zstep. cp_fn FN lo (codec_str_c24 ++ [Z_to_bv 8 0]) U32. zstep. cp_br.
  do 3 zstep. cp_fn FN lo (codec_str_pc ++ [Z_to_bv 8 0]) U32. zstep. cp_br.
  do 3 zstep. cp_fn FN lo (codec_str_c2 ++ [Z_to_bv 8 0]) U32. zstep. cp_br.
  do 3 zstep. cp_fn FN lo (codec_str_pcs ++ [Z_to_bv 8 0]) U32. zstep. cp_br.
  do 3 zstep. cp_fn FN lo (codec_str_nil ++ [Z_to_bv 8 0]) U32. zstep. cp_br.
  (* ld ra, s0, s1; release the frame; addi sp; ret *)
  do 3 zstep.
  match goal with H : stk rsegs _ lo (bv_unsigned sp + -32) |- _ =>
    eapply stk_release in FR; [ | exact H | lia ]; clear H end.
  cbn [cells_size csize Nat.add] in FR.
  replace (bv_unsigned sp + -32 + Z.of_nat 32) with (bv_unsigned sp) in FR by lia.
  do 2 zstep.
  finish.
Qed.
