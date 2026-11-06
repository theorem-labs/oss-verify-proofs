(** ent_build's kind 1 (pod.h:286-295): i = fuzz_u8, v = vocab[i % 9] (the .data.rel.ro pointer table at 0x1de68),
    ent_text(e, v, strlen(v), 1) (memcpy into e.body, the NUL), and when kind's bit 7 is set (and n + 2 <= 96) the
    bytes 'x', NUL after it. From the jump table's target 0x1375c to 0x134f8 (bit 7 clear) or 0x1350c (bit 7 set). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c memcpy_c strlen_c.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Tables Model Layout RoleImg.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog.RoleBuild Require Import EntCut EntFacts EntTbl EntText.
Import ListNotations.
Open Scope Z_scope.

(** Kind 1's ent for the vocab text s. *)
Definition case1_ent (kind : Z) (s : list byte) : ent :=
  let e := ent_text s true in
  if Z.testbit kind 7 && (e_size e + 2 <=? 96) then Ent POD_STRING (e_size e + 2) (e_body e ++ [Z_to_bv 8 120; NUL])
  else e.

(** A register's sign as `bgez` tests it. *)
Lemma signed_neg : forall x : word, bv_signed x < 0 <-> 2^63 <= bv_unsigned x.
Proof.
  intros x. pose proof (bv_lts_zero_r x) as H. unfold bv_lts in H. change (bv_signed (Z_to_bv 64 0)) with 0 in H.
  rewrite <- Z.ltb_lt, H, Z.leb_le. reflexivity.
Qed.

Lemma ent1_eq : forall (b v : byte) rest, bv_unsigned b mod 10 = 1 ->
  ent_build (b :: v :: rest) = (case1_ent (bv_unsigned b) (nth (Z.to_nat (bv_unsigned v mod 9)) vocab []), rest).
Proof. intros b v rest H. unfold ent_build. cbn [fuzz_u8]. rewrite H. reflexivity. Qed.

Lemma ent1_nil : forall (b : byte), bv_unsigned b mod 10 = 1 ->
  ent_build [b] = (case1_ent (bv_unsigned b) (nth 0 vocab []), []).
Proof. intros b H. unfold ent_build. cbn [fuzz_u8]. rewrite H. reflexivity. Qed.

Section Case1.
Variables (sp gp tp s7 s9 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
          (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.
Hypothesis MCPY : memcpy_contract.
Hypothesis STRL : strlen_contract.

Local Abbreviation QE := (QJ sp gp tp s7 s9 F fc m r src pp lo (ent_build r)).
Local Abbreviation S0 := (Z_to_bv 64 (bv_unsigned sp + 0x128)).
Local Abbreviation S1 := (Z_to_bv 64 (bv_unsigned sp + 0xf0)).
Local Abbreviation S2 := (Z_to_bv 64 (0xcccccccd * 2^32)).
Local Abbreviation S8 := (Z_to_bv 64 95).
Local Abbreviation S10 := (Z_to_bv 64 10).

(** 0x13914 .. the join, with s4 = p, the pointer to the text s. *)
Lemma vocab_tail : forall (p : Z) (s : list byte) (kind cur : Z) (r' : list byte)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s11 t3 t4 t5 t6 : word) m1,
  ent_build r = (case1_ent kind s, r') -> str_ok p s = true -> (length s <= 18)%nat ->
  (bv_signed s11 < 0 <-> Z.testbit kind 7 = true) ->
  cur = src + Z.of_nat (length r) - Z.of_nat (length r') ->
  MemC sp m r src pp lo m1 (zeros 104) ->
  bytes_at rsegs m1 (bv_unsigned sp + 40) (le8 (Z_to_bv 64 cur)) ->
  bytes_at rsegs m1 (bv_unsigned sp + 120) (le8 (Z_to_bv 64 (Z.of_nat (length r')))) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 S0 S1 a0 a1 a2 a3 a4 a5 a6 a7 S2 s3 (Z_to_bv 64 p) s5 s6 s7 S8 s9 S10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13914) fc None m1 (seg_rom rsegs)).
Proof.
  intros p s kind cur r' ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s11 t3 t4 t5 t6 m1 Eb Hok Hl Hs -> MC H28 H78.
  pose proof (ep_range sp m r src pp lo HE) as R.
  pose proof (MemC_mem_inv _ _ _ _ _ _ _ _ MC) as MI.
  destruct (str_ok_facts m1 p s MI Hok) as (SB & SL & NN & ROM & P0 & P1).
  pose proof (img_apart sp m r src pp lo HE p (S (length s)) ROM ltac:(lia)) as AP.
  (* 0x13914 mv a0,s4; jal strlen *)
  do 2 step.
  eapply evt_cut.
  { eapply STRL with (str := s) (slack := slack_of (p + Z.of_nat (length s) + 1)).
    - rewrite unsigned_lit by lia. exact SB.
    - exact NN.
    - rewrite unsigned_lit by lia. exact SL.
    - exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
              E & MU2 & WM2 & MI2 & SB2). subst ms'.
  pose proof (MemC_call_nil sp m r src pp lo m1 m2 _ MC MU2 WM2 MI2) as MC2.
  pose proof (bytes_at_transport rsegs _ _ _ _ _ H28 MU2 I) as X28. clear H28. rename X28 into H28.
  pose proof (bytes_at_transport rsegs _ _ _ _ _ H78 MU2 I) as X78. clear H78. rename X78 into H78.
  rewrite unsigned_lit in SB2 by lia.
  clear MC MU2 WM2 MI SB.
  rewrite ret_pc_even by (lia || reflexivity).
  (* 0x1391c addi a1,zero,0x5f; mv s6,a0; mv s5,a0; bltu a0,a1 *)
  do 4 step.
  unfold bv_ltu. rewrite (unsigned_lit (Z.of_nat (length s))) by lia.
  if_true.
  (* 0x13930 addi s3,sp,0x90; mv a0,s3; mv a1,s4; mv a2,s5; jal memcpy *)
  do 5 step.
  destruct (MemC_cells sp m r src pp lo HE m2 _ (bv_unsigned sp + 144) (length s) MC2
              ltac:(lia) ltac:(unfold FRAME_LOCALS; lia)) as (jk & Ljk & CJ).
  apply bytes_at_app in SB2 as [SBs _].
  eapply evt_cut.
  { eapply MCPY with (src := s) (junk := jk); rewrite ?unsigned_lit by lia.
    - exact SBs.
    - lia.
    - rewrite Nat2Z.id. exact CJ.
    - unfold FRAME_LOCALS in AP. lia.
    - exact MI2. }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m3 &
              E3 & MU3 & WM3 & MI3 & RC3 & BS3). subst ms'.
  rewrite !unsigned_lit in MU3, RC3 by lia.
  apply rw_CB_bytes in RC3 as [B3 L3].
  pose proof (MemC_call_e sp m r src pp lo HE m2 m3 _ _ _ _ MC2 MU3 WM3 MI3 B3 ltac:(lia) ltac:(lia) ltac:(lia)) as MC3.
  pose proof (bytes_at_transport rsegs _ _ _ _ _ H28 MU3 ltac:(cbn [disjoint_from]; simpl_len; split; [lia | exact I]))
    as X28. clear H28. rename X28 into H28.
  pose proof (bytes_at_transport rsegs _ _ _ _ _ H78 MU3 ltac:(cbn [disjoint_from]; simpl_len; split; [lia | exact I]))
    as X78. clear H78. rename X78 into H78.
  clear MC2 MU3 WM3 MI3 B3 BS3 CJ SBs MI2.
  rewrite ret_pc_even by (lia || reflexivity).
  (* 0x13944 addi s4,s5,1; add a0,s3,s5; addi s3,zero,8; sb zero,0(a0) *)
  do 3 step.
  pre_store HE (bv_unsigned sp + 144 + Z.of_nat (length s)) 1%nat. step. mstore_e HE (8 + Z.of_nat (length s)).
  (* 0x13954 sw s3,0x88(sp); sw s4,0x8c(sp) *)
  pre_store HE (bv_unsigned sp + 136) 4%nat. step. mstore_e HE 0.
  pre_store HE (bv_unsigned sp + 140) 4%nat. step. mstore_e HE 4.
  (* 0x1395c bgez s11 *)
  step.
  assert (Hl1 : ent_text s true = Ent POD_STRING (Z.of_nat (length s) + 1) (s ++ [NUL])).
  { unfold ent_text. rewrite firstn_all2 by lia. f_equal. rewrite length_app. cbn [length]. lia. }
  if_cases E; zify_cond E.
  - (* bit 7 clear: 0x13b84 ld s6,0x28(sp); j 0x134f8 *)
    assert (K7 : Z.testbit kind 7 = false).
    { destruct (Z.testbit kind 7) eqn:K; [|reflexivity]. exfalso. pose proof (proj2 Hs eq_refl) as X.
      apply signed_neg in X. lia. }
    pose proof (bytes_at_read8 _ _ _ H28 (length_le8 _)) as HR28.
    do 2 step. clear HR28.
    eapply join_134f8.
    + rewrite Eb. unfold case1_ent. rewrite K7. cbn [andb]. rewrite Hl1. reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + eapply MemC_e_ext; [eassumption|]. apply text_chain; [reflexivity | lia | lia | lia | lia | lia].
    + exact H78.
  - (* bit 7 set: 0x13960 .. 0x139a0 *)
    assert (K7 : Z.testbit kind 7 = true) by (apply Hs; apply signed_neg; lia).
    pose proof (bytes_at_read8 _ _ _ H28 (length_le8 _)) as HR28.
    mcells.
    (* ld a6,0x80(sp); addi a1,zero,0x5d; ld a7,0x68(sp); ld t0,0x60(sp); ld a2,0x28(sp); bltu a1,s6 *)
    do 6 step. clear HR28.
    unfold bv_ltu. rewrite (unsigned_lit (Z.of_nat (length s))) by lia.
    if_false.
    (* addi a1,sp,0x90; add a1,a1,s4; addi s4,s5,3; sb zero,2(a0) *)
    do 3 step.
    pre_store HE (bv_unsigned sp + 144 + Z.of_nat (length s) + 2) 1%nat. step.
    mstore_e HE (8 + Z.of_nat (length s) + 2).
    (* addi a0,zero,0x78; sb a0,0(a1) *)
    step.
    pre_store HE (bv_unsigned sp + 144 + (Z.of_nat (length s) + 1)) 1%nat. step.
    mstore_e HE (8 + Z.of_nat (length s) + 1).
    (* sw s4,0x8c(sp) *)
    pre_store HE (bv_unsigned sp + 140) 4%nat. step. mstore_e HE 4.
    (* mv s6,a2; ld s11,0x50(sp); lui s5,0x4; j 0x1350c *)
    mcells. do 4 step.
    eapply join_1350c.
    + rewrite Eb. unfold case1_ent. rewrite K7. rewrite Hl1. cbn [andb e_size e_body].
      replace (Z.of_nat (length s) + 1 + 2 <=? 96) with true by (symmetry; apply Z.leb_le; lia).
      reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + f_equal. cbn [e_size]. lia.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + eapply MemC_e_ext; [eassumption|].
      replace (Z.of_nat (length s) + 1 + 2) with (Z.of_nat (length s) + 3) by lia.
      apply text_chain_x; first [reflexivity | lia].
    + exact H78.
Qed.

(** The pointer load at 0x13910 for vocab entry k, then vocab_tail. *)
Local Ltac c1tail k b v rest' Er Hk Hk9 Lr Hs :=
  rewrite Hk9; do 4 step;
  let HRd := fresh "HRd" in
  lazymatch goal with MC : MemC _ _ _ _ _ _ ?mm _ |- _ =>
    pose proof (relro_read sp m r src pp lo HE mm _ k MC ltac:(lia)) as HRd end;
  unfold RELRO_TBL in HRd; step; clear HRd;
  eapply (vocab_tail _ (nth k vocab []) (bv_unsigned b) (src + 2) rest');
  [ rewrite Er, (ent1_eq b v rest' Hk), Hk9; reflexivity
  | vm_compute; reflexivity
  | apply Nat.leb_le; vm_compute; reflexivity
  | exact Hs
  | rewrite Lr; lia
  | eassumption
  | eassumption
  | replace (Z.of_nat (length rest')) with (Z.of_nat (length r) + -2) by lia; eassumption ].

Lemma case1_ok : case_at sp gp tp s7 s9 F fc m r src pp lo 1 0x1375c.
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s11 t3 t4 t5 t6 b rest m1 Er Hk Hs -> -> -> -> MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  (* 0x1375c beqz s5 *)
  step.
  unfold bv_eqb. rewrite (unsigned_lit (Z.of_nat (length r) - 1)) by (rewrite Er in *; cbn [length] in *; lia).
  destruct rest as [|v rest'].
  - (* no byte left: i = 0; 0x138f4 sd a5,0x28(sp); sd zero,0x78(sp); mv a0,zero *)
    assert (Lr : length r = 1%nat) by (rewrite Er; reflexivity).
    if_true.
    pre_store HE (bv_unsigned sp + 40) 8%nat. step. mstore_out HE. rename HW into H28.
    pre_store HE (bv_unsigned sp + 120) 8%nat. step. mstore_out HE. rename HW into H78.
    step.
    (* 0x13900 slli; auipc; addi; add; ld s4,0(a0) *)
    do 4 step.
    lazymatch goal with MC : MemC _ _ _ _ _ _ ?mm _ |- _ =>
      pose proof (relro_read sp m r src pp lo HE mm _ 0 MC ltac:(lia)) as HRd end.
    unfold RELRO_TBL in HRd. step. clear HRd.
    eapply (vocab_tail _ (nth 0 vocab []) (bv_unsigned b) (src + 1) []).
    + rewrite Er, (ent1_nil b Hk). reflexivity.
    + vm_compute. reflexivity.
    + apply Nat.leb_le. vm_compute. reflexivity.
    + exact Hs.
    + rewrite Lr. cbn [length]. lia.
    + eassumption.
    + exact H28.
    + exact H78.
  - assert (Lr : length r = S (S (length rest'))) by (rewrite Er; reflexivity).
    if_false.
    (* 0x13760 lbu a0,1(s6) *)
    assert (HR : ov_read_bytes rsegs m1 (wa (src + Z.of_nat 1)) 1 = Some [v]).
    { rewrite (MemC_in_byte sp m r src pp lo m1 (zeros 104) 1 MC) by lia. rewrite Er. reflexivity. }
    step. clear HR.
    (* addi s4,s4,-2; sd s4,0x78(sp); addi s6,s6,2; sd s6,0x28(sp) *)
    step.
    pre_store HE (bv_unsigned sp + 120) 8%nat. step. mstore_out HE. rename HW into H78.
    step.
    pre_store HE (bv_unsigned sp + 40) 8%nat. step. mstore_out HE. rename HW into H28.
    (* i % 9 (0x13774-0x1378c); j 0x13900 *)
    do 7 step.
    match goal with |- context [Z.land ?E 255] =>
      replace (Z.land E 255) with (bv_unsigned v mod 9) by (clear - v; revert v; byte_eq) end.
    step.
    pose proof (Z.mod_pos_bound (bv_unsigned v) 9 ltac:(lia)) as Hm.
    assert (Hk9 : bv_unsigned v mod 9 = 0 \/ bv_unsigned v mod 9 = 1 \/ bv_unsigned v mod 9 = 2 \/
                  bv_unsigned v mod 9 = 3 \/ bv_unsigned v mod 9 = 4 \/ bv_unsigned v mod 9 = 5 \/
                  bv_unsigned v mod 9 = 6 \/ bv_unsigned v mod 9 = 7 \/ bv_unsigned v mod 9 = 8) by lia.
    clear Hm.
    destruct Hk9 as [Hk9|[Hk9|[Hk9|[Hk9|[Hk9|[Hk9|[Hk9|[Hk9|Hk9]]]]]]]].
    + c1tail 0%nat b v rest' Er Hk Hk9 Lr Hs.
    + c1tail 1%nat b v rest' Er Hk Hk9 Lr Hs.
    + c1tail 2%nat b v rest' Er Hk Hk9 Lr Hs.
    + c1tail 3%nat b v rest' Er Hk Hk9 Lr Hs.
    + c1tail 4%nat b v rest' Er Hk Hk9 Lr Hs.
    + c1tail 5%nat b v rest' Er Hk Hk9 Lr Hs.
    + c1tail 6%nat b v rest' Er Hk Hk9 Lr Hs.
    + c1tail 7%nat b v rest' Er Hk Hk9 Lr Hs.
    + c1tail 8%nat b v rest' Er Hk Hk9 Lr Hs.
Qed.

End Case1.
