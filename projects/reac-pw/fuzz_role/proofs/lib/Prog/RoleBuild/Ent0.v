(** ent_build's kind 0, ent_headamp_key (pod.h:224-262): c and p, then ch = the decimal text of c % 64 (c < 200,
    the digit loop 0x133a0 and the reverse copy 0x133f4) or odd_ch[c % 14] (c >= 200: the .data.rel.ro pointer,
    strlen, memcpy with its NUL), into ch[24] at sp + 0x110; from 0x13428 the parts and ent_text (Ent0Cut.parts_at,
    a premise here). From the jump table's target 0x13360, and from 0x1337c when no input byte is left. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c memcpy_c strlen_c.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Tables Model Layout RoleImg.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog.RoleBuild Require Import EntCut EntFacts EntTbl EntText Ent0Cut.
Import ListNotations.
Open Scope Z_scope.

Lemma le1_small : forall z, 0 <= z < 256 -> le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof. intros z Hz. unfold le1. rewrite unsigned_lit by lia. reflexivity. Qed.


Lemma byte_lit_unsigned : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 8) with 256. lia.
Qed.

Lemma digit_not_nul : forall d, 0 <= d < 10 -> ~ In NUL [Z_to_bv 8 (48 + d)].
Proof.
  intros d Hd [E|[]]. apply (f_equal bv_unsigned) in E. rewrite byte_lit_unsigned in E by lia.
  change (bv_unsigned NUL) with 0 in E. lia.
Qed.

Lemma digits2_not_nul : forall d1 d0, 0 <= d1 < 10 -> 0 <= d0 < 10 ->
  ~ In NUL [Z_to_bv 8 (48 + d1); Z_to_bv 8 (48 + d0)].
Proof.
  intros d1 d0 H1 H0 [E|[E|[]]]; apply (f_equal bv_unsigned) in E; rewrite byte_lit_unsigned in E by lia;
    change (bv_unsigned NUL) with 0 in E; lia.
Qed.

Lemma str_split : forall (s sl : list byte), s ++ NUL :: sl = (s ++ [NUL]) ++ sl.
Proof. intros s sl. rewrite <- app_assoc. reflexivity. Qed.

Lemma zxb_unsigned : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof. intros b. unfold zxb. pose proof (byte_range b). apply unsigned_lit. lia. Qed.

(** ch as ent_headamp_key picks it from c. *)
Definition chsel (c : Z) : list byte := if c <? 200 then dec64 (c mod 64) else nth (Z.to_nat (c mod 14)) odd_ch [].
Definition key_of (c p : Z) : list byte :=
  join_parts [HPFX; chsel c; if Z.testbit p 7 then [] else DOT; nth (Z.to_nat (p mod 8)) param []].

Lemma ent0_cp : forall (b c pb : byte) rest, bv_unsigned b mod 10 = 0 ->
  ent_build (b :: c :: pb :: rest) = (ent_text (key_of (bv_unsigned c) (bv_unsigned pb)) true, rest).
Proof. intros b c pb rest H. unfold ent_build. cbn [fuzz_u8]. rewrite H. reflexivity. Qed.

Lemma ent0_c1 : forall (b c : byte), bv_unsigned b mod 10 = 0 ->
  ent_build [b; c] = (ent_text (key_of (bv_unsigned c) 0) true, []).
Proof. intros b c H. unfold ent_build. cbn [fuzz_u8]. rewrite H. reflexivity. Qed.

Lemma ent0_b : forall (b : byte), bv_unsigned b mod 10 = 0 -> ent_build [b] = (ent_text (key_of 0 0) true, []).
Proof. intros b H. unfold ent_build. cbn [fuzz_u8]. rewrite H. reflexivity. Qed.

Lemma ent0_nil : ent_build [] = (ent_text (key_of 0 0) true, []).
Proof. reflexivity. Qed.

Section Case0.
Variables (sp gp tp s7 s9 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
          (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.
Hypothesis MCPY : memcpy_contract.
Hypothesis STRL : strlen_contract.
Hypothesis PARTS : parts_at sp gp tp s7 s9 F fc m r src pp lo.

Local Abbreviation QE := (QJ sp gp tp s7 s9 F fc m r src pp lo (ent_build r)).
Local Abbreviation S0 := (Z_to_bv 64 (bv_unsigned sp + 0x128)).
Local Abbreviation S1 := (Z_to_bv 64 (bv_unsigned sp + 0xf0)).
Local Abbreviation S2 := (Z_to_bv 64 (0xcccccccd * 2^32)).
Local Abbreviation S8 := (Z_to_bv 64 95).
Local Abbreviation S10 := (Z_to_bv 64 10).

Definition sep_of (p : Z) : list byte := if Z.testbit p 7 then [] else DOT.

(** 0x13390: the digits of c % 64 (c < 200) into ch, then the parts. *)
Lemma digits_ok : forall (cb : byte) (p : Z) (r' : list byte)
    (ra t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s3 s5 s6 s11 t3 t4 t5 t6 : word) m1,
  bv_unsigned cb < 200 -> 0 <= p < 256 ->
  ent_build r = (ent_text (join_parts [HPFX; dec64 (bv_unsigned cb mod 64); sep_of p;
                                       nth (Z.to_nat (p mod 8)) param []]) true, r') ->
  s6 = Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r')) ->
  MemC sp m r src pp lo m1 (zeros 104) ->
  bytes_at rsegs m1 (bv_unsigned sp + 120) (le8 (Z_to_bv 64 (Z.of_nat (length r')))) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 S0 S1 a0 (zxb cb) a2 a3 a4 a5 a6 a7 S2 s3 (Z_to_bv 64 p) s5 s6 s7 S8 s9 S10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x13390) fc None m1 (seg_rom rsegs)).
Proof.
  intros cb p r' ra t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s3 s5 s6 s11 t3 t4 t5 t6 m1 Hc Hp Eb -> MC H78.
  pose proof (ep_range sp m r src pp lo HE) as R.
  (* 0x13390 mv a0,zero; andi a3,a1,0x3f; addi a4,zero,1; addi a7,zero,9 *)
  do 4 step.
  match goal with |- context [Z.land (bv_unsigned (zxb cb)) 63] =>
    replace (Z.land (bv_unsigned (zxb cb)) 63) with (bv_unsigned cb mod 64) by (clear - cb; revert cb; byte_eq) end.
  pose proof (Z.mod_pos_bound (bv_unsigned cb) 64 ltac:(lia)) as Hv.
  (* loop turn 0: 0x133a0 .. 0x133d0 *)
  do 13 step.
  match goal with |- context [Z.lor ?E 48] =>
    replace (Z.lor E 48) with (48 + (bv_unsigned cb mod 64) mod 10) by (clear - cb; revert cb; byte_eq) end.
  match goal with |- context [Z.shiftr ?E 35] =>
    replace (Z.shiftr E 35) with ((bv_unsigned cb mod 64) / 10) by (clear - cb; revert cb; byte_eq) end.
  (* 0x133d4 sb a6,0(a4) *)
  pre_store HE (bv_unsigned sp + 240) 1%nat. step.
  mstore_out HE. rename HW into HD0.
  rewrite le1_small in HD0 by (pose proof (Z.mod_pos_bound (bv_unsigned cb mod 64) 10 ltac:(lia)); lia).
  (* 0x133d8 addi a4,a2,1; bltu a7,a5 *)
  do 2 step.
  unfold bv_ltu. rewrite (unsigned_lit (bv_unsigned cb mod 64)) by lia.
  destruct (Z.le_gt_cases (bv_unsigned cb mod 64) 9) as [Hv1|Hv2].
  - (* one digit *)
    if_false.
    (* 0x133e0 beqz a0; slli a2; srli a3; addi a2,sp,0x110; add a3,a2,a3 *)
    step. if_false. do 4 step.
    (* 0x133f4 slli a4,a1,32; srli; add a4,s1,a4; lbu a4,0(a4) *)
    pose proof (bytes_at_byte _ _ _ 0 HD0 ltac:(cbn; lia)) as HR. cbn [nth] in HR.
    do 4 step. clear HR.
    (* 0x13404 sb a4,0(a2) *)
    pre_store HE (bv_unsigned sp + 272) 1%nat. step. mstore_out HE. rename HW into HC0.
    rewrite le1_zxb in HC0.
    (* addi a2,a2,1; addi a1,a1,-1; bne a2,a3 *)
    do 3 step. if_false.
    (* 0x13414 slli a0; srli a0; addi a1,sp,0x110; add a0,a1,a0; sb zero,0(a0) *)
    do 4 step.
    pre_store HE (bv_unsigned sp + 273) 1%nat. step. mstore_out HE. rename HW into HN.
    eapply (PARTS p [Z_to_bv 8 (48 + bv_unsigned cb mod 64 mod 10)] r').
    + rewrite Eb. unfold dec64, digit, sep_of. replace (bv_unsigned cb mod 64 <? 10) with true by lia.
      rewrite (Z.mod_small (bv_unsigned cb mod 64) 10) by lia. reflexivity.
    + exact Hp.
    + reflexivity.
    + reflexivity.
    + cbn. lia.
    + apply digit_not_nul. pose proof (Z.mod_pos_bound (bv_unsigned cb mod 64) 10). lia.
    + eassumption.
    + exact H78.
    + apply bytes_at_app. split; [exact HC0|]. cbn [length].
      replace (bv_unsigned sp + 272 + Z.of_nat 1) with (bv_unsigned sp + 273) by lia. exact HN.
  - (* two digits: loop turn 1, 0x133a0 .. 0x133d0 *)
    if_true.
    do 13 step.
    match goal with |- context [Z.lor ?E 48] =>
      replace (Z.lor E 48) with (48 + (bv_unsigned cb mod 64 / 10) mod 10) by (clear - cb; revert cb; byte_eq) end.
    match goal with |- context [Z.shiftr ?E 35] =>
      replace (Z.shiftr E 35) with ((bv_unsigned cb mod 64 / 10) / 10) by (clear - cb; revert cb; byte_eq) end.
    (* 0x133d4 sb a6,0(a4) *)
    pre_store HE (bv_unsigned sp + 241) 1%nat. step. mstore_out HE. rename HW into HD1.
    rewrite le1_small in HD1 by (pose proof (Z.mod_pos_bound (bv_unsigned cb mod 64 / 10) 10 ltac:(lia)); lia).
    (* addi a4,a2,1; bltu a7,a5 *)
    do 2 step.
    unfold bv_ltu. rewrite (unsigned_lit (bv_unsigned cb mod 64 / 10)) by (split; [apply Z.div_pos | ]; lia).
    if_false.
    (* 0x133e0 beqz a0; slli a2; srli a3; addi a2,sp,0x110; add a3,a2,a3 *)
    step. if_false. do 4 step.
    (* reverse turn 1: r[1] to ch[0] *)
    pose proof (bytes_at_byte _ _ _ 0 HD1 ltac:(cbn; lia)) as HR. cbn [nth] in HR.
    do 4 step. clear HR.
    pre_store HE (bv_unsigned sp + 272) 1%nat. step. mstore_out HE. rename HW into HC0.
    rewrite le1_zxb in HC0.
    do 3 step.
    unfold bv_eqb. rewrite (unsigned_lit (bv_unsigned sp + 273)), (unsigned_lit (bv_unsigned sp + 274)) by lia.
    if_true.
    (* reverse turn 2: r[0] to ch[1] *)
    pose proof (bytes_at_byte _ _ _ 0 HD0 ltac:(cbn; lia)) as HR. cbn [nth] in HR.
    do 4 step. clear HR.
    pre_store HE (bv_unsigned sp + 273) 1%nat. step. mstore_out HE. rename HW into HC1.
    rewrite le1_zxb in HC1.
    do 3 step. if_false.
    (* 0x13414 .. 0x13424: ch[2] = 0 *)
    do 4 step.
    pre_store HE (bv_unsigned sp + 274) 1%nat. step. mstore_out HE. rename HW into HN.
    pose proof (Z.mod_pos_bound (bv_unsigned cb mod 64) 10 ltac:(lia)) as Hm10.
    assert (Hd : bv_unsigned cb mod 64 / 10 < 10) by (apply Z.div_lt_upper_bound; lia).
    eapply (PARTS p [Z_to_bv 8 (48 + (bv_unsigned cb mod 64 / 10) mod 10); Z_to_bv 8 (48 + bv_unsigned cb mod 64 mod 10)] r').
    + rewrite Eb. unfold dec64, digit, sep_of. replace (bv_unsigned cb mod 64 <? 10) with false by lia.
      rewrite (Z.mod_small (bv_unsigned cb mod 64 / 10) 10) by (split; [apply Z.div_pos|]; lia). reflexivity.
    + exact Hp.
    + reflexivity.
    + reflexivity.
    + cbn. lia.
    + apply digits2_not_nul; apply Z.mod_pos_bound; lia.
    + eassumption.
    + exact H78.
    + change ([Z_to_bv 8 (48 + (bv_unsigned cb mod 64 / 10) mod 10); Z_to_bv 8 (48 + bv_unsigned cb mod 64 mod 10)]
              ++ [NUL])
        with ([Z_to_bv 8 (48 + (bv_unsigned cb mod 64 / 10) mod 10)] ++
              ([Z_to_bv 8 (48 + bv_unsigned cb mod 64 mod 10)] ++ [NUL])).
      apply bytes_at_app. split; [exact HC0|]. cbn [length].
      replace (bv_unsigned sp + 272 + Z.of_nat 1) with (bv_unsigned sp + 273) by lia.
      apply bytes_at_app. split; [exact HC1|]. cbn [length].
      replace (bv_unsigned sp + 273 + Z.of_nat 1) with (bv_unsigned sp + 274) by lia. exact HN.
Qed.

(** 0x13a64: s3 = o, the pointer to odd_ch's text s; strlen, memcpy(ch, o, |s| + 1), s6 = s5, then the parts. *)
Lemma odd_tail : forall (o : Z) (s : list byte) (p : Z) (r' : list byte)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s11 t3 t4 t5 t6 : word) m1,
  ent_build r = (ent_text (join_parts [HPFX; s; sep_of p; nth (Z.to_nat (p mod 8)) param []]) true, r') ->
  str_ok o s = true -> (length s <= 21)%nat -> 0 <= p < 256 ->
  MemC sp m r src pp lo m1 (zeros 104) ->
  bytes_at rsegs m1 (bv_unsigned sp + 120) (le8 (Z_to_bv 64 (Z.of_nat (length r')))) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 S0 S1 a0 a1 a2 a3 a4 a5 a6 a7 S2 (Z_to_bv 64 o) (Z_to_bv 64 p)
             (Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r'))) s6 s7 S8 s9 S10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13a64) fc None m1 (seg_rom rsegs)).
Proof.
  intros o s p r' ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s11 t3 t4 t5 t6 m1 Eb Hok Hl Hp MC H78.
  pose proof (ep_range sp m r src pp lo HE) as R.
  pose proof (MemC_mem_inv _ _ _ _ _ _ _ _ MC) as MI.
  destruct (str_ok_facts m1 o s MI Hok) as (SB & SL & NN & ROM & P0 & P1).
  pose proof (img_apart sp m r src pp lo HE o (S (length s)) ROM ltac:(lia)) as AP.
  (* 0x13a64 mv a0,s3; jal strlen *)
  do 2 step.
  eapply evt_cut.
  { eapply STRL with (str := s) (slack := slack_of (o + Z.of_nat (length s) + 1)).
    - rewrite unsigned_lit by lia. exact SB.
    - exact NN.
    - rewrite unsigned_lit by lia. exact SL.
    - exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
              E & MU2 & WM2 & MI2 & SB2). subst ms'.
  pose proof (MemC_call_nil sp m r src pp lo m1 m2 _ MC MU2 WM2 MI2) as MC2.
  pose proof (bytes_at_transport rsegs _ _ _ _ _ H78 MU2 I) as X78. clear H78. rename X78 into H78.
  rewrite unsigned_lit in SB2 by lia.
  clear MC MU2 WM2 MI SB.
  rewrite ret_pc_even by (lia || reflexivity).
  (* 0x13a6c addi a2,a0,1; addi a0,sp,0x110; mv a1,s3; jal memcpy *)
  do 4 step.
  destruct (MemC_cells sp m r src pp lo HE m2 _ (bv_unsigned sp + 272) (S (length s)) MC2
              ltac:(lia) ltac:(unfold FRAME_LOCALS; lia)) as (jk & Ljk & CJ).
  change (Z_to_bv 8 0) with NUL in SB2.
  rewrite (str_split s (slack_of (o + Z.of_nat (length s) + 1))) in SB2.
  apply bytes_at_app in SB2 as [SBs _].
  eapply evt_cut.
  { eapply MCPY with (src := s ++ [NUL]) (junk := jk); rewrite ?unsigned_lit by lia.
    - exact SBs.
    - rewrite length_app. cbn [length]. lia.
    - replace (Z.to_nat (Z.of_nat (length s) + 1)) with (S (length s)) by lia. exact CJ.
    - unfold FRAME_LOCALS in AP. lia.
    - exact MI2. }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m3 &
              E3 & MU3 & WM3 & MI3 & RC3 & BS3). subst ms'.
  rewrite !unsigned_lit in MU3, RC3 by lia.
  apply rw_CB_bytes in RC3 as [B3 L3].
  pose proof (MemC_call_hi sp m r src pp lo HE m2 m3 _ _ _ _ MC2 MU3 WM3 MI3 B3
                ltac:(rewrite L3; lia) ltac:(lia) ltac:(unfold FRAME_LOCALS; lia)) as MC3.
  pose proof (bytes_at_transport rsegs _ _ _ _ _ H78 MU3 ltac:(cbn [disjoint_from]; simpl_len; split; [lia | exact I]))
    as X78. clear H78. rename X78 into H78.
  clear MC2 MU3 WM3 MI3 BS3 CJ SBs MI2.
  rewrite ret_pc_even by (lia || reflexivity).
  (* 0x13a7c mv s6,s5; j 0x13428 *)
  do 2 step.
  eapply (PARTS p s r').
  - exact Eb.
  - exact Hp.
  - reflexivity.
  - reflexivity.
  - exact Hl.
  - exact NN.
  - exact MC3.
  - exact H78.
  - exact B3.
Qed.

Local Ltac oddk k Hk14 Eb Hp :=
  rewrite Hk14; do 2 step;
  let HRd := fresh "HRd" in
  lazymatch goal with MC : MemC _ _ _ _ _ _ ?mm _ |- _ =>
    pose proof (relro_read sp m r src pp lo HE mm _ (9 + k)%nat MC ltac:(lia)) as HRd end;
  unfold RELRO_TBL in HRd; step; clear HRd;
  eapply (odd_tail _ (nth k odd_ch []) _ _);
  [ rewrite Eb, Hk14; reflexivity
  | vm_compute; reflexivity
  | apply Nat.leb_le; vm_compute; reflexivity
  | exact Hp
  | eassumption
  | eassumption ].

(** 0x13a34 (c >= 200): odd_ch[c % 14]'s pointer from .data.rel.ro, then odd_tail. *)
Lemma odd_ok : forall (cb : byte) (p : Z) (r' : list byte)
    (ra t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s3 s6 s11 t3 t4 t5 t6 : word) m1,
  200 <= bv_unsigned cb -> 0 <= p < 256 ->
  ent_build r = (ent_text (join_parts [HPFX; nth (Z.to_nat (bv_unsigned cb mod 14)) odd_ch []; sep_of p;
                                       nth (Z.to_nat (p mod 8)) param []]) true, r') ->
  MemC sp m r src pp lo m1 (zeros 104) ->
  bytes_at rsegs m1 (bv_unsigned sp + 120) (le8 (Z_to_bv 64 (Z.of_nat (length r')))) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 S0 S1 a0 (zxb cb) a2 a3 a4 a5 a6 a7 S2 s3 (Z_to_bv 64 p)
             (Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r'))) s6 s7 S8 s9 S10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13a34) fc None m1 (seg_rom rsegs)).
Proof.
  intros cb p r' ra t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s3 s6 s11 t3 t4 t5 t6 m1 Hc Hp Eb MC H78.
  pose proof (ep_range sp m r src pp lo HE) as R.
  mmi.
  (* 0x13a34 .. 0x13a54: c % 14 by multiply, times 8 *)
  do 9 step.
  match goal with |- context [Z.shiftl ?E 3] =>
    replace E with (bv_unsigned cb mod 14) by (clear - cb; revert cb; byte_eq) end.
  pose proof (Z.mod_pos_bound (bv_unsigned cb) 14 ltac:(lia)) as Hm.
  assert (Hk14 : bv_unsigned cb mod 14 = 0 \/ bv_unsigned cb mod 14 = 1 \/ bv_unsigned cb mod 14 = 2 \/
                 bv_unsigned cb mod 14 = 3 \/ bv_unsigned cb mod 14 = 4 \/ bv_unsigned cb mod 14 = 5 \/
                 bv_unsigned cb mod 14 = 6 \/ bv_unsigned cb mod 14 = 7 \/ bv_unsigned cb mod 14 = 8 \/
                 bv_unsigned cb mod 14 = 9 \/ bv_unsigned cb mod 14 = 10 \/ bv_unsigned cb mod 14 = 11 \/
                 bv_unsigned cb mod 14 = 12 \/ bv_unsigned cb mod 14 = 13) by lia.
  clear Hm.
  destruct Hk14 as [Hk14|[Hk14|[Hk14|[Hk14|[Hk14|[Hk14|[Hk14|[Hk14|[Hk14|[Hk14|[Hk14|[Hk14|[Hk14|Hk14]]]]]]]]]]]]].
  - oddk 0%nat Hk14 Eb Hp.
  - oddk 1%nat Hk14 Eb Hp.
  - oddk 2%nat Hk14 Eb Hp.
  - oddk 3%nat Hk14 Eb Hp.
  - oddk 4%nat Hk14 Eb Hp.
  - oddk 5%nat Hk14 Eb Hp.
  - oddk 6%nat Hk14 Eb Hp.
  - oddk 7%nat Hk14 Eb Hp.
  - oddk 8%nat Hk14 Eb Hp.
  - oddk 9%nat Hk14 Eb Hp.
  - oddk 10%nat Hk14 Eb Hp.
  - oddk 11%nat Hk14 Eb Hp.
  - oddk 12%nat Hk14 Eb Hp.
  - oddk 13%nat Hk14 Eb Hp.
Qed.

(** 0x13a20: c = the byte after kind, read; c > 199 to odd_ch, else to the digits. *)
Lemma c_ok : forall (b cb : byte) rest0 (p : Z) (r' : list byte)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s11 t3 t4 t5 t6 : word) m1,
  r = b :: cb :: rest0 -> 0 <= p < 256 ->
  ent_build r = (ent_text (key_of (bv_unsigned cb) p) true, r') ->
  s5 = Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r')) ->
  MemC sp m r src pp lo m1 (zeros 104) ->
  bytes_at rsegs m1 (bv_unsigned sp + 120) (le8 (Z_to_bv 64 (Z.of_nat (length r')))) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 S0 S1 a0 a1 a2 a3 a4 a5 a6 a7 S2 s3 (Z_to_bv 64 p) s5 (Z_to_bv 64 src) s7 S8 s9
             S10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13a20) fc None m1 (seg_rom rsegs)).
Proof.
  intros b cb rest0 p r' ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s11 t3 t4 t5 t6 m1 Er Hp Eb -> MC H78.
  pose proof (ep_range sp m r src pp lo HE) as R.
  assert (HR : ov_read_bytes rsegs m1 (wa (src + Z.of_nat 1)) 1 = Some [cb]).
  { rewrite (MemC_in_byte sp m r src pp lo m1 (zeros 104) 1 MC) by (rewrite Er; cbn [length]; lia).
    rewrite Er. reflexivity. }
  (* 0x13a20 lbu a1,1(s6); addi a0,zero,0xc7; bltu a0,a1 *)
  do 3 step. clear HR.
  unfold bv_ltu. rewrite zxb_unsigned. pose proof (byte_range cb) as Hcb.
  destruct (Z.lt_ge_cases 199 (bv_unsigned cb)) as [Hc|Hc].
  - if_true.
    eapply (odd_ok cb p r'); [lia | exact Hp | | exact MC | exact H78].
    rewrite Eb. unfold key_of, chsel, sep_of. replace (bv_unsigned cb <? 200) with false by lia. reflexivity.
  - if_false.
    (* 0x13a2c mv s6,s5; j 0x13390 *)
    do 2 step.
    eapply (digits_ok cb p r'); [lia | exact Hp | | reflexivity | exact MC | exact H78].
    rewrite Eb. unfold key_of, chsel, sep_of. replace (bv_unsigned cb <? 200) with true by lia. reflexivity.
Qed.

Lemma case0_ok : case_at sp gp tp s7 s9 F fc m r src pp lo 0 0x13360.
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s11 t3 t4 t5 t6 b rest m1 Er Hk Hs -> -> -> -> MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  (* 0x13360 beqz s5 *)
  step.
  unfold bv_eqb. rewrite (unsigned_lit (Z.of_nat (length r) - 1)) by (rewrite Er in *; cbn [length] in *; lia).
  destruct rest as [|cb [|pb rest']].
  - (* only kind: c = p = 0; 0x13380 sd zero,0x78(sp); mv s4,zero; mv a1,zero; mv s6,a5 *)
    assert (Lr : length r = 1%nat) by (rewrite Er; reflexivity).
    if_true.
    pre_store HE (bv_unsigned sp + 120) 8%nat. step. mstore_out HE. rename HW into H78.
    do 3 step.
    eapply (digits_ok (Z_to_bv 8 0) 0 []).
    + rewrite byte_lit_unsigned by lia. lia.
    + lia.
    + rewrite Er, (ent0_b b Hk). reflexivity.
    + f_equal. rewrite Lr. cbn [length]. lia.
    + eassumption.
    + exact H78.
  - (* kind and c: p = 0; 0x13364 addi a0,zero,2; bne s4,a0; 0x1336c .. *)
    assert (Lr : length r = 2%nat) by (rewrite Er; reflexivity).
    if_false.
    do 2 step.
    unfold bv_eqb. rewrite (unsigned_lit (Z.of_nat (length r))) by lia.
    if_false.
    pre_store HE (bv_unsigned sp + 120) 8%nat. step. mstore_out HE. rename HW into H78.
    do 3 step.
    eapply (c_ok b cb [] 0 []).
    + exact Er.
    + lia.
    + rewrite Er, (ent0_c1 b cb Hk). reflexivity.
    + f_equal. rewrite Lr. cbn [length]. lia.
    + eassumption.
    + exact H78.
  - (* kind, c, p: 0x13a0c mv a0,s4; lbu s4,2(s6); addi a0,a0,-3; sd a0,0x78(sp); addi s5,s6,3 *)
    assert (Lr : length r = S (S (S (length rest')))) by (rewrite Er; reflexivity).
    if_false.
    do 2 step.
    unfold bv_eqb. rewrite (unsigned_lit (Z.of_nat (length r))) by lia.
    if_true.
    assert (HR : ov_read_bytes rsegs m1 (wa (src + Z.of_nat 2)) 1 = Some [pb]).
    { rewrite (MemC_in_byte sp m r src pp lo m1 (zeros 104) 2 MC) by lia. rewrite Er. reflexivity. }
    do 3 step. clear HR.
    pre_store HE (bv_unsigned sp + 120) 8%nat. step. mstore_out HE. rename HW into H78.
    step.
    pose proof (byte_range pb) as Hpb.
    eapply (c_ok b cb (pb :: rest') (bv_unsigned pb) rest').
    + exact Er.
    + lia.
    + rewrite Er, (ent0_cp b cb pb rest' Hk). reflexivity.
    + f_equal. rewrite Lr. lia.
    + eassumption.
    + replace (Z.of_nat (length rest')) with (Z.of_nat (length r) + -3) by lia. exact H78.
Qed.

Lemma case0_nil : case0_nil_at sp gp tp s7 s9 F fc m r src pp lo.
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s11 t3 t4 t5 t6 m1 Er -> -> MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  (* 0x1337c mv a5,s6; sd zero,0x78(sp); mv s4,zero; mv a1,zero; mv s6,a5 *)
  step.
  pre_store HE (bv_unsigned sp + 120) 8%nat. step. mstore_out HE. rename HW into H78.
  do 3 step.
  eapply (digits_ok (Z_to_bv 8 0) 0 []).
  - rewrite byte_lit_unsigned by lia. lia.
  - lia.
  - rewrite Er, ent0_nil. reflexivity.
  - f_equal. rewrite Er. cbn [length]. lia.
  - eassumption.
  - exact H78.
Qed.

End Case0.
