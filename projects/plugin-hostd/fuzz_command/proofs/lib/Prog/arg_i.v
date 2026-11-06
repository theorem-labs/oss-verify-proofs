(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColB/W_set0A.v, with its module paths and module names changed; 44 of its 60 lines of code are new or changed and 129 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Prog/SceneTac.v, with its module paths changed; 1051 of its 1066 lines of code are new or changed and 45 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/U/Prog/pcap_source_open.v, with its module paths, module names and numbers changed; 647 of its 708 lines of code are new or changed and 1005 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes FP Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts printf_facts_c snprintf_c RecAns.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Lemma ai_sx32 : forall z, (-2^31 <= z < 2^31)%Z -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648%Z. change (bv_modulus 32) with 4294967296%Z.
  change (2^64)%Z with 18446744073709551616%Z. change (2^31)%Z with 2147483648%Z in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Lemma ai_lts : forall x y, (-2^63 <= x < 2^63)%Z -> (-2^63 <= y < 2^63)%Z ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = Z.ltb x y.
Proof.
  intros x y Hx Hy. unfold bv_lts. rewrite !Z_to_bv_signed.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 64) with 9223372036854775808%Z.
  change (bv_modulus 64) with 18446744073709551616%Z.
  change (2^63)%Z with 9223372036854775808%Z in Hx, Hy.
  rewrite !Z.mod_small by lia.
  all: f_equal; lia.
Qed.

Lemma ai_rd4 : forall m a v, bytes_at rsegs m a (le4 v) -> ov_read_bytes rsegs m (wa (a + 0)) 4 = Some (le4 v).
Proof.
  intros m a v H. rewrite (bytes_at_read rsegs m a _ 0 4 H) by (rewrite ?length_le4; lia).
  f_equal.
Qed.

Lemma ai_pf_dec : forall v, (-2^31 <= v < 2^31)%Z -> pf_bytes (pf_dec v) = dec v.
Proof.
  intros c Hc. unfold pf_dec, dec. unfold pf_bytes.
  assert (P : (10 ^ Z.of_nat (S 9) = 10000000000)%Z) by reflexivity.
  destruct (Z.ltb_spec c 0) as [N|N].
  - cbn [map app]. f_equal. replace (Z.abs c) with (- c)%Z by lia.
    exact (pf_digits_digits 9 11 (- c) [] ltac:(rewrite P; lia) ltac:(lia)).
  - cbn [app]. replace (Z.abs c) with c by lia.
    exact (pf_digits_digits 9 11 c [] ltac:(rewrite P; lia) ltac:(lia)).
Qed.

Definition AI_FMT : list Z := [37%Z; 100%Z].
Definition AI_PS : list pf_piece := [Pd].

Lemma ai_parse : pf_parse AI_FMT = Some AI_PS.
Proof. reflexivity. Qed.

Lemma ai_text : forall v, pf_text AI_PS [AInt v] = Some (pf_dec v).
Proof. intros v. cbn. rewrite app_nil_r. reflexivity. Qed.

Lemma ai_fmt_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x10828 (pf_bytes (AI_FMT ++ [0%Z])).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | lia | cbn; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Definition ai_mid (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (lo e v mv : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32)
                    (m' : word -> option byte) (junk : list byte),
    munch [(lo, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ frm0 fc' /\
    (forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k) /\
    bytes_at rsegs m' (bv_unsigned sp + -32)%Z (dec v ++ Z_to_bv 8 0 :: junk) /\
    length junk = (15 - length (dec v))%nat /\
    rw_cells rsegs m' (bv_unsigned sp + -16)%Z [C8 s0; C8 ra] /\
    bytes_at rsegs m' (e + 4)%Z (le4 (Z_to_bv 64 mv)) /\
    (((mv = 6)%Z /\
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom rsegs)) \/
     ((mv < 6)%Z /\
      ms' = MS (mkR (Z_to_bv 64 0x15b58) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 e) s1
                    (Z_to_bv 64 (bv_unsigned sp + -32)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (Z_to_bv 64 0x15780) fc' None m' (seg_rom rsegs))).

Ltac ai_disj := cbn [disjoint_from]; rewrite ?length_le4, ?length_skipn; repeat (split; [lia|]); try exact I.

Lemma ai_run1 : snprintf_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo e v mv : Z) (canary : word),
  (-2^31 <= v < 2^31)%Z -> (0 <= mv <= 6)%Z -> (0 <= e)%Z -> (e + 8 <= 2^21)%Z ->
  bytes_at rsegs m (e + 4) (le4 (Z_to_bv 64 mv)) ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + 32 + SNPRINTF_K <= bv_unsigned sp)%Z -> (2 ^ 21 <= lo)%Z ->
  (bv_unsigned sp < 2^63)%Z ->
  frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m -> (bv_unsigned sp <= TASK_SIZE)%Z ->
  bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
  evt rsegs (ai_mid ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo e v mv m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) (Z_to_bv 64 v) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15b1c) fc None m (seg_rom rsegs)).
Proof.
  intros SNP ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo e v mv canary HV HMV E0 E8 HE ST LO IE S63 FRM MI TM HTS GG GW.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold SNPRINTF_K, IMG_END, GOT_GUARD, GUARD in *.
  pose proof (dec_length v HV) as DL.
  pose proof (ai_pf_dec v HV) as PD.
  assert (TL : length (pf_dec v) = length (dec v)) by (rewrite <- PD; unfold pf_bytes; rewrite length_map; reflexivity).
  pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  rename FR into FRS.
  apply (rw_cells_split_CB rsegs _ _ [] 16%nat junk [] [8; 8]%nat) in FRS; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FRS.
  carve_frame 16%nat ST.
  do 10 step.
  pose proof (rw_cells_bound _ _ _ _ FR) as FRB. cbn [cells_size csize Nat.add] in FRB.
  assert (BJ : bytes_at rsegs m1 (bv_unsigned sp + -32)%Z junk0).
  { destruct FR as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  pose proof (bytes_at_bound _ _ _ _ BJ) as BJL.
  eapply evt_cut.
  { eapply (SNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo canary AI_FMT AI_PS
              [AInt v] (pf_dec v) junk0).
    - rewrite unsigned_lit by lia. apply ai_fmt_at. exact MI.
    - rewrite unsigned_lit by lia. unfold RO_LO. lia.
    - rewrite unsigned_lit by lia. unfold RO_END, AI_FMT. cbn [length]. lia.
    - exact ai_parse.
    - cbn [pf_args_ok pf_arg_ok]. split; [|exact I]. split; [exact HV | apply lit_mod32].
    - exact (ai_text v).
    - rewrite !unsigned_lit by lia. exact FR.
    - rewrite unsigned_lit by lia. lia.
    - lia.
    - rewrite unsigned_lit by lia. lia.
    - rewrite !unsigned_lit by lia. right. lia.
    - rewrite !unsigned_lit by lia. apply pf_img_free_hi. lia.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. unfold SNPRINTF_K. lia.
    - unfold IMG_END. lia.
    - rewrite unsigned_lit by lia. lia.
    - exact FRM.
    - exact MI.
    - exact (task_mem_munch1 m m1 lo (bv_unsigned sp) TM MU HTS).
    - exact GG.
    - exact GW. }
  intros ms' PO. unfold printf_post in PO.
  destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & Ft & fc' & m2
    & -> & MU2 & WM2 & MI2 & TM2 & FRM2 & FK & ST2 & BT).
  rewrite !unsigned_lit in MU2, BT by lia.
  change (Z.to_nat (16 - 1)) with 15%nat in BT, MU2.
  rewrite (firstn_all2 (n := 15%nat)) in MU2, BT by lia.
  replace (ret_pc (Z_to_bv 64 88900)) with (Z_to_bv 64 88900) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (JL : length junk0 = 16%nat) by (destruct FR as [[[HJ _] _] _]; exact HJ).
  assert (FRS2 : rw_cells rsegs m2 (bv_unsigned sp + -16)%Z [C8 s0; C8 ra]).
  { apply (rw_cells_transport rsegs _ m1 m2 _ _ FRS MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
    split; [lia | split; [lia | exact I]]. }
  assert (MUc : munch [(lo, bv_unsigned sp)]%Z m m2).
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU2].
    unfold sub_fp. cbn [outside]. intros x [Hx _]. split; [lia | split; [lia | exact I]]. }
  assert (HE2 : bytes_at rsegs m2 (e + 4)%Z (le4 (Z_to_bv 64 mv))).
  { match goal with H : bytes_at rsegs ?mm (e + 4)%Z _ |- _ =>
      first [ apply (bytes_at_transport rsegs _ m1 m2 _ _ H MU2); ai_disj
            | apply (bytes_at_transport rsegs _ m m2 _ _ H MUc); ai_disj ] end. }
  destruct (bytes_at_firstn_skipn _ _ _ _ (S (length (pf_dec v))) BJ) as [_ BJT].
  rewrite firstn_length_le in BJT by lia.
  assert (BJT2 : bytes_at rsegs m2 (bv_unsigned sp + -32 + Z.of_nat (S (length (pf_dec v))))%Z
                   (skipn (S (length (pf_dec v))) junk0)).
  { apply (bytes_at_transport rsegs _ m1 m2 _ _ BJT MU2). cbn [disjoint_from]. rewrite length_skipn.
    split; [lia | split; [lia | exact I]]. }
  assert (PB : pf_bytes (pf_dec v ++ [0%Z]) = dec v ++ [Z_to_bv 8 0]).
  { unfold pf_bytes. rewrite map_app. change (map (Z_to_bv 8) (pf_dec v)) with (pf_bytes (pf_dec v)).
    rewrite PD. reflexivity. }
  rewrite PB in BT.
  assert (BUF : bytes_at rsegs m2 (bv_unsigned sp + -32)%Z
                  (dec v ++ Z_to_bv 8 0 :: skipn (S (length (pf_dec v))) junk0)).
  { replace (dec v ++ Z_to_bv 8 0 :: skipn (S (length (pf_dec v))) junk0) with
      ((dec v ++ [Z_to_bv 8 0]) ++ skipn (S (length (pf_dec v))) junk0)
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app. split; [exact BT|]. rewrite length_app, <- TL. cbn [length].
    replace (Z.of_nat (length (pf_dec v) + 1)) with (Z.of_nat (S (length (pf_dec v)))) by lia. exact BJT2. }
  clear BT BJT BJT2 BJ BJL FR.
  pose proof (ai_rd4 m2 (e + 4) _ HE2) as RD.
  step. rewrite ai_sx32 by lia. step. step.
  rewrite ai_lts by lia.
  destruct (Z.ltb_spec 5 mv) as [C|C]; cbv iota.
  - assert (C6 : mv = 6%Z) by lia.
    do 4 step.
    replace (Z_to_bv 64 (bv_unsigned sp + -32 + 32)) with sp
      by (replace (bv_unsigned sp + -32 + 32)%Z with (bv_unsigned sp) by lia; symmetry; apply Z_to_bv_bv_unsigned).
    apply evt_done. unfold ai_mid.
    do 18 eexists. exists (skipn (S (length (pf_dec v))) junk0).
    split; [exact MUc|]. split; [eapply wmono_trans; eassumption|].
    split; [exact MI2|]. split; [exact FRM2|]. split; [exact FK|]. split; [exact BUF|].
    split; [rewrite length_skipn, JL, TL; lia|]. split; [exact FRS2|]. split; [exact HE2|].
    left. split; [exact C6 | reflexivity].
  - do 2 step.
    apply evt_done. unfold ai_mid.
    do 3 eexists. exists (Z_to_bv 64 0). do 14 eexists. exists (skipn (S (length (pf_dec v))) junk0).
    split; [exact MUc|]. split; [eapply wmono_trans; eassumption|].
    split; [exact MI2|]. split; [exact FRM2|]. split; [exact FK|]. split; [exact BUF|].
    split; [rewrite length_skipn, JL, TL; lia|]. split; [exact FRS2|]. split; [exact HE2|].
    right. split; [lia | reflexivity].
Qed.

Definition ai_fin (ra0 sp0 r3 r4 x5 x6 x7 s0v x9 x13 x14 x15 x16 x17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 : word)
    (F : bvmap 5 word) (fc : bv 32) (e mv p : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1' a2' m',
    ms' = MS (mkR ra0 sp0 r3 r4 x5 x6 x7 s0v x9 (Z_to_bv 64 p) a1' a2' x13 x14 x15 x16 x17
                  r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31) F (ret_pc ra0) fc None m' (seg_rom rsegs)
    /\ munch [(e + 4, e + 8); (e + 8 + 8 * mv, e + 16 + 8 * mv)]%Z m m' /\ wmono rsegs m m'
    /\ bytes_at rsegs m' (e + 4) (le4 (Z_to_bv 64 (mv + 1))) /\ bytes_at rsegs m' (e + 8 + 8 * mv) (le8 (Z_to_bv 64 p)).

Lemma ai_run3 : forall r1 ra0 sp0 r3 r4 x5 x6 x7 s0v x9 x11 x12 x13 x14 x15 x16 x17
    r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 (F : bvmap 5 word) fc (m : word -> option byte)
    (e mv p : Z),
  bytes_at rsegs m (e + 4) (le4 (Z_to_bv 64 mv)) -> (0 <= mv < 6)%Z -> wr_at rsegs m e 56 ->
  rw_cells rsegs m (bv_unsigned sp0 - 32 + 16) [C8 s0v; C8 ra0] ->
  (0 <= e)%Z -> (e + 56 <= bv_unsigned sp0 - 32)%Z -> (32 <= bv_unsigned sp0)%Z -> (0 <= p < 2 ^ 64)%Z ->
  evt rsegs (ai_fin ra0 sp0 r3 r4 x5 x6 x7 s0v x9 x13 x14 x15 x16 x17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 F fc e mv p m)
    (MS (mkR r1 (Z_to_bv 64 (bv_unsigned sp0 - 32)) r3 r4 x5 x6 x7 (Z_to_bv 64 e) x9 (Z_to_bv 64 p) x11 x12 x13 x14 x15 x16 x17
             r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31) F (Z_to_bv 64 0x15b58) fc None m (seg_rom rsegs)).
Proof.
  intros r1 ra0 sp0 r3 r4 x5 x6 x7 s0v x9 x11 x12 x13 x14 x15 x16 x17
    r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 F fc m e mv p HE HM HW FR E0 ES S32 HP.
  pose proof (ai_rd4 m (e + 4) _ HE) as RD.
  pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add] in FB.
  step. rewrite ai_sx32 by lia. do 3 step.
  replace (Z_to_bv 64 (e + bv_unsigned (Z_to_bv 64 mv) ≪ 3)) with (Z_to_bv 64 (e + 8 * mv))
    by (rewrite unsigned_lit by lia; rewrite Z.shiftl_mul_pow2 by lia; f_equal; lia).
  pose proof (wr_at_store_ok rsegs m e 56 4 4 HW ltac:(lia) ltac:(lia)) as HS1.
  step.
  set (m1 := write_to_mem m _ (le4 (Z_to_bv 64 (mv + 1)))).
  assert (HW1 : wr_at rsegs m1 e 56) by (apply wr_at_write; exact HW).
  pose proof (wr_at_store_ok rsegs m1 e 56 (8 * mv + 8) 8 HW1 ltac:(lia) ltac:(lia)) as HS2.
  step.
  assert (L4 : Z.of_nat (length (le4 (Z_to_bv 64 (mv + 1)))) = 4%Z) by (rewrite length_le4; reflexivity).
  assert (L8 : Z.of_nat (length (le8 (Z_to_bv 64 p))) = 8%Z) by (rewrite length_le8; reflexivity).
  assert (FR1 : rw_cells rsegs m1 (bv_unsigned sp0 - 32 + 16) [C8 s0v; C8 ra0])
    by (apply rw_cells_frame; [exact FR | lia | rewrite L4; lia | cbn [cells_size csize Nat.add]; rewrite L4; lia]).
  assert (B1 : bytes_at rsegs m1 (e + 4) (le4 (Z_to_bv 64 (mv + 1)))) by (apply bytes_at_write_same; rewrite ?L4; lia).
  assert (MU1 : munch [(e + 4, e + 8); (e + 8 + 8 * mv, e + 16 + 8 * mv)]%Z m m1).
  { apply munch_write; [apply munch_refl | lia | rewrite L4; lia | cbn [inside]; rewrite L4; lia]. }
  assert (WM1 : wmono rsegs m m1) by (apply wmono_write; apply wmono_refl).
  set (m2 := write_to_mem m1 _ (le8 (Z_to_bv 64 p))).
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp0 - 32 + 16) [C8 s0v; C8 ra0])
    by (apply rw_cells_frame; [exact FR1 | lia | rewrite L8; lia | cbn [cells_size csize Nat.add]; rewrite L8; lia]).
  assert (B2 : bytes_at rsegs m2 (e + 4) (le4 (Z_to_bv 64 (mv + 1))))
    by (apply bytes_at_write_other; [exact B1 | lia | rewrite L8; lia | rewrite L4, L8; lia]).
  assert (B3 : bytes_at rsegs m2 (e + 8 + 8 * mv) (le8 (Z_to_bv 64 p))).
  { replace (e + 8 + 8 * mv)%Z with (e + (8 * mv + 8))%Z by lia. apply bytes_at_write_same; rewrite ?L8; lia. }
  assert (MU2 : munch [(e + 4, e + 8); (e + 8 + 8 * mv, e + 16 + 8 * mv)]%Z m m2).
  { apply munch_write; [exact MU1 | lia | rewrite L8; lia | cbn [inside]; rewrite L8; lia]. }
  assert (WM2 : wmono rsegs m m2) by (apply wmono_write; exact WM1).
  clearbody m2. clear FR FR1 HS1 HS2.
  do 4 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 - 32 + 32)) with sp0
    by (replace (bv_unsigned sp0 - 32 + 32)%Z with (bv_unsigned sp0) by lia; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done. unfold ai_fin. do 3 eexists. split; [reflexivity|].
  split; [exact MU2|]. split; [exact WM2|]. split; [exact B2 | exact B3].
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL01 YO10.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecModel RecInv RecInvP RecKindB RecAnsB
  xstrdup_c arg_i_c.
Local Open Scope Z_scope.

Section AI.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOTG : ms_got_guard B = 0x22a68.
Hypothesis GUARDG : ms_guard B = 0x54450.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis SNP : snprintf_contract.

Lemma ai_case6 : forall L A regs mem md (e v m : Z) b,
    call_pre_t B API ARG_I_K L A regs mem md ->
    getr regs 10 = Z_to_bv 64 e -> getr regs 11 = Z_to_bv 64 v -> -2^31 <= v < 2^31 ->
    REC_SC <= e -> e + CALL_SIZE <= G_REC + REC_SIZE ->
    Mem.bytes_at (ms_segs B) mem (e + CALL_OFF_NARGS) (Mem.le4 (Z_to_bv 64 m)) -> m = 6 ->
    f18_words (ms_segs B) mem -> frm_zero fp_csr -> res_ok_slots A b -> ro_agree (ms_segs B) mem ->
    SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 ARG_I) mem (seg_rom (ms_segs B))) md)
      (arg_i_ret B API L A regs mem md e v m b).
Proof using SEGS ERRNO_LOW GOTG GUARDG AX SNP.
  intros L A regs mem md e v m b PRE A0 A1 HV ELO EHI NA M6 F18 FZ RES RA. subst m.
  unfold arg_i_ret.
  destruct PRE as [PRE HTS].
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_val as AC.
  pose proof wx_apart_rsegs as WX.
  assert (KV : ARG_I_K = 8256) by reflexivity.
  rewrite KV in PRE |- *.
  destruct PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  unfold REC_SC, G_REC, REC_SIZE, CALL_SIZE, CALL_OFF_NARGS, SC_SIZE in *.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof (dec_length v HV) as DL.
  rewrite SEGS in RA, HWS, HERR, F18, NA.
  pose proof F18 as (GG & canary & GW).
  assert (GGb : bytes_at rsegs mem snprintf_c.GOT_GUARD (Mem.le8 (Z_to_bv 64 snprintf_c.GUARD))).
  { destruct GG as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (GWb : bytes_at rsegs mem snprintf_c.GUARD (Mem.le8 canary)).
  { destruct GW as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (ST0 : stk rsegs (normalize_cj rsegs mem) (bv_unsigned sp - 8256) (bv_unsigned sp))
    by (apply stk_normalize_cj; [lia | exact HTS | intros a Ha; apply HWS; lia]).
  pose proof (bytes_at_normalize_cj_low rsegs mem snprintf_c.GOT_GUARD (Mem.le8 (Z_to_bv 64 snprintf_c.GUARD)) RA
    ltac:(rewrite Mem.length_le8; unfold snprintf_c.GOT_GUARD, TASK_SIZE; lia) GGb) as GGn.
  pose proof (bytes_at_normalize_cj_low rsegs mem snprintf_c.GUARD (Mem.le8 canary) RA
    ltac:(rewrite Mem.length_le8; unfold snprintf_c.GUARD, TASK_SIZE; lia) GWb) as GWn.
  pose proof (bytes_at_normalize_cj_low rsegs mem (e + 4) (Mem.le4 (Z_to_bv 64 6)) RA
    ltac:(rewrite length_le4; unfold TASK_SIZE; lia) NA) as NAn.
  rewrite SEGS.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
    assert (R10 : reg_get regs 10 = Z_to_bv 64 e) by exact A0.
    assert (R11 : reg_get regs 11 = Z_to_bv 64 v) by exact A1.
    rewrite R10, R11.
    eapply (evt_normalize_cj rsegs); [exact WX | exact RA |].
    eapply (ai_run1 SNP) with (lo := bv_unsigned sp - 8256) (canary := canary) (mv := 6) (e := e) (v := v);
      [exact HV | lia | lia | lia | exact NAn | exact ST0 | unfold SNPRINTF_K; lia | lia | lia | exact FZ
      | exact (mem_inv_cj_inv rsegs _ (mem_inv_cj_normalize rsegs mem))
      | exact (mem_inv_cj_task rsegs _ (mem_inv_cj_normalize rsegs mem)) | exact HTS
      | exact GGn | exact GWn]. }
  intros ms1 (can1 & (s1n & Q1 & REL1 & RO1) & EQ1).
  destruct Q1 as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F1 & fc1 & m1n
    & junk & MU1n & WM1n & MI1n & FRM1 & FK1 & BUF1n & JL & FRS1n & NA1n & [[_ ->] | [C _]]); [|lia].
  destruct (ms_rel_cj_MS _ _ _ _ _ _ _ _ REL1) as [EC1 MR1r].
  revert EC1 MR1r RO1 EQ1. generalize (ms_mem can1) as m1. intros m1 EC1 MR1r RO1 EQ1. subst can1.
  pose proof (munch_rel_cj rsegs _ _ _ _ _ (mem_rel_cj_normalize rsegs mem RA) MR1r RO1 MU1n) as MU1.
  pose proof (wmono_rel_cj rsegs _ _ _ _ (mem_rel_cj_normalize rsegs mem RA) MR1r RO1 WM1n) as WM1.
  pose proof (ro_agree_same_cj rsegs _ _ RA RO1) as RA1.
  pose proof (bytes_at_rel_cj rsegs _ _ _ _ MR1r BUF1n) as BUF1.
  destruct (eqv_mkst_fx _ _ _ _ _ _ _ EQ1) as (R1 & -> & X1).
  clear MU1n WM1n MI1n FRS1n BUF1n EQ1 MR1r.
  assert (RP : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA). rewrite RP.
  assert (OUT1 : forall a, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 8256 <= a < bv_unsigned sp) ->
            outside [(bv_unsigned sp - 8256, bv_unsigned sp)] a) by (intros a _ Ha; cbn; split; [exact Ha | exact I]).
  assert (MR1 : aa_MR API L A m1 md).
  { eapply (mr_frame B _ LAWS L A mem m1 md md HMR).
    - intros a Ho. destruct (owned_low B _ LAWS _ _ _ _ a HMR Ho) as [Ha1 Ha2].
      try rewrite SEGS. eapply munch_mbyte; [exact MU1 | lia | apply OUT1; lia].
    - intros a Ho Hp. destruct (owned_low B _ LAWS _ _ _ _ a HMR Ho) as [Ha1 Ha2].
      eapply munch_present; [exact MU1 | lia | apply OUT1; lia | exact Hp].
    - intros p n i Hin Hi. destruct (mr_blocks B _ LAWS L A mem md p n i HMR Hin Hi) as (Hp & H4 & Hc & _).
      eapply munch_present; [exact MU1 | lia | apply OUT1; lia | exact Hp].
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  apply SR_ret.
  exists (mkFP F1 fc1), L, A, R1, m1, md.
  split; [reflexivity|].
  split.
  { unfold fp_kept. cbn [fp_regs fp_csr]. split; [exact FRM1|].
    intros r Hr. apply FK1. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
    unfold fs_saved in Hr. rewrite Z.mod_small by lia. lia. }
  split.
  { intros q k i Hq _ Hi. destruct (block_facts B _ LAWS _ _ _ _ _ _ i HMR Hq Hi) as (_ & Hlo & Hhi & _).
    try rewrite SEGS. apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
  split; [intros q k Hq; exact Hq|].
  split.
  { replace (dec v ++ Z_to_bv 8 0 :: junk) with ((dec v ++ [Z_to_bv 8 0]) ++ junk) in BUF1
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app in BUF1. replace (bv_unsigned sp - 32) with (bv_unsigned sp + -32) by lia. exact (proj1 BUF1). }
  split; [exact RA1|].
  split.
  { intros i Hi. rewrite GOTG. try rewrite SEGS. apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
  split.
  { destruct (ax_statics AX L A m1 md MR1) as (_ & (g & Hg & HGW) & _).
    apply (f18_words_after mem m1 g F18); [| exact Hg | rewrite SEGS, GUARDG in HGW; exact HGW].
    intros i Hi. unfold snprintf_c.GOT_GUARD. apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
  split; [lia|].
  left. split; [reflexivity|]. split; [|split; [reflexivity | exact RES]].
  split; [exact MR1|]. split; [exact HWF|]. split; [exact HBD|]. split; [apply layout_le_refl|].
  split; [intros; reflexivity|].
  split.
  { intros r Hr. unfold callee_saved in Hr.
    assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct C as [C|C]; [subst r; rewrite (getr_of_eqv _ _ _ X1) by reflexivity; simp_regs; reflexivity|]).
    subst r. rewrite (getr_of_eqv _ _ _ X1) by reflexivity; simp_regs; reflexivity. }
  split; [exists (m_vmmaps md); destruct md as [f [mp lz mt] io fs pr li ti]; reflexivity|].
  split.
  { intros a HA NO1 NO2 NS NE.
    assert (AR : 0 <= a < 2 ^ 64) by (destruct HA as [HA|HA]; [lia | pose proof (in_img_low B SEGS a HA); lia]).
    assert (NSP : ~ (bv_unsigned sp - 8256 <= a < bv_unsigned sp)).
    { intro H. apply NS. left. unfold spZ. change (getr regs 2) with sp. lia. }
    try rewrite SEGS. split; [apply (munch_mbyte _ _ _ _ _ MU1 AR (OUT1 a AR NSP)) | apply (munch_writable _ _ _ _ _ MU1 AR (OUT1 a AR NSP))]. }
  split.
  { intros p n i Hin _ Hi. destruct (mr_blocks B _ LAWS L A mem md p n i HMR Hin Hi) as (_ & Hlo & Hhi & _).
    try rewrite SEGS. apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
  intros a Ha. unfold scratch_k, spZ in Ha. change (getr regs 2) with sp in Ha.
  try rewrite SEGS. apply WM1. destruct Ha as [Ha|Ha]; [apply HWS; lia | apply HERR; exact Ha].
Qed.

Hypothesis GLOB : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis XS : forall fx' : YK11.FPState, @xstrdup_contract fx' rc B API.

Lemma ai_ro_rec : forall a, 143360 <= a < 348160 -> ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha. unfold ro_addr. rewrite unsigned_lit by lia.
  destruct (find_segment rsegs a 1) as [seg|] eqn:F; [|reflexivity].
  destruct (find_segment_in _ _ _ _ F) as (Hin & H1 & H2).
  assert (C : forallb (fun s => (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 143360) || (348160 <=? Z.of_N (seg_base s))
                                || seg_writable s) rsegs = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ rsegs) C seg Hin) as Cs. cbv beta in Cs.
  destruct (seg_writable seg); [reflexivity|].
  rewrite orb_false_r in Cs. apply orb_prop in Cs as [Cs|Cs]; apply Z.leb_le in Cs; lia.
Qed.

Lemma ai_caselt : forall L A regs mem md (e v m : Z) b,
    call_pre_t B API ARG_I_K L A regs mem md ->
    getr regs 10 = Z_to_bv 64 e -> getr regs 11 = Z_to_bv 64 v -> -2^31 <= v < 2^31 ->
    REC_SC <= e -> e + CALL_SIZE <= G_REC + REC_SIZE ->
    Mem.wr_at (ms_segs B) mem e CALL_SIZE ->
    Mem.bytes_at (ms_segs B) mem (e + CALL_OFF_NARGS) (Mem.le4 (Z_to_bv 64 m)) -> 0 <= m < 6 ->
    f18_words (ms_segs B) mem -> frm_zero fp_csr -> res_ok_slots A b ->
    room_slots (sb_malloc b (Z.of_nat (length (dec v)) + 1)) (Z.of_nat (length (dec v)) + 1) ->
    ro_agree (ms_segs B) mem ->
    SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 ARG_I) mem (seg_rom (ms_segs B))) md)
      (arg_i_ret B API L A regs mem md e v m b).
Proof using SEGS ERRNO_LOW GOTG GUARDG AX SNP GLOB XS.
  intros L A regs mem md e v mv b PRE A0 A1 HV ELO EHI WRE NA MV F18 FZ RES ROOM RA.
  unfold arg_i_ret.
  destruct PRE as [PRE HTS].
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_val as AC.
  pose proof wx_apart_rsegs as WX.
  assert (KV : ARG_I_K = 8256) by reflexivity.
  rewrite KV in PRE |- *.
  destruct PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  unfold REC_SC, G_REC, REC_SIZE, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS, SC_SIZE, LMAX in *.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof (dec_length v HV) as DL.
  rewrite SEGS in RA, HWS, HERR, F18, NA, WRE.
  assert (RECI : forall a, e <= a < e + 56 -> in_img B a /\ ~ (errno_addr B <= a < errno_addr B + 4)
                 /\ forall L0 A0 m0 md0, aa_MR API L0 A0 m0 md0 -> ~ owned B L0 A0 a).
  { intros a Ha. destruct (GLOB a) as (Hi & Hs & Hc & He); [exists 0x33d10, 1020; split; [left; reflexivity | lia]|].
    split; [exact Hi|]. split; [exact He|]. intros La Aa m0 md0 HM [Ho|Ho]; [|exact (Hs Ho)].
    exact (Hc (YL01.ax_img AX _ _ _ _ a HM Hi Ho)). }
  assert (EIMG : e + 56 <= 2 ^ 21) by (destruct (RECI e ltac:(lia)) as [Hi _]; pose proof (in_img_low B SEGS e Hi);
    destruct (RECI (e + 55) ltac:(lia)) as [Hi2 _]; pose proof (in_img_low B SEGS (e + 55) Hi2); lia).
  pose proof F18 as (GG & canary & GW).
  assert (GGb : bytes_at rsegs mem snprintf_c.GOT_GUARD (Mem.le8 (Z_to_bv 64 snprintf_c.GUARD))).
  { destruct GG as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (GWb : bytes_at rsegs mem snprintf_c.GUARD (Mem.le8 canary)).
  { destruct GW as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (ST0 : stk rsegs (normalize_cj rsegs mem) (bv_unsigned sp - 8256) (bv_unsigned sp))
    by (apply stk_normalize_cj; [lia | exact HTS | intros a Ha; apply HWS; lia]).
  pose proof (bytes_at_normalize_cj_low rsegs mem snprintf_c.GOT_GUARD (Mem.le8 (Z_to_bv 64 snprintf_c.GUARD)) RA
    ltac:(rewrite Mem.length_le8; unfold snprintf_c.GOT_GUARD, TASK_SIZE; lia) GGb) as GGn.
  pose proof (bytes_at_normalize_cj_low rsegs mem snprintf_c.GUARD (Mem.le8 canary) RA
    ltac:(rewrite Mem.length_le8; unfold snprintf_c.GUARD, TASK_SIZE; lia) GWb) as GWn.
  pose proof (bytes_at_normalize_cj_low rsegs mem (e + 4) (Mem.le4 (Z_to_bv 64 mv)) RA
    ltac:(rewrite length_le4; unfold TASK_SIZE; lia) NA) as NAn.
  rewrite SEGS.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
    assert (R10 : reg_get regs 10 = Z_to_bv 64 e) by exact A0.
    assert (R11 : reg_get regs 11 = Z_to_bv 64 v) by exact A1.
    rewrite R10, R11.
    eapply (evt_normalize_cj rsegs); [exact WX | exact RA |].
    eapply (ai_run1 SNP) with (lo := bv_unsigned sp - 8256) (canary := canary) (mv := mv) (e := e) (v := v);
      [exact HV | lia | lia | lia | exact NAn | exact ST0 | unfold SNPRINTF_K; lia | lia | lia | exact FZ
      | exact (mem_inv_cj_inv rsegs _ (mem_inv_cj_normalize rsegs mem))
      | exact (mem_inv_cj_task rsegs _ (mem_inv_cj_normalize rsegs mem)) | exact HTS
      | exact GGn | exact GWn]. }
  intros ms1 (can1 & (s1n & Q1 & REL1 & RO1) & EQ1).
  destruct Q1 as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F1 & fc1 & m1n
    & junk & MU1n & WM1n & MI1n & FRM1 & FK1 & BUF1n & JL & FRS1n & NA1n & [[C _] | [_ ->]]); [lia|].
  destruct (ms_rel_cj_MS _ _ _ _ _ _ _ _ REL1) as [EC1 MR1r].
  revert EC1 MR1r RO1 EQ1. generalize (ms_mem can1) as m1. intros m1 EC1 MR1r RO1 EQ1. subst can1.
  pose proof (munch_rel_cj rsegs _ _ _ _ _ (mem_rel_cj_normalize rsegs mem RA) MR1r RO1 MU1n) as MU1.
  pose proof (wmono_rel_cj rsegs _ _ _ _ (mem_rel_cj_normalize rsegs mem RA) MR1r RO1 WM1n) as WM1.
  pose proof (ro_agree_same_cj rsegs _ _ RA RO1) as RA1.
  pose proof (bytes_at_rel_cj rsegs _ _ _ _ MR1r BUF1n) as BUF1.
  pose proof (rw_cells_rel_cj rsegs _ _ _ _ MR1r FRS1n) as FRS1.
  pose proof (bytes_at_rel_cj rsegs _ _ _ _ MR1r NA1n) as NA1.
  destruct (eqv_mkst_fx _ _ _ _ _ _ _ EQ1) as (R1 & -> & X1).
  clear MU1n WM1n MI1n FRS1n BUF1n NA1n EQ1 MR1r.
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x15b58) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 32))
    by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; f_equal; lia).
  assert (E1_4 : getr R1 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_8 : getr R1 8 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 (bv_unsigned sp - 32))
    by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; f_equal; lia).
  assert (SP1 : spZ R1 = bv_unsigned sp - 32) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  assert (OUT1 : forall a, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 8256 <= a < bv_unsigned sp) ->
            outside [(bv_unsigned sp - 8256, bv_unsigned sp)] a) by (intros a _ Ha; cbn; split; [exact Ha | exact I]).
  assert (MR1 : aa_MR API L A m1 md).
  { eapply (mr_frame B _ LAWS L A mem m1 md md HMR).
    - intros a Ho. destruct (owned_low B _ LAWS _ _ _ _ a HMR Ho) as [Ha1 Ha2].
      try rewrite SEGS. eapply munch_mbyte; [exact MU1 | lia | apply OUT1; lia].
    - intros a Ho Hp. destruct (owned_low B _ LAWS _ _ _ _ a HMR Ho) as [Ha1 Ha2].
      eapply munch_present; [exact MU1 | lia | apply OUT1; lia | exact Hp].
    - intros p n i Hin Hi. destruct (mr_blocks B _ LAWS L A mem md p n i HMR Hin Hi) as (Hp & H4 & Hc & _).
      eapply munch_present; [exact MU1 | lia | apply OUT1; lia | exact Hp].
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  assert (BUF1' : bytes_at rsegs m1 (bv_unsigned sp - 32) (dec v ++ Z_to_bv 8 0 :: junk))
    by (replace (bv_unsigned sp - 32) with (bv_unsigned sp + -32) by lia; exact BUF1).
  assert (XK : XSTRDUP_K = 8224) by reflexivity.
  rewrite <- SEGS.
  eapply SR_bind.
  { eapply (XS (mkFP F1 fc1) L A R1 m1 md (bv_unsigned sp - 32) (dec v) junk b);
      [ | exact E1_10 | rewrite SEGS; exact BUF1' | exact (dec_no0 v) | unfold LMAX; lia | | | | exact RES | exact ROOM
      | rewrite SEGS; exact RA1].
    - rewrite XK. split; [exact MR1|]. split; [exact HWF|]. split; [exact HBD|].
      split; [rewrite E1_1; apply bv_eq; vm_compute; reflexivity|].
      split; [rewrite SP1; replace (bv_unsigned sp - 32) with (bv_unsigned sp + (-2) * 16) by ring;
              rewrite Z.mod_add by lia; exact HAL|].
      split; [rewrite SP1; lia|].
      split; [rewrite SP1; lia|].
      split; [intros a Ha; rewrite SP1 in Ha; rewrite SEGS; apply WM1; apply HWS; lia|].
      split; [rewrite E1_4; exact HTP|].
      split; [intros a Ha; rewrite SEGS; apply WM1; apply HERR; exact Ha|].
      intros HI. specialize (HAUX HI). rewrite SP1.
      destruct HAUX as (av & ar & W1 & W2 & W3 & W4 & B1 & B2 & B3 & B4 & L1 & L2).
      exists av, ar.
      split.
      { eapply word_mem_munch; [exact MU1 | | exact W1]. intros k Hk.
        assert (SO : owned B L A (ms_libc B + 8 + Z.of_nat k)) by (right; unfold static_owned; lia).
        destruct (owned_low B _ LAWS _ _ _ _ _ HMR SO). split; [lia | apply OUT1; lia]. }
      split.
      { intros k Hk. eapply word_mem_munch; [exact MU1 | | exact (W2 k Hk)]. intros k' Hk'.
        split; [lia | apply OUT1; lia]. }
      split.
      { eapply word_mem_munch; [exact MU1 | | exact W3]. intros k Hk. split; [lia | apply OUT1; lia]. }
      split.
      { eapply word_mem_munch; [exact MU1 | | exact W4]. intros k Hk. split; [lia | apply OUT1; lia]. }
      lia.
    - rewrite JL, Nat2Z.inj_sub by lia. Z.div_mod_to_equations. lia.
    - right. rewrite SP1. lia.
    - left. rewrite SP1. lia. }
  intros c2 RET. unfold xstrdup_ret in RET.
  destruct RET as (L' & A' & R2 & m2 & md2 & p & -> & POST & A0' & NZ & AL & FRESH & BLK & KEPT & UB2 & BP2 & BS2
    & RA2 & GK2 & INIT & REG2 & RES').
  rewrite SEGS in RA2, BP2, BS2.
  rewrite XK in POST. change ALLOC_STACK with 8192 in *.
  destruct POST as (HMR' & HWF' & HBD' & HLE & HSTAB & HPRES & HVM & HFRAME & HBLKS & HSCR).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR') as (Hh2 & Hl2 & Hmat2).
  destruct BLK as (b1 & b2 & BLK1 & BLK2).
  pose proof FRESH as (FR_lo & FR_hi & FR_img).
  assert (BNI : forall L0 A0 m0 md0 q k i, aa_MR API L0 A0 m0 md0 -> In (q, k) (blocks L0 A0) -> 0 <= i < k ->
                ~ in_img B (q + i)).
  { intros La Aa m0 md0 q k i HM Hin Hi. unfold blocks in Hin. apply in_map_iff in Hin as ([p0 k0] & Eq & Hp).
    cbn in Eq. injection Eq as <- <-. exact (YL01.ax_blocks_img AX _ _ _ _ p0 k0 i HM Hp Hi). }
  assert (NOWN : forall a, alloc_ceiling <= a -> ~ owned B L A a /\ ~ owned B L' A' a).
  { intros a Ha. split; intros Ho;
      [destruct (owned_low B _ LAWS _ _ _ _ _ HMR Ho) | destruct (owned_low B _ LAWS _ _ _ _ _ HMR' Ho)]; lia. }
  assert (HI2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 8256 <= a < bv_unsigned sp - 32) ->
     mbyte (ms_segs B) m2 a = mbyte (ms_segs B) m1 a /\
     (writable_at (ms_segs B) m1 a <-> writable_at (ms_segs B) m2 a)).
  { intros a Ha Hs. destruct (NOWN a (proj1 Ha)) as [N1 N2].
    apply HFRAME; [left; exact Ha | exact N1 | exact N2 | | intros F; cbn beta in F; lia].
    unfold scratch_k. rewrite SP1. intros [H|H]; lia. }
  assert (REC2 : forall a, e <= a < e + 56 ->
     mbyte (ms_segs B) m2 a = mbyte (ms_segs B) m1 a /\
     (writable_at (ms_segs B) m1 a <-> writable_at (ms_segs B) m2 a)).
  { intros a Ha. destruct (RECI a Ha) as (Hi & He & Ho).
    apply HFRAME; [right; exact Hi | exact (Ho _ _ _ _ MR1) | exact (Ho _ _ _ _ HMR') | |].
    - unfold scratch_k. rewrite SP1. intros [H|H]; [lia | exact (He H)].
    - intros Hp. apply (FR_img (a - p)); [lia|]. replace (p + (a - p)) with a by ring. exact Hi. }
  assert (E2_2 : reg_get R2 2 = Z_to_bv 64 (bv_unsigned sp - 32))
    by exact (eq_trans (HPRES 2 ltac:(unfold callee_saved; lia)) E1_2).
  assert (E2_8 : reg_get R2 8 = Z_to_bv 64 e) by exact (eq_trans (HPRES 8 ltac:(unfold callee_saved; lia)) E1_8).
  assert (E2_10 : reg_get R2 10 = Z_to_bv 64 p) by exact A0'.
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 32 + 16) [C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m1); [replace (bv_unsigned sp - 32 + 16) with (bv_unsigned sp + -16) by lia; exact FRS1|].
    intros i Hi. cbn in Hi.
    rewrite <- SEGS. destruct (HI2 (bv_unsigned sp - 32 + 16 + i) ltac:(lia) ltac:(lia)) as [E W].
    split; [exact E | apply W]. }
  assert (NA2 : bytes_at rsegs m2 (e + 4) (le4 (Z_to_bv 64 mv))).
  { apply (bytes_at_transfer rsegs m1); [exact NA1|]. intros i Hi. rewrite length_le4 in Hi.
    rewrite <- SEGS. exact (proj1 (REC2 (e + 4 + i) ltac:(lia))). }
  assert (WRE2 : wr_at rsegs m2 e 56).
  { destruct WRE as (W0 & W1 & W2). split; [lia|]. split; [lia|]. intros i Hi.
    assert (Wm : writable_at rsegs mem (e + i)) by exact (W2 i Hi).
    assert (Wm1 : writable_at rsegs m1 (e + i)) by (apply (munch_writable _ _ _ _ _ MU1); [lia | apply OUT1; lia | exact Wm]).
    rewrite <- SEGS in Wm1. pose proof (proj1 (proj2 (REC2 (e + i) ltac:(lia))) Wm1) as Wm2. rewrite SEGS in Wm2.
    exact Wm2. }
  rewrite E1_1, SEGS.
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. cbn [fp_regs fp_csr]. unfold Regs6ss.mkR_of. rewrite E2_2, E2_8, E2_10.
    eapply ai_run3; [exact NA2 | lia | exact WRE2 | exact FR2 | lia | lia | lia | lia]. }
  intros ms3 (can3 & Q3 & EQ3). unfold ai_fin in Q3.
  destruct Q3 as (a1'' & a2'' & m3 & -> & MU3 & WM3 & NA3 & ARG3).
  destruct (eqv_mkst_fx _ _ _ _ _ _ _ EQ3) as (R3 & -> & X3). clear EQ3.
  assert (RP : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
  rewrite RP.
  assert (OUT3 : forall a, 0 <= a < 2 ^ 64 -> ~ (e <= a < e + 56) ->
            outside [(e + 4, e + 8); (e + 8 + 8 * mv, e + 16 + 8 * mv)] a)
    by (intros a _ Ha; cbn; split; [lia | split; [lia | exact I]]).
  assert (MR3 : aa_MR API L' A' m3 md2).
  { eapply (mr_frame B _ LAWS L' A' m2 m3 md2 md2 HMR').
    - intros a Ho. destruct (owned_low B _ LAWS _ _ _ _ a HMR' Ho) as [Ha1 Ha2].
      try rewrite SEGS. eapply munch_mbyte; [exact MU3 | lia | apply OUT3; [lia|]].
      intros Hr. exact (proj2 (proj2 (RECI a Hr)) _ _ _ _ HMR' Ho).
    - intros a Ho Hp. destruct (owned_low B _ LAWS _ _ _ _ a HMR' Ho) as [Ha1 Ha2].
      eapply munch_present; [exact MU3 | lia | apply OUT3; [lia|] | exact Hp].
      intros Hr. exact (proj2 (proj2 (RECI a Hr)) _ _ _ _ HMR' Ho).
    - intros q n i Hin Hi. destruct (mr_blocks B _ LAWS L' A' m2 md2 q n i HMR' Hin Hi) as (Hp & H4 & Hc & _).
      pose proof (YL01.ax_blocks_img AX _ _ _ _ q n i HMR' Hin Hi) as NI.
      eapply munch_present; [exact MU3 | lia | apply OUT3; [lia|] | exact Hp].
      intros Hr. exact (NI (proj1 (RECI _ Hr))).
    - reflexivity.
    - exact Hh2.
    - exact Hl2.
    - exact Hmat2. }
  apply SR_ret.
  exists (mkFP F1 fc1), L', A', R3, m3, md2.
  split; [reflexivity|].
  split.
  { unfold fp_kept. cbn [fp_regs fp_csr]. split; [exact FRM1|].
    intros r Hr. apply FK1. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
    unfold fs_saved in Hr. rewrite Z.mod_small by lia. lia. }
  split.
  { intros q k i Hq _ Hi.
    destruct (block_facts B _ LAWS _ _ _ _ _ _ i HMR Hq Hi) as (_ & Hlo & Hhi & _).
    pose proof (BNI _ _ _ _ q k i HMR Hq Hi) as NI.
    rewrite SEGS. rewrite (munch_mbyte _ _ _ _ (q + i) MU3 ltac:(lia)).
    2: { apply OUT3; [lia|]. intros Hr. exact (NI (proj1 (RECI _ Hr))). }
    pose proof (KEPT q k i Hq (fun F => F) Hi) as KE. rewrite SEGS in KE. rewrite KE.
    apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
  split; [exact UB2|].
  split.
  { apply (bytes_at_transfer rsegs m2); [exact BS2|]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    apply (munch_mbyte _ _ _ _ _ MU3); [lia | apply OUT3; lia]. }
  split.
  { intros x Hx. destruct (Z_le_gt_dec e (bv_unsigned x)) as [D1|D1];
      [destruct (Z_lt_ge_dec (bv_unsigned x) (e + 56)) as [D2|D2]|].
    - exfalso. rewrite <- (Z_to_bv_bv_unsigned x) in Hx. rewrite ai_ro_rec in Hx by lia. discriminate.
    - unfold mrd. pose proof (bv_unsigned_in_range 64 x) as Rx. unfold bv_modulus in Rx.
      rewrite (MU3 x) by (apply OUT3; lia). exact (RA2 x Hx).
    - unfold mrd. pose proof (bv_unsigned_in_range 64 x) as Rx. unfold bv_modulus in Rx.
      rewrite (MU3 x) by (apply OUT3; lia). exact (RA2 x Hx). }
  split.
  { intros i Hi. rewrite GOTG, SEGS.
    rewrite (munch_mbyte _ _ _ _ (0x22a68 + i) MU3 ltac:(lia)) by (apply OUT3; lia).
    pose proof (GK2 i Hi) as G. rewrite GOTG, SEGS in G. rewrite G.
    apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
  split.
  { destruct (ax_statics AX L' A' m3 md2 MR3) as (_ & (g & Hg & HGW) & _).
    apply (f18_words_after mem m3 g F18); [| exact Hg | rewrite SEGS, GUARDG in HGW; exact HGW].
    intros i Hi. unfold snprintf_c.GOT_GUARD.
    rewrite (munch_mbyte _ _ _ _ (0x22a68 + i) MU3 ltac:(lia)) by (apply OUT3; lia).
    pose proof (GK2 i Hi) as G. rewrite GOTG, SEGS in G. rewrite G.
    apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
  split; [exact REG2|].
  right. split; [lia|]. exists p.
  split.
  { split; [exact MR3|]. split; [exact HWF'|]. split; [exact HBD'|]. split; [exact HLE|]. split; [exact HSTAB|].
    split.
    { eapply (preserved_chain (fun r => (r =? 2) || (r =? 8)) regs R1 R2 R3 _ _ X1 HPRES X3).
      - intros r Hr O. unfold callee_saved in Hr.
        assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        repeat (destruct C as [C|C]; [subst r; first [discriminate O | split; reflexivity]|]).
        subst r. split; reflexivity.
      - intros r Hr O. unfold callee_saved in Hr.
        assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        repeat (destruct C as [C|C]; [subst r; first [discriminate O | reflexivity]|]).
        subst r. discriminate O. }
    split; [exact HVM|].
    split.
    { intros a HA NO1 NO2 NS NE. cbn beta in NE.
      assert (AR : 0 <= a < 2 ^ 64) by (destruct HA as [HA|HA]; [lia | pose proof (in_img_low B SEGS a HA); lia]).
      assert (NSP : ~ (bv_unsigned sp - 8256 <= a < bv_unsigned sp)).
      { intro H. apply NS. left. unfold spZ. change (getr regs 2) with sp. lia. }
      assert (NER : ~ (errno_addr B <= a < errno_addr B + 4)) by (intro H; apply NS; right; exact H).
      pose proof (munch_mbyte (ms_segs B) _ _ _ a MU1 AR (OUT1 a AR ltac:(lia))) as E01.
      pose proof (munch_writable (ms_segs B) _ _ _ a MU1 AR (OUT1 a AR ltac:(lia))) as W01.
      assert (H12 : mbyte (ms_segs B) m2 a = mbyte (ms_segs B) m1 a /\
                    (writable_at (ms_segs B) m1 a <-> writable_at (ms_segs B) m2 a)).
      { apply HFRAME; [exact HA | exact NO1 | exact NO2 | | intros F; apply NE; right; right; exact F].
        unfold scratch_k. rewrite SP1. intros [H|H]; [lia | exact (NER H)]. }
      assert (O3 : outside [(e + 4, e + 8); (e + 8 + 8 * mv, e + 16 + 8 * mv)] a).
      { cbn. split; [intros H; apply NE; left; lia | split; [intros H; apply NE; right; left; lia | exact I]]. }
      pose proof (munch_mbyte (ms_segs B) _ _ _ a MU3 AR O3) as E23.
      pose proof (munch_writable (ms_segs B) _ _ _ a MU3 AR O3) as W23.
      split; [rewrite E23, (proj1 H12), E01; reflexivity | rewrite W01, (proj2 H12), W23; tauto]. }
    split.
    { intros q n i Hin Hin' Hi.
      destruct (mr_blocks B _ LAWS L A mem md q n i HMR Hin Hi) as (_ & Hlo & Hhi & _).
      pose proof (YL01.ax_blocks_img AX _ _ _ _ q n i HMR Hin Hi) as NI.
      rewrite (munch_mbyte _ _ _ _ (ptr_addr L q + i) MU3 ltac:(lia)).
      2: { apply OUT3; [lia|]. intros Hr. exact (NI (proj1 (RECI _ Hr))). }
      rewrite (HBLKS q n i Hin Hin' Hi).
      apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
    intros a Ha. unfold scratch_k, spZ in Ha. change (getr regs 2) with sp in Ha.
    rewrite SEGS. apply WM3. rewrite <- SEGS.
    destruct Ha as [Ha|Ha].
    - destruct (Z_lt_ge_dec a (bv_unsigned sp - 32)) as [D|D].
      + apply HSCR. unfold scratch_k. rewrite SP1. left. lia.
      + destruct (NOWN a ltac:(lia)) as [N1 N2].
        apply (proj1 (proj2 (HFRAME a ltac:(left; lia) N1 N2 ltac:(unfold scratch_k; rewrite SP1;
                 intros [H|H]; lia) ltac:(intros F; cbn beta in F; lia)))).
        rewrite SEGS. apply WM1. apply HWS. lia.
    - apply HSCR. right. exact Ha. }
  split; [exact NZ|]. split; [exact AL|]. split; [exact FRESH|].
  split; [exists b1, b2; split; [exact BLK1 | exact BLK2]|].
  split; [exact NA3|]. split; [exact ARG3|].
  split.
  { apply (bytes_at_transfer rsegs m2); [exact BP2|]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    apply (munch_mbyte _ _ _ _ _ MU3); [lia|]. apply OUT3; [lia|]. intros Hr.
    apply (FR_img i); [lia|]. exact (proj1 (RECI _ Hr)). }
  split; [exact INIT | exact RES'].
Qed.

Theorem arg_i_holds : arg_i_contract B API.
Proof using SEGS ERRNO_LOW GOTG GUARDG AX SNP GLOB XS.
  unfold arg_i_contract.
  intros L A regs mem md e v m b PRE A0 A1 HV EAL ELO EHI WRE NA MV F18 FZ RES ROOM RA.
  destruct (Z.eq_dec m 6) as [M6|M6].
  - exact (ai_case6 L A regs mem md e v m b PRE A0 A1 HV ELO EHI NA M6 F18 FZ RES RA).
  - exact (ai_caselt L A regs mem md e v m b PRE A0 A1 HV ELO EHI WRE NA ltac:(lia) F18 FZ RES ROOM RA).
Qed.

End AI.
