(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColB/W_set0A.v, with its module paths and module names changed; 44 of its 60 lines of code are new or changed and 129 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Prog/SceneTac.v, with its module paths changed; 470 of its 484 lines of code are new or changed and 46 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/Prog/codec_main_inv.v, with its module paths and module names changed; 347 of its 391 lines of code are new or changed and 440 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells memcpy_c
  diginet_sysex_encode_c diginet_scribble_encode_c.
Import ListNotations.
Open Scope Z_scope.

(** diginet_scribble_encode of the UBSan image (0x15e50, 51 instructions, frame 0x40): the early
    returns (p NULL, addr > 0x7f), the payload pl[10] at sp'+0xe (addr, 0, memcpy of d_chars bytes of
    chars to sp'+0x10), the call of diginet_sysex_encode on it, and the key store at out+0x1c after a
    0 result. The UBSan traps (unimp at 0x15f18) are refuted: pl is a stack address far from 2^64, p is
    8-aligned (pers_arg) and out 4-aligned. *)

Local Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(* ---- cells and bytes ---- *)

Lemma scr_cells_split : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf Hb] (Ha & Hl & Hw)].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_size_app in Hl, Hw.
  rewrite cells_bytes_length in B2 by exact W1.
  split.
  - split; [split; [exact W1 | exact B1] |]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split; [exact W2 | exact B2] |]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply Hw. lia.
Qed.

Lemma scr_cells_cons : forall m A c rest,
  rw_cells rsegs m A (c :: rest) -> forall B, B = A + Z.of_nat (csize c) ->
  rw_cells rsegs m A [c] /\ rw_cells rsegs m B rest.
Proof.
  intros m A c rest H B EB. change (c :: rest) with ([c] ++ rest) in H.
  apply scr_cells_split in H. destruct H as [H1 H2]. cbn [cells_size] in H2.
  rewrite Nat.add_0_r in H2. subst B. split; assumption.
Qed.

Lemma scr_rebytes : forall m A cs cs',
  rw_cells rsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[Hwf Hb] Hw] Hwf' Heq. split; [split; [exact Hwf' | rewrite Heq; exact Hb] |].
  rewrite <- (cells_bytes_length cs') by assumption. rewrite Heq. rewrite cells_bytes_length by assumption. exact Hw.
Qed.

Lemma scr_stk_rel : forall m lo A cs B,
  stk rsegs m lo A -> rw_cells rsegs m A cs -> lo <= A -> B = A + Z.of_nat (cells_size cs) -> stk rsegs m lo B.
Proof. intros m lo A cs B HS HC HL EB. subst B. eapply stk_release; eassumption. Qed.

(** The frame after the prologue and the two pl stores, cut at pl + 2 + n (the memcpy destination,
    n bytes), pl + 10 and the saved registers. *)
Lemma scr_frame_split : forall m A j1 b z j2 c1 c2 c3 c4 c5,
  rw_cells rsegs m A [CB 14 j1; C1 b; C1 z; CB 8 j2; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5] ->
  forall B C D (n : nat), B = A + 16 -> C = A + 16 + Z.of_nat n -> D = A + 24 -> (n <= 8)%nat ->
  rw_cells rsegs m A [CB 14 j1; C1 b; C1 z] /\ rw_cells rsegs m B [CB n (firstn n j2)] /\
  rw_cells rsegs m C [CB (8 - n) (firstn (8 - n) (skipn n j2))] /\
  rw_cells rsegs m D [C8 c1; C8 c2; C8 c3; C8 c4; C8 c5].
Proof.
  intros m A j1 b z j2 c1 c2 c3 c4 c5 H B C D n EB EC ED Hn.
  change [CB 14 j1; C1 b; C1 z; CB 8 j2; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5]
    with ([CB 14 j1; C1 b; C1 z] ++ [CB 8 j2] ++ [C8 c1; C8 c2; C8 c3; C8 c4; C8 c5]) in H.
  apply scr_cells_split in H. destruct H as [H1 H23]. cbn [cells_size csize Nat.add] in H23.
  apply scr_cells_split in H23. destruct H23 as [H2 H3]. cbn [cells_size csize Nat.add] in H3.
  apply (rw_cells_split_CB rsegs m (A + Z.of_nat 16) [] 8 j2 [] [n; (8 - n)%nat]) in H2;
    [| cbn [sum_nat]; lia].
  cbn [app mk_CB_cells] in H2.
  change [CB n (firstn n j2); CB (8 - n) (firstn (8 - n) (skipn n j2))]
    with ([CB n (firstn n j2)] ++ [CB (8 - n) (firstn (8 - n) (skipn n j2))]) in H2.
  apply scr_cells_split in H2. destruct H2 as [H2a H2b]. cbn [cells_size csize] in H2b.
  split; [exact H1|]. split; [|split].
  - replace B with (A + Z.of_nat 16) by lia. exact H2a.
  - replace C with (A + Z.of_nat 16 + Z.of_nat (n + 0)) by lia. exact H2b.
  - replace D with (A + Z.of_nat 16 + Z.of_nat 8) by lia. exact H3.
Qed.

(** The 2 + n bytes of pl that diginet_sysex_encode reads. *)
Lemma scr_pl_bytes : forall m A j b z B n src C,
  rw_cells rsegs m A [CB 14 j; C1 b; C1 z] -> rw_cells rsegs m B [CB n src] ->
  B = A + 16 -> C = A + 14 -> bytes_at rsegs m C (b :: z :: src).
Proof.
  intros m A j b z B n src C [[W1 B1] _] [[W2 B2] _] EB EC.
  cbn [cells_wf cell_wf] in W1. destruct W1 as [Lj _].
  cbn [cells_bytes cbytes app] in B1, B2.
  apply bytes_at_app in B1. destruct B1 as [_ B1].
  rewrite app_nil_r in B2.
  change (b :: z :: src) with ([b; z] ++ src).
  apply bytes_at_app. split.
  - replace C with (A + Z.of_nat (length j)) by lia. exact B1.
  - cbn [length]. replace (C + Z.of_nat 2) with B by lia. exact B2.
Qed.

Lemma scr_bytes_firstn : forall m a bs n, bytes_at rsegs m a bs -> bytes_at rsegs m a (firstn n bs).
Proof. intros m a bs n H. rewrite <- (firstn_skipn n bs) in H. apply bytes_at_app in H. tauto. Qed.

Lemma scr_bytes_nth : forall m a bs (k : Z) a',
  bytes_at rsegs m a bs -> 0 <= k < Z.of_nat (length bs) -> a' = a + k ->
  ov_read_bytes rsegs m (wa a') 1 = Some [nth (Z.to_nat k) bs (Z_to_bv 8 0)].
Proof.
  intros m a bs k a' H Hk E. subst a'.
  rewrite (bytes_at_read rsegs m a bs k 1 H) by lia.
  f_equal. remember (Z.to_nat k) as j. assert (j < length bs)%nat by lia. clear Heqj Hk H.
  revert j H0. induction bs as [|x bs IH]; intros j Hj; cbn in *; [lia|].
  destruct j as [|j]; [reflexivity|]. apply IH. lia.
Qed.

Lemma scr_le1 : forall z, 0 <= z < 2 ^ 64 -> le1 (Z_to_bv 64 z) = [b8 z].
Proof. intros z Hz. unfold le1, b8. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma scr_b8 : forall v, 0 <= v < 256 -> bv_unsigned (b8 v) = v.
Proof. intros v Hv. unfold b8. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia. Qed.

(* ---- arithmetic ---- *)

Lemma scr_land7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma scr_land3 : forall x, Z.land x 3 = x mod 4.
Proof. intros x. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma scr_s32_small : forall a, 0 <= a < 2 ^ 31 -> s32 a = a.
Proof. intros a Ha. unfold s32. rewrite (proj2 (Z.ltb_lt a (2 ^ 31))) by lia. reflexivity. Qed.

Lemma scr_s32_big : forall a, 127 < a < 2 ^ 32 -> 127 < bv_unsigned (Z_to_bv 64 (s32 a)).
Proof.
  intros a Ha. unfold s32. destruct (Z.ltb_spec a (2 ^ 31)).
  - rewrite unsigned_lit by lia. lia.
  - rewrite unsigned_lit_wrap. Z.div_mod_to_equations. lia.
Qed.

(** A fact about every addr in 0 .. 127, checked on all of them. *)
Lemma scr_all128 : forall (f g : Z -> Z),
  forallb (fun y => Z.eqb (f y) (g y)) (map Z.of_nat (seq 0 128)) = true ->
  forall x, 0 <= x <= 127 -> f x = g x.
Proof.
  intros f g H x Hx. rewrite forallb_forall in H.
  apply Z.eqb_eq. apply H. apply in_map_iff. exists (Z.to_nat x). split; [lia |]. apply in_seq. lia.
Qed.

(* ---- the model ---- *)

Lemma scr_map_firstn : forall (A B : Type) (f : A -> B) n (l : list A), map f (firstn n l) = firstn n (map f l).
Proof. induction n as [|n IH]; intros [|x l]; cbn; try reflexivity. f_equal. apply IH. Qed.

Lemma scr_zb_pl : forall a cs n, zb (b8 a :: b8 0 :: firstn n cs) = [u8 a; 0] ++ firstn n (zb cs).
Proof.
  intros a cs n. unfold zb. cbn [map app]. rewrite scr_map_firstn. f_equal.
  all: unfold b8, u8; rewrite ?Z_to_bv_unsigned; reflexivity.
Qed.

Lemma scr_sysex_rc : forall dev fn pl rc o, sysex_spec dev fn pl = (rc, o) ->
  -11 <= rc <= 0 /\ (rc <> 0 -> o = None) /\
  (rc = 0 -> exists dp, o = Some ([0xf0; 0x13; dev; fn] ++ pl ++ [0xf7], 0, dp) /\ Z.of_nat (length pl) + 5 <= 24).
Proof.
  intros dev fn pl rc o H. unfold sysex_spec, E_ARG, E_REFUSED, E_RANGE, E_SPACE in H.
  destruct (127 <? dev) eqn:E1.
  { injection H as <- <-. split; [lia|]. split; [reflexivity|]. intros; exfalso; lia. }
  destruct (fn =? 112) eqn:E2.
  { injection H as <- <-. split; [lia|]. split; [reflexivity|]. intros; exfalso; lia. }
  destruct (127 <? fn) eqn:E3.
  { injection H as <- <-. split; [lia|]. split; [reflexivity|]. intros; exfalso; lia. }
  destruct (24 <? Z.of_nat (length pl) + 5) eqn:E4.
  { injection H as <- <-. split; [lia|]. split; [reflexivity|]. intros; exfalso; lia. }
  destruct (existsb (fun x => Z.testbit x 7) pl) eqn:E5.
  { injection H as <- <-. split; [lia|]. split; [reflexivity|]. intros; exfalso; lia. }
  injection H as <- <-. split; [lia|]. split; [intros; exfalso; lia|].
  intros _. eexists. split; [reflexivity|]. apply Z.ltb_ge in E4. lia.
Qed.

Lemma scr_with_key_none : forall rc k, with_key (rc, None) k = (rc, None).
Proof. intros [|p|p] k; reflexivity. Qed.

Lemma scr_cmd_out_len : forall before bs k disp, length before = 32%nat -> (length bs <= 24)%nat ->
  length (cmd_out before (Some (bs, k, disp))) = 32%nat.
Proof.
  intros before bs k disp Hb Hl. unfold cmd_out, bz.
  rewrite !length_app, !length_map. repeat (rewrite length_firstn || rewrite length_skipn).
  rewrite length_le4. cbn [length]. lia.
Qed.

(** The key store: out's bytes after diginet_sysex_encode with the 4 key bytes replaced. *)
Lemma scr_cmd_out_key : forall before bs k k' disp, length before = 32%nat -> (length bs <= 24)%nat ->
  firstn 28 (cmd_out before (Some (bs, k, disp))) ++ le4 (Z_to_bv 64 k') = cmd_out before (Some (bs, k', disp)).
Proof.
  intros before bs k k' disp Hb Hl. unfold cmd_out. rewrite !app_assoc.
  match goal with |- firstn 28 (?X ++ _) ++ _ = ?X ++ _ =>
    assert (LX : length X = 28%nat)
      by (unfold bz; rewrite !length_app, !length_map; repeat (rewrite length_firstn || rewrite length_skipn);
          cbn [length]; lia);
    rewrite <- LX, firstn_app_exact; reflexivity
  end.
Qed.

(* ---- the walk ---- *)

Section Scribble.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
          (m : word -> option byte) (lo : Z) (pd : option desk) (addr : Z) (cs before : list byte) (a3 : word).
Hypothesis LO : lo + 112 <= bv_unsigned sp.

Definition scr_Q (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 112, bv_unsigned sp); (bv_unsigned a3, bv_unsigned a3 + 32)] m m' /\
    wmono rsegs m m' /\
    mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp) /\
    let '(rc, o) := scribble_spec pd addr (zb cs) in
    a0' = Z_to_bv 64 rc /\ rw_cells rsegs m' (bv_unsigned a3) [CB 32 (cmd_out before o)].

(** The epilogue at 0x15efc: restore ra, s0 .. s3, release the frame, return. *)
Lemma scr_exit : forall (ra' t0' t1' t2' x8 x9 b1 b2 b3 b4 b5 b6 b7 x18 x19 t3' t4' t5' t6' : word)
                        (rc : Z) (o : option cmd) (m1 : word -> option byte),
  scribble_spec pd addr (zb cs) = (rc, o) ->
  rw_cells rsegs m1 (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m1 lo (bv_unsigned sp + -40) ->
  rw_cells rsegs m1 (bv_unsigned a3) [CB 32 (cmd_out before o)] ->
  munch [(bv_unsigned sp - 112, bv_unsigned sp); (bv_unsigned a3, bv_unsigned a3 + 32)] m m1 ->
  wmono rsegs m m1 ->
  mem_inv rsegs m1 ->
  evt rsegs scr_Q
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0' t1' t2' x8 x9 (Z_to_bv 64 rc) b1 b2 b3 b4 b5 b6 b7
             x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x15efc) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra' t0' t1' t2' x8 x9 b1 b2 b3 b4 b5 b6 b7 x18 x19 t3' t4' t5' t6' rc o m1 ESP FS ST40 HO MU WM HMI.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST40 as [Hlo _].
  do 7 zstep.
  pose proof (scr_stk_rel _ _ _ _ (bv_unsigned sp) ST40 FS ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as STF.
  apply evt_done. unfold scr_Q. rewrite ESP.
  do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact HMI|]. split; [exact STF|].
  split; [reflexivity | exact HO].
Qed.

Local Ltac cur_mem := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => mm end.

(** A byte store of a register: the stored list is le1 of a literal word. *)
Local Ltac fix_sb := first [ rewrite (scr_le1 addr) by lia | rewrite (scr_le1 0) by lia ]; mem_after_store.

Local Ltac refute_trap T := exfalso; zify_cond T; repeat (rewrite Z.mod_small in T by lia); lia.

(** The early returns: the frame still [CB 24 _ :: saved]. *)
Local Ltac early_exit :=
  match goal with
  | FRh : rw_cells rsegs ?mm (bv_unsigned sp + -64) (CB 24 ?x :: ?rest),
    STh : stk rsegs ?mm lo (bv_unsigned sp + -64) |- _ =>
    let F24 := fresh "F24" in let FSV := fresh "FSV" in let ST40 := fresh "ST40" in
    destruct (scr_cells_cons _ _ _ _ FRh (bv_unsigned sp + -40) ltac:(cbn [csize]; lia)) as [F24 FSV];
    pose proof (scr_stk_rel _ _ _ _ (bv_unsigned sp + -40) STh F24 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as ST40;
    eapply scr_exit with (o := None);
    [ | exact FSV | exact ST40 | eassumption | eassumption | eassumption | eassumption ]
  end.

Lemma scr_main : memcpy_contract -> diginet_sysex_encode_contract ->
  forall (t0 t1 t2 a0 a1 a2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  pers_arg m a0 pd ->
  (forall d, pd = Some d -> disj (bv_unsigned a0 + 16) 4 (bv_unsigned sp - 112) 112) ->
  (forall d, pd = Some d -> d_chars d <= 8 /\ d_chars d <= Z.of_nat (length cs)) ->
  arg_u32 a1 addr ->
  bv_unsigned a2 <> 0 ->
  bytes_at rsegs m (bv_unsigned a2) cs ->
  bv_unsigned a3 <> 0 ->
  rw_cells rsegs m (bv_unsigned a3) [CB 32 before] ->
  bv_unsigned a3 mod 4 = 0 ->
  bv_unsigned sp <= bv_unsigned a2 ->
  bv_unsigned sp <= bv_unsigned a3 ->
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp) ->
  evt rsegs scr_Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15e50) fc None m (seg_rom rsegs)).
Proof.
  intros MC SX t0 t1 t2 a0 a1 a2 a4 a5 a6 a7 t3 t4 t5 t6 HP HD1 HDC HA1 HA2 HCS HA3 HOUT HOA HSA2 HSA3 HMI ST.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (bv_unsigned a3, bv_unsigned a3 + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. pose proof (bv_unsigned_in_range 64 a2) as Ra2.
  pose proof (bv_unsigned_in_range 64 a3) as Ra3. pose proof (bv_unsigned_in_range 64 a0) as Ra0.
  unfold bv_modulus in Rsp, Ra2, Ra3, Ra0.
  pose proof ST as [Hlo _].
  pose proof (bytes_at_bound rsegs m _ _ HCS) as BCS.
  pose proof (rw_cells_bound rsegs m _ _ HOUT) as BOUT. cbn [cells_size csize] in BOUT.
  pose proof HOUT as [[WB _] _]. cbn [cells_wf cell_wf] in WB. destruct WB as [LB _].
  unfold diginet_sysex_encode_contract, DIGINET_SYSEX_ENCODE, diginet_sysex_encode_pre, DIGINET_SYSEX_ENCODE_DEPTH in SX.
  unfold memcpy_contract in MC.
  destruct pd as [d|] eqn:Epd.
  2: {
    (* p = NULL: E_ARG *)
    cbn [pers_arg] in HP. subst a0.
    carve_frame 64%nat ST.
    do 8 zstep.
    zstep. if_cases K1; [exfalso; zify_cond K1; lia |].
    zstep. if_cases K2; [| exfalso; zify_cond K2; lia].
    early_exit. rewrite Epd. reflexivity. }
  destruct d as [dv dst dc dct].
  specialize (HD1 _ eq_refl). specialize (HDC _ eq_refl). cbn [d_chars] in HDC. destruct HDC as [HDC8 HDCL].
  unfold disj in HD1.
  cbn [pers_arg] in HP. destruct HP as (HA0 & HA08 & HOK).
  unfold pers_ok, desk_ok in HOK. cbn [d_dev d_strips d_chars d_counter] in HOK.
  destruct HOK as ((Hdv & Hdst & Hdc & Hdct) & HPK).
  unfold bz in HPK. cbn [map] in HPK.
  assert (HSRC : bytes_at rsegs m (bv_unsigned a2) (firstn (Z.to_nat dc) cs)) by (apply scr_bytes_firstn; exact HCS).
  assert (UC : bv_unsigned (b8 dc) = dc) by (apply scr_b8; lia).
  assert (UV : bv_unsigned (b8 dv) = dv) by (apply scr_b8; lia).
  carve_frame 64%nat ST.
  do 8 zstep.
  zstep. if_cases K1; [exfalso; zify_cond K1; lia |].
  zstep. if_cases K2; [exfalso; zify_cond K2; lia |].
  zstep.
  zstep. if_cases K3; [exfalso; zify_cond K3; lia |].
  do 2 zstep.
  destruct (Z_le_gt_dec addr 127) as [Hle | Hgt].
  2: {
    (* addr > 0x7f: E_RANGE *)
    assert (H127 : 127 < bv_unsigned a1) by (destruct HA1 as [Ha ->]; apply scr_s32_big; lia).
    zstep. if_cases K4; [exfalso; zify_cond K4; lia |].
    do 2 zstep.
    early_exit.
    rewrite Epd. unfold scribble_spec. rewrite (proj2 (Z.ltb_lt 127 addr)) by lia. reflexivity. }
  destruct HA1 as [Ha Ea1]. rewrite (scr_s32_small addr) in Ea1 by lia. subst a1.
  zstep. if_cases K4; [| exfalso; zify_cond K4; lia].
  (* pl[0] = addr, pl[1] = 0, the pointer-overflow and alignment traps *)
  zstep. zstep.
  zstep. fix_sb.
  zstep. if_cases T1; [refute_trap T1 |].
  zstep.
  zstep. fix_sb.
  zstep. if_cases T2; [refute_trap T2 |].
  zstep.
  zstep. if_cases T3; [exfalso; zify_cond T3; rewrite scr_land7 in T3; lia |].
  (* lbu s3, 0x12(s2): d_chars *)
  let mm := cur_mem in
  assert (HRc : ov_read_bytes rsegs mm (wa (bv_unsigned a0 + 18)) 1 = Some [b8 dc])
    by (erewrite (scr_bytes_nth _ _ _ 2 _ HPK) by (cbn [length]; lia); reflexivity).
  zstep. clear HRc. cbv beta. rewrite UC.
  pose proof (scr_frame_split _ _ _ _ _ _ _ _ _ _ _ FR (bv_unsigned sp + -48) (bv_unsigned sp + -48 + dc)
                (bv_unsigned sp + -40) (Z.to_nat dc) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (FRlo & FRb & FRr & FRsv).
  clear FR.
  assert (UB48 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  assert (UD : bv_unsigned (Z_to_bv 64 dc) = dc) by (apply unsigned_lit; lia).
  do 4 zstep.
  (* memcpy(pl + 2, chars, d_chars) *)
  let mm := cur_mem in
  eapply evt_cut;
  [ eapply MC with (src := firstn (Z.to_nat dc) cs);
    [ exact HSRC
    | rewrite UD, length_firstn; lia
    | rewrite UB48, UD; exact FRb
    | rewrite UB48, UD; lia
    | exact HMI ]
  | post_call rsegs mm ].
  rewrite ?UB48, ?UD in *.
  match goal with H : rw_cells rsegs _ (bv_unsigned sp + -48) [CB (Z.to_nat dc) (firstn (Z.to_nat dc) cs)] |- _ =>
    rename H into FRmc end.
  (* lbu a0, 0x10(s2): device *)
  let mm := cur_mem in
  assert (HRd : ov_read_bytes rsegs mm (wa (bv_unsigned a0 + 16)) 1 = Some [b8 dv])
    by (erewrite (scr_bytes_nth _ _ _ 0 _ HPK) by (cbn [length]; lia); reflexivity).
  zstep. clear HRd. cbv beta. rewrite UV.
  do 5 zstep.
  let mm := cur_mem in
  assert (HPL : bytes_at rsegs mm (bv_unsigned sp + -50) (b8 addr :: b8 0 :: firstn (Z.to_nat dc) cs))
    by (eapply scr_pl_bytes; [exact FRlo | exact FRmc | lia | lia]).
  assert (U64 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
  assert (U50 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -50)) = bv_unsigned sp + -50) by (apply unsigned_lit; lia).
  assert (UD2 : bv_unsigned (Z_to_bv 64 (dc + 2)) = dc + 2) by (apply unsigned_lit; lia).
  (* diginet_sysex_encode(device, 0x40, pl, 2 + d_chars, out) *)
  let mm := cur_mem in
  eapply evt_cut;
  [ eapply SX with (dev := dv) (fn := 64) (pl := b8 addr :: b8 0 :: firstn (Z.to_nat dc) cs) (before := before) (lo := lo);
    unfold arg_zx, disj;
    split; [split; [lia | rewrite ?UV; reflexivity] |];
    split; [split; [lia | reflexivity] |];
    split; [rewrite U50; lia |];
    split; [rewrite U50; exact HPL |];
    split; [rewrite UD2; cbn [length]; rewrite length_firstn; lia |];
    split; [exact HA3 |];
    split; [eassumption |];
    split; [exact HOA |];
    split; [rewrite U50; cbn [length]; rewrite length_firstn; lia |];
    split; [rewrite U64, U50; lia |];
    split; [rewrite U64; lia |];
    split; [eassumption |];
    split; [rewrite U64; eassumption |];
    rewrite U64; lia
  | post_call rsegs mm ].
  clear MC SX.
  match goal with H : stk rsegs _ lo (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64))) |- _ => rewrite U64 in H end.
  match goal with H : context [sysex_spec] |- _ => rename H into SXP end.
  rewrite scr_zb_pl in SXP.
  destruct (sysex_spec dv 64 ([u8 addr; 0] ++ firstn (Z.to_nat dc) (zb cs))) as [rc o] eqn:ESX.
  pose proof (scr_sysex_rc _ _ _ _ _ ESX) as (RCr & RCne & RCeq).
  destruct SXP as [Ea0 HO].
  match type of Ea0 with ?x = _ => subst x end.
  match goal with H : stk rsegs ?mm lo (bv_unsigned sp + -64) |- _ =>
    pose proof (scr_stk_rel _ _ _ _ (bv_unsigned sp + -48) H FRlo ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as ST1 end.
  pose proof (scr_stk_rel _ _ _ _ (bv_unsigned sp + -48 + dc) ST1 FRmc ltac:(lia) ltac:(cbn [cells_size csize]; lia)) as ST2.
  pose proof (scr_stk_rel _ _ _ _ (bv_unsigned sp + -40) ST2 FRr ltac:(lia) ltac:(cbn [cells_size csize]; lia)) as ST3.
  clear ST1 ST2.
  destruct (Z.eq_dec rc 0) as [Hrc0 | Hrcn].
  2: {
    (* diginet_sysex_encode failed: its rc, out unchanged *)
    specialize (RCne Hrcn). subst o.
    zstep. if_cases B1; [| exfalso; zify_cond B1; lia].
    eapply scr_exit; [ | exact FRsv | exact ST3 | exact HO | eassumption | eassumption | eassumption ].
    rewrite Epd. unfold scribble_spec. cbn [d_dev d_chars].
    rewrite (proj2 (Z.ltb_ge 127 addr)) by lia. rewrite ESX. apply scr_with_key_none. }
  subst rc. destruct (RCeq eq_refl) as (dp & Eo & Hlen). subst o.
  zstep. if_cases B1; [exfalso; zify_cond B1; lia |].
  zstep.
  zstep. if_cases T4; [exfalso; zify_cond T4; rewrite scr_land3 in T4; lia |].
  do 3 zstep.
  (* out->key = DIGINET_KEY(7, addr) *)
  match goal with H : rw_cells rsegs _ (bv_unsigned a3) _ |- _ => rename H into HK end.
  match type of HK with rw_cells rsegs _ (bv_unsigned a3) [CB 28 ?Fb; C4 ?v] =>
    assert (Ev : v = Z_to_bv 64 (KEY 7 addr))
      by (f_equal; clear - Ha Hle; assert (Ha' : 0 <= addr <= 127) by lia; clear Ha Hle; revert addr Ha';
          match goal with |- forall z, _ -> @?L z = @?R z => apply (scr_all128 L R); vm_compute; reflexivity end)
  end.
  rewrite Ev in HK.
  assert (LBS : Nat.le (length ([0xf0; 0x13; dv; 64] ++ ([u8 addr; 0] ++ firstn (Z.to_nat dc) (zb cs)) ++ [0xf7])) 24)
    by (rewrite !length_app, length_firstn; cbn [length]; lia).
  let mm := cur_mem in
  assert (HO' : rw_cells rsegs mm (bv_unsigned a3)
                  [CB 32 (cmd_out before (Some ([0xf0; 0x13; dv; 64] ++ ([u8 addr; 0] ++ firstn (Z.to_nat dc) (zb cs)) ++ [0xf7], KEY 7 addr, dp)))]).
  { eapply scr_rebytes; [exact HK | |].
    - cbn [cells_wf cell_wf]. split; [|exact I]. apply scr_cmd_out_len; [exact LB | exact LBS].
    - cbn [cells_bytes cbytes]. rewrite !app_nil_r. symmetry.
      apply scr_cmd_out_key; [exact LB | exact LBS]. }
  eapply scr_exit; [ | exact FRsv | exact ST3 | exact HO' | eassumption | eassumption | eassumption ].
  rewrite Epd. unfold scribble_spec. cbn [d_dev d_chars].
  rewrite (proj2 (Z.ltb_ge 127 addr)) by lia. rewrite ESX. reflexivity.
Qed.

End Scribble.

Theorem diginet_scribble_encode_holds : memcpy_contract -> diginet_sysex_encode_contract -> diginet_scribble_encode_contract.
Proof.
  intros MC SX. unfold diginet_scribble_encode_contract, diginet_scribble_encode_pre, DIGINET_SCRIBBLE_ENCODE,
    DIGINET_SCRIBBLE_ENCODE_DEPTH.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo pd addr cs before (HP & HD1 & HDC & HA1 & HA2 & HCS & HA3 & HOUT & HOA & HSA2 & HSA3 & HMI & ST & LO).
  eapply scr_main; eassumption.
Qed.
