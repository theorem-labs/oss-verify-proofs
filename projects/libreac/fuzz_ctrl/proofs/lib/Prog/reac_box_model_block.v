(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColB/W_set0A.v, with its module paths and module names changed; 1390 of its 1411 lines of code are new or changed and 124 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib
  RcSynth RcSynthLib memset_c memcpy_c build_dt1_single_c reac_box_model_block_c.
Import ListNotations.
Open Scope Z_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

Ltac mem_after_store_opt ::=
  try fix_lit_store;
  try rewrite le1_zxb;
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      lazymatch goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.

Lemma mb_rw1 : forall segs m A n X, rw_cells segs m A [CB n X] -> bytes_at segs m A X.
Proof. intros segs m A n X [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. Qed.

Lemma mb_cells_sub : forall segs m A cs k n, rw_cells segs m A cs ->
  bytes_at segs m (A + Z.of_nat (cells_size (firstn k cs))) (cells_bytes (firstn n (skipn k cs))).
Proof.
  intros segs m A cs k n [[Hwf HB] _].
  rewrite <- (firstn_skipn k cs) in Hwf, HB. rewrite cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in HB. apply bytes_at_app in HB. destruct HB as [_ HB].
  rewrite (cells_bytes_length _ W1) in HB.
  rewrite <- (firstn_skipn n (skipn k cs)) in HB. rewrite cells_bytes_app in HB.
  apply bytes_at_app in HB. destruct HB as [HB _]. exact HB.
Qed.

Lemma mb_take : forall segs m A cs k, rw_cells segs m A cs ->
  rw_cells segs m A (CB (cells_size (firstn k cs)) (cells_bytes (firstn k cs)) :: skipn k cs).
Proof. exact rs_rw_take. Qed.

Ltac ulit := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) by lia end.
Ltac cond_solve := unfold_cond; ulit; first [solve_cond_rec | solve_cond_base].
Ltac if_t := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  replace c with true; [cbv iota | symmetry; cond_solve] end.
Ltac if_f := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  replace c with false; [cbv iota | symmetry; cond_solve] end.

Lemma mb_upd_app : forall (Y R bs : list byte) k, (k + length bs <= length Y)%nat ->
  upd_bytes (Y ++ R) k bs = upd_bytes Y k bs ++ R.
Proof.
  intros Y R bs k H. unfold upd_bytes. rewrite firstn_app, skipn_app.
  replace (k - length Y)%nat with 0%nat by lia. replace (k + length bs - length Y)%nat with 0%nat by lia.
  rewrite firstn_O, skipn_O, app_nil_r, <- !app_assoc. reflexivity.
Qed.

Lemma mb_rw_cb0 : forall segs m A n Y cs (k : Z) bs, rw_cells segs m A (CB n Y :: cs) -> 0 <= k ->
  (Z.to_nat k + length bs <= n)%nat ->
  rw_cells segs (write_to_mem m (wa (A + k)) bs) A (CB n (upd_bytes Y (Z.to_nat k) bs) :: cs).
Proof.
  intros segs m A n Y cs k bs [[Hwf HB] HW] Hk Hn. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [LY Hwf].
  cbn [cells_bytes cbytes] in HB. split; [split|].
  - cbn [cells_wf cell_wf]. split; [rewrite upd_bytes_length; lia | exact Hwf].
  - cbn [cells_bytes cbytes]. rewrite <- mb_upd_app by lia.
    apply bytes_at_write_inside; [exact HB | exact Hk | rewrite length_app; lia].
  - cbn [cells_size csize] in HW |- *. apply wr_at_write. exact HW.
Qed.

Lemma mb_sw2 : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap. change (bv_half_modulus 32) with 2147483648. unfold bv_wrap.
  change (bv_modulus 32) with 4294967296. rewrite Z.mod_small by lia. lia.
Qed.

Ltac wsimp := repeat (match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) by lia
  | |- context [bv_swrap 32 ?x] => rewrite (mb_sw2 x) by lia
  end); rewrite ?Z.add_0_r.

Lemma mb_upd_pre : forall (J0 Y bs : list byte) i, (i + length bs <= length Y)%nat ->
  upd_bytes (J0 ++ Y) (length J0 + i) bs = J0 ++ upd_bytes Y i bs.
Proof.
  intros J0 Y bs i H. unfold upd_bytes. rewrite firstn_app, skipn_app.
  replace (length J0 + i - length J0)%nat with i by lia. replace (length J0 + i + length bs - length J0)%nat with (i + length bs)%nat by lia.
  rewrite firstn_all2 by lia. rewrite skipn_all2 by lia. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma mb_upd_mid : forall (J0 Y J2 bs : list byte) k i, length J0 = k -> (i + length bs <= length Y)%nat ->
  upd_bytes (J0 ++ Y ++ J2) (k + i) bs = J0 ++ upd_bytes Y i bs ++ J2.
Proof.
  intros J0 Y J2 bs k i <- H. rewrite mb_upd_pre by (rewrite length_app; lia). rewrite mb_upd_app by exact H. reflexivity.
Qed.

Lemma mb_zz8 : forall j : list byte, length j = 48%nat ->
  upd_bytes (upd_bytes j (Z.to_nat 8) (le8 (Z_to_bv 64 0))) (Z.to_nat 16) (le8 (Z_to_bv 64 0)) =
  firstn 8 j ++ zeros 16 ++ skipn 24 j.
Proof.
  intros j L. do 48 (destruct j as [|? j]; [discriminate|]). destruct j; [|discriminate]. reflexivity.
Qed.

Lemma mb_zz32 : forall j : list byte, length j = 48%nat ->
  upd_bytes (upd_bytes j (Z.to_nat 32) (le8 (Z_to_bv 64 0))) (Z.to_nat 40) (le8 (Z_to_bv 64 0)) =
  firstn 32 j ++ zeros 16 ++ skipn 48 j.
Proof.
  intros j L. do 48 (destruct j as [|? j]; [discriminate|]). destruct j; [|discriminate]. reflexivity.
Qed.

Lemma mb_sx32_eq0 : forall w, 0 <= w < 2^32 -> bv_eqb (sx32 (Z_to_bv 64 w)) (Z_to_bv 64 0) = (w =? 0).
Proof.
  intros w Hw. destruct (Z.eqb_spec w 0) as [->|N]; [reflexivity|].
  unfold bv_eqb, sx32. apply Z.eqb_neq. rewrite (unsigned_lit w) by lia. rewrite unsigned_lit_wrap.
  change (bv_unsigned (Z_to_bv 64 0)) with 0. unfold bv_swrap. change (bv_half_modulus 32) with 2147483648.
  unfold bv_wrap. change (bv_modulus 32) with 4294967296. Z.div_mod_to_equations. lia.
Qed.

Lemma mb_win : forall (J0 NM J2 : list byte) k d n, length J0 = k -> (d + n <= length NM)%nat ->
  firstn n (skipn (k + d) (J0 ++ NM ++ J2)) = firstn n (skipn d NM).
Proof.
  intros J0 NM J2 k d n <- H. rewrite skipn_app, skipn_all2 by lia. replace (length J0 + d - length J0)%nat with d by lia.
  cbn [app]. rewrite skipn_app, firstn_app, length_skipn.
  replace (n - (length NM - d))%nat with 0%nat by lia. rewrite firstn_O, app_nil_r. reflexivity.
Qed.

Lemma mb_rw_split1 : forall segs m A c cs, rw_cells segs m A (c :: cs) ->
  rw_cells segs m A [c] /\ rw_cells segs m (A + Z.of_nat (csize c)) cs.
Proof.
  intros segs m A c cs [[Hwf HB] HW]. cbn [cells_wf] in Hwf. destruct Hwf as [W1 W2].
  cbn [cells_bytes] in HB. apply bytes_at_app in HB. destruct HB as [B1 B2].
  rewrite (cbytes_length c W1) in B2. cbn [cells_size] in HW.
  split; split; [split| | split|].
  - cbn [cells_wf]. tauto.
  - cbn [cells_bytes]. rewrite app_nil_r. exact B1.
  - cbn [cells_size]. rewrite Nat.add_0_r. eapply wr_at_prefix; [exact HW | lia].
  - exact W2.
  - exact B2.
  - apply (wr_at_sub segs m A _ _ _ HW); lia.
Qed.

Lemma mb_rw_join1 : forall segs m A c cs, rw_cells segs m A [c] -> rw_cells segs m (A + Z.of_nat (csize c)) cs ->
  rw_cells segs m A (c :: cs).
Proof.
  intros segs m A c cs [[W1 B1] H1] [[W2 B2] H2]. cbn [cells_wf] in W1. destruct W1 as [W1 _].
  cbn [cells_bytes] in B1. rewrite app_nil_r in B1. cbn [cells_size] in H1. rewrite Nat.add_0_r in H1.
  split; [split|].
  - cbn [cells_wf]. tauto.
  - cbn [cells_bytes]. apply bytes_at_app. split; [exact B1|]. rewrite (cbytes_length c W1). exact B2.
  - cbn [cells_size]. destruct H1 as (HA & Hn1 & F1). destruct H2 as (HA2 & Hn2 & F2).
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat (csize c))) as [L|L]; [apply F1; lia|].
    replace (A + i) with (A + Z.of_nat (csize c) + (i - Z.of_nat (csize c))) by lia. apply F2. lia.
Qed.

Lemma mb_psum_app : forall A B k, psum (A ++ B) (length A + k) = psum A (length A) + psum B k.
Proof.
  intros A B k. induction k as [|k IH].
  - rewrite Nat.add_0_r, psum_app_l by lia. cbn [psum]. lia.
  - rewrite Nat.add_succ_r, !rs_psum_S, IH, app_nth2 by lia.
    replace (length A + k - length A)%nat with k by lia. lia.
Qed.

Lemma mb_j6 : forall (J0 NM J2 c8 c9 c10 c11 c12 : list byte), length J0 = 32%nat -> length NM = 16%nat -> J2 = [] ->
  length c8 = 1%nat -> length c9 = 1%nat -> length c10 = 1%nat -> length c11 = 1%nat -> length c12 = 1%nat ->
  let J' := upd_bytes (upd_bytes (upd_bytes (upd_bytes (upd_bytes (J0 ++ NM ++ J2) 8 c8) 9 c9) 10 c10) 11 c11) 12 c12 in
  firstn 16 (skipn 32 J') = NM /\
  firstn 21 (skipn 8 (upd_bytes J' 13 NM)) = c8 ++ c9 ++ c10 ++ c11 ++ c12 ++ NM /\
  firstn 6 (skipn 42 (upd_bytes J' 13 NM)) = firstn 6 (skipn 10 NM).
Proof.
  intros J0 NM J2 c8 c9 c10 c11 c12 L0 LN -> L8 L9 L10 L11 L12 J'.
  do 32 (destruct J0 as [|? J0]; [discriminate|]). destruct J0; [|discriminate].
  do 16 (destruct NM as [|? NM]; [discriminate|]). destruct NM; [|discriminate].
  destruct c8 as [|? [|]]; try discriminate. destruct c9 as [|? [|]]; try discriminate.
  destruct c10 as [|? [|]]; try discriminate. destruct c11 as [|? [|]]; try discriminate.
  destruct c12 as [|? [|]]; try discriminate.
  subst J'. split; [|split]; reflexivity.
Qed.

Lemma mb_and127 : forall s, 0 <= s < 2^31 ->
  le1 (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (Z_to_bv 64 s))))) 127)) =
  [bz ((- s) mod 128)].
Proof.
  intros s Hs. rewrite (unsigned_lit s) by lia. rewrite rc_le1_lit. f_equal. unfold bz. f_equal.
  rewrite unsigned_lit_wrap. change 127 with (Z.ones 7). rewrite Z.land_ones by lia. change (2^7) with 128.
  unfold bv_swrap. change (bv_half_modulus 32) with 2147483648. unfold bv_wrap. change (bv_modulus 32) with 4294967296.
  Z.div_mod_to_equations. lia.
Qed.

Lemma mb_fin6 : forall (Y : list byte) c15 c16, length Y = 6%nat ->
  firstn 31 (upd_bytes (upd_bytes (map bz [4; 2; 0; 13; 0; 2; 0; 254; 8] ++ Y ++ zeros 17) 15 [c15]) 16 [c16]) =
  map bz [4; 2; 0; 13; 0; 2; 0; 254; 8] ++ Y ++ [c15; c16] ++ zeros 14.
Proof.
  intros Y c15 c16 L. do 6 (destruct Y as [|? Y]; [discriminate|]). destruct Y; [|discriminate]. reflexivity.
Qed.

Section Main.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p b o : Z) (row nb ob : list byte).
  Hypothesis HMS : memset_contract.
  Hypothesis HMC : memcpy_contract.
  Hypothesis HBD : build_dt1_single_contract.
  Hypothesis Rsp : 0 <= bv_unsigned sp < 2^64.
  Hypothesis Rlo : 0 <= bv_unsigned sp - 160.
  Hypothesis Hp : 0 < p < 2^64.
  Hypothesis Ho : 0 < o < 2^64.
  Hypothesis Hb : 0 <= b < 2^64.
  Hypothesis Ho32 : o + 32 <= 2^64.
  Hypothesis Hp296 : p + 296 <= 2^64.
  Hypothesis DOS : bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - 160.
  Hypothesis DOJ : o + 32 <= JOIN_0013 \/ JOIN_0013 + 64 <= o.
  Hypothesis Hlen : length row = 296%nat.
  Hypothesis Hp8 : p mod 8 = 0.
  Hypothesis DRS : bv_unsigned sp <= p \/ p + 296 <= bv_unsigned sp - 160.
  Hypothesis DRO : o + 32 <= p \/ p + 296 <= o.
  Hypothesis HNO : (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    name_ok nb /\ (bv_unsigned sp <= rname row \/ rname row + Z.of_nat (length nb) <= bv_unsigned sp - 160) /\
    (o + 32 <= rname row \/ rname row + Z.of_nat (length nb) <= o).
  Hypothesis ST0 : stk rsegs m (bv_unsigned sp - 160) (bv_unsigned sp).
  Hypothesis HRB0 : bytes_at rsegs m p row.
  Hypothesis HNB0 : (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 -> bytes_at rsegs m (rname row) nb.
  Hypothesis HOC0 : rw_cells rsegs m o [CB 32 ob].
  Hypothesis MI0 : mem_inv rsegs m.

  Definition Q := reac_box_model_block_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o row nb.

  Definition FS (m' : word -> option byte) (j : list byte) : Prop :=
    rw_cells rsegs m' (bv_unsigned sp + -112) [CB 48 j; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
    stk rsegs m' (bv_unsigned sp - 160) (bv_unsigned sp + -112) /\
    bytes_at rsegs m' p row /\
    ((b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 -> bytes_at rsegs m' (rname row) nb) /\
    munch [(bv_unsigned sp - 160, bv_unsigned sp); (o, o + 32)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m'.

  Definition R0 (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' : word) :=
    mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' (Z_to_bv 64 o) (Z_to_bv 64 p)
        a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3' t4' t5' t6'.

  Definition at_ (pc : Z) (R : bvmap 5 word) (m' : word -> option byte) : machine_state :=
    MS R F (Z_to_bv 64 pc) fc None m' (seg_rom rsegs).

  Lemma epi : forall (r : Z) X ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' t3' t4' t5' t6' m' j,
    FS m' j -> bytes_at rsegs m' o X -> X = synth row b nb -> r = rc row b ->
    evt rsegs Q (at_ 0x15274 (R0 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 r) s3' s4' s5' s6'
                                 t3' t4' t5' t6') m').
  Proof.
    intros r X ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' t3' t4' t5' t6' m' j
      (FR & ST & HRB & HNB & MU & WM & MI) HX EX Er. subst r X. unfold at_, R0.
    do 11 step.
    apply evt_done. unfold Q, reac_box_model_block_post.
    replace ((p =? 0) || (o =? 0)) with false by (symmetry; apply orb_false_iff; split; apply Z.eqb_neq; lia).
    do 15 eexists. split; [reflexivity|].
    split; [split; [exact HX | exact MU]|].
    split; [exact WM|]. split; [exact MI|].
    pose proof (stk_release rsegs m' _ _ _ ST FR ltac:(lia)) as STf. cbn [cells_size csize Nat.add] in STf.
    replace (bv_unsigned sp + -112 + Z.of_nat 112) with (bv_unsigned sp) in STf by lia. exact STf.
  Qed.

  Lemma fin : forall X ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' m' j,
    FS m' j -> bytes_at rsegs m' o X -> X = synth row b nb -> rc row b = 1 ->
    evt rsegs Q (at_ 0x15270 (R0 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6'
                                 t3' t4' t5' t6') m').
  Proof.
    intros X ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' m' j HF HX EX Er.
    unfold at_, R0. step.
    eapply epi; [exact HF | exact HX | exact EX | symmetry; exact Er].
  Qed.

  Lemma exz : forall (r : Z) ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' t3' t4' t5' t6' m' j,
    FS m' j -> rw_cells rsegs m' o [CB 32 (zeros 32)] -> synth row b nb = zeros 32 -> r = rc row b ->
    evt rsegs Q (at_ 0x15274 (R0 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 r) s3' s4' s5' s6'
                                 t3' t4' t5' t6') m').
  Proof.
    intros r ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' t3' t4' t5' t6' m' j HF HO EZ Er.
    eapply epi; [exact HF | exact (mb_rw1 _ _ _ _ _ HO) | symmetry; exact EZ | exact Er].
  Qed.

  Lemma call_ms : forall (ret : Z) (k n : nat) (v : Z) X (a0 a1 a2 : word)
      t0 t1 t2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' t3 t4 t5 t6 m' j,
    ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret -> (k + n <= 32)%nat -> (1 <= n)%nat -> 0 <= v < 256 ->
    bv_unsigned a0 = o + Z.of_nat k -> bv_unsigned a1 = v -> bv_unsigned a2 = Z.of_nat n ->
    FS m' j -> rw_cells rsegs m' o [CB 32 X] ->
    (forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m'',
       FS m'' j -> rw_cells rsegs m'' o [CB 32 (upd_bytes X k (repeat (bz v) n))] ->
       evt rsegs Q (at_ ret (R0 (Z_to_bv 64 ret) t0' t1' t2' a0 a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6'
                                t3' t4' t5' t6') m'')) ->
    evt rsegs Q (MS (R0 (Z_to_bv 64 ret) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' t3 t4 t5 t6)
                    F (Z_to_bv 64 MEMSET) fc None m' (seg_rom rsegs)).
  Proof.
    intros ret k n v X a0 a1 a2 t0 t1 t2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' t3 t4 t5 t6 m' j Hret Hkn Hn Hv
      E0 E1 E2 (FR & ST & HRB & HNB & MU & WM & MI) HO K.
    unfold R0.
    pose proof (rs_rw_sub rsegs m' o 32 X k n HO Hkn) as HS.
    eapply evt_cut.
    { eapply HMS; [ | exact MI]. rewrite E0, E2, Nat2Z.id. exact HS. }
    intros ms' PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & E & MU2 & WM2 & MI2 & RW2).
    subst ms'. rewrite E0, E1, E2, Nat2Z.id in RW2. rewrite E0, E2 in MU2. rewrite Z.mod_small in RW2 by lia.
    change (Z_to_bv 8 v) with (bz v) in RW2.
    pose proof (rs_rw_upd rsegs m' m2 o 32 X k n _ HO Hkn MU2 WM2 RW2) as HO2.
    assert (HNB2 : (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 -> bytes_at rsegs m2 (rname row) nb).
    { intros B5 H1 H2. destruct (HNO B5 H1 H2) as (_ & _ & DNO).
      eapply bytes_at_transport; [exact (HNB B5 H1 H2) | exact MU2 | cbn [disjoint_from]; lia]. }
    clear HS RW2 HO HNB.
    transport_after_call rsegs m' m2 MU2 WM2. clear MU2 WM2.
    rewrite Hret. apply K; [|exact HO2].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact HNB2|].
    split; [assumption|]. split; assumption.
  Qed.

  Lemma call_mc : forall (ret : Z) (k n : nat) (A : Z) Sb X (a0 a1 a2 : word)
      t0 t1 t2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' t3 t4 t5 t6 m' j,
    ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret -> (k + n <= 32)%nat -> (1 <= n)%nat -> length Sb = n ->
    bv_unsigned a0 = o + Z.of_nat k -> bv_unsigned a1 = A -> bv_unsigned a2 = Z.of_nat n ->
    (A + Z.of_nat n <= o + Z.of_nat k \/ o + Z.of_nat k + Z.of_nat n <= A) ->
    FS m' j -> rw_cells rsegs m' o [CB 32 X] -> bytes_at rsegs m' A Sb ->
    (forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m'',
       FS m'' j -> rw_cells rsegs m'' o [CB 32 (upd_bytes X k Sb)] ->
       evt rsegs Q (at_ ret (R0 (Z_to_bv 64 ret) t0' t1' t2' a0 a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6'
                                t3' t4' t5' t6') m'')) ->
    evt rsegs Q (MS (R0 (Z_to_bv 64 ret) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' t3 t4 t5 t6)
                    F (Z_to_bv 64 0x1d3d8) fc None m' (seg_rom rsegs)).
  Proof.
    intros ret k n A Sb X a0 a1 a2 t0 t1 t2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' t3 t4 t5 t6 m' j Hret Hkn Hn LS
      E0 E1 E2 DSO (FR & ST & HRB & HNB & MU & WM & MI) HO HSb K.
    unfold R0.
    pose proof (rs_rw_sub rsegs m' o 32 X k n HO Hkn) as HS.
    eapply evt_cut.
    { eapply HMC; [ | | | | exact MI].
      - rewrite E1. exact HSb.
      - rewrite E2, Nat2Z.id. exact LS.
      - rewrite E0, E2, Nat2Z.id. exact HS.
      - rewrite E0, E1, E2. lia. }
    intros ms' PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & E & MU2 & WM2 & MI2 & RW2 & SB2).
    subst ms'. rewrite E0, E2, Nat2Z.id in RW2. rewrite E0, E2 in MU2. clear SB2.
    pose proof (rs_rw_upd rsegs m' m2 o 32 X k n _ HO Hkn MU2 WM2 RW2) as HO2.
    assert (HNB2 : (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 -> bytes_at rsegs m2 (rname row) nb).
    { intros B5 H1 H2. destruct (HNO B5 H1 H2) as (_ & _ & DNO).
      eapply bytes_at_transport; [exact (HNB B5 H1 H2) | exact MU2 | cbn [disjoint_from]; lia]. }
    clear HS RW2 HO HNB HSb.
    transport_after_call rsegs m' m2 MU2 WM2. clear MU2 WM2.
    rewrite Hret. apply K; [|exact HO2].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact HNB2|].
    split; [assumption|]. split; assumption.
  Qed.

  Lemma jcopy : forall (A : Z) JJ ra' t0' t1' t2' a0' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' m' j,
    FS m' j -> rw_cells rsegs m' o [CB 32 (zeros 32)] ->
    bytes_at rsegs m' A JJ -> length JJ = 32%nat -> (o + 32 <= A \/ A + 32 <= o) ->
    JJ = synth row b nb -> rc row b = 1 ->
    evt rsegs Q (at_ 0x14fc4 (R0 ra' t0' t1' t2' a0' (Z_to_bv 64 A) a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6'
                                 t3' t4' t5' t6') m').
  Proof.
    intros A JJ ra' t0' t1' t2' a0' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' m' j
      HF HO HJ LJ DJ EJ Er.
    pose proof (bytes_at_bound _ _ _ _ HJ) as BJ. rewrite LJ in BJ.
    unfold at_, R0. step. step. step.
    eapply (call_mc 0x14fd0 0 32 A JJ (zeros 32)); [apply ret_pc_even; [lia | reflexivity] | lia | lia | exact LJ
           | rewrite unsigned_lit; lia
           | rewrite unsigned_lit; lia | rewrite unsigned_lit; lia | lia | exact HF | exact HO | exact HJ |].
    intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m'' HF2 HO2.
    unfold at_, R0. step.
    eapply fin; [exact HF2 | exact (mb_rw1 _ _ _ _ _ HO2) | | exact Er].
    rewrite <- EJ. unfold upd_bytes. rewrite LJ. change (firstn 0 (zeros 32)) with (@nil byte).
    change (skipn (0 + 32) (zeros 32)) with (@nil byte). rewrite app_nil_r. reflexivity.
  Qed.

  Lemma FS_mi : forall m' j, FS m' j -> mem_inv rsegs m'.
  Proof. intros m' j (_ & _ & _ & _ & _ & _ & MI). exact MI. Qed.

  Lemma hnb_tr : forall m1 m2, munch [(bv_unsigned sp - 160, bv_unsigned sp); (o, o + 32)] m1 m2 ->
    ((b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 -> bytes_at rsegs m1 (rname row) nb) ->
    ((b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 -> bytes_at rsegs m2 (rname row) nb).
  Proof.
    intros m1 m2 MU H B5 H1 H2. destruct (HNO B5 H1 H2) as (_ & DS & DO).
    eapply bytes_at_transport; [exact (H B5 H1 H2) | exact MU | cbn [disjoint_from]; lia].
  Qed.

  Lemma rom_at : forall m' A bs, mem_inv rsegs m' ->
    (ro_bytes_b rsegs A bs && (0 <=? A) && (A + Z.of_nat (length bs) <=? 2^64))%bool = true ->
    bytes_at rsegs m' A bs.
  Proof.
    intros m' A bs Hm H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Z.leb_le in H2. apply Z.leb_le in H3.
    apply ro_bytes_at; [exact Hm | exact H2 | exact H3 |]. apply ro_bytes_b_sound. exact H1.
  Qed.

  Lemma cs1 : forall ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' m' j,
    b = 1 -> FS m' j -> rw_cells rsegs m' o [CB 32 (zeros 32)] ->
    evt rsegs Q (at_ 0x14fbc (R0 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6'
                                 t3' t4' t5' t6') m').
  Proof.
    intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' m' j Eb HF HO.
    unfold at_, R0. step. step.
    eapply (jcopy 0x106e4 J14); [exact HF | exact HO | | reflexivity | unfold JOIN_0013 in DOJ; lia
                                | rewrite Eb; reflexivity | rewrite Eb; reflexivity].
    apply rom_at; [exact (FS_mi m' j HF) | vm_compute; reflexivity].
  Qed.

  Lemma cs2 : forall ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' m' j,
    b = 2 -> FS m' j -> rw_cells rsegs m' o [CB 32 (zeros 32)] ->
    evt rsegs Q (at_ 0x14f98 (R0 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6'
                                 t3' t4' t5' t6') m').
  Proof.
    intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' m' j Eb HF HO.
    unfold at_, R0. step. step. step.
    eapply (jcopy 0x106c4 J13); [exact HF | exact HO | | reflexivity | unfold JOIN_0013 in DOJ; lia
                                | rewrite Eb; reflexivity | rewrite Eb; reflexivity].
    apply rom_at; [exact (FS_mi m' j HF) | vm_compute; reflexivity].
  Qed.

  Lemma bdc : forall (A : Z) (n : nat) D (a1 a2 a3 : word) ra' t0' t1' t2' a4' a5' a6' a7' s2' s3' s4' s5' s6'
      t3' t4' t5' t6' m' j,
    (n <= 9)%nat -> length D = n -> bv_unsigned a1 = A -> bv_unsigned a2 = bv_unsigned sp + -112 + 8 ->
    bv_unsigned a3 = Z.of_nat n ->
    FS m' j -> rw_cells rsegs m' o [CB 32 (zeros 32)] -> bytes_at rsegs m' (bv_unsigned sp + -112 + 8) D ->
    dt1s A D = synth row b nb -> rc row b = 1 ->
    evt rsegs Q (at_ 0x1526c (R0 ra' t0' t1' t2' (Z_to_bv 64 o) a1 a2 a3 a4' a5' a6' a7' s2' s3' s4' s5' s6'
                                 t3' t4' t5' t6') m').
  Proof.
    intros A n D a1 a2 a3 ra' t0' t1' t2' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' m' j
      Hn LD E1 E2 E3 (FR & ST & HRB & HNB & MU & WM & MI) HO HD ED Er.
    pose proof HO as [_ WO]. cbn [cells_size csize Nat.add] in WO.
    pose proof (bytes_at_bound _ _ _ _ HD) as BD. rewrite LD in BD.
    unfold at_, R0. step.
    eapply evt_cut.
    { eapply HBD with (ob := zeros 32) (D := D); rewrite ?E1, ?E2, ?E3, ?unsigned_lit by lia.
      - replace (bv_unsigned sp + -112 - 48) with (bv_unsigned sp - 160) by lia. exact ST.
      - lia.
      - lia.
      - lia.
      - exact HO.
      - lia.
      - rewrite Nat2Z.id. exact LD.
      - exact HD.
      - lia.
      - lia.
      - lia.
      - exact MI. }
    intros ms' PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & E & HB2 & _ & _ &
                    MU2 & WM2 & MI2 & ST2).
    subst ms'. rewrite E1, E3, Nat2Z.id, (unsigned_lit o) in HB2 by lia.
    rewrite E3, (unsigned_lit o), (unsigned_lit (bv_unsigned sp + -112)) in MU2 by lia.
    rewrite (unsigned_lit (bv_unsigned sp + -112)) in ST2 by lia.
    replace (bv_unsigned sp + -112 - 48) with (bv_unsigned sp - 160) in MU2, ST2 by lia.
    assert (MU3 : munch [(bv_unsigned sp - 160, bv_unsigned sp); (o, o + 32)] m' m2).
    { eapply munch_weaken; [|exact MU2]. unfold sub_fp. cbn [outside]. intros. repeat split; try exact I; lia. }
    pose proof (hnb_tr m' m2 MU3 HNB) as HNB2.
    pose proof (wr_at_transport rsegs m' m2 o 32 WO WM2) as WO2.
    pose proof (rw_cells_transport rsegs _ m' m2 _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia))
      as FR2.
    pose proof (bytes_at_transport rsegs _ m' m2 _ _ HRB MU2 ltac:(cbn [disjoint_from]; rewrite Hlen; lia)) as HRB2.
    pose proof (munch_trans _ _ _ _ MU MU3) as MU4. pose proof (wmono_trans rsegs _ _ _ WM WM2) as WM4.
    clear MU MU2 MU3 WM WM2 HNB HO HD ST MI FR HRB.
    replace (ret_pc (Z_to_bv 64 0x15270)) with (Z_to_bv 64 0x15270) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    eapply fin; [ | exact HB2 | | exact Er].
    - split; [exact FR2|]. split; [exact ST2|]. split; [exact HRB2|]. split; [exact HNB2|].
      split; [exact MU4|]. split; [exact WM4 | exact MI2].
    - rewrite <- ED. unfold dt1s. rewrite LD. reflexivity.
  Qed.

  Lemma cs4 : forall ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' t3' t4' t5' t6' m' j,
    b = 4 -> FS m' j -> rw_cells rsegs m' o [CB 32 (zeros 32)] ->
    evt rsegs Q (at_ 0x14f4c (R0 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (-1)) s3' s4' s5' s6'
                                 t3' t4' t5' t6') m').
  Proof.
    intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' t3' t4' t5' t6' m' j Eb HF HO.
    destruct HF as (FR & ST & HRB & HNB & MU & WM & MI). clear HNB.
    pose proof (rs_rd2 rsegs m' p row 268 HRB ltac:(lia)) as R1.
    pose proof (rs_rd2 rsegs m' p row 270 HRB ltac:(lia)) as R2.
    pose proof (rs_rd2 rsegs m' p row 272 HRB ltac:(lia)) as R3.
    change (Z.of_nat 268) with 268 in R1. change (Z.of_nat 270) with 270 in R2. change (Z.of_nat 272) with 272 in R3.
    unfold at_, R0.
    do 19 step.
    match goal with H : rw_cells rsegs ?mm (bv_unsigned sp + -112) _ |- _ =>
      pose proof (mb_cells_sub _ _ _ _ 1 8 H) as HD; pose proof (mb_take _ _ _ _ 10 H) as FR'; clear H end.
    cbn [firstn skipn cells_size cells_bytes csize cbytes app Nat.add] in HD, FR'.
    change (Z.of_nat 8) with 8 in HD.
    match type of HD with bytes_at _ _ _ ?DD => eapply (bdc 1536 8 DD) end.
    - lia.
    - reflexivity.
    - rewrite unsigned_lit; lia.
    - rewrite unsigned_lit; lia.
    - rewrite unsigned_lit; lia.
    - split; [exact FR'|]. split; [exact ST|]. split; [exact HRB|]. split; [intros [E|E]; lia|].
      split; [exact MU|]. split; [exact WM | exact MI].
    - exact HO.
    - exact HD.
    - rewrite Eb. change (synth row 4 nb) with (dt1s 1536 (rvb row)). apply (f_equal (dt1s 1536)). unfold rvb.
      rewrite !rs_hi16, !rs_lo16 by apply rs_rw16_range. reflexivity.
    - rewrite Eb. reflexivity.
  Qed.

  Lemma cs3 : forall ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' t3' t4' t5' t6' m' j,
    b = 3 -> FS m' j -> rw_cells rsegs m' o [CB 32 (zeros 32)] ->
    evt rsegs Q (at_ 0x14fa4 (R0 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (-1)) s3' s4' s5' s6'
                                 t3' t4' t5' t6') m').
  Proof.
    intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' t3' t4' t5' t6' m' j Eb HF HO.
    pose proof (rs_rd2 rsegs m' p row 266 (proj1 (proj2 (proj2 HF))) ltac:(lia)) as R1.
    change (Z.of_nat 266) with 266 in R1.
    pose proof (rs_rw16_range row 266) as RV.
    unfold at_, R0.
    step. rewrite rs_zx16. step. step. step.
    rewrite (unsigned_lit (rw16 row 266)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^4) with 16.
    destruct (Z.leb_spec (fwm row) 9999) as [FW|FW]; unfold fwm in FW.
    - if_t.
      destruct HF as (FR & ST & HRB & HNB & MU & WM & MI). clear HNB.
      do 37 step.
      match goal with H : rw_cells rsegs ?mm (bv_unsigned sp + -112) _ |- _ =>
        pose proof (mb_cells_sub _ _ _ _ 1 4 H) as HD; pose proof (mb_take _ _ _ _ 6 H) as FR'; clear H end.
      cbn [firstn skipn cells_size cells_bytes csize cbytes app Nat.add] in HD, FR'.
      change (Z.of_nat 8) with 8 in HD.
      assert (Hv : 0 <= rw16 row 266 < 10000) by lia.
      match type of HD with bytes_at _ _ _ ?DD =>
        assert (EDD : DD = digits (fwm row)); [|eapply (bdc 0 4 DD)] end.
      + clear - Hv. unfold digits, fwm. cbn [map]. revert Hv. generalize (rw16 row 266). intros v Hv.
        repeat apply rc_cons_eq; try reflexivity; unfold bz; rs_brute_tac v.
      + lia.
      + reflexivity.
      + rewrite unsigned_lit; lia.
      + rewrite unsigned_lit; lia.
      + rewrite unsigned_lit; lia.
      + split; [exact FR'|]. split; [exact ST|]. split; [exact HRB|]. split; [intros [E|E]; lia|].
        split; [exact MU|]. split; [exact WM | exact MI].
      + exact HO.
      + exact HD.
      + rewrite EDD, Eb. change (synth row 3 nb) with (if fwm row <=? 9999 then dt1s 0 (digits (fwm row)) else zeros 32).
        replace (fwm row <=? 9999) with true by (symmetry; apply Z.leb_le; unfold fwm; lia). reflexivity.
      + rewrite Eb. change (rc row 3) with (if fwm row <=? 9999 then 1 else -1).
        replace (fwm row <=? 9999) with true by (symmetry; apply Z.leb_le; unfold fwm; lia). reflexivity.
    - if_f. step. step.
      eapply exz; [exact HF | exact HO | | ].
      + rewrite Eb. change (synth row 3 nb) with (if fwm row <=? 9999 then dt1s 0 (digits (fwm row)) else zeros 32).
        replace (fwm row <=? 9999) with false by (symmetry; apply Z.leb_gt; unfold fwm; lia). reflexivity.
      + rewrite Eb. change (rc row 3) with (if fwm row <=? 9999 then 1 else -1).
        replace (fwm row <=? 9999) with false by (symmetry; apply Z.leb_gt; unfold fwm; lia). reflexivity.
  Qed.

  Definition INV (m' : word -> option byte) (X j : list byte) : Prop := FS m' j /\ rw_cells rsegs m' o [CB 32 X].

  Lemma inv_row : forall m' X j, INV m' X j -> bytes_at rsegs m' p row.
  Proof. intros m' X j ((_ & _ & HRB & _) & _). exact HRB. Qed.

  Lemma inv_out : forall m' X j, INV m' X j -> bytes_at rsegs m' o X.
  Proof. intros m' X j (_ & HO). exact (mb_rw1 _ _ _ _ _ HO). Qed.

  Lemma inv_len : forall m' X j, INV m' X j -> length X = 32%nat.
  Proof. intros m' X j (_ & [[[L _] _] _]). exact L. Qed.

  Lemma inv_ok : forall m' X j (k : Z) (n : nat), INV m' X j -> 0 <= k -> k + Z.of_nat n <= 32 ->
    store_ok rsegs m' (wa (o + k)) n = true.
  Proof.
    intros m' X j k n (_ & [_ WO]) Hk Hn. cbn [cells_size csize Nat.add] in WO. change (Z.of_nat 32) with 32 in WO.
    apply (wr_at_store_ok rsegs m' o 32); [exact WO | lia | lia].
  Qed.

  Lemma inv_store : forall m' X j (k : Z) A bs, INV m' X j -> 0 <= k -> k + Z.of_nat (length bs) <= 32 ->
    A = wa (o + k) -> INV (write_to_mem m' A bs) (upd_bytes X (Z.to_nat k) bs) j.
  Proof.
    intros m' X j k A bs ((FR & ST & HRB & HNB & MU & WM & MI) & [[Hwf HB] WO]) Hk Hn ->.
    cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [LX _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
    cbn [cells_size csize Nat.add] in WO. change (Z.of_nat 32) with 32 in WO.
    pose proof (wr_at_store_ok rsegs m' o 32 k (length bs) WO Hk Hn) as HS.
    split; [split; [|split; [|split; [|split; [|split; [|split]]]]] | split; [split|]].
    - apply rw_cells_frame; [exact FR | lia | lia | cbn [cells_size csize Nat.add]; lia].
    - apply stk_write; [exact ST | lia | lia].
    - apply bytes_at_write_other; [exact HRB | lia | lia | rewrite Hlen; lia].
    - intros B5 H1 H2. destruct (HNO B5 H1 H2) as (_ & _ & DO).
      apply bytes_at_write_other; [exact (HNB B5 H1 H2) | lia | lia | lia].
    - apply munch_write; [exact MU | lia | lia | cbn [inside]; right; left; lia].
    - apply wmono_write; exact WM.
    - apply mem_inv_store; [exact MI | exact HS].
    - cbn [cells_wf cell_wf]. split; [rewrite upd_bytes_length; lia | exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_write_inside; [exact HB | lia | lia].
    - cbn [cells_size csize Nat.add]. change (Z.of_nat 32) with 32. apply wr_at_write. exact WO.
  Qed.

  Lemma inv_fok : forall m' X j (k : Z) (n : nat), INV m' X j -> 0 <= k -> k + Z.of_nat n <= 48 ->
    store_ok rsegs m' (wa (bv_unsigned sp + -112 + k)) n = true.
  Proof.
    intros m' X j k n ((FR & _) & _) Hk Hn. destruct FR as [_ WF]. cbn [cells_size csize Nat.add] in WF.
    apply (wr_at_store_ok rsegs m' (bv_unsigned sp + -112) (Z.of_nat 112)); [exact WF | lia | lia].
  Qed.

  Lemma inv_fstore : forall m' X j (k : Z) A bs, INV m' X j -> 0 <= k -> k + Z.of_nat (length bs) <= 48 ->
    A = wa (bv_unsigned sp + -112 + k) -> INV (write_to_mem m' A bs) X (upd_bytes j (Z.to_nat k) bs).
  Proof.
    intros m' X j k A bs ((FR & ST & HRB & HNB & MU & WM & MI) & HO) Hk Hn ->.
    pose proof FR as [_ WF]. cbn [cells_size csize Nat.add] in WF.
    pose proof (wr_at_store_ok rsegs m' (bv_unsigned sp + -112) (Z.of_nat 112) k (length bs) WF Hk ltac:(lia)) as HS.
    split; [split; [|split; [|split; [|split; [|split; [|split]]]]] |].
    - apply mb_rw_cb0; [exact FR | lia | lia].
    - apply stk_write; [exact ST | lia | lia].
    - apply bytes_at_write_other; [exact HRB | lia | lia | rewrite Hlen; lia].
    - intros B5 H1 H2. destruct (HNO B5 H1 H2) as (_ & DS & _).
      apply bytes_at_write_other; [exact (HNB B5 H1 H2) | lia | lia | lia].
    - apply munch_write; [exact MU | lia | lia | cbn [inside]; left; lia].
    - apply wmono_write; exact WM.
    - apply mem_inv_store; [exact MI | exact HS].
    - apply rw_cells_frame; [exact HO | lia | lia | cbn [cells_size csize Nat.add]; lia].
  Qed.

  Ltac ost k n :=
    lazymatch goal with
    | PI : INV ?mc ?X ?J |- _ =>
        let HS := fresh "HS" in
        pose proof (inv_ok mc X J k n PI ltac:(lia) ltac:(lia)) as HS;
        step; clear HS;
        lazymatch goal with
        | |- evt _ _ (MS _ _ _ _ _ (write_to_mem mc ?A ?bs) _) =>
            let PI' := fresh "PI" in
            pose proof (inv_store mc X J k A bs PI ltac:(lia) ltac:(cbn [length]; rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1; cbn [length]; lia)
                          ltac:(first [reflexivity | unfold wa; f_equal; lia])) as PI';
            clear PI; rename PI' into PI; let mc' := fresh "mc" in set (mc' := write_to_mem mc A bs) in *; clearbody mc'
        end
    end.

  Ltac fst k n :=
    lazymatch goal with
    | PI : INV ?mc ?X ?J |- _ =>
        let HS := fresh "HS" in
        pose proof (inv_fok mc X J k n PI ltac:(lia) ltac:(lia)) as HS;
        step; clear HS;
        lazymatch goal with
        | |- evt _ _ (MS _ _ _ _ _ (write_to_mem mc ?A ?bs) _) =>
            let PI' := fresh "PI" in
            pose proof (inv_fstore mc X J k A bs PI ltac:(lia) ltac:(cbn [length]; rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1; cbn [length]; lia)
                          ltac:(first [reflexivity | unfold wa; f_equal; lia])) as PI';
            clear PI; rename PI' into PI; let mc' := fresh "mc" in set (mc' := write_to_mem mc A bs) in *; clearbody mc'
        end
    end.

  Ltac rrow k :=
    lazymatch goal with
    | PI : INV ?mc ?X ?J |- _ =>
        let R := fresh "RD" in
        pose proof (rd_byte rsegs mc p row k (inv_row mc X J PI) ltac:(rewrite Hlen; lia)) as R;
        let z := eval vm_compute in (Z.of_nat k) in change (Z.of_nat k) with z in R
    end.

  Lemma stchk : forall X ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' m' j,
    INV m' X j -> withchk (firstn 31 X) = synth row b nb -> rc row b = 1 ->
    evt rsegs Q (at_ 0x151c4 (R0 ra' t0' t1' t2' (Z_to_bv 64 (psum X 31)) a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5'
                                 s6' t3' t4' t5' t6') m').
  Proof.
    intros X ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' m' j PI EX Er.
    pose proof (inv_len m' X j PI) as LX.
    unfold at_, R0.
    step. ost 31 1%nat. rewrite rc_le1_negw in PI. step.
    destruct PI as [HF HO]. eapply fin; [exact HF | exact (mb_rw1 _ _ _ _ _ HO) | | exact Er].
    rewrite <- EX. unfold withchk, chk, upd_bytes, bz. rewrite rs_psum_firstn by lia.
    change (Z.to_nat 31) with 31%nat. cbn [length Nat.add]. rewrite (skipn_all2 X) by lia.
    rewrite app_nil_r. reflexivity.
  Qed.

  Lemma oloop0 : forall k i X (x2 : word) ra' t0' t1' t2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' m' j,
    (i + k = 31)%nat -> (0 < k)%nat -> x2 = Z_to_bv 64 (o + Z.of_nat i) ->
    INV m' X j -> withchk (firstn 31 X) = synth row b nb -> rc row b = 1 ->
    evt rsegs Q (at_ 0x15350 (R0 ra' t0' t1' t2' (Z_to_bv 64 (psum X i)) (Z_to_bv 64 (o + 31)) x2 a3' a4' a5' a6' a7'
                             s2' s3' s4' s5' s6' t3' t4' t5' t6') m').
  Proof.
    induction k as [|k IH];
      intros i X x2 ra' t0' t1' t2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' m' j Hik Hk E2 PI EX Er;
      [lia|].
    subst x2.
    pose proof (inv_len m' X j PI) as LX.
    pose proof (rd_byte rsegs m' o X i (inv_out m' X j PI) ltac:(lia)) as RD.
    pose proof (psum_range X i) as PR.
    unfold at_, R0.
    step. step. step.
    rewrite psum_S_zxb.
    step.
    rewrite (rc_eqb_lit (o + Z.of_nat i + 1) (o + 31)) by lia.
    destruct k as [|k].
    - replace (o + Z.of_nat i + 1 =? o + 31) with true by (symmetry; apply Z.eqb_eq; lia).
      cbn [negb]. cbv iota.
      replace (S i) with 31%nat by lia.
      step.
      eapply stchk; [exact PI | exact EX | exact Er].
    - replace (o + Z.of_nat i + 1 =? o + 31) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [negb]. cbv iota.
      eapply (IH (S i)); first [lia | eassumption | f_equal; lia].
  Qed.

  Lemma oloop5 : forall k i X (x2 : word) ra' t0' t1' t2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' m' j,
    (i + k = 31)%nat -> (0 < k)%nat -> x2 = Z_to_bv 64 (o + Z.of_nat i) ->
    INV m' X j -> withchk (firstn 31 X) = synth row b nb -> rc row b = 1 ->
    evt rsegs Q (at_ 0x150b0 (R0 ra' t0' t1' t2' (Z_to_bv 64 (psum X i)) (Z_to_bv 64 (o + 31)) x2 a3' a4' a5' a6' a7'
                             s2' s3' s4' s5' s6' t3' t4' t5' t6') m').
  Proof.
    induction k as [|k IH];
      intros i X x2 ra' t0' t1' t2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' m' j Hik Hk E2 PI EX Er;
      [lia|].
    subst x2.
    pose proof (inv_len m' X j PI) as LX.
    pose proof (rd_byte rsegs m' o X i (inv_out m' X j PI) ltac:(lia)) as RD.
    pose proof (psum_range X i) as PR.
    unfold at_, R0.
    step. step. step.
    rewrite psum_S_zxb.
    step.
    rewrite (rc_eqb_lit (o + Z.of_nat i + 1) (o + 31)) by lia.
    destruct k as [|k].
    - replace (o + Z.of_nat i + 1 =? o + 31) with true by (symmetry; apply Z.eqb_eq; lia).
      cbn [negb]. cbv iota.
      replace (S i) with 31%nat by lia.
      step.
      eapply stchk; [exact PI | exact EX | exact Er].
    - replace (o + Z.of_nat i + 1 =? o + 31) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [negb]. cbv iota.
      eapply (IH (S i)); first [lia | eassumption | f_equal; lia].
  Qed.

  Lemma oloop6 : forall k i X (x2 : word) ra' t0' t1' t2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' m' j,
    (i + k = 31)%nat -> (0 < k)%nat -> x2 = Z_to_bv 64 (o + Z.of_nat i) ->
    INV m' X j -> withchk (firstn 31 X) = synth row b nb -> rc row b = 1 ->
    evt rsegs Q (at_ 0x151b4 (R0 ra' t0' t1' t2' (Z_to_bv 64 (psum X i)) (Z_to_bv 64 (o + 31)) x2 a3' a4' a5' a6' a7'
                             s2' s3' s4' s5' s6' t3' t4' t5' t6') m').
  Proof.
    induction k as [|k IH];
      intros i X x2 ra' t0' t1' t2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' m' j Hik Hk E2 PI EX Er;
      [lia|].
    subst x2.
    pose proof (inv_len m' X j PI) as LX.
    pose proof (rd_byte rsegs m' o X i (inv_out m' X j PI) ltac:(lia)) as RD.
    pose proof (psum_range X i) as PR.
    unfold at_, R0.
    step. step. step.
    rewrite psum_S_zxb.
    step.
    rewrite (rc_eqb_lit (o + Z.of_nat i + 1) (o + 31)) by lia.
    destruct k as [|k].
    - replace (o + Z.of_nat i + 1 =? o + 31) with true by (symmetry; apply Z.eqb_eq; lia).
      cbn [negb]. cbv iota.
      replace (S i) with 31%nat by lia.
      
      eapply stchk; [exact PI | exact EX | exact Er].
    - replace (o + Z.of_nat i + 1 =? o + 31) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [negb]. cbv iota.
      eapply (IH (S i)); first [lia | eassumption | f_equal; lia].
  Qed.

  Definition H8 : list byte := [bz 1; bz 3; bz 0; bz 16; sel row; bz 0; bz 0; strap row].

  Lemma gram_eq : synok row = true -> withchk (firstn 31 (H8 ++ (slots row ++ tail row) ++ zeros 1)) = gram row.
  Proof.
    intros SOK. pose proof (rs_gram31_len row Hlen SOK) as G.
    replace (firstn 31 (H8 ++ (slots row ++ tail row) ++ zeros 1)) with (gram31 row).
    - unfold withchk, chk, gram. rewrite rs_gram_chk. reflexivity.
    - assert (L31 : length (H8 ++ slots row ++ tail row) = 31%nat) by (unfold gram31 in G; exact G).
      rewrite app_assoc, firstn_app, L31, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 by lia. reflexivity.
  Qed.

  Lemma mc0 : forall ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' m' j,
    b = 0 -> synok row = true -> INV m' (H8 ++ slots row ++ zeros 12) j ->
    evt rsegs Q (at_ 0x15334 (R0 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6'
                                 t3' t4' t5' t6') m').
  Proof.
    intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' m' j Eb SOK PI.
    pose proof (rs_slots_len row SOK) as LS.
    assert (LT : length (tail row) = 11%nat) by (unfold tail; rewrite length_firstn, length_skipn; lia).
    pose proof (bytes_at_sub rsegs m' p row 254 11 (inv_row m' _ _ PI) ltac:(lia)) as HT.
    change (firstn 11 (skipn 254 row)) with (tail row) in HT. change (Z.of_nat 254) with 254 in HT.
    destruct PI as [HF HO].
    unfold at_, R0. step. step. step. step.
    eapply (call_mc 0x15344 20 11 (p + 254) (tail row) (H8 ++ slots row ++ zeros 12));
      [apply ret_pc_even; [lia | reflexivity] | lia | lia | exact LT
      | rewrite unsigned_lit; lia | rewrite unsigned_lit; lia | rewrite unsigned_lit; lia | lia
      | exact HF | exact HO | exact HT |].
    intros u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 m2 HF2 HO2.
    rewrite (rs_upd_fill H8 (slots row) (tail row) 12 20) in HO2 by (unfold H8; cbn [length]; lia).
    rewrite LT in HO2. change (12 - 11)%nat with 1%nat in HO2.
    assert (PI2 : INV m2 (H8 ++ (slots row ++ tail row) ++ zeros 1) j) by (split; assumption).
    unfold at_, R0. step. step. step.
    eapply (oloop0 31 0); [lia | lia | f_equal; lia | exact PI2 | | rewrite Eb; exact (proj1 (rs_synth_gram row nb SOK))].
    rewrite (gram_eq SOK). rewrite Eb. symmetry. exact (proj2 (rs_synth_gram row nb SOK)).
  Qed.

  Lemma tail0 : forall (k : nat) P (s2w : word) ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' t3' t4' t5'
      t6' m' j,
    b = 0 -> synok row = true -> (k <= 12)%nat -> length P = k -> P ++ repeat (bz 3) (12 - k) = slots row ->
    bv_unsigned s2w = Z.of_nat k -> INV m' (H8 ++ P ++ zeros (24 - k)) j ->
    evt rsegs Q (at_ 0x15310 (R0 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2w s3' s4' s5' s6'
                                 t3' t4' t5' t6') m').
  Proof.
    intros k P s2w ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' t3' t4' t5' t6' m' j Eb SOK Hk LP EP E2 PI.
    unfold at_, R0. step. step. step.
    rewrite E2. wsimp. rewrite rc_ltu_lit by lia.
    destruct (Z.ltb_spec 11 (Z.of_nat k)) as [K12|K11]; cbv iota.
    - assert (E12 : k = 12%nat) by lia. rewrite E12 in EP, PI. replace (P ++ repeat (bz 3) (12 - 12)) with P in EP
        by (rewrite Nat.sub_diag; cbn [repeat]; rewrite app_nil_r; reflexivity).
      rewrite EP in PI. change (24 - 12)%nat with 12%nat in PI. eapply mc0; eassumption.
    - step. step. step. step. step. step.
      destruct PI as [HF HO].
      eapply (call_ms 0x15334 (8 + k) (12 - k) 3 (H8 ++ P ++ zeros (24 - k)));
        [apply ret_pc_even; [lia | reflexivity] | lia | lia | lia | wsimp; lia | wsimp; lia | rewrite ?E2; wsimp; lia
        | exact HF | exact HO |].
      intros u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 m2 HF2 HO2.
      rewrite (rs_upd_fill H8 P (repeat (bz 3) (12 - k)) (24 - k) (8 + k)) in HO2
        by (unfold H8; cbn [length]; rewrite ?repeat_length; lia).
      rewrite EP, repeat_length in HO2. replace (24 - k - (12 - k))%nat with 12%nat in HO2 by lia.
      eapply mc0; [exact Eb | exact SOK | split; eassumption].
  Qed.

  Definition nsi : nat := Z.to_nat (ic row / 4).
  Definition nso : nat := Z.to_nat (oc row / 4).

  Lemma sfacts : synok row = true -> Z.of_nat nsi = ic row / 4 /\ Z.of_nat nso = oc row / 4 /\ (nsi + nso <= 12)%nat /\
    (ic row = 0 -> nsi = 0%nat) /\ (ic row <> 0 -> 1 <= ic row / 4) /\ (oc row = 0 -> nso = 0%nat) /\
    (oc row <> 0 -> 1 <= oc row / 4) /\ 0 <= ic row < 2^31 /\ 0 <= oc row < 2^31.
  Proof.
    intros S. unfold synok in S. rewrite !andb_true_iff in S. destruct S as ((((S1 & S2) & S3) & S4) & S5).
    apply Z.leb_le in S1, S2, S5. apply Z.eqb_eq in S3, S4.
    pose proof (rs_ic_range row). pose proof (rs_oc_range row). unfold nsi, nso.
    assert (0 <= ic row / 4) by (apply Z.div_pos; lia). assert (0 <= oc row / 4) by (apply Z.div_pos; lia).
    repeat split; try lia.
    all: intros E; first [rewrite E; reflexivity | Z.div_mod_to_equations; lia].
  Qed.

  Lemma l2b : forall (s2w : word) ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' t3' t4' t5' t6' m' j,
    b = 0 -> synok row = true -> lay row <> 1 -> bv_unsigned s2w = Z.of_nat nsi ->
    INV m' (H8 ++ repeat (bz 2) nsi ++ zeros (24 - nsi)) j ->
    evt rsegs Q (at_ 0x152e8 (R0 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2w s3' (Z_to_bv 64 (oc row / 4)) s5'
                                 (Z_to_bv 64 (oc row)) t3' t4' t5' t6') m').
  Proof.
    intros s2w ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' t3' t4' t5' t6' m' j Eb SOK L E2 PI.
    destruct (sfacts SOK) as (FI & FO & F12 & ZI & NI & ZO & NO & RI & RO).
    pose proof (rs_slots_2 row L) as SL. fold nsi nso in SL.
    unfold at_, R0. step. rewrite rc_eqb_lit by lia.
    destruct (Z.eqb_spec (oc row) 0) as [O0|O0]; cbv iota.
    - eapply (tail0 nsi (repeat (bz 2) nsi ++ repeat (bz 1) nso)); [exact Eb | exact SOK | lia
        | rewrite length_app, !repeat_length, (ZO O0); lia | rewrite SL, <- app_assoc, (ZO O0), Nat.sub_0_r; reflexivity
        | exact E2 | ].
      rewrite (ZO O0). cbn [repeat]. rewrite app_nil_r. exact PI.
    - step. step. step. step. step. step. step.
      rewrite (rs_seqz (oc row / 4)) by lia.
      step.
      destruct PI as [HF HO].
      eapply (call_ms 0x1530c (8 + nsi) nso 1 (H8 ++ repeat (bz 2) nsi ++ zeros (24 - nsi)));
        [apply ret_pc_even; [lia | reflexivity] | lia | lia | lia | rewrite ?E2; wsimp; lia | wsimp; lia | wsimp; lia
        | exact HF | exact HO |].
      intros u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 m2 HF2 HO2.
      rewrite (rs_upd_fill H8 (repeat (bz 2) nsi) (repeat (bz 1) nso) (24 - nsi) (8 + nsi)) in HO2
        by (unfold H8; cbn [length]; rewrite ?repeat_length; lia).
      rewrite repeat_length in HO2. replace (24 - nsi - nso)%nat with (24 - (nsi + nso))%nat in HO2 by lia.
      unfold at_, R0. step.
      eapply (tail0 (nsi + nso) (repeat (bz 2) nsi ++ repeat (bz 1) nso)); [exact Eb | exact SOK | lia
        | rewrite length_app, !repeat_length; lia | rewrite SL, <- app_assoc, Nat.sub_add_distr; reflexivity
        | rewrite ?E2; wsimp; lia | split; eassumption].
  Qed.

  Lemma l2a : forall ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' t3' t4' t5' t6' m' j,
    b = 0 -> synok row = true -> lay row <> 1 -> INV m' (H8 ++ [] ++ zeros 24) j ->
    evt rsegs Q (at_ 0x152a0 (R0 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' (Z_to_bv 64 (ic row / 4))
                     (Z_to_bv 64 (oc row / 4)) (Z_to_bv 64 (ic row)) (Z_to_bv 64 (oc row)) t3' t4' t5' t6') m').
  Proof.
    intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' t3' t4' t5' t6' m' j Eb SOK L PI.
    destruct (sfacts SOK) as (FI & FO & F12 & ZI & NI & ZO & NO & RI & RO).
    unfold at_, R0. step. rewrite rc_eqb_lit by lia.
    destruct (Z.eqb_spec (ic row) 0) as [I0|I0]; cbv iota.
    - step.
      eapply l2b; [exact Eb | exact SOK | exact L | rewrite (ZI I0); reflexivity |].
      rewrite (ZI I0). exact PI.
    - step. step. step. step. step.
      rewrite (rs_seqz (ic row / 4)) by lia.
      step.
      destruct PI as [HF HO].
      eapply (call_ms 0x152bc 8 nsi 2 (H8 ++ [] ++ zeros 24));
        [apply ret_pc_even; [lia | reflexivity] | lia | lia | lia | wsimp; lia | wsimp; lia | wsimp; lia
        | exact HF | exact HO |].
      intros u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 m2 HF2 HO2.
      rewrite (rs_upd_fill H8 [] (repeat (bz 2) nsi) 24 8) in HO2 by (unfold H8; cbn [length]; rewrite ?repeat_length; lia).
      rewrite repeat_length in HO2. cbn [app] in HO2.
      unfold at_, R0. step.
      eapply l2b; [exact Eb | exact SOK | exact L | wsimp; lia | split; eassumption].
  Qed.

  Lemma l1b : forall (s2w : word) ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' t3' t4' t5' t6' m' j,
    b = 0 -> synok row = true -> lay row = 1 -> bv_unsigned s2w = Z.of_nat nso ->
    INV m' (H8 ++ repeat (bz 1) nso ++ zeros (24 - nso)) j ->
    evt rsegs Q (at_ 0x152c4 (R0 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2w (Z_to_bv 64 (ic row / 4)) s4'
                                 (Z_to_bv 64 (ic row)) s6' t3' t4' t5' t6') m').
  Proof.
    intros s2w ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' t3' t4' t5' t6' m' j Eb SOK L E2 PI.
    destruct (sfacts SOK) as (FI & FO & F12 & ZI & NI & ZO & NO & RI & RO).
    pose proof (rs_slots_1 row L) as SL. fold nsi nso in SL.
    unfold at_, R0. step. rewrite rc_eqb_lit by lia.
    destruct (Z.eqb_spec (ic row) 0) as [I0|I0]; cbv iota.
    - eapply (tail0 nso (repeat (bz 1) nso)); [exact Eb | exact SOK | lia | apply repeat_length
        | rewrite SL, (ZI I0); reflexivity | exact E2 | exact PI].
    - step. step. step. step. step. step. step. step.
      rewrite (rs_seqz (ic row / 4)) by lia.
      step.
      destruct PI as [HF HO].
      eapply (call_ms 0x1530c (8 + nso) nsi 0 (H8 ++ repeat (bz 1) nso ++ zeros (24 - nso)));
        [apply ret_pc_even; [lia | reflexivity] | lia | lia | lia | rewrite ?E2; wsimp; lia | wsimp; lia | wsimp; lia
        | exact HF | exact HO |].
      intros u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 m2 HF2 HO2.
      rewrite (rs_upd_fill H8 (repeat (bz 1) nso) (repeat (bz 0) nsi) (24 - nso) (8 + nso)) in HO2
        by (unfold H8; cbn [length]; rewrite ?repeat_length; lia).
      rewrite repeat_length in HO2. replace (24 - nso - nsi)%nat with (24 - (nso + nsi))%nat in HO2 by lia.
      unfold at_, R0. step.
      eapply (tail0 (nso + nsi) (repeat (bz 1) nso ++ repeat (bz 0) nsi)); [exact Eb | exact SOK | lia
        | rewrite length_app, !repeat_length; lia
        | rewrite SL, <- app_assoc; do 2 f_equal; f_equal; lia
        | rewrite ?E2; wsimp; lia | split; eassumption].
  Qed.

  Lemma l1a : forall ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' t3' t4' t5' t6' m' j,
    b = 0 -> synok row = true -> lay row = 1 -> INV m' (H8 ++ [] ++ zeros 24) j ->
    evt rsegs Q (at_ 0x14f2c (R0 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' (Z_to_bv 64 (ic row / 4))
                     (Z_to_bv 64 (oc row / 4)) (Z_to_bv 64 (ic row)) (Z_to_bv 64 (oc row)) t3' t4' t5' t6') m').
  Proof.
    intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' t3' t4' t5' t6' m' j Eb SOK L PI.
    destruct (sfacts SOK) as (FI & FO & F12 & ZI & NI & ZO & NO & RI & RO).
    unfold at_, R0. step. rewrite rc_eqb_lit by lia.
    destruct (Z.eqb_spec (oc row) 0) as [O0|O0]; cbv iota.
    - step.
      eapply l1b; [exact Eb | exact SOK | exact L | rewrite (ZO O0); reflexivity |].
      rewrite (ZO O0). exact PI.
    - step. step. step. step. step.
      rewrite (rs_seqz (oc row / 4)) by lia.
      step.
      destruct PI as [HF HO].
      eapply (call_ms 0x14f48 8 nso 1 (H8 ++ [] ++ zeros 24));
        [apply ret_pc_even; [lia | reflexivity] | lia | lia | lia | wsimp; lia | wsimp; lia | wsimp; lia
        | exact HF | exact HO |].
      intros u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 m2 HF2 HO2.
      rewrite (rs_upd_fill H8 [] (repeat (bz 1) nso) 24 8) in HO2 by (unfold H8; cbn [length]; rewrite ?repeat_length; lia).
      rewrite repeat_length in HO2. cbn [app] in HO2.
      unfold at_, R0. step.
      eapply l1b; [exact Eb | exact SOK | exact L | wsimp; lia | split; eassumption].
  Qed.

  Lemma cs0 : forall ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' t3' t4' t5' t6' m' j,
    b = 0 -> FS m' j -> rw_cells rsegs m' o [CB 32 (zeros 32)] ->
    evt rsegs Q (at_ 0x14ec0 (R0 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (-1)) s3' s4' s5' s6'
                                 t3' t4' t5' t6') m').
  Proof.
    intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' t3' t4' t5' t6' m' j Eb HF HO.
    pose proof (proj1 (proj2 (proj2 HF))) as HRB.
    pose proof (rs_rd4 rsegs m' p row 16 HRB ltac:(lia)) as R16.
    pose proof (rs_rd4 rsegs m' p row 20 HRB ltac:(lia)) as R20.
    change (Z.of_nat 16) with 16 in R16. change (Z.of_nat 20) with 20 in R20.
    pose proof (rs_ic_range row) as RI. pose proof (rs_oc_range row) as RO.
    assert (SF : forall P : Prop, (synok row = false -> P) -> (synok row = true -> P) -> P)
      by (intros P H1 H2; destruct (synok row); auto).
    unfold at_, R0.
    assert (SYF : forall X, synok row = false -> X = synth row b nb -> X = zeros 32).
    { intros X S E. rewrite E, Eb. change (synth row 0 nb) with (if synok row then gram row else zeros 32).
      rewrite S. reflexivity. }
    assert (RCF : synok row = false -> -1 = rc row b).
    { intros S. rewrite Eb. change (rc row 0) with (if synok row then 1 else -1). rewrite S. reflexivity. }
    step. rewrite rs_sx32_ic. step.
    rewrite rs_lts0 by lia.
    destruct (Z.ltb_spec (ic row) 0) as [I0|I0]; cbv iota.
    { assert (S : synok row = false).
      { unfold synok. replace (0 <=? ic row) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
      eapply exz; [exact HF | exact HO | exact (SYF _ S eq_refl) | exact (RCF S)]. }
    step. rewrite rs_sx32_oc. step.
    rewrite rs_lts0 by lia.
    destruct (Z.ltb_spec (oc row) 0) as [O0|O0]; cbv iota.
    { assert (S : synok row = false).
      { unfold synok. replace (0 <=? oc row) with false by (symmetry; apply Z.leb_gt; lia).
        rewrite !andb_false_r. reflexivity. }
      eapply exz; [exact HF | exact HO | exact (SYF _ S eq_refl) | exact (RCF S)]. }
    step. step. step.
    rewrite (rs_or3 (ic row) (oc row)) by lia.
    destruct (Z.eqb_spec (ic row mod 4) 0) as [IM|IM]; [destruct (Z.eqb_spec (oc row mod 4) 0) as [OM|OM]|];
      cbn [andb negb]; cbv iota.
    2,3: assert (S : synok row = false) by
           (unfold synok; rewrite ?(proj2 (Z.eqb_neq _ _) IM), ?(proj2 (Z.eqb_neq _ _) OM), ?andb_false_r; reflexivity);
         eapply exz; [exact HF | exact HO | exact (SYF _ S eq_refl) | exact (RCF S)].
    step. rewrite rs_srliw2 by lia. step. rewrite rs_srliw2 by lia. step. step.
    assert (RSI : 0 <= ic row / 4 <= 2^29) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    assert (RSO : 0 <= oc row / 4 <= 2^29) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    step. rewrite rc_ltu_lit by lia.
    destruct (Z.ltb_spec 12 (oc row / 4 + ic row / 4)) as [G|G]; cbv iota.
    { assert (S : synok row = false).
      { unfold synok. replace (ic row / 4 + oc row / 4 <=? 12) with false by (symmetry; apply Z.leb_gt; lia).
        rewrite andb_false_r. reflexivity. }
      eapply exz; [exact HF | exact HO | exact (SYF _ S eq_refl) | exact (RCF S)]. }
    assert (SOK : synok row = true)
      by (unfold synok; repeat (apply andb_true_iff; split); first [apply Z.leb_le | apply Z.eqb_eq]; lia).
    assert (PI : INV m' (zeros 32) j) by (split; assumption).
    clear HF HO HRB R16 R20 SYF RCF SF.
    step. step. step.
    ost 0 1%nat. ost 1 1%nat. ost 2 1%nat. ost 3 1%nat.
    rrow 252%nat. step. ost 4 1%nat. ost 5 1%nat. ost 6 1%nat.
    rrow 253%nat. step. ost 7 1%nat.
    rrow 290%nat. step. step.
    match goal with PI : INV ?mc ?X ?J |- _ =>
      replace X with (H8 ++ [] ++ zeros 24) in PI by reflexivity end.
    rewrite rs_zxb_eqb by lia. change (bv_unsigned (nth 290 row (Z_to_bv 8 0))) with (lay row).
    destruct (Z.eqb_spec (lay row) 1) as [L1|L1]; cbn [negb]; cbv iota.
    - eapply l1a; eassumption.
    - eapply l2a; eassumption.
  Qed.

  Lemma FS_jlen : forall m' j, FS m' j -> length j = 48%nat.
  Proof. intros m' j ([[[L _] _] _] & _). exact L. Qed.

  Lemma inv_hnb : forall m' X J, INV m' X J -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    bytes_at rsegs m' (rname row) nb.
  Proof. intros m' X J ((_ & _ & _ & HNB & _) & _) B5 H1 H2. exact (HNB B5 H1 H2). Qed.

  Lemma inv_frame : forall m' X J (k n : nat), INV m' X J -> (k + n <= 48)%nat ->
    bytes_at rsegs m' (bv_unsigned sp + -112 + Z.of_nat k) (firstn n (skipn k J)).
  Proof. intros m' X J k n ((FR & _) & _) H. exact (rs_cell0_sub _ _ _ _ _ _ k n FR H). Qed.

  Lemma nloop5 : forall k i (x0 x1 x2 : word) J0 J2 X ra' t0' t1' t2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' m',
    (i + k = 16)%nat -> (0 < k)%nat -> b = 5 -> has row <> 0 -> rname row <> 0 ->
    (forall j, (j < i)%nat -> bv_unsigned (nth j nb (Z_to_bv 8 0)) <> 0) ->
    length J0 = 8%nat ->
    x0 = Z_to_bv 64 (rname row + Z.of_nat i) -> x1 = Z_to_bv 64 (Z.of_nat k) ->
    x2 = Z_to_bv 64 (bv_unsigned sp + -112 + 8 + Z.of_nat i) ->
    INV m' X (J0 ++ (firstn i nb ++ repeat (bz 0) (16 - i)) ++ J2) ->
    (forall (y0 y1 y2 y3 : word) m'', INV m'' X (J0 ++ nmf nb ++ J2) ->
       evt rsegs Q (at_ 0x15010 (R0 ra' t0' t1' t2' y0 y1 y2 y3 a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6') m'')) ->
    evt rsegs Q (at_ 0x14ff4 (R0 ra' t0' t1' t2' x0 x1 x2 a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6') m').
  Proof.
    induction k as [|k IH];
      intros i x0 x1 x2 J0 J2 X ra' t0' t1' t2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' m'
        Hik Hk Eb H1 H2 Hnz LJ0 E0 E1 E2 PI K; [lia|].
    subst x0 x1 x2.
    assert (B56 : b = 5 \/ b = 6) by (left; exact Eb).
    destruct (HNO B56 H1 H2) as (OK & DS & DO).
    pose proof (name_ok_lt nb i OK ltac:(lia) Hnz) as Hi.
    pose proof (bytes_at_bound _ _ _ _ (inv_hnb m' X _ PI B56 H1 H2)) as BN.
    pose proof (rd_byte rsegs m' (rname row) nb i (inv_hnb m' X _ PI B56 H1 H2) Hi) as RD.
    pose proof (rs_rw64_range row 280) as RN. change (rw64 row 280) with (rname row) in RN.
    unfold at_, R0.
    step. step. rewrite rc_zxb_eqb0.
    destruct (Z.eqb_spec (bv_unsigned (nth i nb (Z_to_bv 8 0))) 0) as [C0|CNZ]; cbv iota.
    - apply K. rewrite (nmf_stop nb i Hi ltac:(lia) Hnz C0). exact PI.
    - fst (8 + Z.of_nat i) 1%nat.
      rewrite Z2Nat.inj_add, Nat2Z.id in PI by lia. change (Z.to_nat 8) with 8%nat in PI.
      rewrite (mb_upd_mid J0 _ J2 _ 8 i LJ0) in PI by (rewrite length_app, length_firstn, repeat_length; cbn [length]; lia).
      rewrite upd_prefix in PI by lia.
      step. step. step. step.
      rewrite rc_eqb_lit by lia.
      destruct k as [|k].
      + replace (Z.of_nat (S 0) + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
        cbn [negb]. cbv iota.
        assert (L16 : length nb = 16%nat) by (destruct OK as (OKl & _ & _); lia).
        replace (S i) with 16%nat in PI by lia.
        rewrite <- (nmf_full nb L16) in PI.
        2:{ intros j' Hj'. destruct (Nat.eq_dec j' i) as [->|Ne]; [exact CNZ | apply Hnz; lia]. }
        apply K. exact PI.
      + replace (Z.of_nat (S (S k)) + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        cbn [negb]. cbv iota.
        eapply (IH (S i)); [lia | lia | exact Eb | exact H1 | exact H2 | | exact LJ0 | f_equal; lia | f_equal; lia
                            | f_equal; lia | exact PI | exact K].
        intros j' Hj'. destruct (Nat.eq_dec j' i) as [->|Ne]; [exact CNZ | apply Hnz; lia].
  Qed.

  Definition H21 : list byte := map bz [4; 1; 0; 27; 0; 2; 0; 254; 22; 240; 65; 10; 0; 0; 18; 18; 5; 0; 16; 0; 1].

  Lemma after5 : forall J0 J2 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' m',
    b = 5 -> has row <> 0 -> length J0 = 8%nat -> INV m' (zeros 32) (J0 ++ nmr row nb ++ J2) ->
    evt rsegs Q (at_ 0x15010 (R0 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6'
                                 t3' t4' t5' t6') m').
  Proof.
    intros J0 J2 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' m' Eb H0 LJ0 PI.
    pose proof (rs_nmr_len row nb) as LN.
    unfold at_, R0.
    do 8 step.
    ost 0 1%nat. ost 1 1%nat. ost 2 1%nat. ost 3 1%nat. step.
    ost 4 1%nat. ost 5 1%nat. ost 6 1%nat. ost 7 1%nat. step.
    ost 8 1%nat. ost 9 1%nat. ost 10 1%nat. ost 11 1%nat. step.
    ost 12 1%nat. ost 13 1%nat. ost 14 1%nat. ost 15 1%nat. step.
    ost 16 1%nat. ost 17 1%nat. ost 18 1%nat. ost 19 1%nat. ost 20 1%nat.
    rewrite !rc_le1_lit in PI.
    replace (Z_to_bv 8 (-2)) with (bz 254) in PI by (apply Z_to_bv8_mod; reflexivity).
    replace (Z_to_bv 8 (-16)) with (bz 240) in PI by (apply Z_to_bv8_mod; reflexivity).
    match goal with PI : INV ?mc ?X ?J |- _ =>
      replace X with (H21 ++ [] ++ zeros 11) in PI by reflexivity end.
    pose proof (inv_frame _ _ _ 8 10 PI ltac:(lia)) as HS.
    pose proof (mb_win J0 (nmr row nb) J2 8 0 10 LJ0 ltac:(lia)) as W. cbn [Nat.add skipn] in W. rewrite W in HS.
    change (Z.of_nat 8) with 8 in HS. replace (bv_unsigned sp + -112 + 8) with (bv_unsigned sp + -104) in HS by lia.
    step. step. step. step.
    destruct PI as [HF HO].
    eapply (call_mc 0x150a4 21 10 (bv_unsigned sp + -104) (firstn 10 (nmr row nb)) (H21 ++ [] ++ zeros 11));
      [apply ret_pc_even; [lia | reflexivity] | lia | lia | rewrite length_firstn; lia
      | wsimp; lia | wsimp; lia | wsimp; lia | lia | exact HF | exact HO | exact HS |].
    intros u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 m2 HF2 HO2.
    rewrite (rs_upd_fill H21 [] (firstn 10 (nmr row nb)) 11 21) in HO2
      by (try (unfold H21; reflexivity); rewrite length_firstn; lia).
    rewrite length_firstn in HO2. replace (11 - Nat.min 10 (length (nmr row nb)))%nat with 1%nat in HO2 by lia.
    cbn [app] in HO2.
    unfold at_, R0. step. step. step.
    eapply (oloop5 31 0); [lia | lia | f_equal; lia | split; eassumption | |].
    - rewrite Eb. change (synth row 5 nb) with (if has row =? 0 then zeros 32 else idf (nmr row nb)).
      replace (has row =? 0) with false by (symmetry; apply Z.eqb_neq; exact H0).
      unfold idf. f_equal.
      rewrite app_assoc, firstn_app, length_app, length_firstn. replace (31 - (length H21 + Nat.min 10 (length (nmr row nb))))%nat with 0%nat
        by (unfold H21; cbn [length map]; lia).
      rewrite firstn_O, app_nil_r, firstn_all2 by (rewrite length_app, length_firstn; unfold H21; cbn [length map]; lia).
      reflexivity.
    - rewrite Eb. change (rc row 5) with (if has row =? 0 then 0 else 1).
      replace (has row =? 0) with false by (symmetry; apply Z.eqb_neq; exact H0). reflexivity.
  Qed.

  Lemma cs5 : forall ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' t3' t4' t5' t6' m' j,
    b = 5 -> FS m' j -> rw_cells rsegs m' o [CB 32 (zeros 32)] ->
    evt rsegs Q (at_ 0x14fd4 (R0 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (-1)) s3' s4' s5' s6'
                                 t3' t4' t5' t6') m').
  Proof.
    intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' t3' t4' t5' t6' m' j Eb HF HO.
    pose proof (proj1 (proj2 (proj2 HF))) as HRB.
    pose proof (FS_jlen m' j HF) as LJ.
    pose proof (rs_rd4 rsegs m' p row 56 HRB ltac:(lia)) as R56. change (Z.of_nat 56) with 56 in R56.
    pose proof (rs_rd8 rsegs m' p row 280 HRB ltac:(lia)) as R280. change (Z.of_nat 280) with 280 in R280.
    pose proof (rs_rw32_range row 56) as RH. pose proof (rs_rw64_range row 280) as RN.
    change (rw64 row 280) with (rname row) in R280, RN.
    unfold at_, R0. step. step. rewrite mb_sx32_eq0 by lia. change (rw32 row 56) with (has row).
    destruct (Z.eqb_spec (has row) 0) as [H0|H0]; cbv iota.
    - step. step. eapply exz; [exact HF | exact HO | |].
      + rewrite Eb. change (synth row 5 nb) with (if has row =? 0 then zeros 32 else idf (nmr row nb)).
        rewrite (proj2 (Z.eqb_eq _ _) H0). reflexivity.
      + rewrite Eb. change (rc row 5) with (if has row =? 0 then 0 else 1).
        rewrite (proj2 (Z.eqb_eq _ _) H0). reflexivity.
    - step.
      assert (PI : INV m' (zeros 32) j) by (split; assumption). clear HF HO HRB R56 R280.
      fst 8 8%nat. fst 16 8%nat.
      rewrite (mb_zz8 j LJ) in PI.
      step. rewrite rc_eqb_lit by lia.
      destruct (Z.eqb_spec (rname row) 0) as [N0|N0]; cbv iota.
      + eapply (after5 (firstn 8 j) (skipn 24 j)); [exact Eb | exact H0 | rewrite length_firstn; lia |].
        unfold nmr. rewrite (proj2 (Z.eqb_eq _ _) N0). exact PI.
      + step. step.
        eapply (nloop5 16 0 _ _ _ (firstn 8 j) (skipn 24 j)); [lia | lia | exact Eb | exact H0 | exact N0 | intros; lia | rewrite length_firstn; lia
                              | f_equal; lia | reflexivity | f_equal; lia | exact PI |].
        intros y0 y1 y2 y3 m'' PI2.
        eapply (after5 (firstn 8 j) (skipn 24 j)); [exact Eb | exact H0 | rewrite length_firstn; lia |].
        unfold nmr. rewrite (proj2 (Z.eqb_neq _ _) N0). exact PI2.
  Qed.

  Lemma call_mcf : forall (ret : Z) (d s n : nat) X (a0 a1 a2 : word) t0 t1 t2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6'
      t3 t4 t5 t6 m' J,
    ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret -> (d + n <= s \/ s + n <= d)%nat -> (d + n <= 48)%nat ->
    (s + n <= 48)%nat -> (1 <= n)%nat ->
    bv_unsigned a0 = bv_unsigned sp + -112 + Z.of_nat d -> bv_unsigned a1 = bv_unsigned sp + -112 + Z.of_nat s ->
    bv_unsigned a2 = Z.of_nat n -> INV m' X J ->
    (forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m'',
       INV m'' X (upd_bytes J d (firstn n (skipn s J))) ->
       evt rsegs Q (at_ ret (R0 (Z_to_bv 64 ret) t0' t1' t2' a0 a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6'
                                t3' t4' t5' t6') m'')) ->
    evt rsegs Q (MS (R0 (Z_to_bv 64 ret) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' t3 t4 t5 t6)
                    F (Z_to_bv 64 0x1d3d8) fc None m' (seg_rom rsegs)).
  Proof.
    intros ret d s n X a0 a1 a2 t0 t1 t2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' t3 t4 t5 t6 m' J Hret Dds Hd Hs Hn
      E0 E1 E2 ((FR & ST & HRB & HNB & MU & WM & MI) & HO) K.
    destruct (mb_rw_split1 _ _ _ _ _ FR) as [FH FT]. cbn [csize] in FT.
    pose proof (rs_rw_sub rsegs m' _ 48 J d n FH Hd) as HD.
    pose proof (rs_cell0_sub rsegs m' _ 48 J [] s n FH Hs) as HSrc.
    unfold R0.
    eapply evt_cut.
    { eapply HMC; [ | | | | exact MI].
      - rewrite E1. exact HSrc.
      - rewrite E2, Nat2Z.id, length_firstn, length_skipn. pose proof (FS_jlen m' J (conj FR (conj ST (conj HRB (conj HNB (conj MU (conj WM MI))))))). lia.
      - rewrite E0, E2, Nat2Z.id. exact HD.
      - rewrite E0, E1, E2. lia. }
    intros ms' PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & E & MU2 & WM2 & MI2 & RW2 & SB2).
    subst ms'. rewrite E0, E2, Nat2Z.id in RW2. rewrite E0, E2 in MU2. clear SB2.
    pose proof (rs_rw_upd rsegs m' m2 _ 48 J d n _ FH Hd MU2 WM2 RW2) as FH2.
    pose proof (rw_cells_transport rsegs _ m' m2 _ _ FT MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia))
      as FT2.
    pose proof (mb_rw_join1 _ _ _ _ _ FH2 FT2) as FR2.
    assert (MU3 : munch [(bv_unsigned sp - 160, bv_unsigned sp); (o, o + 32)] m' m2).
    { eapply munch_weaken; [|exact MU2]. unfold sub_fp. cbn [outside]. intros. repeat split; try exact I; lia. }
    pose proof (hnb_tr m' m2 MU3 HNB) as HNB2.
    pose proof (stk_transport_disjoint rsegs _ m' m2 _ _ ST MU2 WM2 ltac:(cbn [disjoint_from]; lia)) as ST2.
    pose proof (bytes_at_transport rsegs _ m' m2 _ _ HRB MU2 ltac:(cbn [disjoint_from]; rewrite Hlen; lia)) as HRB2.
    pose proof (rw_cells_transport rsegs _ m' m2 _ _ HO MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia))
      as HO2.
    rewrite Hret. apply K.
    split; [|exact HO2].
    split; [exact FR2|]. split; [exact ST2|]. split; [exact HRB2|]. split; [exact HNB2|].
    split; [exact (munch_trans _ _ _ _ MU MU3)|]. split; [exact (wmono_trans _ _ _ _ WM WM2) | exact MI2].
  Qed.

  Lemma nloop6 : forall k i (x0 x1 x2 : word) J0 J2 X ra' t0' t1' t2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' m',
    (i + k = 16)%nat -> (0 < k)%nat -> b = 6 -> has row <> 0 -> rname row <> 0 ->
    (forall j, (j < i)%nat -> bv_unsigned (nth j nb (Z_to_bv 8 0)) <> 0) ->
    length J0 = 32%nat ->
    x0 = Z_to_bv 64 (rname row + Z.of_nat i) -> x1 = Z_to_bv 64 (Z.of_nat k) ->
    x2 = Z_to_bv 64 (bv_unsigned sp + -112 + 32 + Z.of_nat i) ->
    INV m' X (J0 ++ (firstn i nb ++ repeat (bz 0) (16 - i)) ++ J2) ->
    (forall (y0 y1 y2 y3 : word) m'', INV m'' X (J0 ++ nmf nb ++ J2) ->
       evt rsegs Q (at_ 0x15100 (R0 ra' t0' t1' t2' y0 y1 y2 y3 a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6') m'')) ->
    evt rsegs Q (at_ 0x150e4 (R0 ra' t0' t1' t2' x0 x1 x2 a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6') m').
  Proof.
    induction k as [|k IH];
      intros i x0 x1 x2 J0 J2 X ra' t0' t1' t2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' m'
        Hik Hk Eb H1 H2 Hnz LJ0 E0 E1 E2 PI K; [lia|].
    subst x0 x1 x2.
    assert (B56 : b = 5 \/ b = 6) by (right; exact Eb).
    destruct (HNO B56 H1 H2) as (OK & DS & DO).
    pose proof (name_ok_lt nb i OK ltac:(lia) Hnz) as Hi.
    pose proof (bytes_at_bound _ _ _ _ (inv_hnb m' X _ PI B56 H1 H2)) as BN.
    pose proof (rd_byte rsegs m' (rname row) nb i (inv_hnb m' X _ PI B56 H1 H2) Hi) as RD.
    pose proof (rs_rw64_range row 280) as RN. change (rw64 row 280) with (rname row) in RN.
    unfold at_, R0.
    step. step. rewrite rc_zxb_eqb0.
    destruct (Z.eqb_spec (bv_unsigned (nth i nb (Z_to_bv 8 0))) 0) as [C0|CNZ]; cbv iota.
    - apply K. rewrite (nmf_stop nb i Hi ltac:(lia) Hnz C0). exact PI.
    - fst (32 + Z.of_nat i) 1%nat.
      rewrite Z2Nat.inj_add, Nat2Z.id in PI by lia. change (Z.to_nat 32) with 32%nat in PI.
      rewrite (mb_upd_mid J0 _ J2 _ 32 i LJ0) in PI by (rewrite length_app, length_firstn, repeat_length; cbn [length]; lia).
      rewrite upd_prefix in PI by lia.
      step. step. step. step.
      rewrite rc_eqb_lit by lia.
      destruct k as [|k].
      + replace (Z.of_nat (S 0) + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
        cbn [negb]. cbv iota.
        assert (L16 : length nb = 16%nat) by (destruct OK as (OKl & _ & _); lia).
        replace (S i) with 16%nat in PI by lia.
        rewrite <- (nmf_full nb L16) in PI.
        2:{ intros j' Hj'. destruct (Nat.eq_dec j' i) as [->|Ne]; [exact CNZ | apply Hnz; lia]. }
        apply K. exact PI.
      + replace (Z.of_nat (S (S k)) + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        cbn [negb]. cbv iota.
        eapply (IH (S i)); [lia | lia | exact Eb | exact H1 | exact H2 | | exact LJ0 | f_equal; lia | f_equal; lia
                            | f_equal; lia | exact PI | exact K].
        intros j' Hj'. destruct (Nat.eq_dec j' i) as [->|Ne]; [exact CNZ | apply Hnz; lia].
  Qed.

  Lemma sloop : forall k i R (x0 a2w : word) ra' t0' t1' t2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' m',
    (i + k = 21)%nat -> (0 < k)%nat -> length R = 21%nat -> bytes_at rsegs m' (bv_unsigned sp + -104) R ->
    bv_unsigned a2w = bv_unsigned sp + -83 -> x0 = Z_to_bv 64 (bv_unsigned sp + -104 + Z.of_nat i) ->
    (forall y0 y3, evt rsegs Q (at_ 0x15194 (R0 ra' t0' t1' t2' y0 (Z_to_bv 64 (psum R 21)) a2w y3 a4' a5' a6' a7'
                                                 s2' s3' s4' s5' s6' t3' t4' t5' t6') m')) ->
    evt rsegs Q (at_ 0x15184 (R0 ra' t0' t1' t2' x0 (Z_to_bv 64 (psum R i)) a2w a3' a4' a5' a6' a7'
                                 s2' s3' s4' s5' s6' t3' t4' t5' t6') m').
  Proof.
    induction k as [|k IH];
      intros i R x0 a2w ra' t0' t1' t2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' m' Hik Hk LR HR E2 E0 K;
      [lia|].
    subst x0.
    pose proof (bytes_at_bound _ _ _ _ HR) as BR. rewrite LR in BR.
    pose proof (rd_byte rsegs m' _ R i HR ltac:(lia)) as RD.
    pose proof (psum_range R i) as PR.
    unfold at_, R0.
    step. step. step.
    rewrite psum_S_zxb.
    step.
    rewrite (rc_eqb_w2 (Z_to_bv 64 (bv_unsigned sp + -104 + Z.of_nat i + 1)) a2w
               (bv_unsigned sp + -104 + Z.of_nat i + 1) (bv_unsigned sp + -83)) by (try rewrite unsigned_lit; lia).
    destruct k as [|k].
    - replace (bv_unsigned sp + -104 + Z.of_nat i + 1 =? bv_unsigned sp + -83) with true
        by (symmetry; apply Z.eqb_eq; lia).
      cbn [negb]. cbv iota. replace (S i) with 21%nat by lia. apply K.
    - replace (bv_unsigned sp + -104 + Z.of_nat i + 1 =? bv_unsigned sp + -83) with false
        by (symmetry; apply Z.eqb_neq; lia).
      cbn [negb]. cbv iota.
      eapply (IH (S i)); first [lia | eassumption | f_equal; lia].
  Qed.

  Definition H9 : list byte := map bz [4; 2; 0; 13; 0; 2; 0; 254; 8].

  Lemma after6 : forall J0 J2 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' m',
    b = 6 -> has row <> 0 -> length J0 = 32%nat -> INV m' (zeros 32) (J0 ++ nmr row nb ++ J2) ->
    evt rsegs Q (at_ 0x15100 (R0 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6'
                                 t3' t4' t5' t6') m').
  Proof.
    intros J0 J2 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' m' Eb H0 LJ0 PI.
    pose proof (rs_nmr_len row nb) as LN0.
    pose proof (FS_jlen _ _ (proj1 PI)) as LJ. rewrite !length_app, LJ0 in LJ.
    assert (LN : length (nmr row nb) = 16%nat) by lia.
    assert (EJ2 : J2 = []) by (destruct J2; [reflexivity | cbn [length] in LJ; lia]).
    unfold at_, R0.
    step. step. step.
    fst 8 1%nat. fst 9 1%nat. fst 10 1%nat. fst 11 1%nat. fst 12 1%nat.
    change (Z.to_nat 8) with 8%nat in PI. change (Z.to_nat 9) with 9%nat in PI. change (Z.to_nat 10) with 10%nat in PI.
    change (Z.to_nat 11) with 11%nat in PI. change (Z.to_nat 12) with 12%nat in PI.
    step. step. step. step.
    eapply (call_mcf 0x15130 13 32 16); [apply ret_pc_even; [lia | reflexivity] | lia | lia | lia | lia
      | wsimp; lia | wsimp; lia | wsimp; lia | exact PI |].
    intros u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 m2 PI2. clear PI. rename PI2 into PI.
    destruct (mb_j6 J0 (nmr row nb) J2 (le1 (Z_to_bv 64 5)) (le1 (Z_to_bv 64 0)) (le1 (Z_to_bv 64 16))
                (le1 (Z_to_bv 64 0)) (le1 (Z_to_bv 64 1)) LJ0 LN EJ2 eq_refl eq_refl eq_refl eq_refl eq_refl)
      as (MJ1 & MJ2 & MJ3).
    rewrite MJ1 in PI. clear MJ1. rewrite !rc_le1_lit in PI, MJ2, MJ3.
    unfold at_, R0. step. step. step. step.
    ost 0 1%nat. ost 1 1%nat. ost 2 1%nat. ost 3 1%nat. step.
    ost 4 1%nat. ost 5 1%nat. ost 6 1%nat. ost 7 1%nat. step.
    ost 8 1%nat.
    rewrite !rc_le1_lit in PI.
    replace (Z_to_bv 8 (-2)) with (bz 254) in PI by (apply Z_to_bv8_mod; reflexivity).
    match goal with PI : INV ?mc ?X ?J |- _ =>
      replace X with (H9 ++ [] ++ zeros 23) in PI by reflexivity end.
    pose proof (inv_frame _ _ _ 42 6 PI ltac:(lia)) as HY. rewrite MJ3 in HY.
    change (Z.of_nat 42) with 42 in HY. replace (bv_unsigned sp + -112 + 42) with (bv_unsigned sp + -70) in HY by lia.
    step. step. step.
    destruct PI as [HF HO].
    eapply (call_mc 0x15178 9 6 (bv_unsigned sp + -70) (firstn 6 (skipn 10 (nmr row nb))) (H9 ++ [] ++ zeros 23));
      [apply ret_pc_even; [lia | reflexivity] | lia | lia | rewrite length_firstn, length_skipn; lia
      | wsimp; lia | wsimp; lia | wsimp; lia | lia | exact HF | exact HO | exact HY |].
    intros u0' u1' u2' y1 y2 y3 y4 y5 y6 y7 u3' u4' u5' u6' m3 HF3 HO3.
    rewrite (rs_upd_fill H9 [] (firstn 6 (skipn 10 (nmr row nb))) 23 9) in HO3
      by (try (unfold H9; reflexivity); rewrite length_firstn, length_skipn; lia).
    rewrite length_firstn, length_skipn in HO3.
    replace (23 - Nat.min 6 (length (nmr row nb) - 10))%nat with 17%nat in HO3 by lia. cbn [app] in HO3.
    match type of HF3 with FS _ ?JJ =>
      assert (PI : INV m3 (H9 ++ firstn 6 (skipn 10 (nmr row nb)) ++ zeros 17) JJ) by (split; assumption) end.
    clear HF HO HF3 HO3 HY.
    pose proof (inv_frame _ _ _ 8 21 PI ltac:(lia)) as HR. rewrite MJ2 in HR. cbn [app] in HR.
    change (Z.of_nat 8) with 8 in HR. replace (bv_unsigned sp + -112 + 8) with (bv_unsigned sp + -104) in HR by lia.
    unfold at_, R0. step. step. step.
    match type of HR with bytes_at _ _ _ ?RR =>
      assert (PS : psum RR 21 = 22 + psum (nmr row nb) 16)
        by exact (mb_psum_app [Z_to_bv 8 5; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 1] (nmr row nb) 16);
      pose proof (psum_range RR 21) as PR;
      eapply (sloop 21 0 RR); [lia | lia | cbn [length]; rewrite LN; reflexivity | exact HR | wsimp; lia | f_equal; lia |]
    end.
    intros z0 z3.
    unfold at_, R0. step. step. step. step.
    ost 15 1%nat. rewrite mb_and127 in PI by lia.
    ost 16 1%nat. rewrite rc_le1_lit in PI.
    replace (Z_to_bv 8 (-9)) with (bz 247) in PI by (apply Z_to_bv8_mod; reflexivity).
    change (Z.to_nat 15) with 15%nat in PI. change (Z.to_nat 16) with 16%nat in PI.
    step. step.
    eapply (oloop6 31 0); [lia | lia | f_equal; lia | exact PI | |].
    - unfold H9. rewrite mb_fin6 by (rewrite length_firstn, length_skipn; lia).
      rewrite Eb. change (synth row 6 nb) with (if has row =? 0 then zeros 32 else idl (nmr row nb)).
      replace (has row =? 0) with false by (symmetry; apply Z.eqb_neq; exact H0).
      unfold idl, idl31, idlc. rewrite PS. reflexivity.
    - rewrite Eb. change (rc row 6) with (if has row =? 0 then 0 else 1).
      replace (has row =? 0) with false by (symmetry; apply Z.eqb_neq; exact H0). reflexivity.
  Qed.

  Lemma cs6 : forall ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' t3' t4' t5' t6' m' j,
    b = 6 -> FS m' j -> rw_cells rsegs m' o [CB 32 (zeros 32)] ->
    evt rsegs Q (at_ 0x150c4 (R0 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (-1)) s3' s4' s5' s6'
                                 t3' t4' t5' t6') m').
  Proof.
    intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' t3' t4' t5' t6' m' j Eb HF HO.
    pose proof (proj1 (proj2 (proj2 HF))) as HRB.
    pose proof (FS_jlen m' j HF) as LJ.
    pose proof (rs_rd4 rsegs m' p row 56 HRB ltac:(lia)) as R56. change (Z.of_nat 56) with 56 in R56.
    pose proof (rs_rd8 rsegs m' p row 280 HRB ltac:(lia)) as R280. change (Z.of_nat 280) with 280 in R280.
    pose proof (rs_rw32_range row 56) as RH. pose proof (rs_rw64_range row 280) as RN.
    change (rw64 row 280) with (rname row) in R280, RN.
    unfold at_, R0. step. step. rewrite mb_sx32_eq0 by lia. change (rw32 row 56) with (has row).
    destruct (Z.eqb_spec (has row) 0) as [H0|H0]; cbv iota.
    - step. step. eapply exz; [exact HF | exact HO | |].
      + rewrite Eb. change (synth row 6 nb) with (if has row =? 0 then zeros 32 else idl (nmr row nb)).
        rewrite (proj2 (Z.eqb_eq _ _) H0). reflexivity.
      + rewrite Eb. change (rc row 6) with (if has row =? 0 then 0 else 1).
        rewrite (proj2 (Z.eqb_eq _ _) H0). reflexivity.
    - step.
      assert (PI : INV m' (zeros 32) j) by (split; assumption). clear HF HO HRB R56 R280.
      fst 32 8%nat. fst 40 8%nat.
      rewrite (mb_zz32 j LJ) in PI.
      step. rewrite rc_eqb_lit by lia.
      destruct (Z.eqb_spec (rname row) 0) as [N0|N0]; cbv iota.
      + eapply (after6 (firstn 32 j) (skipn 48 j)); [exact Eb | exact H0 | rewrite length_firstn; lia |].
        unfold nmr. rewrite (proj2 (Z.eqb_eq _ _) N0). exact PI.
      + step. step.
        eapply (nloop6 16 0 _ _ _ (firstn 32 j) (skipn 48 j)); [lia | lia | exact Eb | exact H0 | exact N0 | intros; lia | rewrite length_firstn; lia
                              | f_equal; lia | reflexivity | f_equal; lia | exact PI |].
        intros y0 y1 y2 y3 m'' PI2.
        eapply (after6 (firstn 32 j) (skipn 48 j)); [exact Eb | exact H0 | rewrite length_firstn; lia |].
        unfold nmr. rewrite (proj2 (Z.eqb_neq _ _) N0). exact PI2.
  Qed.

  Lemma after_ms : forall t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4' s5' s6' t3 t4 t5 t6 m' j,
    FS m' j -> rw_cells rsegs m' o [CB 32 (zeros 32)] ->
    evt rsegs Q (at_ 0x14e9c (R0 (Z_to_bv 64 0x14e9c) t0 t1 t2 (Z_to_bv 64 o) a1 a2 a3 a4 a5 a6 a7
                     (Z_to_bv 64 (-1)) (Z_to_bv 64 b) s4' s5' s6' t3 t4 t5 t6) m').
  Proof.
    intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4' s5' s6' t3 t4 t5 t6 m' j HF HO.
    pose proof (FS_mi m' j HF) as MI.
    unfold at_, R0.
    step. step.
    destruct (Z.ltb_spec 6 b) as [B6|B6].
    - if_t.
      eapply exz; [exact HF | exact HO | | ].
      + unfold synth. replace (6 <? b) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
      + unfold rc. replace (6 <? b) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
    - if_f.
      assert (EB : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6) by lia.
      destruct EB as [Eb|[Eb|[Eb|[Eb|[Eb|[Eb|Eb]]]]]]; rewrite Eb; do 7 step.
      + eapply cs0; eassumption.
      + eapply cs1; eassumption.
      + eapply cs2; eassumption.
      + eapply cs3; eassumption.
      + eapply cs4; eassumption.
      + eapply cs5; eassumption.
      + eapply cs6; eassumption.
  Qed.


  Lemma main_nz : forall m0 t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    munch [(bv_unsigned sp - 160, bv_unsigned sp); (o, o + 32)] m m0 -> wmono rsegs m m0 ->
    stk rsegs m0 (bv_unsigned sp - 160) (bv_unsigned sp) -> mem_inv rsegs m0 -> bytes_at rsegs m0 p row ->
    rw_cells rsegs m0 o [CB 32 ob] ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 b) (Z_to_bv 64 o) a3 a4 a5 a6 a7
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 REAC_BOX_MODEL_BLOCK) fc None m0
                    (seg_rom rsegs)).
  Proof.
    intros m0 t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 MU WM ST MI HRB HOC. unfold REAC_BOX_MODEL_BLOCK.
    pose proof HOC as [[[Lob _] _] _]. cbn [cell_wf] in Lob.
    destruct (stk_carve rsegs m0 _ _ 112 ST ltac:(lia)) as [ST1 [junk FR]]. clear ST.
    change (Z.of_nat 112) with 112 in ST1, FR.
    replace (bv_unsigned sp - 112) with (bv_unsigned sp + -112) in ST1, FR by lia.
    step. step. step. step. step. step. step. step. step.
    step. step. if_f.
    step. step. if_f.
    step. step. step. step. step. step.
    eapply (call_ms 0x14e9c 0 32 0 ob); [apply ret_pc_even; [lia | reflexivity] | lia | lia | lia
           | rewrite unsigned_lit; lia | rewrite unsigned_lit; lia | rewrite unsigned_lit; lia | | exact HOC |].
    { split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split; [eapply hnb_tr; [eassumption | exact HNB0]|]. split; [eassumption|]. split; eassumption. }
    intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m'' HF2 HO2.
    eapply after_ms; [exact HF2 |].
    unfold upd_bytes in HO2. rewrite repeat_length in HO2. cbn [firstn app Nat.add] in HO2.
    rewrite skipn_all2 in HO2 by lia. rewrite app_nil_r in HO2. exact HO2.
  Qed.
End Main.

Lemma early : forall ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p b o : Z) (row nb : list byte),
  0 <= p < 2^64 -> 0 <= o < 2^64 -> (p = 0 \/ o = 0) ->
  stk rsegs m (bv_unsigned sp - 160) (bv_unsigned sp) -> mem_inv rsegs m ->
  evt rsegs (reac_box_model_block_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o row nb)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 b) (Z_to_bv 64 o) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 REAC_BOX_MODEL_BLOCK) fc None m
        (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m p b o row nb
    Rp Ro Hpo ST MI.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp. pose proof ST as (Rlo & _ & _).
  pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold reac_box_model_block_post, REAC_BOX_MODEL_BLOCK.
  replace ((p =? 0) || (o =? 0)) with true by (destruct Hpo as [-> | ->]; [reflexivity | symmetry; apply orb_true_r]).
  destruct (stk_carve rsegs m _ _ 112 ST ltac:(lia)) as [ST1 [junk FR]]. clear ST.
  change (Z.of_nat 112) with 112 in ST1, FR.
  replace (bv_unsigned sp - 112) with (bv_unsigned sp + -112) in ST1, FR by lia.
  step. step. step. step. step. step. step. step. step. step. step.
  destruct (Z.eq_dec p 0) as [P0|P0].
  - subst p. if_t.
    do 11 step.
    apply evt_done. do 15 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    match goal with FR' : rw_cells rsegs ?mm _ _, ST' : stk rsegs ?mm _ _ |- _ =>
      pose proof (stk_release rsegs mm _ _ _ ST' FR' ltac:(lia)) as STf end.
    cbn [cells_size csize Nat.add] in STf.
    replace (bv_unsigned sp + -112 + Z.of_nat 112) with (bv_unsigned sp) in STf by lia. exact STf.
  - destruct Hpo as [Hpo|O0]; [contradiction|]. subst o. if_f.
    step. step. if_t.
    do 11 step.
    apply evt_done. do 15 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    match goal with FR' : rw_cells rsegs ?mm _ _, ST' : stk rsegs ?mm _ _ |- _ =>
      pose proof (stk_release rsegs mm _ _ _ ST' FR' ltac:(lia)) as STf end.
    cbn [cells_size csize Nat.add] in STf.
    replace (bv_unsigned sp + -112 + Z.of_nat 112) with (bv_unsigned sp) in STf by lia. exact STf.
Qed.

Theorem reac_box_model_block_holds : memset_contract -> memcpy_contract -> build_dt1_single_contract ->
  reac_box_model_block_contract.
Proof.
  intros HMS HMC HBD. unfold reac_box_model_block_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    p b o row nb ob -> -> -> Rp Rb Ro Hal ST HP HN HO MI.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof ST as (Rlo & _ & _).
  destruct (Z.eq_dec p 0) as [P0|P0]; [eapply early; eauto|].
  destruct (Z.eq_dec o 0) as [O0|O0]; [eapply early; eauto|].
  destruct (HP P0) as (Hp8 & Hlen & HRB & DRS & DRO').
  destruct (HO O0) as (HOC & DOS & DOJ).
  assert (DRO : o + 32 <= p \/ p + 296 <= o) by (destruct DRO' as [E|E]; [contradiction | exact E]).
  pose proof (rw_cells_bound rsegs m o _ HOC) as Bo. cbn [cells_size csize Nat.add] in Bo.
  pose proof (bytes_at_bound rsegs m p row HRB) as Bp. rewrite Hlen in Bp.
  assert (HNO : (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    name_ok nb /\ (bv_unsigned sp <= rname row \/ rname row + Z.of_nat (length nb) <= bv_unsigned sp - 160) /\
    (o + 32 <= rname row \/ rname row + Z.of_nat (length nb) <= o)).
  { intros B5 H1 H2. destruct (HN P0 B5 H1 H2) as (N1 & _ & N3 & N4). split; [exact N1|]. split; [exact N3|].
    destruct N4 as [E|E]; [contradiction | exact E]. }
  assert (HNB0 : (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 -> bytes_at rsegs m (rname row) nb).
  { intros B5 H1 H2. destruct (HN P0 B5 H1 H2) as (_ & N2 & _). exact N2. }
  eapply main_nz with (ob := ob); try eassumption; try lia.
  - apply munch_refl.
  - apply wmono_refl.
Qed.
