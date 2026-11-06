(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* The walk of check_events_fields (fuzz/fuzz_decode.c:187-263) in fuzz_decode.ubsan, at 0x13868 (168 words,
   48-byte frame), against lib/U/Prog/check_events_fields_c.v. 160 of the 168 instructions are walked: every one but
   the `j` to the abort at 0x13924, 0x1395c, 0x13a30, 0x13a60 and 0x13ab8, the `j` to the unimp at 0x139f8, the
   `jal abort` at 0x13b00 and the unimp at 0x13b04. The walk is split at two join points: [dispatch] starts at
   0x138e0 (after the maker flag s4) and splits on the kind of the owed event into the kind lemmas kind_*, and
   [join] starts at 0x13990 (the maker test of ev->device), from which the epilogue returns to ra. The counter
   (0x13a28) and the scribble write (0x13a94) call bcmp through lib/U/Prog/bcmp.v's bcmp_holds; memcmp_arr relates
   memcmp_model on the bytes of the two arrays to DgnSpec.bytes_eq.
   Abort site: every branch to the `jal abort` at 0x13b00 (the bne / beq after each pair of loads, the bnez after
   each bcmp and the beqz of ev->text[len]) is not taken because check_events_fields_ok (map bz bb) ow ev = true:
   for the kind the dispatch reaches, it gives each field of ev equal (over Z) to the owed one, so the two loads of
   a test read one value (a byte cell b8 z, a halfword cell, or for the fader's lsb_missing an lw of the C int
   ow_lsb_missing, which is a byte), bytes_eq gives bcmp the result 0, and byte_at (de_text ev) len = 0 gives the
   NUL; the maker test at 0x139a4 is reached only when the flag s4 is 1, which is the model's maker.
   UBSan traps (each branches to the unimp at 0x13b04):
   - 0x13888 `andi a1, a1, 7` / 0x1388c `bnez a1` (o misaligned): not taken by o mod 8 = 0 (land7_0);
   - the alignment tests of e (`andi _, s1, 7` then 0x138f4, 0x13934, 0x1396c, 0x13998, 0x13a00, 0x13a38, 0x13a68,
     0x13ac0 `bnez`, and 0x139f4 `beqz` past the `j` at 0x139f8): not taken by e mod 8 = 0 (land7_0);
   - 0x138b4 `bltu a1, a0` (b + sysex_at wraps): not taken as b + sysex_at < b + length bb <= 2^64 (bytes_at and
     the premise sysex_at < length bb when the status is F0);
   - 0x138b8-0x138c4 `snez` / `seqz` / `xor` / `beqz` and 0x138c8 `beqz a0` (b NULL, or b + sysex_at NULL): not
     taken by the premise 0 < b when the status is F0, and 0 <= sysex_at (snez_pos, seqz_pos);
   - 0x13aa0 `bgeu s2, a0` with a0 = 9 (the index of ev->text past char[9]): not taken by the premise
     se_len <= 8 for a scribble write (s2 = ev->len = e->len);
   - 0x13aa4 `not a0, s3` / 0x13aa8 `bltu a0, s2` (e + 20 + len wraps): not taken by e + 80 <= 2^64 (ro_cells)
     and len <= 8. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnDecHarness.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import DgnChkLib.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import DgnLayout bcmp_c bcmp check_events_fields_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- the values of the tests ---- *)

(* andi _, _, 7 of an 8-aligned address *)
Lemma land7_0 : forall x, 0 <= x < 2^64 -> x mod 8 = 0 -> Z.land (bv_unsigned (Z_to_bv 64 x)) 7 = 0.
Proof.
  intros x Hx H. rewrite unsigned_lit by lia. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H.
Qed.

(* addiw rd, rs, dd then bltu c, rd, rs holding the C int K: taken when K + dd is outside [0, c] *)
Lemma addiw_ltu : forall K dd c, -2^31 <= K < 2^31 -> 0 <= c < 2^30 -> -2^30 < dd <= 0 ->
  K + dd < 0 \/ c < K + dd ->
  bv_ltu (Z_to_bv 64 c) (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 K) + dd))) = true.
Proof.
  intros K dd c HK Hc Hd H. rewrite bv_ltu_Z, !unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  apply Z.ltb_lt.
  replace (2^64) with 18446744073709551616 by reflexivity.
  replace (2^32) with 4294967296 by reflexivity. replace (2^31) with 2147483648 by reflexivity.
  replace (2^31) with 2147483648 in HK by reflexivity.
  replace (2^30) with 1073741824 in Hc, Hd by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

(* bltu c, x with x a small integer outside [0, c] *)
Lemma ltu_out : forall c x, 0 <= c < 2^62 -> -2^62 < x < 2^62 -> x < 0 \/ c < x ->
  bv_ltu (Z_to_bv 64 c) (Z_to_bv 64 x) = true.
Proof.
  intros c x Hc Hx H. rewrite bv_ltu_Z, !unsigned_lit_wrap. apply Z.ltb_lt.
  replace (2^64) with 18446744073709551616 by reflexivity.
  replace (2^62) with 4611686018427387904 in Hc, Hx by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

(* snez of a nonzero address *)
Lemma snez_pos : forall z, 0 < z < 2^64 -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 z) = Z_to_bv 64 1.
Proof.
  intros z Hz. rewrite v_sltu_b2z, !unsigned_lit by lia.
  replace (0 <? z) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

(* seqz of a nonzero address *)
Lemma seqz_pos : forall z, 0 < z < 2^64 -> v_sltiu (Z_to_bv 64 z) 1 = Z_to_bv 64 0.
Proof.
  intros z Hz. rewrite v_sltiu_b2z, unsigned_lit by lia. change (bv_wrap 64 1) with 1.
  replace (z <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

(* addi -0x13 / seqz of a loaded byte: the byte is SPEC_MAKER *)
Lemma seqz19 : forall x : byte,
  v_sltiu (Z_to_bv 64 (bv_unsigned x + -19)) 1 = Z_to_bv 64 (Z.b2z (bz x =? 19)).
Proof.
  intros x. unfold bz. pose proof (bv_unsigned_in_range 8 x) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8) with 256 in R.
  rewrite v_sltiu_b2z, unsigned_lit_wrap. change (bv_wrap 64 1) with 1.
  destruct (Z.eqb_spec (bv_unsigned x) 19) as [E|N].
  - rewrite E. reflexivity.
  - replace ((bv_unsigned x + -19) mod 2^64 <? 1) with false; [reflexivity|].
    symmetry. apply Z.ltb_ge. replace (2^64) with 18446744073709551616 by reflexivity.
    Z.div_mod_to_equations. lia.
Qed.

Lemma seqz19z : forall x : byte,
  v_sltiu (Z_to_bv 64 (bv_unsigned (zxb x) + -19)) 1 = Z_to_bv 64 (Z.b2z (bz x =? 19)).
Proof.
  intros x. unfold zxb. rewrite unsigned_lit; [apply seqz19|].
  pose proof (bv_unsigned_in_range 8 x) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. lia.
Qed.

(* ---- the bytes the walk reads by address: the maker byte, the arrays bcmp compares ---- *)

Lemma firstn1_skipn : forall {A} (l : list A) j d, (j < length l)%nat -> firstn 1 (skipn j l) = [nth j l d].
Proof.
  induction l as [|x l IH]; intros j d H; cbn in H; [lia|].
  destruct j as [|j]; cbn; [reflexivity|]. apply IH. lia.
Qed.

Lemma rd_byte : forall m b bb k, bytes_at rsegs m b bb -> 0 <= k < Z.of_nat (length bb) ->
  ov_read_bytes rsegs m (wa (b + k)) 1 = Some [nth (Z.to_nat k) bb (b8 0)].
Proof.
  intros m b bb k H Hk. rewrite (bytes_at_read rsegs m b bb k 1 H) by lia.
  rewrite (firstn1_skipn bb (Z.to_nat k) (b8 0)) by lia. reflexivity.
Qed.

(* b[sysex_at] in the model *)
Lemma byte_at_map_bz : forall bb k, byte_at (map bz bb) k = bz (nth (Z.to_nat k) bb (b8 0)).
Proof. intros bb k. unfold byte_at. exact (map_nth bz bb (b8 0) (Z.to_nat k)). Qed.

Lemma cells_bytes_arr : forall n l, cells_bytes (arr_cells n l) = map (fun i => b8 (nth i l 0)) (seq 0 n).
Proof.
  intros n l. unfold arr_cells. induction (seq 0 n) as [|i s IH]; cbn [map cells_bytes cbytes app]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma ro_cells_mid : forall segs m A pre mid post,
  ro_cells segs m A (pre ++ mid ++ post) -> ro_cells segs m (A + Z.of_nat (cells_size pre)) mid.
Proof.
  intros segs m A pre mid post [Hwf Hb].
  apply cells_wf_app in Hwf as [W1 W23]. apply cells_wf_app in W23 as [W2 W3].
  rewrite !cells_bytes_app in Hb. apply bytes_at_app in Hb as [_ Hb]. apply bytes_at_app in Hb as [Hb _].
  rewrite cells_bytes_length in Hb by exact W1. split; assumption.
Qed.

Local Ltac at_addr H T :=
  lazymatch type of H with
  | ro_cells _ _ ?A _ => replace A with T in H by (cbn [cells_size csize Nat.add app arr_cells map seq]; lia)
  end.

Lemma ev_text_bytes : forall m e b mpad ev, ro_cells rsegs m e (event_cells b mpad ev) ->
  bytes_at rsegs m (e + 20) (map (fun i => b8 (nth i (de_text ev) 0)) (seq 0 9)).
Proof.
  intros m e b mpad ev H. unfold event_cells in H. apply ro_cells_mid in H. at_addr H (e + 20).
  rewrite <- cells_bytes_arr. exact (proj2 H).
Qed.

Lemma ev_seg_bytes : forall m e b mpad ev, ro_cells rsegs m e (event_cells b mpad ev) ->
  bytes_at rsegs m (e + 29) (map (fun i => b8 (nth i (de_seg ev) 0)) (seq 0 8)).
Proof.
  intros m e b mpad ev H. unfold event_cells in H. rewrite app_assoc in H. apply ro_cells_mid in H.
  at_addr H (e + 29). rewrite <- cells_bytes_arr. exact (proj2 H).
Qed.

Lemma ow_text_bytes : forall m o p1 p2 ow, ro_cells rsegs m o (owed_cells p1 p2 ow) ->
  bytes_at rsegs m (o + 77) (map (fun i => b8 (nth i (se_text (ow_e ow)) 0)) (seq 0 8)).
Proof.
  intros m o p1 p2 ow H. unfold owed_cells in H. apply ro_cells_mid in H. rewrite spec_msg_cells_size in H.
  unfold spec_event_cells in H. apply ro_cells_mid in H. at_addr H (o + 77).
  rewrite <- cells_bytes_arr. exact (proj2 H).
Qed.

Lemma ow_seg_bytes : forall m o p1 p2 ow, ro_cells rsegs m o (owed_cells p1 p2 ow) ->
  bytes_at rsegs m (o + 85) (map (fun i => b8 (nth i (se_seg (ow_e ow)) 0)) (seq 0 8)).
Proof.
  intros m o p1 p2 ow H. unfold owed_cells in H. apply ro_cells_mid in H. rewrite spec_msg_cells_size in H.
  unfold spec_event_cells in H. rewrite app_assoc in H. apply ro_cells_mid in H. at_addr H (o + 85).
  rewrite <- cells_bytes_arr. exact (proj2 H).
Qed.

(* ---- memcmp_model on equal prefixes, and DgnSpec.bytes_eq ---- *)

Lemma memcmp_model_eq : forall n l r, (n <= length l)%nat -> (n <= length r)%nat ->
  (forall i, (i < n)%nat -> nth i l (b8 0) = nth i r (b8 0)) -> memcmp_model l r n = Some 0.
Proof.
  induction n as [|n IH]; intros l r Hl Hr H; [reflexivity|].
  destruct l as [|x l]; [cbn in Hl; lia|]. destruct r as [|y r]; [cbn in Hr; lia|].
  cbn [memcmp_model]. pose proof (H 0%nat ltac:(lia)) as H0. cbn in H0. subst y. rewrite Z.eqb_refl.
  apply IH; [cbn in Hl; lia | cbn in Hr; lia |]. intros i Hi. exact (H (S i) ltac:(lia)).
Qed.

Lemma nth_map_seq : forall {B} (f : nat -> B) n i d, (i < n)%nat -> nth i (map f (seq 0 n)) d = f i.
Proof.
  intros B f n i d Hi. rewrite nth_indep with (d' := f 0%nat) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. reflexivity.
Qed.

(* memcmp (x, y, k) over the bytes of two C arrays held as lists Z is 0 when bytes_eq k holds *)
Lemma memcmp_arr : forall n1 n2 l1 l2 k, 0 <= k -> (Z.to_nat k <= n1)%nat -> (Z.to_nat k <= n2)%nat ->
  bytes_eq k l1 l2 = true ->
  memcmp_model (map (fun i => b8 (nth i l1 0)) (seq 0 n1)) (map (fun i => b8 (nth i l2 0)) (seq 0 n2))
    (Z.to_nat k) = Some 0.
Proof.
  intros n1 n2 l1 l2 k Hk H1 H2 HE.
  apply memcmp_model_eq; [rewrite length_map, length_seq; lia | rewrite length_map, length_seq; lia |].
  intros i Hi. rewrite !nth_map_seq by lia. f_equal.
  unfold bytes_eq in HE. rewrite forallb_forall in HE.
  assert (IN : In (Z.of_nat i) (zseq (Z.to_nat k))) by (unfold zseq; apply in_map; apply in_seq; lia).
  apply HE, Z.eqb_eq in IN. unfold byte_at in IN. rewrite Nat2Z.id in IN. exact IN.
Qed.

(* ---- the model's facts ---- *)

(* the maker test of fuzz_decode.c:261 *)
Lemma ok_maker : forall bl ow ev, check_events_fields_ok bl ow ev = true ->
  (sm_status (ow_m ow) =? 240) && (3 <=? sm_sysex_len (ow_m ow)) &&
  (byte_at bl (sm_sysex_at (ow_m ow)) =? SPEC_MAKER) = true -> de_device ev = se_device (ow_e ow).
Proof.
  intros bl ow ev H Hm. unfold check_events_fields_ok in H. cbv zeta in H.
  apply andb_true_iff in H as [_ H]. rewrite Hm in H. cbn [implb] in H. apply Z.eqb_eq. exact H.
Qed.

(* the tests of check_events_fields_ok for a kind given as a number *)
Local Ltac okt H HK :=
  unfold check_events_fields_ok in H; cbv zeta in H; rewrite HK in H;
  unfold SPEC_EV_FADER, SPEC_EV_TOUCH, SPEC_EV_STRIP_BUTTON, SPEC_EV_SECTION_BUTTON, SPEC_EV_VPOT, SPEC_EV_JOG,
    SPEC_EV_RING, SPEC_EV_METER, SPEC_EV_STRIP_LEDS, SPEC_EV_SCRIBBLE, SPEC_EV_COUNTER, SPEC_DIGITS in H;
  cbn [Z.eqb Pos.eqb implb andb orb] in H;
  rewrite ?andb_true_r in H; rewrite ?andb_true_iff in H.

Local Ltac splitH H :=
  lazymatch type of H with
  | _ /\ _ => let H1 := fresh "E" in let H2 := fresh "E" in destruct H as [H1 H2]; splitH H1; splitH H2
  | Z.eqb _ _ = true => apply Z.eqb_eq in H
  | _ => idtac
  end.

(* ---- the walk's tactics ---- *)

(* a test whose condition is closed *)
Local Ltac lit_if :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) =>
      let v := eval vm_compute in cnd in
      lazymatch v with true => idtac | false => idtac end;
      replace cnd with v by (vm_compute; reflexivity); cbv iota
  end.

Local Ltac adv := step; try lit_if.

(* a test decided over Z *)
Local Ltac ulit :=
  repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by lia end.
Local Ltac cnd := cbv beta delta [c_eq c_ltu c_lts]; rewrite ?bv_ltu_Z; try unfold bv_eqb; ulit; decide_tests;
  reflexivity.
Local Ltac brz v :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with v by (symmetry; cnd); cbv iota
  end.

(* a bne / beq of two loads of one value: the two registers are equal after one of the model's equalities *)
Local Ltac resolve_eq :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      lazymatch c with
      | context [bv_eqb ?A ?B] =>
          replace (bv_eqb A B) with true
            by (symmetry; first [ apply eqb_same
                                | match goal with E : _ = _ |- _ => rewrite E; apply eqb_same end ])
      end
  end; cbv beta iota delta [negb].
Local Ltac same := step; resolve_eq.

(* andi _, _, 7 and its test, of an 8-aligned address *)
Local Ltac algn x := step; rewrite (land7_0 x) by (first [assumption | lia]); step; lit_if.

(* jal bcmp: its call with the two byte lists and the result 0 *)
Local Ltac bcall LS RS :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply (bcmp_holds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LS RS 0)
      | post_call segs mm ]
  end.

(* ---- the post-condition, and the join point 0x13990 ---- *)

Definition cef_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (lo : Z) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                    (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp).

Local Ltac flat HE HO :=
  unfold event_cells, dmsg_cells, arr_cells in HE; cbn [map seq app] in HE;
  unfold owed_cells, spec_msg_cells, spec_event_cells, arr_cells in HO; cbn [map seq app] in HO.

Local Ltac bounds HE HO :=
  let RE := fresh "RE" in let RO := fresh "RO" in
  pose proof (ro_cells_bound _ _ _ _ HE) as RE; rewrite event_cells_size in RE; change (Z.of_nat 80) with 80 in RE;
  pose proof (ro_cells_bound _ _ _ _ HO) as RO; rewrite owed_cells_size in RO; change (Z.of_nat 120) with 120 in RO.

(* 0x13990-0x139c4: if s4 (the maker flag), ev->device against e->device; then the epilogue *)
Lemma join : forall (rr sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 t3 t4 t5 t6
                     ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (lo b o e : Z) (ow : owed) (ev : dgn_event)
    (p1 p2 mpad : list byte) (mk : bool),
  e mod 8 = 0 ->
  (mk = true -> de_device ev = se_device (ow_e ow)) ->
  ro_cells rsegs m e (event_cells b mpad ev) ->
  ro_cells rsegs m o (owed_cells p1 p2 ow) ->
  rw_cells rsegs m (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m lo (bv_unsigned sp + -48) ->
  lo + 48 <= bv_unsigned sp ->
  munch [(bv_unsigned sp + -48, bv_unsigned sp)] m0 m ->
  wmono rsegs m0 m ->
  mem_inv rsegs m ->
  evt rsegs (cef_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo)
    (MS (mkR rr (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 e)
             a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 (Z_to_bv 64 (Z.b2z mk)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13990) fc None m (seg_rom rsegs)).
Proof.
  intros rr sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    F fc m0 m lo b o e ow ev p1 p2 mpad mk AE MKD HE HO FR ST HLO MU WM MI.
  bounds HE HO. flat HE HO.
  (* 0x13990 beqz s4; when s4 = 1: 0x13994-0x13998 the alignment of e, 0x1399c-0x139a4 ev->device against
     e->device *)
  destruct mk; cbn [Z.b2z];
    [ adv; algn e; pose proof (MKD eq_refl) as DV; step; step; same
    | adv ].
  all: do 8 step.                           (* 0x139a8-0x139c4: the six loads, addi sp, ret *)
  all: apply evt_done; unfold cef_post; do 16 eexists; split; [reflexivity|];
       split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
       release_frame FR ST (bv_unsigned sp); exact ST.
Qed.

Local Ltac jn :=
  eapply join;
  match goal with
  | HE0 : ro_cells _ _ _ (event_cells _ _ _) |- ro_cells _ _ _ (event_cells _ _ _) => exact HE0
  | HO0 : ro_cells _ _ _ (owed_cells _ _ _) |- ro_cells _ _ _ (owed_cells _ _ _) => exact HO0
  | |- _ => eassumption
  end.

(* ---- the kind dispatch from 0x138e0 ---- *)

Definition at_dispatch (Kc : Z -> Prop) : Prop :=
  forall (rr sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 t3 t4 t5 t6
          ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (lo b o e : Z) (bl : list Z) (ow : owed)
         (ev : dgn_event) (p1 p2 mpad : list byte) (mk : bool),
    Kc (se_kind (ow_e ow)) ->
    check_events_fields_ok bl ow ev = true ->
    -2^31 <= se_kind (ow_e ow) < 2^31 ->
    0 <= ow_lsb_missing ow < 256 ->
    (se_kind (ow_e ow) = SPEC_EV_SCRIBBLE -> 0 <= se_len (ow_e ow) <= 8) ->
    e mod 8 = 0 ->
    (mk = true -> de_device ev = se_device (ow_e ow)) ->
    ro_cells rsegs m e (event_cells b mpad ev) ->
    ro_cells rsegs m o (owed_cells p1 p2 ow) ->
    rw_cells rsegs m (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs m lo (bv_unsigned sp + -48) ->
    lo + 48 <= bv_unsigned sp ->
    munch [(bv_unsigned sp + -48, bv_unsigned sp)] m0 m ->
    wmono rsegs m0 m ->
    mem_inv rsegs m ->
    evt rsegs (cef_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo)
      (MS (mkR rr (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 e)
               a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 (Z_to_bv 64 (Z.b2z mk)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x138e0) fc None m (seg_rom rsegs)).

(* the start of every kind lemma: the cells in flat form (the folded ones kept for [join]), then 0x138e0
   `lw a0, 0x38(s0)`, the kind of the owed event *)
Local Ltac kpre :=
  unfold at_dispatch;
  intros rr sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    F fc m0 m lo b o e bl ow ev p1 p2 mpad mk HK OK RK RLM RSC AE MKD HE HO FR ST HLO MU WM MI;
  cbv beta in HK;
  bounds HE HO;
  let HE0 := fresh "HE0" in let HO0 := fresh "HO0" in pose proof HE as HE0; pose proof HO as HO0;
  flat HE HO;
  step; rewrite (sx32_int (se_kind (ow_e ow))) by lia.

(* kinds 2..4, a key: 0x138e4-0x13924, then 0x13984-0x1398c for 2 and 3 *)
Lemma kind_key : at_dispatch (fun k => 2 <= k <= 4).
Proof.
  kpre.
  assert (KC : se_kind (ow_e ow) = 2 \/ se_kind (ow_e ow) = 3 \/ se_kind (ow_e ow) = 4) by lia.
  destruct KC as [K|[K|K]]; okt OK K; splitH OK; rewrite K.
  all: do 3 adv.                            (* addiw; addi; 0x138ec bltu not taken *)
  all: algn e.                              (* 0x138f0, 0x138f4 *)
  all: step; step; same.                    (* 0x138f8-0x13900: button *)
  all: step; step; same.                    (* 0x13904-0x1390c: on *)
  all: do 2 adv.                            (* addi a1, 4; 0x13914 bne a0, a1 *)
  all: step; step; same.                    (* 4: 0x13918-0x13920 zone; 2, 3: 0x13984-0x1398c strip *)
  all: jn.
Qed.

(* kind 1, a fader: 0x13928-0x1395c *)
Lemma kind_fader : at_dispatch (fun k => k = 1).
Proof.
  kpre. okt OK HK. splitH OK. rewrite HK.
  do 5 adv.                                 (* addiw; addi; 0x138ec bltu taken; addi a1, 1; 0x1392c bne *)
  algn e.                                   (* 0x13930, 0x13934 *)
  step; step; same.                         (* 0x13938-0x13940: strip *)
  step; step; same.                         (* 0x13944-0x1394c: value *)
  step; step; step.                         (* 0x13950-0x13958: ev->lsb_missing, o->lsb_missing *)
  match goal with E : de_lsb_missing ev = _ |- _ => rewrite E end.
  rewrite (zxb_b8 (ow_lsb_missing ow)), (sx32_int (ow_lsb_missing ow)) by lia.
  resolve_eq.
  jn.
Qed.

(* kinds 5 and 6, a V-Pot or the jog: 0x13960-0x13980, then 0x13984-0x1398c for 5 *)
Lemma kind_pot : at_dispatch (fun k => 5 <= k <= 6).
Proof.
  kpre.
  assert (KC : se_kind (ow_e ow) = 5 \/ se_kind (ow_e ow) = 6) by lia.
  destruct KC as [K|K]; okt OK K; splitH OK; rewrite K.
  all: do 7 adv.                            (* to 0x13960; addiw; 0x13964 bltu not taken *)
  all: algn e.                              (* 0x13968, 0x1396c *)
  all: step; step; same.                    (* 0x13970-0x13978: delta *)
  all: do 2 adv.                            (* addi a1, 5; 0x13980 bne a0, a1 *)
  1: step; step; same.                      (* 5: 0x13984-0x1398c strip *)
  all: jn.
Qed.

(* the dispatch of the kinds 7..11 through the jump table at 0x103c4: 17 instructions to the kind's case *)
Local Ltac table := do 17 adv.

(* kind 7, a ring: 0x139f0-0x139f4, then 0x13a48-0x13a5c *)
Lemma kind_ring : at_dispatch (fun k => k = 7).
Proof.
  kpre. okt OK HK. splitH OK. rewrite HK.
  table.
  algn e.                                   (* 0x139f0, 0x139f4 beqz to 0x13a48 *)
  step; step; same.                         (* strip *)
  step; step; same.                         (* mask *)
  jn.
Qed.

(* kind 8, a meter: 0x13abc-0x13afc *)
Lemma kind_meter : at_dispatch (fun k => k = 8).
Proof.
  kpre. okt OK HK. splitH OK. rewrite HK.
  table.
  algn e.                                   (* 0x13abc, 0x13ac0 *)
  step; step; same.                         (* addr *)
  step; step; same.                         (* strip *)
  step; step; same.                         (* right *)
  step; step; same.                         (* mask *)
  step; step; same.                         (* segments *)
  jn.
Qed.

(* kind 9, LEDs: 0x13a34-0x13a44, then 0x13a48-0x13a5c *)
Lemma kind_leds : at_dispatch (fun k => k = 9).
Proof.
  kpre. okt OK HK. splitH OK. rewrite HK.
  table.
  algn e.                                   (* 0x13a34, 0x13a38 *)
  step; step; same.                         (* addr *)
  step; step; same.                         (* strip *)
  step; step; same.                         (* mask *)
  jn.
Qed.

(* kind 11, the counter: 0x139fc-0x13a2c *)
Lemma kind_counter : at_dispatch (fun k => k = 11).
Proof.
  kpre. okt OK HK. splitH OK. rewrite HK.
  pose proof (ev_seg_bytes _ _ _ _ _ HE0) as SGE. pose proof (ow_seg_bytes _ _ _ _ _ HO0) as SGO.
  table.
  algn e.                                   (* 0x139fc, 0x13a00 *)
  step; step; same.                         (* addr *)
  step; step; same.                         (* dots *)
  do 4 step.                                (* addi a0, s1, 0x1d; addi a1, s0, 0x55; addi a2, 8; jal bcmp *)
  bcall (map (fun i => b8 (nth i (de_seg ev) 0)) (seq 0 8))
        (map (fun i => b8 (nth i (se_seg (ow_e ow)) 0)) (seq 0 8)).
  1: rewrite unsigned_lit by lia; exact SGE.
  1: rewrite unsigned_lit by lia; exact SGO.
  1: rewrite unsigned_lit by lia; apply memcmp_arr; [lia | lia | lia | assumption].
  1: assumption.
  adv.                                      (* 0x13a2c beqz a0 *)
  jn.
Qed.

(* kind 10, a scribble write: 0x13a64-0x13ab4 *)
Local Ltac fix_nt NT :=
  unfold byte_at in NT;
  lazymatch type of NT with
  | context [Z.to_nat ?z] => let v := eval vm_compute in (Z.to_nat z) in change (Z.to_nat z) with v in NT
  end.

Lemma kind_scribble : at_dispatch (fun k => k = 10).
Proof.
  kpre. okt OK HK. splitH OK. rewrite HK. specialize (RSC HK).
  pose proof (ev_text_bytes _ _ _ _ _ HE0) as TXE. pose proof (ow_text_bytes _ _ _ _ _ HO0) as TXO.
  table.
  algn e.                                   (* 0x13a64, 0x13a68 *)
  step; step; same.                         (* addr *)
  step; step; same.                         (* 0x13a78-0x13a80: len, s2 = ev->len *)
  match goal with E : de_len ev = _ |- _ => rewrite E end.
  rewrite (zxb_b8 (se_len (ow_e ow))) by lia.
  do 5 step.                                (* addi s3, s1, 0x14; addi a1, s0, 0x4d; mv a0, s3; mv a2, s2; jal *)
  bcall (map (fun i => b8 (nth i (de_text ev) 0)) (seq 0 9))
        (map (fun i => b8 (nth i (se_text (ow_e ow)) 0)) (seq 0 8)).
  1: rewrite unsigned_lit by lia; exact TXE.
  1: rewrite unsigned_lit by lia; exact TXO.
  1: rewrite unsigned_lit by lia; apply memcmp_arr; [lia | lia | lia | assumption].
  1: assumption.
  adv.                                      (* 0x13a98 bnez a0 *)
  step; step; brz false.                    (* addi a0, 9; 0x13aa0 bgeu s2, a0 *)
  step. rewrite (unsigned_lit (e + 20)) by lia. rewrite zb_lxor_ones by lia.   (* 0x13aa4 not a0, s3 *)
  step; brz false.                          (* 0x13aa8 bltu a0, s2 *)
  step.                                     (* add s2, s3, s2 *)
  match goal with E : byte_at (de_text ev) _ = 0 |- _ => rename E into NT end.
  assert (LC : se_len (ow_e ow) = 0 \/ se_len (ow_e ow) = 1 \/ se_len (ow_e ow) = 2 \/ se_len (ow_e ow) = 3 \/
               se_len (ow_e ow) = 4 \/ se_len (ow_e ow) = 5 \/ se_len (ow_e ow) = 6 \/ se_len (ow_e ow) = 7 \/
               se_len (ow_e ow) = 8) by lia.
  destruct LC as [HL|[HL|[HL|[HL|[HL|[HL|[HL|[HL|HL]]]]]]]]; rewrite HL in NT |- *; fix_nt NT.
  all: step; rewrite NT.                    (* 0x13ab0 lbu a0, 0(s2): ev->text[len] *)
  all: adv.                                 (* 0x13ab4 beqz a0 *)
  all: jn.
Qed.

(* every other kind: 0x138e4-0x139d0 to 0x13990 *)
Lemma kind_other : at_dispatch (fun k => k < 1 \/ 11 < k).
Proof.
  kpre.
  step. step. step.                         (* addiw a1, a0, -2; addi a2, 2; 0x138ec bltu a2, a1 *)
  rewrite (addiw_ltu (se_kind (ow_e ow)) (-2) 2) by lia. cbv iota.
  step. step.                               (* addi a1, 1; 0x1392c bne a0, a1 *)
  rewrite (eqb_int64 (se_kind (ow_e ow)) 1) by lia.
  rewrite (proj2 (Z.eqb_neq (se_kind (ow_e ow)) 1)) by lia. cbv beta iota delta [negb].
  step. step.                               (* addiw a2, a0, -5; 0x13964 bltu a1, a2 *)
  rewrite (addiw_ltu (se_kind (ow_e ow)) (-5) 1) by lia. cbv iota.
  step. step. step.                         (* addi a0, a0, -7; addi a1, 4; 0x139d0 bltu a1, a0 *)
  rewrite (ltu_out 4 (se_kind (ow_e ow) + -7)) by lia. cbv iota.
  jn.
Qed.

Local Ltac use L := let H := fresh "L" in pose proof L as H; unfold at_dispatch in H; eapply H.

Lemma dispatch : at_dispatch (fun _ => True).
Proof.
  unfold at_dispatch.
  intros rr sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    F fc m0 m lo b o e bl ow ev p1 p2 mpad mk _ OK RK RLM RSC AE MKD HE HO FR ST HLO MU WM MI.
  assert (KC : se_kind (ow_e ow) = 1 \/ 2 <= se_kind (ow_e ow) <= 4 \/ 5 <= se_kind (ow_e ow) <= 6 \/
               se_kind (ow_e ow) = 7 \/ se_kind (ow_e ow) = 8 \/ se_kind (ow_e ow) = 9 \/
               se_kind (ow_e ow) = 10 \/ se_kind (ow_e ow) = 11 \/
               (se_kind (ow_e ow) < 1 \/ 11 < se_kind (ow_e ow))) by lia.
  destruct KC as [K|[K|[K|[K|[K|[K|[K|[K|K]]]]]]]];
    [ use kind_fader | use kind_key | use kind_pot | use kind_ring | use kind_meter | use kind_leds
    | use kind_scribble | use kind_counter | use kind_other ];
    first [ exact K | eassumption ].
Qed.

(* ---- the walk ---- *)

Theorem check_events_fields_holds : check_events_fields_contract.
Proof.
  unfold check_events_fields_contract, CHECK_EVENTS_FIELDS, CHECK_EVENTS_FIELDS_FRAME, OW_SIZE, DE_SIZE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    b o e lo bb ow ev p1 p2 mpad OK RK RST RLEN RSA RLM RSC AO AE HB BB HO HE ST HLO DB DO DE MI.
  change (evt rsegs _ ?S) with (evt rsegs (cef_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo) S).
  pose proof (bytes_at_bound _ _ _ _ BB) as RB.
  bounds HE HO.
  pose proof (ok_maker _ _ _ OK) as MK.
  pose proof dispatch as D. unfold at_dispatch in D.
  flat HE HO.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  do 7 step.                                (* 0x13868-0x13880: addi sp; sd ra, s0, s1, s2, s3, s4 *)
  step.                                     (* mv s0, a1 *)
  algn o.                                   (* 0x13888, 0x1388c *)
  step.                                     (* mv s1, a2 *)
  step. rewrite (zxb_b8 (sm_status (ow_m ow))) by lia.   (* lbu a1, 0x20(s0): o->m.status *)
  step. step.                               (* addi a2, 0xf0; 0x1389c bne a1, a2 *)
  rewrite (eqb_int64 (sm_status (ow_m ow)) 240) by lia.
  destruct (Z.eqb_spec (sm_status (ow_m ow)) 240) as [EST|NST]; cbv beta iota delta [negb].
  2:{ step.                                 (* 0x138dc mv s4, zero *)
      eapply D with (mk := false) (b := b) (mpad := mpad) (p1 := p1) (p2 := p2);
        first [ exact I | eassumption | let X := fresh in intros X; discriminate X ]. }
  specialize (HB EST). specialize (RSA EST).
  step. step. step.                         (* ld a1, 0x30(s0); addi a2, 3; 0x138a8 bltu a1, a2 *)
  cbv beta delta [c_ltu]. rewrite bv_ltu_Z, (unsigned_lit (sm_sysex_len (ow_m ow))), (unsigned_lit 3) by lia.
  destruct (Z.ltb_spec (sm_sysex_len (ow_m ow)) 3) as [L3|G3]; cbv iota.
  { step.                                   (* 0x138dc mv s4, zero *)
    eapply D with (mk := false) (b := b) (mpad := mpad) (p1 := p1) (p2 := p2);
      first [ exact I | eassumption | let X := fresh in intros X; discriminate X ]. }
  step. step.                               (* ld a1, 0x28(s0); add a1, a0, a1 *)
  step; brz false.                          (* 0x138b4 bltu a1, a0 *)
  step. rewrite (snez_pos b) by lia.        (* snez a2, a0 *)
  step. rewrite (seqz_pos (b + sm_sysex_at (ow_m ow))) by lia.   (* seqz a3, a1 *)
  step. adv.                                (* xor a2, a2, a3; 0x138c4 beqz a2 *)
  step; brz false.                          (* 0x138c8 beqz a0 *)
  match goal with HBB : bytes_at rsegs ?mm b bb |- _ =>
    pose proof (rd_byte mm b bb (sm_sysex_at (ow_m ow)) HBB ltac:(lia)) as HR end.
  step.                                     (* lbu a0, 0(a1): b[sysex_at] *)
  step. step.                               (* addi a0, a0, -0x13; seqz s4, a0 *)
  first [ rewrite seqz19z | rewrite seqz19 ].
  step.                                     (* j 0x138e0 *)
  eapply D with (mk := (bz (nth (Z.to_nat (sm_sysex_at (ow_m ow))) bb (b8 0)) =? 19))
    (b := b) (mpad := mpad) (p1 := p1) (p2 := p2);
    first [ exact I | eassumption | idtac ].
  intros Hm. apply MK. unfold SPEC_MAKER.
  rewrite byte_at_map_bz, Hm, ?EST, (proj2 (Z.leb_le 3 (sm_sysex_len (ow_m ow)))) by lia. reflexivity.
Qed.
