(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* LLVMFuzzerTestOneInput_seg.dstep_stmt: the decoder loop's memset (&o.m, 0, 56) (0x1309c .. 0x130a8), the
   inlined spec_msg_step (0x130ac .. 0x13168, out of line 0x131e4 .. 0x13224 and 0x13310 .. 0x133cc), the stores
   of o.next and o.status_out and memset (&o.e, 0, 44) of the plain image. The first memset leaves spec_msg_cells
   of an all-zero record (dstep_memset), so every store hits one cell. A step that is no message ends at 0x13180
   through dstep_dend (o = owed0 m = owed_at); a sysex (the F7 scan 0x130e0 .. 0x130f0 is dstep_scan, by
   induction on len - i) hands off at 0x13228, a channel message (dstep_chan, dstep_chan2, the data-byte loop
   0x13344 .. 0x13358 unrolled for one or two bytes) at 0x133d0, both through dstep_ez. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib DgnDecHarness.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import memset_c memcpy_c DgnLayout.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import LLVMFuzzerTestOneInput_seg.
Import ListNotations.
Open Scope Z_scope.

(* ---- cell lists ---- *)

(* cs with the cell at byte offset k replaced by the list mid *)
Fixpoint dstep_splice (cs : list cell) (k : nat) (mid : list cell) : list cell :=
  match cs with
  | [] => []
  | c :: cs' => if Nat.eqb k 0 then mid ++ cs' else c :: dstep_splice cs' (k - csize c) mid
  end.

Lemma dstep_splice_split : forall cs k c mid,
  cell_at cs k = Some c ->
  exists pre post, cs = pre ++ c :: post /\ cells_size pre = k /\ dstep_splice cs k mid = pre ++ mid ++ post.
Proof.
  induction cs as [|c0 cs IH]; intros k c mid H; [discriminate|].
  cbn [cell_at dstep_splice] in *. destruct (Nat.eqb_spec k 0).
  - inversion H; subst. exists [], cs. repeat split; auto.
  - destruct (Nat.ltb_spec0 k (csize c0)); [discriminate|].
    destruct (IH _ _ mid H) as (pre & post & -> & Hsz & Hs).
    exists (c0 :: pre), post. repeat split; auto.
    + cbn. lia.
    + cbn. rewrite Hs. reflexivity.
Qed.

Lemma dstep_rw_app : forall segs m A cs1 cs2, rw_cells segs m A cs1 ->
  rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells segs m A (cs1 ++ cs2).
Proof.
  intros segs m A cs1 cs2 [[W1 B1] (R1a & R1b & R1)] [[W2 B2] (R2a & R2b & R2)].
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|].
    rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i (Z.of_nat (cells_size cs1))) as [H|H]; [apply R1; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
    apply R2. lia.
Qed.

Lemma dstep_rw_split : forall segs m A pre c post,
  rw_cells segs m A (pre ++ c :: post) ->
  rw_cells segs m A pre /\ rw_cells segs m (A + Z.of_nat (cells_size pre)) [c] /\
  rw_cells segs m (A + Z.of_nat (cells_size pre) + Z.of_nat (csize c)) post.
Proof.
  intros segs m A pre c post [[Hwf Hb] (Ha & Hn & Hw)].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 [Wc W2]].
  rewrite cells_bytes_app in Hb. cbn [cells_bytes] in Hb.
  apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite (cells_bytes_length pre W1) in B2.
  apply bytes_at_app in B2. destruct B2 as [Bc B3].
  rewrite (cbytes_length c Wc) in B3.
  rewrite cells_size_app in Hn, Hw. cbn [cells_size] in Hn, Hw.
  split; [|split].
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split; [cbn; tauto | cbn [cells_bytes]; rewrite app_nil_r; exact Bc]|].
    split; [lia|]. split; [cbn [cells_size]; lia|]. intros i Hi. cbn [cells_size] in Hi.
    replace (A + Z.of_nat (cells_size pre) + i) with (A + (Z.of_nat (cells_size pre) + i)) by lia.
    apply Hw. lia.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size pre) + Z.of_nat (csize c) + i)
      with (A + (Z.of_nat (cells_size pre) + Z.of_nat (csize c) + i)) by lia.
    apply Hw. lia.
Qed.

(* a cell list's meaning is its bytes *)
Lemma dstep_rwc_bytes : forall segs m A cs cs', rw_cells segs m A cs -> cells_wf cs' ->
  cells_bytes cs' = cells_bytes cs -> rw_cells segs m A cs'.
Proof.
  intros segs m A cs cs' [[Hwf Hb] Hw] Hwf' E.
  split; [split; [exact Hwf' | rewrite E; exact Hb]|].
  rewrite <- (cells_bytes_length cs' Hwf'), E, (cells_bytes_length cs Hwf). exact Hw.
Qed.

Lemma dstep_sub_fp : forall W a n, inside W a n -> sub_fp [(a, a + n)] W.
Proof.
  intros W a n Hin x Hout. cbn [outside]. split; [|exact I].
  intros Hx. exact (inside_not_outside W a n x Hin Hx Hout).
Qed.

(* memset (A + k, 0, n) over the cell CB n junk at byte offset k of a frame cs: the frame afterwards has the
   cells mid (n zero bytes) in its place *)
Lemma dstep_memset : memset_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (W : list (Z * Z)) (A : Z) (cs mid : list cell)
    (k n : nat) (junk : list byte) (B : Z) (bs : list byte) (Q : machine_state -> Prop),
  rw_cells rsegs m A cs -> A + Z.of_nat k + Z.of_nat n < 2 ^ 64 -> cell_at cs k = Some (CB n junk) ->
  cells_wf mid -> cells_bytes mid = repeat (Z_to_bv 8 0) n -> mem_inv rsegs m -> munch W m0 m -> wmono rsegs m0 m ->
  inside W (A + Z.of_nat k) (Z.of_nat n) -> bytes_at rsegs m B bs ->
  (B + Z.of_nat (length bs) <= A + Z.of_nat k \/ A + Z.of_nat k + Z.of_nat n <= B) ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
     munch W m0 m' -> wmono rsegs m0 m' -> mem_inv rsegs m' -> bytes_at rsegs m' B bs ->
     rw_cells rsegs m' A (dstep_splice cs k mid) ->
     evt rsegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (A + Z.of_nat k)) a1' a2' a3' a4' a5' a6' a7'
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (A + Z.of_nat k)) (Z_to_bv 64 0)
                     (Z_to_bv 64 (Z.of_nat n)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 MEMSET) fc None m (seg_rom rsegs)).
Proof.
  intros MSC ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m0 m W A cs mid k n junk B bs Q RW Hn0 Hc Wm Bm MI MU WM Hin BA HD K.
  destruct (dstep_splice_split cs k _ mid Hc) as (pre & post & -> & Hk & Es). rewrite Es in K.
  pose proof (rw_cells_bound _ _ _ _ RW) as Hbd. rewrite cells_size_app in Hbd. cbn [cells_size csize] in Hbd.
  destruct (dstep_rw_split _ _ _ _ _ _ RW) as (R1 & R2 & R3). cbn [csize] in R3. rewrite Hk in R2, R3.
  eapply evt_cut.
  { eapply (MSC ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (A + Z.of_nat k)) (Z_to_bv 64 0) (Z_to_bv 64 (Z.of_nat n))
      a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m junk).
    - rewrite !unsigned_lit by lia. rewrite Nat2Z.id. exact R2.
    - exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU1 & WM1
    & MI1 & RW1).
  rewrite !unsigned_lit in MU1 by lia. rewrite !unsigned_lit in RW1 by lia. rewrite Nat2Z.id in RW1.
  replace (bv_unsigned (Z_to_bv 64 0) mod 256) with 0 in RW1 by reflexivity.
  replace (0 mod 256) with 0 in RW1 by reflexivity.
  apply K; try assumption.
  - eapply munch_trans; [exact MU|]. eapply munch_weaken; [apply dstep_sub_fp; exact Hin | exact MU1].
  - eapply wmono_trans; [exact WM | exact WM1].
  - eapply (bytes_at_transport rsegs _ m m' B bs BA MU1). cbn [disjoint_from]. lia.
  - assert (R1' : rw_cells rsegs m' A pre).
    { eapply (rw_cells_transport rsegs _ m m' A pre R1 MU1 WM1). cbn [disjoint_from]. lia. }
    assert (R3' : rw_cells rsegs m' (A + Z.of_nat k + Z.of_nat n) post).
    { eapply (rw_cells_transport rsegs _ m m' _ post R3 MU1 WM1). cbn [disjoint_from]. lia. }
    assert (R2' : rw_cells rsegs m' (A + Z.of_nat k) mid).
    { apply (dstep_rwc_bytes rsegs m' _ _ mid RW1 Wm). rewrite Bm. cbn [cells_bytes cbytes]. symmetry. apply app_nil_r. }
    apply dstep_rw_app; [exact R1'|]. rewrite Hk. apply dstep_rw_app; [exact R2'|].
    replace (A + Z.of_nat k + Z.of_nat (cells_size mid)) with (A + Z.of_nat k + Z.of_nat n); [exact R3'|].
    destruct R2' as [[Wm' Bm'] _]. rewrite <- (cells_bytes_length mid Wm'), Bm, repeat_length. reflexivity.
Qed.

Definition dstep_zmsg : spec_msg := SpecMsg 0 0 0 0 0 0 0 0 0 0 0.

Lemma dstep_zmsg_bytes : cells_bytes (spec_msg_cells dstep_zmsg) = repeat (Z_to_bv 8 0) 56.
Proof. vm_compute. reflexivity. Qed.

Lemma dstep_zev_bytes : cells_bytes (spec_event_cells se_zero ++ [C4 (Z_to_bv 64 0)]) = repeat (Z_to_bv 8 0) 44.
Proof. vm_compute. reflexivity. Qed.

(* sb stores the low byte of its register *)
Lemma dstep_le1 : forall z, le1 (Z_to_bv 64 z) = [b8 z].
Proof.
  intros z. unfold le1, b8. rewrite Z_to_bv_unsigned. change (bv_wrap 64 z) with (z mod 2 ^ 64).
  rewrite (Z_to_le_bytes_mod 1 z 64) by (cbn; lia). reflexivity.
Qed.

Ltac sbfix :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) => rewrite (dstep_le1 z); mem_after_store
  | _ => idtac
  end.
Ltac dst := step; sbfix.

(* a body byte *)
Lemma dstep_rd : forall m a bs i, bytes_at rsegs m a bs -> 0 <= i < Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (Z_to_bv 64 (a + i)) 1 = Some [nth (Z.to_nat i) bs (Z_to_bv 8 0)].
Proof.
  intros m a bs i H Hi.
  change (Z_to_bv 64 (a + i)) with (wa (a + i)).
  rewrite (bytes_at_read rsegs m a bs i 1 H ltac:(lia) ltac:(lia)).
  f_equal. assert (Hj : (Z.to_nat i < length bs)%nat) by lia. clear H Hi. revert Hj. generalize (Z.to_nat i) as j.
  induction bs as [|x bs IH]; intros [|j] Hj; cbn [length] in Hj.
  - lia.
  - lia.
  - reflexivity.
  - cbn [skipn nth]. apply IH. lia.
Qed.

Lemma dstep_byte_at : forall bb i, byte_at (bzl bb) i = bv_unsigned (nth (Z.to_nat i) bb (Z_to_bv 8 0)).
Proof.
  intros bb i. unfold byte_at, bzl.
  transitivity (nth (Z.to_nat i) (map bz bb) (bz (Z_to_bv 8 0))); [reflexivity|]. rewrite map_nth. reflexivity.
Qed.

Lemma dstep_rw_eq : forall segs m A cs cs', rw_cells segs m A cs -> cs = cs' -> rw_cells segs m A cs'.
Proof. intros; subst; assumption. Qed.

Ltac dsolve :=
  unfold bv_eqb, bv_ltu, bv_leu, bv_lts, zxb, sxb; cbn [negb];
  repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end;
  fold_lit_ux; solve_cond_rec.
Ltac take b :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; dsolve]
  end.

(* the frame once o.m is written: the rest of struct owed still unwritten *)
Definition dstep_fo (j0 : list byte) (w10 : word) (body : Z) (oj : list byte) (rest : list cell) (M : spec_msg)
    : list cell :=
  fr_head j0 (Z_to_bv 64 0x103a4) w10 body ++ spec_msg_cells M ++
  CB 44 (firstn 44 (skipn 56 oj)) :: CB 4 (ow_p1 oj) :: CB 8 (firstn 8 (skipn 104 oj)) ::
  CB 1 (firstn 1 (skipn 112 oj)) :: CB 7 (ow_p2 oj) :: rest.

(* memset (&o.e, 0, 44) at 0x13170, 0x13218 or 0x133c0 (addi a2, zero, 0x2c; mv a0, s3; mv a1, zero; jal memset) *)
Lemma dstep_ez : memset_contract ->
  forall (pc : Z) (x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27
          x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (Sp body : Z) (bb j0 je p1 p2 : list byte)
    (w10 : word) (rest : list cell) (M : spec_msg) (next so : Z) (Q : machine_state -> Prop),
  pc = 0x13170 \/ pc = 0x13218 \/ pc = 0x133c0 ->
  0 <= Sp -> Sp + 448 <= 2 ^ 63 -> body + Z.of_nat (length bb) <= Sp ->
  bytes_at rsegs m body bb -> mem_inv rsegs m -> munch [(Sp + 32, Sp + 152)] m0 m -> wmono rsegs m0 m ->
  rw_cells rsegs m Sp (fr_head j0 (Z_to_bv 64 0x103a4) w10 body ++ spec_msg_cells M ++
    CB 44 je :: CB 4 p1 :: C8 (Z_to_bv 64 next) :: C1 (b8 so) :: CB 7 p2 :: rest) ->
  (forall (r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 : word) (m' : word -> option byte),
     munch [(Sp + 32, Sp + 152)] m0 m' -> wmono rsegs m0 m' -> mem_inv rsegs m' -> bytes_at rsegs m' body bb ->
     rw_cells rsegs m' Sp (fr_head j0 (Z_to_bv 64 0x103a4) w10 body ++
       owed_cells p1 p2 (Owed M se_zero 0 next so) ++ rest) ->
     evt rsegs Q (MS (mkR r1 (Z_to_bv 64 Sp) x3 x4 r5 r6 r7 x8 x9 r10 r11 r12 r13 r14 r15 r16 r17 x18
                        (Z_to_bv 64 (Sp + 88)) x20 x21 x22 x23 x24 x25 x26 x27 r28 r29 r30 r31)
                     F (Z_to_bv 64 (pc + 16)) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18
                     (Z_to_bv 64 (Sp + 88)) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Proof.
  intros MSC pc x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m0 m Sp body bb j0 je p1 p2 w10 rest M next so Q Hpc HS0 HS1 HB1 BA MI MU WM FR K.
  cbn [fr_head spec_msg_cells app] in FR.
  destruct Hpc as [-> | [-> | ->]]; do 4 step;
  (eapply (dstep_memset MSC) with (A := Sp) (k := 88%nat) (n := 44%nat)
    (mid := spec_event_cells se_zero ++ [C4 (Z_to_bv 64 0)])
    (W := [(Sp + 32, Sp + 152)]) (m0 := m0) (B := body) (bs := bb);
    [exact FR | lia | reflexivity | cbn; tauto | exact dstep_zev_bytes | exact MI | exact MU | exact WM
    | cbn [inside]; lia | exact BA | lia | ]);
  intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m1 MU1 WM1 MI1 BA1 FR1;
  rewrite ret_pc_even by first [lia | reflexivity];
  (apply K; [exact MU1 | exact WM1 | exact MI1 | exact BA1 | eapply dstep_rw_eq; [exact FR1 | reflexivity]]).
Qed.

(* 0x13168 (sd s0, 0x88(sp); sb s7, 0x90(sp)) to 0x13180 for a step that is no message *)
Lemma dstep_dend : memset_contract ->
  forall (x1 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x25 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (Sp body : Z) (bb j0 oj : list byte) (w10 : word)
    (rest : list cell) (M : spec_msg) (Q : machine_state -> Prop),
  0 <= Sp -> Sp + 448 <= 2 ^ 63 -> body + Z.of_nat (length bb) <= Sp ->
  bytes_at rsegs m body bb -> mem_inv rsegs m -> munch [(Sp + 32, Sp + 152)] m0 m -> wmono rsegs m0 m ->
  rw_cells rsegs m Sp (dstep_fo j0 w10 body oj rest M) ->
  dend Q x3 x4 x22 F fc m0 Sp body bb j0 oj w10 rest (owed0 M) ->
  evt rsegs Q (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 (Z_to_bv 64 (sm_next M)) x9 x10 x11 x12 x13 x14 x15 x16 x17
                     (Z_to_bv 64 (Z.of_nat (length bb))) (Z_to_bv 64 (Sp + 88)) x20 (Z_to_bv 64 body) x22
                     (Z_to_bv 64 (sm_status_out M)) (Z_to_bv 64 (- Z.of_nat (length bb))) x25 (Z_to_bv 64 247)
                     (Z_to_bv 64 1) x28 x29 x30 x31)
                  F (Z_to_bv 64 0x13168) fc None m (seg_rom rsegs)).
Proof.
  intros MSC x1 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x25 x28 x29 x30 x31
    F fc m0 m Sp body bb j0 oj w10 rest M Q HS0 HS1 HB1 BA MI MU WM FR K.
  unfold dstep_fo in FR. cbn [fr_head spec_msg_cells app] in FR.
  dst. dst.
  eapply (dstep_ez MSC 0x13170) with (M := M); [left; reflexivity | exact HS0 | exact HS1 | exact HB1 | exact BA | exact MI
    | exact MU | exact WM | exact FR | ].
  intros r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 m' MU' WM' MI' BA' FR'.
  exact (K r1 r5 r6 r7 _ x9 r10 r11 r12 r13 r14 r15 r16 r17 x20 _ x25 r28 r29 r30 r31 m' MU' WM' MI' BA' FR').
Qed.

Lemma dstep_owed_end : forall b len pos st, sm_code (spec_msg_step b len pos st) <> 1 ->
  owed_at b len pos st = owed0 (spec_msg_step b len pos st).
Proof.
  intros b len pos st H. unfold owed_at. cbv zeta.
  replace (negb (sm_code (spec_msg_step b len pos st) =? 1)) with true by (symmetry; apply Z.eqb_neq in H; rewrite H; reflexivity).
  reflexivity.
Qed.

(* ---- the model, path by path ---- *)
Lemma dstep_m_end : forall b len pos st, len <= pos ->
  spec_msg_step b len pos st = SpecMsg 0 pos 0 pos 0 0 0 0 st 0 0.
Proof. intros b len pos st H. unfold spec_msg_step. replace (len <=? pos) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.

Ltac dend_path E :=
  lazymatch goal with
  | K : sm_code (spec_msg_step ?b ?len ?pos ?st) <> 1 -> _ |- _ =>
      let C := fresh "C" in
      assert (C : sm_code (spec_msg_step b len pos st) <> 1) by (rewrite E; cbv; discriminate);
      specialize (K C); rewrite (dstep_owed_end _ _ _ _ C) in K; rewrite E in K
  end.

Lemma dstep_m_sx : forall b len pos st, pos < len -> byte_at b pos = 240 ->
  spec_msg_step b len pos st =
  (let i := scan_f7 b len (pos + 1) (Z.to_nat (len - (pos + 1))) in
   if i =? len then SpecMsg (-6) pos 0 len 0 0 0 0 0 0 0
   else SpecMsg 1 pos (i + 1 - pos) (i + 1) 240 0 0 0 0 (pos + 1) (i - pos - 1)).
Proof.
  intros b len pos st H H0. unfold spec_msg_step.
  replace (len <=? pos) with false by (symmetry; apply Z.leb_gt; lia). cbv zeta. rewrite H0. reflexivity.
Qed.

(* ---- words ---- *)
Lemma dstep_not : forall x, 0 <= x < 2 ^ 64 ->
  Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 x)) 18446744073709551615) = Z_to_bv 64 (- (x + 1)).
Proof.
  intros x Hx. rewrite unsigned_lit by lia. rewrite lnot_mod64 by lia.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite Z.mod_mod by lia. f_equal. unfold Z.lnot. lia.
Qed.

Lemma dstep_eqb : forall a b, - 2 ^ 63 <= a < 2 ^ 63 -> - 2 ^ 63 <= b < 2 ^ 63 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64).
  destruct (Z.eqb_spec a b) as [->|Hne]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E. apply Hne. Z.div_mod_to_equations. lia.
Qed.

Lemma dstep_sub_r : forall x y, Z_to_bv 64 (x - bv_unsigned (Z_to_bv 64 y)) = Z_to_bv 64 (x - y).
Proof.
  intros. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zminus_mod_idemp_r. reflexivity.
Qed.
Lemma dstep_sub_l : forall x y, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) - y) = Z_to_bv 64 (x - y).
Proof.
  intros. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zminus_mod_idemp_l. reflexivity.
Qed.

(* ---- the F7 scan, 0x130e0 .. 0x130f0 ---- *)
Lemma dstep_scan_hit : forall b len i k, i < len -> byte_at b i = 247 -> scan_f7 b len i (S k) = i.
Proof.
  intros b len i k H H0. cbn [scan_f7]. replace (i <? len) with true by (symmetry; apply Z.ltb_lt; lia).
  rewrite H0. reflexivity.
Qed.
Lemma dstep_scan_miss : forall b len i k, i < len -> byte_at b i <> 247 ->
  scan_f7 b len i (S k) = scan_f7 b len (i + 1) k.
Proof.
  intros b len i k H H0. cbn [scan_f7]. replace (i <? len) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (byte_at b i =? 247) with false by (symmetry; apply Z.eqb_neq; exact H0). reflexivity.
Qed.
Lemma dstep_scan_ge : forall b len k i, i <= scan_f7 b len i k.
Proof.
  intros b len k. induction k as [|k IH]; intros i; cbn [scan_f7]; [lia|].
  destruct (_ && _); [specialize (IH (i + 1)); lia | lia].
Qed.

Lemma dstep_scan :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (body : Z) (bb : list byte)
    (Q : machine_state -> Prop),
  bytes_at rsegs m body bb -> Z.of_nat (length bb) < 2 ^ 26 -> 0 <= body -> body + Z.of_nat (length bb) < 2 ^ 63 ->
  forall (k : nat) (i : Z) (x12 : word),
  0 <= i < Z.of_nat (length bb) -> Z.to_nat (Z.of_nat (length bb) - i) = k ->
  (scan_f7 (bzl bb) (Z.of_nat (length bb)) i k < Z.of_nat (length bb) ->
   forall a1 a2 : word,
   evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (- scan_f7 (bzl bb) (Z.of_nat (length bb)) i k))
                      a1 a2 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 (- Z.of_nat (length bb))) x25
                      (Z_to_bv 64 247) x27 x28 x29 x30 x31)
                   F (Z_to_bv 64 0x13148) fc None m (seg_rom rsegs))) ->
  (scan_f7 (bzl bb) (Z.of_nat (length bb)) i k = Z.of_nat (length bb) ->
   forall a0 a1 a2 : word,
   evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 a0 a1 a2 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                      (Z_to_bv 64 (- Z.of_nat (length bb))) x25 (Z_to_bv 64 247) x27 x28 x29 x30 x31)
                   F (Z_to_bv 64 0x130f4) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (- i)) (Z_to_bv 64 (body + i)) x12 x13 x14 x15 x16 x17
                     x18 x19 x20 x21 x22 x23 (Z_to_bv 64 (- Z.of_nat (length bb))) x25 (Z_to_bv 64 247) x27
                     x28 x29 x30 x31)
                  F (Z_to_bv 64 0x130e0) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x27 x28 x29 x30 x31
    F fc m body bb Q BA HL HB0 HB1 k.
  induction k as [|k IH]; intros i x12 Hi Hk K1 K2; [lia|].
  pose proof (dstep_rd m body bb i BA ltac:(lia)) as RD.
  pose proof (dstep_byte_at bb i) as BAT.
  set (bi := nth (Z.to_nat i) bb (Z_to_bv 8 0)) in *.
  pose proof (bv_unsigned_in_range 8 bi) as Rbi. unfold bv_modulus in Rbi. change (2 ^ Z.of_N 8) with 256 in Rbi.
  step. step.
  destruct (Z.eq_dec (bv_unsigned bi) 247) as [E|E].
  - take true.
    rewrite (dstep_scan_hit (bzl bb) (Z.of_nat (length bb)) i k ltac:(lia) ltac:(lia)) in K1. apply K1. lia.
  - take false.
    rewrite (dstep_scan_miss (bzl bb) (Z.of_nat (length bb)) i k ltac:(lia) ltac:(lia)) in K1, K2.
    step. step. step.
    rewrite (dstep_eqb (- Z.of_nat (length bb)) (- i + -1)) by lia.
    destruct (Z.eq_dec (i + 1) (Z.of_nat (length bb))) as [E1|E1].
    + take false. apply K2.
      replace k with O by lia. cbn [scan_f7]. exact E1.
    + take true.
      replace (Z_to_bv 64 (- i + -1)) with (Z_to_bv 64 (- (i + 1))) by (f_equal; lia).
      replace (Z_to_bv 64 (body + i + 1)) with (Z_to_bv 64 (body + (i + 1))) by (f_equal; lia).
      apply IH; [lia | lia | exact K1 | exact K2].
Qed.

Lemma dstep_cons_eq : forall {A} (a b : A) l l', a = b -> l = l' -> a :: l = b :: l'.
Proof. intros; subst; reflexivity. Qed.

Ltac ceq1 :=
  first [ reflexivity
        | f_equal; f_equal; lia
        | f_equal; unfold b8; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity ].
Ltac ceq := repeat (apply dstep_cons_eq; [ceq1 | ]); reflexivity.

Ltac mcbn := cbn [dstep_fo fr_head spec_msg_cells app sm_code sm_at sm_len sm_next sm_status sm_running sm_d1 sm_d2
                  sm_status_out sm_sysex_at sm_sysex_len].

(* the end for a step that is no message: K is the dend continuation, rewritten to owed0 M *)
Ltac dend_call MSC mm K :=
  eapply (dstep_dend MSC) with (M := mm);
  [ eassumption | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
  | eapply dstep_rw_eq; [eassumption | mcbn; ceq]
  | exact K ].

(* memset (&o.e, 0, 44) at pcv, o.m = mm, o.next = nxv, o.status_out = sov *)
Ltac ez_call MSC pcv mm nxv sov :=
  eapply (dstep_ez MSC pcv) with (M := mm) (next := nxv) (so := sov);
  [ lia | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
  | eapply dstep_rw_eq; [eassumption | mcbn; ceq] | ].

(* the hand-off: E is the model of the step, K the dmid continuation *)
Ltac dmid_fin E K :=
  rewrite E in K; specialize (K eq_refl); cbn [sm_code sm_status] in K;
  specialize (K ltac:(first [reflexivity | lia]));
  unfold dmid in K;
  let r1 := fresh "r1" in let r5 := fresh "r5" in let r6 := fresh "r6" in let r7 := fresh "r7" in
  let r10 := fresh "r10" in let r11 := fresh "r11" in let r12 := fresh "r12" in let r13 := fresh "r13" in
  let r14 := fresh "r14" in let r15 := fresh "r15" in let r16 := fresh "r16" in let r17 := fresh "r17" in
  let r28 := fresh "r28" in let r29 := fresh "r29" in let r30 := fresh "r30" in let r31 := fresh "r31" in
  let mm := fresh "m" in
  intros r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 mm ? ? ? ? ?;
  eapply K; try eassumption; first [intros Hn; exfalso; apply Hn; reflexivity | intros _; reflexivity].

Ltac dend_with MSC E :=
  dend_path E;
  lazymatch goal with K : dend _ _ _ _ _ _ _ _ _ _ _ _ _ _ (owed0 ?M) |- _ => dend_call MSC M K end.

Ltac dmid_with MSC pcv E K :=
  lazymatch type of E with _ = ?M => ez_call MSC pcv M (sm_next M) (sm_status_out M) end;
  dmid_fin E K.

(* ---- the channel message, 0x13310 .. 0x133cc ---- *)

Lemma dstep_not2 : forall z,
  Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 z)) 18446744073709551615) = Z_to_bv 64 (- z - 1).
Proof.
  intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  change 18446744073709551615 with (Z.ones 64).
  replace (- z - 1) with (Z.lnot z) by (unfold Z.lnot; lia).
  apply Z.bits_inj'. intros n Hn.
  destruct (Z_lt_le_dec n 64).
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite Z.lxor_spec, Z.ones_spec_low by lia.
    rewrite Z.mod_pow2_bits_low by lia. rewrite Z.lnot_spec by lia. destruct (Z.testbit z n); reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma dstep_neg : forall z, Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 z)) = Z_to_bv 64 (- z).
Proof.
  intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zminus_mod_idemp_r. reflexivity.
Qed.

Lemma dstep_sub : forall a b,
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 a) - bv_unsigned (Z_to_bv 64 b)) = Z_to_bv 64 (a - b).
Proof.
  intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r. reflexivity.
Qed.

(* snez (sltu zero, x) of a signed 64-bit value *)
Lemma dstep_snez : forall z, -2^63 <= z < 2^63 ->
  v_sltu (Z_to_bv 64 0) (Z_to_bv 64 z) = Z_to_bv 64 (Z.b2z (negb (z =? 0))).
Proof.
  intros z Hz. rewrite v_sltu_b2z. f_equal. f_equal.
  rewrite !unsigned_lit_wrap. change (0 mod 2^64) with 0.
  replace (2^64) with 18446744073709551616 by reflexivity.
  replace (2^63) with 9223372036854775808 in Hz by reflexivity.
  destruct (Z.eqb_spec z 0) as [->|N]; [reflexivity|].
  apply Z.ltb_lt. Z.div_mod_to_equations. lia.
Qed.

Lemma dstep_all256 : forall (P : Z -> bool), forallb P (map Z.of_nat (seq 0 256)) = true ->
  forall z, 0 <= z < 256 -> P z = true.
Proof.
  intros P H z Hz. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat z).
  split; [lia | apply in_seq; lia].
Qed.

(* slli 56 then srai 56, and bltz: the byte's bit 7 *)
Lemma dstep_bf_srai : forall z, 0 <= z < 256 ->
  bv_lts (Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl z 56))) 56)) (Z_to_bv 64 0) = (128 <=? z).
Proof.
  intros z Hz. apply Bool.eqb_prop.
  exact (dstep_all256 (fun z => Bool.eqb (bv_lts (Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl z 56))) 56))
    (Z_to_bv 64 0)) (128 <=? z)) ltac:(vm_compute; reflexivity) z Hz).
Qed.

(* slli 56 and bltz *)
Lemma dstep_bf_sll : forall z, 0 <= z < 256 ->
  bv_lts (Z_to_bv 64 (Z.shiftl z 56)) (Z_to_bv 64 0) = (128 <=? z).
Proof.
  intros z Hz. apply Bool.eqb_prop.
  exact (dstep_all256 (fun z => Bool.eqb (bv_lts (Z_to_bv 64 (Z.shiftl z 56)) (Z_to_bv 64 0)) (128 <=? z))
    ltac:(vm_compute; reflexivity) z Hz).
Qed.

(* srli 7 *)
Lemma dstep_bf_srl7 : forall z, 0 <= z < 256 -> Z.shiftr z 7 = (if 128 <=? z then 1 else 0).
Proof.
  intros z Hz. apply Z.eqb_eq.
  exact (dstep_all256 (fun z => Z.shiftr z 7 =? (if 128 <=? z then 1 else 0)) ltac:(vm_compute; reflexivity) z Hz).
Qed.

(* andi 0xe0 *)
Lemma dstep_bf_land : forall z, 0 <= z < 256 -> 0 <= Z.land z 224 < 256.
Proof.
  intros z Hz.
  pose proof (dstep_all256 (fun z => (0 <=? Z.land z 224) && (Z.land z 224 <? 256)) ltac:(vm_compute; reflexivity)
    z Hz) as H.
  apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

(* the length test of spec.h:341 on the status's high nibble, as the code does it on bits 7..5 *)
Lemma dstep_bf_n : forall z, 0 <= z < 256 ->
  ((Z.land z 240 =? 192) || (Z.land z 240 =? 208)) = (Z.land z 224 =? 192).
Proof.
  intros z Hz. apply Bool.eqb_prop.
  exact (dstep_all256 (fun z => Bool.eqb ((Z.land z 240 =? 192) || (Z.land z 240 =? 208)) (Z.land z 224 =? 192))
    ltac:(vm_compute; reflexivity) z Hz).
Qed.

Lemma dstep_b8_bz : forall b : byte, Z_to_bv 8 (bz b) = b.
Proof.
  intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* lb and bltz: the byte's bit 7 *)
Lemma dstep_lts_sxb : forall b : byte, bv_lts (sxb b) (Z_to_bv 64 0) = (128 <=? bz b).
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8) with 256 in R.
  pose proof (dstep_all256 (fun z => Bool.eqb (bv_lts (sxb (Z_to_bv 8 z)) (Z_to_bv 64 0)) (128 <=? z))
    ltac:(vm_compute; reflexivity) (bz b) R) as H.
  cbv beta in H. apply Bool.eqb_prop in H. rewrite dstep_b8_bz in H. exact H.
Qed.

(* not, slli 56, srli 63: running = lead < 0x80 *)
Lemma dstep_bf_run : forall z, 0 <= z < 256 ->
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (- z - 1))) 56))) 63) =
  Z_to_bv 64 (if z <? 128 then 1 else 0).
Proof.
  intros z Hz.
  pose proof (dstep_all256 (fun z => bv_eqb (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64
    (Z.shiftl (bv_unsigned (Z_to_bv 64 (- z - 1))) 56))) 63)) (Z_to_bv 64 (if z <? 128 then 1 else 0)))
    ltac:(vm_compute; reflexivity) z Hz) as H.
  cbv beta in H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H.
Qed.

Lemma dstep_m_status : forall b len pos st, pos < len -> 240 < byte_at b pos ->
  spec_msg_step b len pos st =
  {| sm_code := -8; sm_at := pos; sm_len := 0; sm_next := pos + 1; sm_status := 0; sm_running := 0; sm_d1 := 0;
     sm_d2 := 0; sm_status_out := 0; sm_sysex_at := 0; sm_sysex_len := 0 |}.
Proof.
  intros b len pos st H1 H2. unfold spec_msg_step. cbv beta zeta.
  rewrite (proj2 (Z.leb_gt len pos) H1), (proj2 (Z.eqb_neq (byte_at b pos) 240) ltac:(lia)),
    (proj2 (Z.ltb_lt 240 (byte_at b pos)) H2). reflexivity.
Qed.

Lemma dstep_m_nost : forall b len pos, pos < len -> byte_at b pos < 128 ->
  spec_msg_step b len pos 0 =
  {| sm_code := -7; sm_at := pos; sm_len := 0; sm_next := pos + 1; sm_status := 0; sm_running := 0; sm_d1 := 0;
     sm_d2 := 0; sm_status_out := 0; sm_sysex_at := 0; sm_sysex_len := 0 |}.
Proof.
  intros b len pos H1 H2. unfold spec_msg_step. cbv beta zeta.
  rewrite (proj2 (Z.leb_gt len pos) H1), (proj2 (Z.eqb_neq (byte_at b pos) 240) ltac:(lia)),
    (proj2 (Z.ltb_ge 240 (byte_at b pos)) ltac:(lia)), (proj2 (Z.ltb_lt (byte_at b pos) 128) H2). reflexivity.
Qed.

(* a channel message: lead is the byte at pos, stv the status in force, pos + dz the first data byte, nb the
   test for one data byte (spec.h:339-363) *)
Lemma dstep_m_chan : forall b len pos st lead stv dz nb,
  pos < len -> byte_at b pos = lead -> 0 <= lead < 240 -> (128 <= lead \/ st <> 0) ->
  stv = (if 128 <=? lead then lead else st) -> dz = (if 128 <=? lead then 1 else 0) ->
  ((Z.land stv 240 =? 192) || (Z.land stv 240 =? 208)) = nb ->
  spec_msg_step b len pos st =
  if len <? pos + dz + (if nb then 1 else 2) then
    {| sm_code := -6; sm_at := pos; sm_len := 0; sm_next := len; sm_status := 0; sm_running := 0; sm_d1 := 0;
       sm_d2 := 0; sm_status_out := st; sm_sysex_at := 0; sm_sysex_len := 0 |}
  else if 128 <=? byte_at b (pos + dz) then
    {| sm_code := -6; sm_at := pos; sm_len := 0; sm_next := pos + dz; sm_status := 0; sm_running := 0;
       sm_d1 := 0; sm_d2 := 0; sm_status_out := 0; sm_sysex_at := 0; sm_sysex_len := 0 |}
  else if negb nb && (128 <=? byte_at b (pos + dz + 1)) then
    {| sm_code := -6; sm_at := pos; sm_len := 0; sm_next := pos + dz + 1; sm_status := 0; sm_running := 0;
       sm_d1 := 0; sm_d2 := 0; sm_status_out := 0; sm_sysex_at := 0; sm_sysex_len := 0 |}
  else
    {| sm_code := 1; sm_at := pos; sm_len := pos + dz + (if nb then 1 else 2) - pos;
       sm_next := pos + dz + (if nb then 1 else 2); sm_status := stv;
       sm_running := if lead <? 128 then 1 else 0; sm_d1 := byte_at b (pos + dz);
       sm_d2 := if nb then 0 else byte_at b (pos + dz + 1); sm_status_out := stv; sm_sysex_at := 0;
       sm_sysex_len := 0 |}.
Proof.
  intros b len pos st lead stv dz nb H1 H2 H3 H4 Hstv Hdz Hnb.
  unfold spec_msg_step. cbv beta zeta.
  rewrite (proj2 (Z.leb_gt len pos) H1), H2.
  rewrite (proj2 (Z.eqb_neq lead 240)) by lia. rewrite (proj2 (Z.ltb_ge 240 lead)) by lia.
  revert Hnb. subst stv dz.
  destruct (Z.leb_spec 128 lead) as [Hh|Hh]; intros Hnb.
  - rewrite (proj2 (Z.ltb_ge lead 128)) by lia. rewrite Hnb. cbv beta iota.
    destruct nb; reflexivity.
  - rewrite (proj2 (Z.ltb_lt lead 128)) by lia. rewrite (proj2 (Z.eqb_neq st 0)) by lia. rewrite Hnb.
    cbv beta iota. rewrite !Z.add_0_r. destruct nb; reflexivity.
Qed.

(* the struct spec_msg after the stores of at and status_out (0x130ac, 0x130b0) *)
Definition dstep_m1 (pos status : Z) : spec_msg := SpecMsg 0 pos 0 0 0 0 0 0 status 0 0.

Ltac sstep := step; try (rewrite dstep_le1; mem_after_store_opt); rewrite ?dstep_not2, ?dstep_neg, ?dstep_sub.
Ltac rds i D ED := lazymatch goal with
  | BA : bytes_at rsegs ?mm ?a ?bs |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let HR := fresh "HR" in pose proof (dstep_rd mm a bs i BA ltac:(lia)) as HR;
      step;
      set (D := nth (Z.to_nat i) bs (Z_to_bv 8 0)) in *;
      let RL := fresh "RL" in
      pose proof (bv_unsigned_in_range 8 D) as RL; unfold bv_modulus in RL;
      change (2 ^ Z.of_N 8) with 256 in RL; change (bv_unsigned D) with (bz D) in RL;
      assert (ED : byte_at (bzl bs) i = bz D) by (apply dstep_byte_at);
      clear HR
  end.
Ltac rd2 i D := lazymatch goal with
  | BA : bytes_at rsegs ?mm ?a ?bs |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let HR := fresh "HR" in pose proof (dstep_rd mm a bs i BA ltac:(lia)) as HR;
      change (nth (Z.to_nat i) bs (Z_to_bv 8 0)) with D in HR;
      step; change (zxb D) with (Z_to_bv 64 (bz D)); clear HR
  end.
Ltac run_to t := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) => tryif constr_eq p t then fail else sstep
  end).
Ltac zdec := repeat match goal with
  | |- context [?a <=? ?b] => first [rewrite (proj2 (Z.leb_le a b)) by lia | rewrite (proj2 (Z.leb_gt a b)) by lia]
  | |- context [?a <? ?b] => first [rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia]
  end.
Ltac mfin := zdec; cbv beta iota; cbn [negb andb]; first [reflexivity | f_equal; first [reflexivity | lia]].

Lemma dstep_chan2 : memset_contract ->
  forall (x1 x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x22 x25 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
    (Sp body pos status : Z) (bb j0 oj : list byte) (w10 : word) (rest : list cell)
    (Q : machine_state -> Prop) (L : byte) (stv dz : Z),
  seg_ok Sp body bb -> 0 <= pos < Z.of_nat (length bb) -> 0 <= status < 240 ->
  byte_at (bzl bb) pos = bz L -> 0 <= bz L < 240 -> (128 <= bz L \/ status <> 0) ->
  stv = (if 128 <=? bz L then bz L else status) -> dz = (if 128 <=? bz L then 1 else 0) ->
  (sm_code (spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos status) <> 1 ->
   dend Q x3 x4 x22 F fc m0 Sp body bb j0 oj w10 rest (owed_at (bzl bb) (Z.of_nat (length bb)) pos status)) ->
  (sm_code (spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos status) = 1 ->
   sm_status (spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos status) <> 240 ->
   dmid Q 0x133d0 x3 x4 x22 F fc m0 Sp body bb j0 oj w10 rest pos
     (spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos status)) ->
  munch [(Sp + 32, Sp + 152)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> bytes_at rsegs m body bb ->
  rw_cells rsegs m Sp (dstep_fo j0 w10 body oj rest (dstep_m1 pos status)) ->
  evt rsegs Q
    (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 (Z_to_bv 64 pos) (Z_to_bv 64 stv) (Z_to_bv 64 (bz L))
           x11 x12 x13 x14 x15 x16 x17
           (Z_to_bv 64 (Z.of_nat (length bb))) (Z_to_bv 64 (Sp + 88)) x20 (Z_to_bv 64 body) x22
           (Z_to_bv 64 status) (Z_to_bv 64 (- Z.of_nat (length bb))) x25 (Z_to_bv 64 247) (Z_to_bv 64 1)
           x28 x29 x30 x31)
        F (Z_to_bv 64 0x1331c) fc None m (seg_rom rsegs)).
Proof.
  intros MSC x1 x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x22 x25 x28 x29 x30 x31
    F fc m0 m Sp body pos status bb j0 oj w10 rest Q L stv dz SEG Hpos Hst EL HL HLs Hsv Hdz Kend Kch MU WM MI BA FR.
  pose proof SEG as (HS0 & HS1 & HB0 & HB1 & HLn).
  unfold dstep_m1 in FR.
  cbn [dstep_fo fr_head spec_msg_cells app sm_code sm_at sm_len sm_next sm_status sm_running sm_d1 sm_d2
       sm_status_out sm_sysex_at sm_sysex_len] in FR.
  assert (Hstv : 0 <= stv < 256) by (subst stv; destruct (128 <=? bz L); lia).
  assert (Hstv240 : stv < 240) by (subst stv; destruct (128 <=? bz L); lia).
  assert (Hdz' : Z.shiftr (bz L) 7 = dz) by (rewrite dstep_bf_srl7 by lia; subst dz; reflexivity).
  assert (Hdz2 : dz = 0 \/ dz = 1) by (subst dz; destruct (128 <=? bz L); lia).
  pose proof (dstep_bf_land stv Hstv) as Hland.
  sstep. rewrite (unsigned_lit (bz L)) by lia. rewrite Hdz'.
  sstep. rewrite (unsigned_lit stv) by lia.
  sstep. sstep. sstep.
  rewrite dstep_snez by lia.
  destruct (Z.eq_dec (Z.land stv 224) 192) as [N1|N2].
  - (* one data byte: C0 .. DF *)
    assert (Hnb : ((Z.land stv 240 =? 192) || (Z.land stv 240 =? 208)) = true)
      by (rewrite dstep_bf_n by lia; apply Z.eqb_eq; exact N1).
    pose proof (dstep_m_chan (bzl bb) (Z.of_nat (length bb)) pos status (bz L) stv dz true
      ltac:(lia) EL ltac:(lia) HLs Hsv Hdz Hnb) as Em.
    rewrite N1. change (Z.b2z (negb (192 + -192 =? 0))) with 0.
    sstep. sstep. step.
    destruct (Z_lt_le_dec (Z.of_nat (length bb)) (1 + (pos + dz))) as [Hs|Hs].
    + (* cut short at the end of the body *)
      take true. run_to 0x13168.
      assert (E : spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos status =
        {| sm_code := -6; sm_at := pos; sm_len := 0; sm_next := Z.of_nat (length bb); sm_status := 0;
           sm_running := 0; sm_d1 := 0; sm_d2 := 0; sm_status_out := status; sm_sysex_at := 0; sm_sysex_len := 0 |})
        by (rewrite Em; mfin).
      dend_with MSC E.
    + take false. sstep. sstep.
      rds (pos + dz) D0 ED0. step. rewrite dstep_lts_sxb.
      destruct (Z_lt_le_dec (bz D0) 128) as [D0l|D0h].
      2: { (* a status byte where d1 is due *)
        take true. run_to 0x13168. rewrite Z.opp_involutive in *.
        assert (E : spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos status =
          {| sm_code := -6; sm_at := pos; sm_len := 0; sm_next := pos + dz; sm_status := 0;
             sm_running := 0; sm_d1 := 0; sm_d2 := 0; sm_status_out := 0; sm_sysex_at := 0; sm_sysex_len := 0 |})
          by (rewrite Em, ED0; mfin).
        dend_with MSC E. }
      take false. sstep. sstep. sstep. step. take false.
      sstep. sstep. sstep.
      rewrite (dstep_bf_run (bz L)) by lia.
      sstep. sstep. sstep. sstep.
      rd2 (pos + dz) D0.
      sstep. sstep. step. take false.
      run_to 0x133c0.
      assert (E : spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos status =
        {| sm_code := 1; sm_at := pos; sm_len := 1 + (pos + dz) - pos; sm_next := 1 + (pos + dz); sm_status := stv;
           sm_running := if bz L <? 128 then 1 else 0; sm_d1 := bz D0; sm_d2 := 0; sm_status_out := stv;
           sm_sysex_at := 0; sm_sysex_len := 0 |})
        by (rewrite Em, ED0; mfin).
      dmid_with MSC 0x133c0 E Kch.
  - (* two data bytes *)
    assert (Hnb : ((Z.land stv 240 =? 192) || (Z.land stv 240 =? 208)) = false)
      by (rewrite dstep_bf_n by lia; apply Z.eqb_neq; exact N2).
    pose proof (dstep_m_chan (bzl bb) (Z.of_nat (length bb)) pos status (bz L) stv dz false
      ltac:(lia) EL ltac:(lia) HLs Hsv Hdz Hnb) as Em.
    rewrite (proj2 (Z.eqb_neq (Z.land stv 224 + -192) 0)) by lia. change (Z.b2z (negb false)) with 1.
    sstep. sstep. step.
    destruct (Z_lt_le_dec (Z.of_nat (length bb)) (2 + (pos + dz))) as [Hs|Hs].
    + (* cut short at the end of the body *)
      take true. run_to 0x13168.
      assert (E : spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos status =
        {| sm_code := -6; sm_at := pos; sm_len := 0; sm_next := Z.of_nat (length bb); sm_status := 0;
           sm_running := 0; sm_d1 := 0; sm_d2 := 0; sm_status_out := status; sm_sysex_at := 0; sm_sysex_len := 0 |})
        by (rewrite Em; mfin).
      dend_with MSC E.
    + take false. sstep. sstep.
      rds (pos + dz) D0 ED0. step. rewrite dstep_lts_sxb.
      destruct (Z_lt_le_dec (bz D0) 128) as [D0l|D0h].
      2: { (* a status byte where d1 is due *)
        take true. run_to 0x13168. rewrite Z.opp_involutive in *.
        assert (E : spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos status =
          {| sm_code := -6; sm_at := pos; sm_len := 0; sm_next := pos + dz; sm_status := 0;
             sm_running := 0; sm_d1 := 0; sm_d2 := 0; sm_status_out := 0; sm_sysex_at := 0; sm_sysex_len := 0 |})
          by (rewrite Em, ED0; mfin).
        dend_with MSC E. }
      take false. sstep. sstep. sstep. step. take true.
      rds (pos + dz + 1) D1 ED1. step. rewrite dstep_lts_sxb.
      destruct (Z_lt_le_dec (bz D1) 128) as [D1l|D1h].
      2: { (* a status byte where d2 is due *)
        take true. run_to 0x13168.
        replace (- (- (pos + dz) + -1)) with (pos + dz + 1) in * by lia.
        assert (E : spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos status =
          {| sm_code := -6; sm_at := pos; sm_len := 0; sm_next := pos + dz + 1; sm_status := 0;
             sm_running := 0; sm_d1 := 0; sm_d2 := 0; sm_status_out := 0; sm_sysex_at := 0; sm_sysex_len := 0 |})
          by (rewrite Em, ED0, ED1; mfin).
        dend_with MSC E. }
      take false. sstep. sstep. sstep. step. take false.
      sstep. sstep. sstep.
      rewrite (dstep_bf_run (bz L)) by lia.
      sstep. sstep. sstep. sstep.
      rd2 (pos + dz) D0.
      sstep. sstep. step. take true.
      rd2 (pos + dz + 1) D1.
      run_to 0x133c0.
      assert (E : spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos status =
        {| sm_code := 1; sm_at := pos; sm_len := 2 + (pos + dz) - pos; sm_next := 2 + (pos + dz); sm_status := stv;
           sm_running := if bz L <? 128 then 1 else 0; sm_d1 := bz D0; sm_d2 := bz D1; sm_status_out := stv;
           sm_sysex_at := 0; sm_sysex_len := 0 |})
        by (rewrite Em, ED0, ED1; mfin).
      dmid_with MSC 0x133c0 E Kch.
Qed.

(* ---- a channel message, 0x13310: s1 = the status in force, then dstep_chan2 ---- *)
Lemma dstep_chan : memset_contract ->
  forall (x1 x3 x4 x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x20 x22 x25 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
    (Sp body pos status : Z) (bb j0 oj : list byte) (w10 : word) (rest : list cell)
    (Q : machine_state -> Prop) (L : byte),
  seg_ok Sp body bb -> 0 <= pos < Z.of_nat (length bb) -> 0 <= status < 240 ->
  byte_at (bzl bb) pos = bz L -> 0 <= bz L < 240 -> (128 <= bz L \/ status <> 0) ->
  (sm_code (spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos status) <> 1 ->
   dend Q x3 x4 x22 F fc m0 Sp body bb j0 oj w10 rest (owed_at (bzl bb) (Z.of_nat (length bb)) pos status)) ->
  (sm_code (spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos status) = 1 ->
   sm_status (spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos status) <> 240 ->
   dmid Q 0x133d0 x3 x4 x22 F fc m0 Sp body bb j0 oj w10 rest pos
     (spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos status)) ->
  munch [(Sp + 32, Sp + 152)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> bytes_at rsegs m body bb ->
  rw_cells rsegs m Sp (dstep_fo j0 w10 body oj rest (dstep_m1 pos status)) ->
  evt rsegs Q
    (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 (Z_to_bv 64 pos) x9 (Z_to_bv 64 (bz L))
           (Z_to_bv 64 (Z.shiftl (bz L) 56)) x12 x13 x14 x15 x16 x17
           (Z_to_bv 64 (Z.of_nat (length bb))) (Z_to_bv 64 (Sp + 88)) x20 (Z_to_bv 64 body) x22
           (Z_to_bv 64 status) (Z_to_bv 64 (- Z.of_nat (length bb))) x25 (Z_to_bv 64 247) (Z_to_bv 64 1)
           x28 x29 x30 x31)
        F (Z_to_bv 64 0x13310) fc None m (seg_rom rsegs)).
Proof.
  intros MSC x1 x3 x4 x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x20 x22 x25 x28 x29 x30 x31
    F fc m0 m Sp body pos status bb j0 oj w10 rest Q L SEG Hpos Hst EL HL HLs Kend Kch MU WM MI BA FR.
  sstep. step.
  rewrite (dstep_bf_sll (bz L)) by lia.
  destruct (Z_lt_le_dec (bz L) 128) as [Hl128|Hg128].
  - take false. sstep.
    eapply (dstep_chan2 MSC) with (L := L) (stv := status) (dz := 0); try eassumption; try lia.
    + rewrite (proj2 (Z.leb_gt 128 (bz L))) by lia. reflexivity.
    + rewrite (proj2 (Z.leb_gt 128 (bz L))) by lia. reflexivity.
  - take true.
    eapply (dstep_chan2 MSC) with (L := L) (stv := bz L) (dz := 1); try eassumption; try lia.
    + rewrite (proj2 (Z.leb_le 128 (bz L))) by lia. reflexivity.
    + rewrite (proj2 (Z.leb_le 128 (bz L))) by lia. reflexivity.
Qed.

Theorem dstep_holds : dstep_stmt.
Proof.
  unfold dstep_stmt.
  intros MSC x1 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x25 x28 x29 x30 x31
    F fc m Sp body pos status bb j0 oj w10 rest Q SOK Hpos Hst BA FR MI Kend Ksys Kch.
  pose proof SOK as (HS0 & HS1 & HB0 & HB1 & HL).
  pose proof (proj1 (proj1 FR)) as WF. apply cells_wf_app in WF. destruct WF as [_ [WF _]]. cbn [cell_wf] in WF.
  apply (rw_cells_split_CB rsegs m Sp _ 120 oj rest [56; 44; 4; 8; 1; 7]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells fr_head app] in FR. rewrite !skipn_skipn in FR. cbn [Nat.add] in FR.
  rewrite (firstn_all2 (n := 7) (skipn 113 oj)) in FR by (rewrite length_skipn; lia).
  change (skipn 113 oj) with (ow_p2 oj) in FR. change (firstn 4 (skipn 100 oj)) with (ow_p1 oj) in FR.
  pose proof (munch_refl [(Sp + 32, Sp + 152)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 4 step.
  eapply (dstep_memset MSC) with (A := Sp) (k := 32%nat) (n := 56%nat) (mid := spec_msg_cells dstep_zmsg)
    (W := [(Sp + 32, Sp + 152)]) (m0 := m) (B := body) (bs := bb);
    [exact FR | lia | reflexivity | cbn; tauto | exact dstep_zmsg_bytes | exact MI | exact MU | exact WM
    | cbn [inside]; lia | exact BA | lia | ].
  clear FR MU WM MI BA.
  intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m1 MU WM MI BA FR.
  rewrite ret_pc_even by first [lia | reflexivity].
  cbv [dstep_splice csize Nat.eqb Nat.sub app] in FR. cbn [spec_msg_cells dstep_zmsg sm_code sm_at sm_len sm_next sm_status sm_running sm_d1 sm_d2 sm_status_out sm_sysex_at sm_sysex_len app] in FR.
  step. dst.
  step.
  destruct (Z_lt_le_dec pos (Z.of_nat (length bb))) as [Hlt|Hge].
  2:{ (* at >= len: the end, code 0 *)
    take true. step. step.
    pose proof (dstep_m_end (bzl bb) (Z.of_nat (length bb)) pos status Hge) as E.
    dend_path E.
    eapply (dstep_dend MSC) with (M := SpecMsg 0 pos 0 pos 0 0 0 0 status 0 0);
      [exact HS0 | exact HS1 | exact HB1 | exact BA | exact MI | exact MU | exact WM | exact FR | exact Kend]. }
  take false.
  step.
  pose proof (dstep_rd m1 body bb pos BA ltac:(lia)) as RD.
  step.
  set (bt := nth (Z.to_nat pos) bb (Z_to_bv 8 0)) in *.
  pose proof (bv_unsigned_in_range 8 bt) as Rbt. unfold bv_modulus in Rbt. change (2 ^ Z.of_N 8) with 256 in Rbt.
  pose proof (dstep_byte_at bb pos) as BAT. fold bt in BAT.
  step. step.
  destruct (Z.eq_dec (bv_unsigned bt) 240) as [L240|N240].
  - (* a sysex *)
    take false.
    pose proof (dstep_m_sx (bzl bb) (Z.of_nat (length bb)) pos status Hlt ltac:(lia)) as E0.
    do 3 step.
    destruct (Z_lt_le_dec (pos + 1) (Z.of_nat (length bb))) as [Hlt1|Hge1].
    2:{ (* no byte after F0: truncated *)
      take true. dst. step.
      take false.
      do 5 step.
      replace (Z.to_nat (Z.of_nat (length bb) - (pos + 1))) with O in E0 by lia.
      cbn [scan_f7] in E0. cbv zeta in E0.
      replace (pos + 1 =? Z.of_nat (length bb)) with true in E0 by (symmetry; apply Z.eqb_eq; lia).
      dend_path E0.
      dend_call MSC (SpecMsg (-6) pos 0 (Z.of_nat (length bb)) 0 0 0 0 0 0 0) Kend. }
    take false.
    do 3 step.
    rewrite (dstep_not pos) by lia.
    replace (Z_to_bv 64 (body + 1 + pos)) with (Z_to_bv 64 (body + (pos + 1))) by (f_equal; lia).
    eapply (dstep_scan _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 body bb Q BA HL ltac:(lia) ltac:(lia)
      _ (pos + 1) _ ltac:(lia) eq_refl).
    + (* F7 at i0 < len: the message *)
      intros Hi a1'' a2''.
      set (i0 := scan_f7 (bzl bb) (Z.of_nat (length bb)) (pos + 1) (Z.to_nat (Z.of_nat (length bb) - (pos + 1)))) in *.
      pose proof (dstep_scan_ge (bzl bb) (Z.of_nat (length bb)) (Z.to_nat (Z.of_nat (length bb) - (pos + 1))) (pos + 1))
        as Hge0. fold i0 in Hge0.
      cbv zeta in E0. replace (i0 =? Z.of_nat (length bb)) with false in E0 by (symmetry; apply Z.eqb_neq; lia).
      step. rewrite dstep_sub_r. replace (Z_to_bv 64 (0 - - i0)) with (Z_to_bv 64 i0) by (f_equal; lia).
      dst. step. take true.
      step. rewrite (dstep_not pos) by lia.
      step. replace (Z_to_bv 64 (i0 + - (pos + 1))) with (Z_to_bv 64 (i0 - pos - 1)) by (f_equal; lia).
      step. step. rewrite dstep_sub_l, dstep_sub_r.
      step. step. step. step. dst. step. step. step. dst.
      ez_call MSC 0x13218 (SpecMsg 1 pos (i0 + 1 - pos) (i0 + 1) 240 0 0 0 0 (pos + 1) (i0 - pos - 1)) (i0 + 1) 0.
      dmid_fin E0 Ksys.
    + (* no F7: truncated *)
      intros Hi a0'' a1'' a2''.
      dst. step. do 5 step.
      cbv zeta in E0. rewrite Hi, Z.eqb_refl in E0.
      dend_path E0.
      dend_call MSC (SpecMsg (-6) pos 0 (Z.of_nat (length bb)) 0 0 0 0 0 0 0) Kend.
  - (* not F0 *)
    take true.
    change (zxb bt) with (Z_to_bv 64 (bz bt)).
    assert (Rbz : 0 <= bz bt < 256) by exact Rbt. assert (Nbz : bz bt <> 240) by exact N240.
    change (bv_unsigned bt) with (bz bt) in BAT.
    step. step.
    destruct (Z_lt_le_dec (bz bt) 241) as [H241|H241].
    2:{ (* F1 .. FF *)
      take false. step. step. step. step. step. dst. step.
      pose proof (dstep_m_status (bzl bb) (Z.of_nat (length bb)) pos status Hlt ltac:(unfold bz in *; lia)) as E.
      dend_with MSC E. }
    take true.
    step. step.
    rewrite (unsigned_lit (bz bt)) by (unfold bz; lia).
    destruct (Z.eq_dec status 0) as [S0|S0].
    + subst status. take false. step. step.
      rewrite dstep_bf_srai by (unfold bz; lia).
      destruct (Z_lt_le_dec (bz bt) 128) as [H128|H128].
      * (* a data byte and no running status *)
        take false. do 6 step.
        pose proof (dstep_m_nost (bzl bb) (Z.of_nat (length bb)) pos Hlt ltac:(unfold bz in *; lia)) as E.
        dend_with MSC E.
      * take true.
        eapply (dstep_chan MSC) with (L := bt); try eassumption; try (unfold bz in *; lia).
    + take true.
      eapply (dstep_chan MSC) with (L := bt); try eassumption; try (unfold bz in *; lia).
Qed.
