From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Prog Require Import memset_c memcpy_c check_gate_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- cell-list plumbing ---- *)

Lemma rwc_cons : forall segs m A c cs, rw_cells segs m A (c :: cs) ->
  rw_cells segs m A [c] /\ rw_cells segs m (A + Z.of_nat (csize c)) cs.
Proof.
  intros segs m A c cs [[[Hc Hwf] Hb] (W0 & W1 & Hw)].
  cbn [cells_bytes cells_size] in Hb, W1, Hw. apply bytes_at_app in Hb as [Hb1 Hb2].
  rewrite cbytes_length in Hb2 by exact Hc.
  split.
  - split; [split; [split; [exact Hc | exact I] | cbn [cells_bytes]; rewrite app_nil_r; exact Hb1]|].
    cbn [cells_size]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split; [exact Hwf | exact Hb2]|]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (csize c) + i) with (A + (Z.of_nat (csize c) + i)) by lia. apply Hw. lia.
Qed.

Lemma rwc_join : forall segs m A c cs, rw_cells segs m A [c] ->
  rw_cells segs m (A + Z.of_nat (csize c)) cs -> rw_cells segs m A (c :: cs).
Proof.
  intros segs m A c cs [[[Hc _] Hb1] (W0 & W1 & Hw1)] [[Hwf Hb2] (V0 & V1 & Hw2)].
  cbn [cells_bytes cells_size] in Hb1, W1, Hw1. rewrite app_nil_r in Hb1.
  split; [split; [split; [exact Hc | exact Hwf]|]|].
  - cbn [cells_bytes]. apply bytes_at_app. split; [exact Hb1|]. rewrite cbytes_length by exact Hc. exact Hb2.
  - cbn [cells_size]. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i (Z.of_nat (csize c))) as [H|H]; [apply Hw1; lia|].
    replace (A + i) with (A + Z.of_nat (csize c) + (i - Z.of_nat (csize c))) by lia. apply Hw2. lia.
Qed.

Lemma firstn1_nth : forall (l : list byte) k d, (k < length l)%nat -> firstn 1 (skipn k l) = [nth k l d].
Proof.
  induction l as [|x l IH]; intros [|k] d H; cbn [length] in H; try lia; [reflexivity|].
  cbn [skipn nth]. apply IH. lia.
Qed.

Lemma rwc_cb : forall segs m A n (js : list byte), length js = n ->
  bytes_at segs m A js -> wr_at segs m A (Z.of_nat n) -> rw_cells segs m A [CB n js].
Proof.
  intros segs m A n js Hl Hb Hw. split.
  - split; [cbn [cells_wf cell_wf]; split; [exact Hl | exact I]|].
    cbn [cells_bytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hw.
Qed.

Lemma rwc_cb_inv : forall segs m A n (js : list byte), rw_cells segs m A [CB n js] ->
  length js = n /\ bytes_at segs m A js /\ wr_at segs m A (Z.of_nat n).
Proof.
  intros segs m A n js [[Hwf Hb] Hw].
  cbn [cells_wf cell_wf] in Hwf. cbn [cells_bytes] in Hb. rewrite app_nil_r in Hb.
  cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw.
  split; [apply Hwf | split; [exact Hb | exact Hw]].
Qed.

Lemma rwc_cb_split : forall segs m A n js k, rw_cells segs m A [CB n js] -> (k <= n)%nat ->
  rw_cells segs m A [CB k (firstn k js)] /\ rw_cells segs m (A + Z.of_nat k) [CB (n - k) (skipn k js)].
Proof.
  intros segs m A n js k H Hk. destruct (rwc_cb_inv _ _ _ _ _ H) as (Hl & Hb & Hw).
  rewrite <- (firstn_skipn k js) in Hb. apply bytes_at_app in Hb as [Hb1 Hb2].
  rewrite firstn_length_le in Hb2 by lia.
  destruct Hw as (W0 & W1 & Hw).
  split.
  - apply rwc_cb; [rewrite firstn_length_le by lia; reflexivity | exact Hb1 |].
    split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - apply rwc_cb; [rewrite length_skipn; lia | exact Hb2 |].
    split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat k + i) with (A + (Z.of_nat k + i)) by lia. apply Hw. lia.
Qed.

Lemma rwc_cb_join : forall segs m A k js1 n2 js2, rw_cells segs m A [CB k js1] ->
  rw_cells segs m (A + Z.of_nat k) [CB n2 js2] -> rw_cells segs m A [CB (k + n2) (js1 ++ js2)].
Proof.
  intros segs m A k js1 n2 js2 H1 H2.
  destruct (rwc_cb_inv _ _ _ _ _ H1) as (L1 & B1 & (W0 & W1 & Hw1)).
  destruct (rwc_cb_inv _ _ _ _ _ H2) as (L2 & B2 & (V0 & V1 & Hw2)).
  apply rwc_cb.
  - rewrite app_length. lia.
  - apply bytes_at_app. split; [exact B1|]. rewrite L1. exact B2.
  - split; [lia|]. split; [rewrite Nat2Z.inj_add; lia|]. intros i Hi.
    rewrite Nat2Z.inj_add in Hi.
    destruct (Z_lt_le_dec i (Z.of_nat k)) as [H|H]; [apply Hw1; lia|].
    replace (A + i) with (A + Z.of_nat k + (i - Z.of_nat k)) by lia. apply Hw2. lia.
Qed.

Definition lsv (ra s0 s1 s2 s3 s4 s5 : word) : list cell :=
  [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma e0_cond : forall u, 0 <= u < 2 ^ 26 ->
  negb (bv_eqb (Z_to_bv 64 (Z.shiftr u 26)) (Z_to_bv 64 0)) = false.
Proof.
  intros u Hu. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

(* 0x12c6c-0x12cac: the prologue (frame 0xa0, seven saved registers at sp + 0x68), the size >= 2^26 test (not
   taken: lib/U/Prog/LLVMFuzzerTestOneInput_early.v takes it), then memset(head, 0, 53) with head = sp + 0x33 *)
Lemma s1a :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo P n : Z) (Q : machine_state -> Prop),
    memset_contract ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 160 <= bv_unsigned sp -> mem_inv rsegs m -> bv_unsigned sp < 2 ^ 63 ->
    0 <= n < 2 ^ 26 -> 0 <= P < 2 ^ 64 ->
    (forall (m' : word -> option byte) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
            (jv jp jh : list byte),
       stk rsegs m' lo (bv_unsigned sp - 160) -> mem_inv rsegs m' ->
       munch [(bv_unsigned sp - 160, bv_unsigned sp)] m m' -> wmono rsegs m m' ->
       rw_cells rsegs m' (bv_unsigned sp - 160) [CB 48 jv] ->
       rw_cells rsegs m' (bv_unsigned sp - 160 + 48) [CB 3 jp] ->
       rw_cells rsegs m' (bv_unsigned sp - 160 + 51) [CB 53 jh] ->
       rw_cells rsegs m' (bv_unsigned sp - 160 + 104) (lsv ra s0 s1 s2 s3 s4 s5) ->
       evt rsegs Q (MS (mkR (Z_to_bv 64 0x12cb0) (Z_to_bv 64 (bv_unsigned sp - 160)) gp tp t0' t1' t2'
                          (Z_to_bv 64 n) (Z_to_bv 64 P) (Z_to_bv 64 (bv_unsigned sp - 160 + 51)) a1' a2' a3' a4'
                          a5' a6' a7' (Z_to_bv 64 (bv_unsigned sp - 160 + 51)) (Z_to_bv 64 53) s4 s5 s6 s7 s8 s9
                          s10 s11 t3' t4' t5' t6')
                       F (Z_to_bv 64 0x12cb0) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
                       s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x12c6c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo P n Q MSET ST LO MI H63 Hn HP K.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof ST as (Hlo0 & _ & _).
  pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 160%nat ST.
  do 11 step.
  rewrite (unsigned_lit n) by lia. if_false_by (e0_cond n ltac:(lia)).
  do 6 step.
  replace (bv_unsigned sp + -160) with (bv_unsigned sp - 160) in * by lia.
  replace (bv_unsigned sp + -109) with (bv_unsigned sp - 160 + 51) in * by lia.
  apply (rw_cells_split_CB rsegs _ _ [] 104 _ _ [48; 3; 53]%nat) in FR; [|reflexivity].
  cbn [app mk_CB_cells] in FR.
  apply rwc_cons in FR as [FV FR]. apply rwc_cons in FR as [FP FR]. apply rwc_cons in FR as [FH FS].
  cbn [csize] in FP, FH, FS.
  replace (bv_unsigned sp - 160 + Z.of_nat 48) with (bv_unsigned sp - 160 + 48) in FP, FH, FS by lia.
  replace (bv_unsigned sp - 160 + 48 + Z.of_nat 3) with (bv_unsigned sp - 160 + 51) in FH, FS by lia.
  replace (bv_unsigned sp - 160 + 51 + Z.of_nat 53) with (bv_unsigned sp - 160 + 104) in FS by lia.
  eapply evt_cut.
  { eapply MSET; [rewrite !unsigned_lit by lia; exact FH | exact MI]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU' & WM'
    & MI' & FH').
  rewrite ret_pc_even by first [lia | reflexivity].
  rewrite (unsigned_lit (bv_unsigned sp - 160 + 51)), (unsigned_lit 53) in MU', FH' by lia.
  assert (Dv : disjoint_from [(bv_unsigned sp - 160 + 51, bv_unsigned sp - 160 + 51 + 53)]
                 (bv_unsigned sp - 160) (Z.of_nat (cells_size [CB 48 (firstn 48 junk)])))
    by (cbn [disjoint_from cells_size csize]; split; [lia | exact I]).
  assert (Dp : disjoint_from [(bv_unsigned sp - 160 + 51, bv_unsigned sp - 160 + 51 + 53)]
                 (bv_unsigned sp - 160 + 48) (Z.of_nat (cells_size [CB 3 (firstn 3 (skipn 48 junk))])))
    by (cbn [disjoint_from cells_size csize]; split; [lia | exact I]).
  assert (Ds : disjoint_from [(bv_unsigned sp - 160 + 51, bv_unsigned sp - 160 + 51 + 53)]
                 (bv_unsigned sp - 160 + 104) (Z.of_nat (cells_size (lsv ra s0 s1 s2 s3 s4 s5))))
    by (cbn [disjoint_from cells_size csize lsv]; split; [lia | exact I]).
  pose proof (rw_cells_transport rsegs _ _ m' _ _ FV MU' WM' Dv) as FV'.
  pose proof (rw_cells_transport rsegs _ _ m' _ _ FP MU' WM' Dp) as FP'.
  pose proof (rw_cells_transport rsegs _ _ m' _ _ FS MU' WM' Ds) as FS'.
  pose proof (stk_transport_disjoint rsegs _ _ m' _ _ ST MU' WM'
    ltac:(cbn [disjoint_from]; split; [lia | exact I])) as ST'.
  pose proof (munch_trans _ m _ m' MU (munch_weaken [(bv_unsigned sp - 160 + 51, bv_unsigned sp - 160 + 51 + 53)]
    [(bv_unsigned sp - 160, bv_unsigned sp)] _ m'
    ltac:(unfold sub_fp; cbn [outside]; intros x [Hx _]; split; [lia | exact I]) MU')) as MU2.
  pose proof (wmono_trans rsegs m _ m' WM WM') as WM2.
  exact (K m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' _ _ _ ST' MI' MU2 WM2 FV' FP' FH' FS').
Qed.

Ltac usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end.
Ltac solve_c := unfold bv_eqb, bv_ltu, bv_leu, bv_lts; cbn [negb]; usub; fold_lit_ux; solve_cond_rec.
Ltac take b := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; solve_c]
  end.

(* 0x12cb0-0x12cc4: the clamp of memcpy's length to HEAD = 53 and memcpy(head, data, min(size, 53)) *)
Lemma s1b :
  forall (x1 x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sp lo P n : Z) (pl jh : list byte)
         (Q : machine_state -> Prop),
    memcpy_contract ->
    0 <= lo -> lo <= Sp -> 0 <= Sp -> Sp + 160 <= 2 ^ 63 -> 0 <= n < 2 ^ 26 -> 0 <= P < 2 ^ 64 ->
    n = Z.of_nat (length pl) -> (0 < n -> bytes_at rsegs m P pl) -> (0 < n -> P + n <= lo) ->
    mem_inv rsegs m -> rw_cells rsegs m (Sp + 51) [CB 53 jh] ->
    (forall (m' : word -> option byte) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
            (jh' : list byte),
       mem_inv rsegs m' -> munch [(Sp + 51, Sp + 51 + 53)] m m' -> wmono rsegs m m' ->
       rw_cells rsegs m' (Sp + 51) [CB 53 jh'] ->
       evt rsegs Q (MS (mkR (Z_to_bv 64 0x12cc8) (Z_to_bv 64 Sp) x3 x4 t0' t1' t2' (Z_to_bv 64 n) (Z_to_bv 64 P)
                          (Z_to_bv 64 (Sp + 51)) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (Sp + 51))
                          (Z_to_bv 64 53) x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6')
                       F (Z_to_bv 64 0x12cc8) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 (Z_to_bv 64 n) (Z_to_bv 64 P) (Z_to_bv 64 (Sp + 51))
                       x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (Sp + 51)) (Z_to_bv 64 53) x20 x21 x22 x23 x24 x25
                       x26 x27 x28 x29 x30 x31)
                    F (Z_to_bv 64 0x12cb0) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    F fc m Sp lo P n pl jh Q MCPY Hlo0 Hlo Hsp0 Hsp Hn HP Hlen HPB HPL MI FH K.
  (* k = min n 53, the bytes copied *)
  assert (CALL : forall k, 0 <= k <= 53 -> k <= n ->
    evt rsegs Q (MS (mkR (Z_to_bv 64 0x12cc8) (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 (Z_to_bv 64 n) (Z_to_bv 64 P)
                       (Z_to_bv 64 (Sp + 51)) (Z_to_bv 64 P) (Z_to_bv 64 k) x13 x14 x15 x16 x17
                       (Z_to_bv 64 (Sp + 51))
                       (Z_to_bv 64 53) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                    F (Z_to_bv 64 0x1b0b0) fc None m (seg_rom rsegs))).
  { intros k Hk Hkn.
    destruct (rwc_cb_split rsegs m (Sp + 51) 53 jh (Z.to_nat k) FH ltac:(lia)) as [FH1 FH2].
    eapply evt_cut.
    { eapply MCPY with (src := firstn (Z.to_nat k) pl).
      - rewrite (unsigned_lit P) by lia.
        destruct (Z.eq_dec n 0) as [N0|N0].
        + rewrite N0 in Hkn. replace (Z.to_nat k) with 0%nat by lia. cbn [firstn].
          apply bytes_at_nil. lia.
        + pose proof (HPB ltac:(lia)) as HB.
          rewrite <- (firstn_skipn (Z.to_nat k) pl) in HB. apply bytes_at_app in HB as [HB _]. exact HB.
      - rewrite (unsigned_lit k) by lia. rewrite firstn_length. lia.
      - rewrite (unsigned_lit (Sp + 51)), (unsigned_lit k) by lia. exact FH1.
      - rewrite (unsigned_lit (Sp + 51)), (unsigned_lit k), (unsigned_lit P) by lia.
        destruct (Z.eq_dec n 0) as [N0|N0]; [lia|]. pose proof (HPL ltac:(lia)). lia.
      - exact MI. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU' &
      WM' & MI' & FH1' & _).
    rewrite ret_pc_even by first [lia | reflexivity].
    rewrite !unsigned_lit in MU', FH1' by lia.
    assert (D2 : disjoint_from [(Sp + 51, Sp + 51 + k)] (Sp + 51 + Z.of_nat (Z.to_nat k))
                   (Z.of_nat (cells_size [CB (53 - Z.to_nat k) (skipn (Z.to_nat k) jh)])))
      by (cbn [disjoint_from cells_size csize]; split; [lia | exact I]).
    pose proof (rw_cells_transport rsegs _ _ m' _ _ FH2 MU' WM' D2) as FH2'.
    pose proof (rwc_cb_join rsegs m' (Sp + 51) (Z.to_nat k) (firstn (Z.to_nat k) pl) _ _ FH1' FH2') as HM2.
    replace (Z.to_nat k + (53 - Z.to_nat k))%nat with 53%nat in HM2 by lia.
    apply (K m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
             (firstn (Z.to_nat k) pl ++ skipn (Z.to_nat k) jh) MI'); [| exact WM' | exact HM2].
    eapply munch_weaken; [| exact MU']. unfold sub_fp. cbn [outside]. intros x [Hx _]. split; [lia | exact I]. }
  do 2 step.
  destruct (Z_lt_le_dec n 53) as [Hlt|Hge].
  - take true. do 3 step. apply (CALL n); lia.
  - take false. do 4 step. apply (CALL 53); lia.
Qed.

Lemma rwc_cb_write : forall segs m A n js k bs a, rw_cells segs m A [CB n js] ->
  a = A + k -> 0 <= k -> (Z.to_nat k + length bs <= n)%nat ->
  rw_cells segs (write_to_mem m (wa a) bs) A [CB n (upd_bytes js (Z.to_nat k) bs)].
Proof.
  intros segs m A n js k bs a H -> Hk Hn. destruct (rwc_cb_inv _ _ _ _ _ H) as (Hl & Hb & Hw).
  apply rwc_cb.
  - rewrite upd_bytes_length by lia. exact Hl.
  - apply bytes_at_write_inside; [exact Hb | lia | lia].
  - apply wr_at_write. exact Hw.
Qed.

(* 0x12d34-0x12d68: one round of `v[s] = (int32_t)fuzz_le32(head + 5 + 4 * s)`: the four bytes of head at
   a1 - 3 .. a1, the little-endian word, the store to v + 4 * s, and the two pointer bumps. *)
Lemma s1body :
  forall (x1 x3 x4 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sp lo : Z) (jv jh : list byte) (sv : list cell)
         (s : nat) (iz az : Z) (Q : machine_state -> Prop),
    0 <= lo -> lo <= Sp -> Sp + 160 <= 2 ^ 63 ->
    length jv = 48%nat -> length jh = 53%nat -> (s < 12)%nat ->
    iz = 4 * Z.of_nat s -> az = Sp + 59 + 4 * Z.of_nat s ->
    rw_cells rsegs m Sp [CB 48 jv] -> bytes_at rsegs m (Sp + 51) jh -> rw_cells rsegs m (Sp + 104) sv ->
    stk rsegs m lo Sp -> mem_inv rsegs m ->
    (forall (m' : word -> option byte) (jv' : list byte) (y14 y15 y16 y17 : word),
       length jv' = 48%nat ->
       rw_cells rsegs m' Sp [CB 48 jv'] -> bytes_at rsegs m' (Sp + 51) jh -> rw_cells rsegs m' (Sp + 104) sv ->
       stk rsegs m' lo Sp -> mem_inv rsegs m' ->
       munch [(Sp, Sp + 48)] m m' -> wmono rsegs m m' ->
       evt rsegs Q (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (iz + 4)) (Z_to_bv 64 (az + 4))
                          (Z_to_bv 64 (Sp + 107)) (Z_to_bv 64 Sp) y14 y15 y16 y17 x18 x19 x20 x21 x22 x23 x24 x25
                          x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x12d6c) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 iz) (Z_to_bv 64 az)
                       (Z_to_bv 64 (Sp + 107)) (Z_to_bv 64 Sp) x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
                       x27 x28 x29 x30 x31)
                    F (Z_to_bv 64 0x12d34) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x3 x4 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    F fc m Sp lo jv jh sv s iz az Q Hlo0 Hlo Hsp Hjv Hjh Hs Hiz Haz FV BH FS ST MI K.
  subst iz az.
  pose proof (rw_cells_bound rsegs m Sp _ FV) as (Hsp0 & _).
  destruct (rwc_cb_inv _ _ _ _ _ FV) as (_ & BV & WV).
  assert (RD : forall j, (j < 53)%nat -> Z.of_nat j = 51 + Z.of_nat j - 51 ->
    ov_read_bytes rsegs m (wa (Sp + 51 + Z.of_nat j)) 1 = Some [nth j jh (Z_to_bv 8 0)]).
  { intros j Hj _. rewrite (bytes_at_read rsegs m (Sp + 51) jh (Z.of_nat j) 1 BH ltac:(lia) ltac:(lia)).
    f_equal. rewrite Nat2Z.id. apply firstn1_nth. lia. }
  assert (R6 : ov_read_bytes rsegs m (wa (Sp + 59 + 4 * Z.of_nat s + -2)) 1 =
               Some [nth (6 + 4 * s)%nat jh (Z_to_bv 8 0)]).
  { replace (Sp + 59 + 4 * Z.of_nat s + -2) with (Sp + 51 + Z.of_nat (6 + 4 * s)) by lia.
    apply RD; lia. }
  assert (R5 : ov_read_bytes rsegs m (wa (Sp + 59 + 4 * Z.of_nat s + -3)) 1 =
               Some [nth (5 + 4 * s)%nat jh (Z_to_bv 8 0)]).
  { replace (Sp + 59 + 4 * Z.of_nat s + -3) with (Sp + 51 + Z.of_nat (5 + 4 * s)) by lia.
    apply RD; lia. }
  assert (R7 : ov_read_bytes rsegs m (wa (Sp + 59 + 4 * Z.of_nat s + -1)) 1 =
               Some [nth (7 + 4 * s)%nat jh (Z_to_bv 8 0)]).
  { replace (Sp + 59 + 4 * Z.of_nat s + -1) with (Sp + 51 + Z.of_nat (7 + 4 * s)) by lia.
    apply RD; lia. }
  assert (R8 : ov_read_bytes rsegs m (wa (Sp + 59 + 4 * Z.of_nat s + 0)) 1 =
               Some [nth (8 + 4 * s)%nat jh (Z_to_bv 8 0)]).
  { replace (Sp + 59 + 4 * Z.of_nat s + 0) with (Sp + 51 + Z.of_nat (8 + 4 * s)) by lia.
    apply RD; lia. }
  do 12 step.
  assert (HS : store_ok rsegs m (wa (Sp + 4 * Z.of_nat s + 0)) 4 = true).
  { replace (Sp + 4 * Z.of_nat s + 0) with (Sp + 4 * Z.of_nat s) by lia.
    apply (wr_at_store_ok rsegs m Sp 48 (4 * Z.of_nat s) 4 WV); lia. }
  step.
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?bs) _) =>
      pose proof (rwc_cb_write rsegs m Sp 48 jv (4 * Z.of_nat s) bs (Sp + 4 * Z.of_nat s + 0) FV ltac:(lia)
        ltac:(lia) ltac:(rewrite length_le4; lia)) as FV';
      pose proof (bytes_at_write_other rsegs m (Sp + 4 * Z.of_nat s + 0) bs (Sp + 51) jh BH ltac:(lia)
        ltac:(rewrite length_le4; lia) ltac:(rewrite length_le4; lia)) as BH';
      pose proof (rw_cells_frame rsegs m (Sp + 104) sv (Sp + 4 * Z.of_nat s + 0) bs FS ltac:(lia)
        ltac:(rewrite length_le4; lia) ltac:(rewrite length_le4; lia)) as FS';
      pose proof (stk_write rsegs m lo Sp (Sp + 4 * Z.of_nat s + 0) bs ST ltac:(lia)
        ltac:(rewrite length_le4; lia)) as ST';
      pose proof (mem_inv_store rsegs m (wa (Sp + 4 * Z.of_nat s + 0)) bs MI
        ltac:(rewrite length_le4; exact HS)) as MI';
      pose proof (munch_write [(Sp, Sp + 48)] m m (Sp + 4 * Z.of_nat s + 0) bs (munch_refl _ m)
        ltac:(lia) ltac:(rewrite length_le4; lia)
        ltac:(cbn [inside]; left; rewrite length_le4; lia)) as MU';
      pose proof (wmono_write rsegs m m (wa (Sp + 4 * Z.of_nat s + 0)) bs (wmono_refl rsegs m)) as WM'
  end.
  step.
  apply (K _ (upd_bytes jv (Z.to_nat (4 * Z.of_nat s)) _) _ _ _ _
           ltac:(rewrite upd_bytes_length by (rewrite length_le4; lia); exact Hjv)
           FV' BH' FS' ST' MI' MU' WM').
Qed.

(* 0x12d34-0x12d6c, twelve rounds: the loop `for (s = 0; s < 12; s++) v[s] = fuzz_le32(head + 5 + 4 * s)` *)
Lemma s1loop : forall (k : nat)
    (x1 x3 x4 x5 x6 x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (Sp lo : Z) (jh : list byte) (sv : list cell)
    (Q : machine_state -> Prop),
  0 <= lo -> lo <= Sp -> Sp + 160 <= 2 ^ 63 -> length jh = 53%nat ->
  (forall (m' : word -> option byte) (jv' : list byte) (y10 y11 y14 y15 y16 y17 : word),
     length jv' = 48%nat ->
     rw_cells rsegs m' Sp [CB 48 jv'] -> bytes_at rsegs m' (Sp + 51) jh -> rw_cells rsegs m' (Sp + 104) sv ->
     stk rsegs m' lo Sp -> mem_inv rsegs m' -> munch [(Sp, Sp + 48)] m0 m' -> wmono rsegs m0 m' ->
     evt rsegs Q (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 x8 x9 y10 y11 (Z_to_bv 64 (Sp + 107))
                        (Z_to_bv 64 Sp) y14 y15 y16 y17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x12d70) fc None m' (seg_rom rsegs))) ->
  forall (s : nat) (m : word -> option byte) (jv : list byte) (x14 x15 x16 x17 : word) (iz az : Z),
  (s + k = 11)%nat -> iz = 4 * Z.of_nat s -> az = Sp + 59 + 4 * Z.of_nat s -> length jv = 48%nat ->
  rw_cells rsegs m Sp [CB 48 jv] -> bytes_at rsegs m (Sp + 51) jh -> rw_cells rsegs m (Sp + 104) sv ->
  stk rsegs m lo Sp -> mem_inv rsegs m -> munch [(Sp, Sp + 48)] m0 m -> wmono rsegs m0 m ->
  evt rsegs Q (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 iz) (Z_to_bv 64 az)
                     (Z_to_bv 64 (Sp + 107)) (Z_to_bv 64 Sp) x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
                     x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x12d34) fc None m (seg_rom rsegs)).
Proof.
  induction k as [|k IH]; intros x1 x3 x4 x5 x6 x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    F fc m0 Sp lo jh sv Q Hlo0 Hlo Hsp Hjh K s m jv x14 x15 x16 x17 iz az Hk Hiz Haz Hjv FV BH FS ST MI MU WM.
  - eapply s1body; try eassumption; try lia.
    intros m' jv' y14 y15 y16 y17 Hjv' FV' BH' FS' ST' MI' MU' WM'.
    step. take false.
    apply (K m' jv' _ _ y14 y15 y16 y17 Hjv' FV' BH' FS' ST' MI'
             (munch_trans _ m0 m m' MU MU') (wmono_trans rsegs m0 m m' WM WM')).
  - eapply s1body; try eassumption; try lia.
    intros m' jv' y14 y15 y16 y17 Hjv' FV' BH' FS' ST' MI' MU' WM'.
    step. take true.
    apply (IH x1 x3 x4 x5 x6 x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
             F fc m0 Sp lo jh sv Q Hlo0 Hlo Hsp Hjh K (S s) m' jv' y14 y15 y16 y17 (iz + 4) (az + 4)
             ltac:(lia) ltac:(lia) ltac:(lia) Hjv' FV' BH' FS' ST' MI'
             (munch_trans _ m0 m m' MU MU') (wmono_trans rsegs m0 m m' WM WM')).
Qed.

Lemma zxb_u : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. unfold zxb. apply unsigned_lit. lia.
Qed.

(* 0x12cc8-0x12d30: the four UBSan pointer checks on head (none taken: head = sp + 0x33 is on the stack,
   below 2^63), the five head bytes of slot and ctr, and the loop's pointers *)
Lemma s1c :
  forall (x1 x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sp n P : Z) (jh : list byte)
         (Q : machine_state -> Prop),
    0 <= Sp -> Sp + 160 <= 2 ^ 63 -> length jh = 53%nat -> bytes_at rsegs m (Sp + 51) jh ->
    (forall (y14 y15 y16 y17 w3 : word) (slot : Z), -2 <= slot <= 253 ->
       evt rsegs Q (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 (Z_to_bv 64 n) (Z_to_bv 64 P) (Z_to_bv 64 0)
                          (Z_to_bv 64 (Sp + 59)) (Z_to_bv 64 (Sp + 107)) (Z_to_bv 64 Sp) y14 y15 y16 y17
                          (Z_to_bv 64 slot) w3 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x12d34) fc None m (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 (Z_to_bv 64 n) (Z_to_bv 64 P) (Z_to_bv 64 (Sp + 51))
                       x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (Sp + 51)) (Z_to_bv 64 53) x20 x21 x22 x23 x24 x25
                       x26 x27 x28 x29 x30 x31)
                    F (Z_to_bv 64 0x12cc8) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    F fc m Sp n P jh Q Hsp0 Hsp Hjh BH K.
  assert (RD : forall j, (j < 53)%nat ->
    ov_read_bytes rsegs m (wa (Sp + 51 + Z.of_nat j)) 1 = Some [nth j jh (Z_to_bv 8 0)]).
  { intros j Hj. rewrite (bytes_at_read rsegs m (Sp + 51) jh (Z.of_nat j) 1 BH ltac:(lia) ltac:(lia)).
    f_equal. rewrite Nat2Z.id. apply firstn1_nth. lia. }
  assert (R0 : ov_read_bytes rsegs m (wa (Sp + 51)) 1 = Some [nth 0 jh (Z_to_bv 8 0)])
    by (replace (Sp + 51) with (Sp + 51 + Z.of_nat 0) by lia; apply RD; lia).
  assert (R1 : ov_read_bytes rsegs m (wa (Sp + 52)) 1 = Some [nth 1 jh (Z_to_bv 8 0)])
    by (replace (Sp + 52) with (Sp + 51 + Z.of_nat 1) by lia; apply RD; lia).
  assert (R2 : ov_read_bytes rsegs m (wa (Sp + 53)) 1 = Some [nth 2 jh (Z_to_bv 8 0)])
    by (replace (Sp + 53) with (Sp + 51 + Z.of_nat 2) by lia; apply RD; lia).
  assert (R3 : ov_read_bytes rsegs m (wa (Sp + 54)) 1 = Some [nth 3 jh (Z_to_bv 8 0)])
    by (replace (Sp + 54) with (Sp + 51 + Z.of_nat 3) by lia; apply RD; lia).
  assert (R4 : ov_read_bytes rsegs m (wa (Sp + 55)) 1 = Some [nth 4 jh (Z_to_bv 8 0)])
    by (replace (Sp + 55) with (Sp + 51 + Z.of_nat 4) by lia; apply RD; lia).
  pose proof (bv_unsigned_in_range 8 (nth 0 jh (Z_to_bv 8 0))) as Hb0.
  unfold bv_modulus in Hb0. change (2 ^ Z.of_N 8) with 256 in Hb0.
  do 2 step. take false. do 3 step. take false. do 3 step. take false. do 3 step. take false.
  do 16 step.
  rewrite ?zxb_u.
  eapply K. lia.
Qed.

Lemma land_ones64 : forall x, 0 <= x < 2 ^ 64 -> Z.land 18446744073709551615 x = x.
Proof.
  intros x Hx. replace 18446744073709551615 with (Z.ones 64) by (vm_compute; reflexivity).
  rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Lemma u_neg1 : bv_unsigned (Z_to_bv 64 (-1)) = 18446744073709551615.
Proof. vm_compute. reflexivity. Qed.

(* 0x12d70-0x12d7c: `size > HEAD ? size - HEAD : 0` as a mask of the borrow of size - HEAD *)
Lemma mask_sub53 : forall n, 0 <= n < 2 ^ 26 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltu (Z_to_bv 64 n) (Z_to_bv 64 (n + -53))) + -1)))
                     (bv_unsigned (Z_to_bv 64 (n + -53))))
  = Z_to_bv 64 (Z.max (n - 53) 0).
Proof.
  intros n Hn. unfold v_sltu, c_ltu, bv_ltu. rewrite (unsigned_lit n) by lia.
  destruct (Z_lt_le_dec n 53) as [Hlt|Hge].
  - assert (E : bv_unsigned (Z_to_bv 64 (n + -53)) = n - 53 + 2 ^ 64).
    { rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
      rewrite <- (Z.mod_unique (n + -53) (2 ^ 64) (-1) (n - 53 + 2 ^ 64)); lia. }
    rewrite E. rewrite (proj2 (Z.ltb_lt n (n - 53 + 2 ^ 64)) ltac:(lia)).
    rewrite (unsigned_lit 1) by lia. change (1 + -1) with 0. rewrite (unsigned_lit 0) by lia.
    rewrite Z.land_0_l. f_equal. lia.
  - assert (E : bv_unsigned (Z_to_bv 64 (n + -53)) = n - 53) by (rewrite unsigned_lit; lia).
    rewrite E. rewrite (proj2 (Z.ltb_ge n (n - 53)) ltac:(lia)).
    rewrite (unsigned_lit 0) by lia. change (0 + -1) with (-1). rewrite u_neg1.
    rewrite land_ones64 by lia. f_equal. lia.
Qed.

(* 0x12d8c-0x12d94: `HEAD * (size > HEAD)` as a mask of size <u 54 *)
Lemma maski_53 : forall n, 0 <= n < 2 ^ 26 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltiu (Z_to_bv 64 n) 54) + -1))) 53)
  = Z_to_bv 64 (if n <? 54 then 0 else 53).
Proof.
  intros n Hn. unfold v_sltiu. rewrite (unsigned_lit n) by lia.
  replace (bv_wrap 64 54) with 54 by (vm_compute; reflexivity).
  destruct (Z.ltb_spec n 54).
  - rewrite (unsigned_lit 1) by lia. change (1 + -1) with 0. rewrite (unsigned_lit 0) by lia.
    rewrite Z.land_0_l. reflexivity.
  - rewrite (unsigned_lit 0) by lia. change (0 + -1) with (-1). rewrite u_neg1.
    rewrite land_ones64 by lia. reflexivity.
Qed.

Definition nzb (p : Z) : Z := if p =? 0 then 0 else 1.

Lemma sltu0 : forall n, 0 <= n < 2 ^ 64 -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 n) = Z_to_bv 64 (nzb n).
Proof.
  intros n Hn. unfold v_sltu, c_ltu, bv_ltu, nzb. rewrite !unsigned_lit by lia.
  destruct (Z.eqb_spec n 0); destruct (Z.ltb_spec 0 n); try reflexivity; lia.
Qed.

(* the UBSan null-arithmetic check `snez a0, s1` / `seqz a1, s5` / `xor` / `beqz`: data + HEAD * (size > HEAD)
   is NULL exactly when data is *)
Lemma nzx : forall p a, 0 <= p < 2 ^ 64 -> 0 <= a < 2 ^ 64 -> (p = 0 <-> a = 0) ->
  bv_eqb (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 (nzb p))) (bv_unsigned (v_sltiu (Z_to_bv 64 a) 1))))
    (Z_to_bv 64 0) = false.
Proof.
  intros p a Hp Ha Hiff. unfold v_sltiu, nzb. rewrite (unsigned_lit a) by lia.
  replace (bv_wrap 64 1) with 1 by (vm_compute; reflexivity).
  destruct (Z.eqb_spec p 0); destruct (Z.ltb_spec a 1); try lia; reflexivity.
Qed.

(* 0x12db0-0x12db4: malloc(n ? n : 1) *)
Lemma dupsize : forall k, 0 <= k < 2 ^ 63 ->
  Z_to_bv 64 (k + bv_unsigned (v_sltiu (Z_to_bv 64 k) 1)) = Z_to_bv 64 (if k =? 0 then 1 else k).
Proof.
  intros k Hk. unfold v_sltiu. rewrite (unsigned_lit k) by lia.
  replace (bv_wrap 64 1) with 1 by (vm_compute; reflexivity).
  destruct (Z.ltb_spec k 1); destruct (Z.eqb_spec k 0); try lia.
  - rewrite (unsigned_lit 1) by lia. f_equal. lia.
  - rewrite (unsigned_lit 0) by lia. f_equal. lia.
Qed.

(* 0x12d70-0x12db8: n = min(size > HEAD ? size - HEAD : 0, W_RECV_MAX), the source pointer
   data + HEAD * (size > HEAD) with its two UBSan checks (neither taken), and the call
   malloc(n ? n : 1) of the inlined fuzz_dup *)
Lemma s1d :
  forall (x1 x3 x4 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
          x31 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sp lo n P : Z) (Q : machine_state -> Prop),
    0 <= lo -> lo <= Sp -> Sp + 160 <= 2 ^ 63 -> 0 <= n < 2 ^ 26 -> 0 <= P < 2 ^ 64 ->
    (0 < n -> 4096 <= P /\ P + n <= lo) ->
    (forall (nf src : Z) (y11 y12 y13 y14 y15 y16 y17 : word),
       nf = Z.min (Z.max (n - 53) 0) 1600 -> src = (if n <? 54 then 0 else 53) + P ->
       evt rsegs Q (MS (mkR (Z_to_bv 64 0x12dbc) (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 (Z_to_bv 64 n) (Z_to_bv 64 P)
                          (Z_to_bv 64 (if nf =? 0 then 1 else nf)) y11 y12 y13 y14 y15 y16 y17 x18 x19
                          (Z_to_bv 64 nf) (Z_to_bv 64 src) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x14240) fc None m (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 (Z_to_bv 64 n) (Z_to_bv 64 P) x10 x11 x12 x13 x14 x15
                       x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                    F (Z_to_bv 64 0x12d70) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x3 x4 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    F fc m Sp lo n P Q Hlo0 Hlo Hsp Hn HP HPB K.
  assert (TAIL : forall nf, nf = Z.min (Z.max (n - 53) 0) 1600 ->
    forall (y10 y11 y12 y13 y14 y15 y16 y17 : word),
    evt rsegs Q (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 (Z_to_bv 64 n) (Z_to_bv 64 P) y10 y11 y12 y13 y14 y15
                       y16 y17 x18 x19 (Z_to_bv 64 nf) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                    F (Z_to_bv 64 0x12d8c) fc None m (seg_rom rsegs))).
  { intros nf Hnf y10 y11 y12 y13 y14 y15 y16 y17.
    assert (Hnf0 : 0 <= nf <= 1600) by lia.
    assert (Hoff : 0 <= (if n <? 54 then 0 else 53) <= 53) by (destruct (n <? 54); lia).
    assert (Hsrc : 0 <= (if n <? 54 then 0 else 53) + P < 2 ^ 64).
    { destruct (Z.ltb_spec n 54) as [H54|H54]; [lia|]. destruct (HPB ltac:(lia)). lia. }
    assert (Hsrc0 : P = 0 <-> (if n <? 54 then 0 else 53) + P = 0).
    { destruct (Z.ltb_spec n 54) as [H54|H54]; [lia|]. destruct (HPB ltac:(lia)). lia. }
    do 3 step. rewrite maski_53 by lia.
    step.
    step. take false.
    step. rewrite sltu0 by lia.
    do 3 step.
    if_false_by (nzx P ((if n <? 54 then 0 else 53) + P) ltac:(lia) ltac:(lia) Hsrc0).
    do 2 step. rewrite dupsize by lia.
    step.
    apply (K nf ((if n <? 54 then 0 else 53) + P)); [exact Hnf | reflexivity]. }
  do 4 step. rewrite mask_sub53 by lia.
  do 2 step.
  destruct (Z_lt_le_dec (Z.max (n - 53) 0) 1600) as [Hlt|Hge].
  - take true. apply (TAIL (Z.max (n - 53) 0)); lia.
  - take false. step. apply (TAIL 1600); lia.
Qed.

(* 0x12dbc-0x12de8: the `if (!b) abort();` of the inlined fuzz_dup (not taken: the allocator never returns
   NULL), its `if (n) memcpy(b, p, n);`, and the call check_restamp(f, n, ctr) *)
Lemma s1e :
  forall (x1 x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 w3 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sp lo n P nf nf' f src : Z)
         (sbs junk : list byte) (Q : machine_state -> Prop),
    memcpy_contract ->
    0 <= n < 2 ^ 26 -> 0 <= nf <= 1600 -> (0 < nf <-> 53 < n) -> nf' = Z.max nf 1 ->
    4096 <= f -> f + nf' <= lo -> 0 <= lo -> lo <= Sp -> Sp + 160 <= 2 ^ 63 ->
    0 <= src -> src < 2 ^ 64 -> (src + nf <= f \/ f + nf' <= src) ->
    (0 < nf -> bytes_at rsegs m src sbs) -> Z.of_nat (length sbs) = nf ->
    rw_cells rsegs m f [CB (Z.to_nat nf') junk] -> mem_inv rsegs m ->
    (forall (m' : word -> option byte) (y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word)
            (junk' : list byte),
       munch [(f, f + nf')] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
       rw_cells rsegs m' f [CB (Z.to_nat nf') junk'] ->
       evt rsegs Q (MS (mkR (Z_to_bv 64 0x12dec) (Z_to_bv 64 Sp) x3 x4 y5 y6 y7 (Z_to_bv 64 n) (Z_to_bv 64 f)
                          (Z_to_bv 64 f) (Z_to_bv 64 nf) w3 y13 y14 y15 y16 y17 x18 w3 (Z_to_bv 64 nf)
                          (Z_to_bv 64 src) x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x12e58) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 (Z_to_bv 64 n) (Z_to_bv 64 P)
                       (Z_to_bv 64 f) x11 x12 x13 x14 x15 x16 x17 x18 w3 (Z_to_bv 64 nf) (Z_to_bv 64 src)
                       x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                    F (Z_to_bv 64 0x12dbc) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 w3
    F fc m Sp lo n P nf nf' f src sbs junk Q MCPY Hn Hnf Hnfn Hnf' Hf Hfl Hlo0 Hlo Hsp Hsrc0 Hsrc Hdisj HSB Hsbs
    FB MI K.
  pose proof (rw_cells_bound rsegs m f _ FB) as (_ & Hfb).
  cbn [cells_size csize] in Hfb. rewrite Nat.add_0_r, Z2Nat.id in Hfb by lia.
  step. take false.
  do 3 step.
  destruct (Z_lt_le_dec n 54) as [Hlt|Hge].
  - take true.
    do 4 step.
    apply (K m _ _ _ _ _ _ _ _ _ _ _ _ junk (munch_refl _ m) (wmono_refl rsegs m) MI FB).
  - take false.
    assert (Hnf0 : 0 < nf) by lia.
    replace (Z.to_nat nf') with (Z.to_nat nf) in FB by lia.
    do 4 step.
    eapply evt_cut.
    { eapply MCPY with (src := sbs).
      - rewrite (unsigned_lit src) by lia. apply HSB. lia.
      - rewrite (unsigned_lit nf) by lia. lia.
      - rewrite (unsigned_lit f), (unsigned_lit nf) by lia. exact FB.
      - rewrite (unsigned_lit f), (unsigned_lit src), (unsigned_lit nf) by lia. lia.
      - exact MI. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU' &
      WM' & MI' & FB' & _).
    rewrite ret_pc_even by first [lia | reflexivity].
    rewrite !unsigned_lit in MU', FB' by lia.
    do 4 step.
    replace (Z.to_nat nf) with (Z.to_nat nf') in FB' by lia.
    refine (K m' _ _ _ _ _ _ _ _ _ _ _ _ sbs _ WM' MI' FB').
    eapply munch_weaken; [| exact MU']. unfold sub_fp. cbn [outside]. intros x [Hx _]. split; [lia | exact I].
Qed.

(* 0x12dec-0x12df4: the call check_mute(f, n) *)
Lemma s1f :
  forall (x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
          x31 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sp nf f : Z) (Q : machine_state -> Prop),
    evt rsegs Q (MS (mkR (Z_to_bv 64 0x12df8) (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 f) (Z_to_bv 64 f)
                       (Z_to_bv 64 nf) x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 nf) x21 x22 x23 x24 x25 x26
                       x27 x28 x29 x30 x31)
                    F (Z_to_bv 64 0x12f50) fc None m (seg_rom rsegs)) ->
    evt rsegs Q (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 f) x10 x11 x12 x13 x14 x15 x16 x17 x18
                       x19 (Z_to_bv 64 nf) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                    F (Z_to_bv 64 0x12dec) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    F fc m Sp nf f Q K.
  do 3 step. exact K.
Qed.

(* 0x12df8-0x12e18: the call check_gate(f, n, slot) (an evt leaf) and the call check_inject(f, n, slot, v) *)
Lemma s1g :
  forall (x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
          x31 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sp lo nf f slot : Z) (bs : list byte)
         (Q : machine_state -> Prop),
    check_gate_contract ->
    0 <= nf <= 1600 -> 4096 <= f -> f + nf <= lo -> 0 <= lo -> lo + 80 <= Sp -> Sp + 160 <= 2 ^ 63 ->
    -2 <= slot <= 253 ->
    bytes_at rsegs m f bs -> Z.of_nat (length bs) = nf ->
    mem_inv rsegs m -> stk rsegs m lo Sp ->
    (forall (m' : word -> option byte) (y5 y6 y7 y14 y15 y16 y17 y28 y29 y30 y31 : word),
       munch [(Sp - 80, Sp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo Sp ->
       evt rsegs Q (MS (mkR (Z_to_bv 64 0x12e1c) (Z_to_bv 64 Sp) x3 x4 y5 y6 y7 x8 (Z_to_bv 64 f)
                          (Z_to_bv 64 f) (Z_to_bv 64 nf) (Z_to_bv 64 slot) (Z_to_bv 64 Sp) y14 y15 y16 y17
                          (Z_to_bv 64 slot) x19 (Z_to_bv 64 nf) x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x130b0) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 f) x10 x11 x12 x13 x14 x15 x16 x17
                       (Z_to_bv 64 slot) x19 (Z_to_bv 64 nf) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                    F (Z_to_bv 64 0x12df8) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    F fc m Sp lo nf f slot bs Q CG Hnf Hf Hfl Hlo0 Hlo Hsp Hslot HB Hbs MI ST K.
  do 4 step.
  eapply evt_cut.
  { eapply CG with (bs := bs) (lo := lo) (slot := slot).
    - exact MI.
    - rewrite (unsigned_lit Sp) by lia. exact ST.
    - rewrite (unsigned_lit Sp) by lia. lia.
    - rewrite (unsigned_lit f) by lia. lia.
    - rewrite (unsigned_lit f) by lia. exact HB.
    - rewrite (unsigned_lit nf) by lia. lia.
    - rewrite (unsigned_lit nf) by lia. lia.
    - rewrite (unsigned_lit f), (unsigned_lit nf), (unsigned_lit Sp) by lia. lia.
    - reflexivity.
    - lia. }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> &
    MU' & WM' & MI' & ST').
  rewrite ret_pc_even by first [lia | reflexivity].
  rewrite !unsigned_lit in MU', ST' by lia.
  do 5 step.
  apply (K m' _ _ _ _ _ _ _ _ _ _ _ MU' WM' MI' ST').
Qed.

(* 0x12e1c-0x12e20: the call free(f) *)
Lemma s1h :
  forall (x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
          x30 x31 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sp f : Z) (Q : machine_state -> Prop),
    evt rsegs Q (MS (mkR (Z_to_bv 64 0x12e24) (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 f) (Z_to_bv 64 f)
                       x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                    F (Z_to_bv 64 0x14100) fc None m (seg_rom rsegs)) ->
    evt rsegs Q (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 f) x10 x11 x12 x13 x14 x15 x16 x17 x18
                       x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                    F (Z_to_bv 64 0x12e1c) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 F fc m Sp f Q K.
  do 2 step. exact K.
Qed.

(* 0x12e24-0x12e48: return 0, the epilogue and the return *)
Lemma s1i :
  forall (ra s0 s1 s2 s3 s4 s5 gp tp : word)
         (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
          x31 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sp lo : Z) (Q : machine_state -> Prop),
    0 <= lo -> lo <= Sp -> Sp + 160 <= 2 ^ 63 ->
    rw_cells rsegs m (Sp + 104) (lsv ra s0 s1 s2 s3 s4 s5) ->
    (forall (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 : word),
       evt rsegs Q (MS (mkR ra (Z_to_bv 64 (Sp + 160)) gp tp y5 y6 y7 s0 s1 (Z_to_bv 64 0) y11 y12 y13 y14 y15
                          y16 y17 s2 s3 s4 s5 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (ret_pc ra) fc None m (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR x1 (Z_to_bv 64 Sp) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
                       x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                    F (Z_to_bv 64 0x12e24) fc None m (seg_rom rsegs)).
Proof.
  intros ra s0 s1 s2 s3 s4 s5 gp tp x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
    x24 x25 x26 x27 x28 x29 x30 x31 F fc m Sp lo Q Hlo0 Hlo Hsp FS K.
  unfold lsv in FS.
  do 10 step.
  apply K.
Qed.
