From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Reusable Require Import YK11 YK0o YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c slot_inv uslot_norm uslot_exit.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_classify_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import disco_table_c hunt_c uslot_R0_R3.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require uslot_known.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require slot_ser_J2.
Import ListNotations.
Open Scope Z_scope.

Definition LO (X : Z) : Z := X + SLOT_FRAME - SLOT_STACK.

Lemma rp13 : forall regs regs', regs_preserved regs regs' ->
  getr regs' 2 = getr regs 2 /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4 /\
  getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\
  getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21 /\
  getr regs' 22 = getr regs 22 /\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\
  getr regs' 25 = getr regs 25 /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.
Proof.
  intros regs regs' H.
  repeat split; first
    [ exact (H 2 ltac:(unfold callee_saved; lia)) | exact (H 3 ltac:(unfold callee_saved; lia))
    | exact (H 4 ltac:(unfold callee_saved; lia)) | exact (H 8 ltac:(unfold callee_saved; lia))
    | exact (H 9 ltac:(unfold callee_saved; lia)) | exact (H 18 ltac:(unfold callee_saved; lia))
    | exact (H 19 ltac:(unfold callee_saved; lia)) | exact (H 20 ltac:(unfold callee_saved; lia))
    | exact (H 21 ltac:(unfold callee_saved; lia)) | exact (H 22 ltac:(unfold callee_saved; lia))
    | exact (H 23 ltac:(unfold callee_saved; lia)) | exact (H 24 ltac:(unfold callee_saved; lia))
    | exact (H 25 ltac:(unfold callee_saved; lia)) | exact (H 26 ltac:(unfold callee_saved; lia))
    | exact (H 27 ltac:(unfold callee_saved; lia)) ].
Qed.

Lemma rw_flat : forall m A cs, rw_cells rsegs m A cs -> rw_cells rsegs m A [CB (cells_size cs) (cells_bytes cs)].
Proof.
  intros m A cs [[Hwf Hb] Hw]. split; [split|].
  - cbn. split; [apply cells_bytes_length; exact Hwf | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hw.
Qed.

Lemma rw_unflat : forall m A cs, cells_wf cs -> rw_cells rsegs m A [CB (cells_size cs) (cells_bytes cs)] ->
  rw_cells rsegs m A cs.
Proof.
  intros m A cs Hwf [[_ Hb] Hw]. split; [split|].
  - exact Hwf.
  - cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
  - cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw. exact Hw.
Qed.

Lemma rw_join : forall m A B cs1 cs2, B = A + Z.of_nat (cells_size cs1) ->
  rw_cells rsegs m A cs1 -> rw_cells rsegs m B cs2 -> rw_cells rsegs m A (cs1 ++ cs2).
Proof. intros m A B cs1 cs2 -> H1 H2. apply uslot_known.rw_cells_app. split; assumption. Qed.

Lemma rw_split : forall m A B cs1 cs2, B = A + Z.of_nat (cells_size cs1) ->
  rw_cells rsegs m A (cs1 ++ cs2) -> rw_cells rsegs m A cs1 /\ rw_cells rsegs m B cs2.
Proof. intros m A B cs1 cs2 -> H. apply uslot_known.rw_cells_app. exact H. Qed.

Lemma rw_c8 : forall m A bs, rw_cells rsegs m A [CB 8 bs] -> exists w, rw_cells rsegs m A [C8 w].
Proof.
  intros m A bs H. pose proof H as [[[L _] _] _]. exists (le_bytes_to_word bs).
  apply (rw_unflat m A [C8 (le_bytes_to_word bs)]); [cbn; tauto|].
  cbn [cells_size csize cells_bytes cbytes]. rewrite app_nil_r. rewrite slot_ser_J2.le8_inv2 by exact L. exact H.
Qed.

Lemma rw_c8_cb : forall m A w, rw_cells rsegs m A [C8 w] -> rw_cells rsegs m A [CB 8 (le8 w)].
Proof.
  intros m A w H. apply rw_flat in H. cbn [cells_size csize cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H.
Qed.

Lemma rw_cb_sub : forall m A n bs k j, (k + j <= n)%nat ->
  rw_cells rsegs m A [CB n bs] -> rw_cells rsegs m (A + Z.of_nat k) [CB j (firstn j (skipn k bs))].
Proof.
  intros m A n bs k j Hkj H. pose proof H as [[[L _] _] _]. cbn [cell_wf] in L.
  assert (E : bs = firstn k bs ++ firstn j (skipn k bs) ++ skipn (k + j) bs) by (symmetry; apply CB3_bytes; lia).
  assert (H' : rw_cells rsegs m A ([CB k (firstn k bs)] ++ [CB j (firstn j (skipn k bs))] ++ [CB (n - k - j) (skipn (k + j) bs)])).
  { apply (rw_unflat m A); [cbn; rewrite !length_firstn, length_skipn, !length_skipn; repeat split; lia|].
    cbn [cells_size csize cells_bytes cbytes app]. rewrite !app_nil_r. rewrite <- E.
    replace (k + (j + (n - k - j + 0)))%nat with n by lia. exact H. }
  destruct (rw_split m A (A + Z.of_nat k) [CB k (firstn k bs)]
    ([CB j (firstn j (skipn k bs))] ++ [CB (n - k - j) (skipn (k + j) bs)]) ltac:(cbn [cells_size csize]; lia) H')
    as [_ H2].
  destruct (rw_split m (A + Z.of_nat k) (A + Z.of_nat k + Z.of_nat j) [CB j (firstn j (skipn k bs))]
    [CB (n - k - j) (skipn (k + j) bs)] ltac:(cbn [cells_size csize]; lia) H2) as [H3 _]. exact H3.
Qed.

Lemma rw_bytes : forall m A n bs, rw_cells rsegs m A [CB n bs] -> bytes_at rsegs m A bs.
Proof. intros m A n bs [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. Qed.

Lemma rw_agree : forall m m' X n A cs, agree m m' X n -> X <= A -> A + Z.of_nat (cells_size cs) <= X + n ->
  rw_cells rsegs m A cs -> rw_cells rsegs m' A cs.
Proof.
  intros m m' X n A cs HA H1 H2 H. apply (rw_cells_agree m m' A cs H).
  apply (agree_sub m m' X n); [exact HA | exact H1 | exact H2].
Qed.

Lemma bytes_agree : forall m m' X n A bs, agree m m' X n -> X <= A -> A + Z.of_nat (length bs) <= X + n ->
  bytes_at rsegs m A bs -> bytes_at rsegs m' A bs.
Proof.
  intros m m' X n A bs HA H1 H2 H. apply (bytes_at_agree m m' A bs H).
  apply (agree_sub m m' X n); [exact HA | exact H1 | exact H2].
Qed.

Definition P_EXIT (X h : Z) (regs0 : bvmap 5 word) (R : bvmap 5 word) (m : word -> option byte) : Prop :=
  getr R 2 = Z_to_bv 64 X /\ getr R 3 = getr regs0 3 /\ getr R 4 = Z_to_bv 64 0x31a20 /\
  rw_cells rsegs m (X + 168) [C8 (Z_to_bv 64 h)] /\ rw_cells rsegs m (X + 2520) (saved_of regs0).

Definition P_FREEH (X h : Z) (regs0 : bvmap 5 word) (R : bvmap 5 word) (m : word -> option byte) : Prop :=
  getr R 1 = Z_to_bv 64 R29_RET /\ getr R 10 = Z_to_bv 64 h /\
  getr R 2 = Z_to_bv 64 X /\ getr R 3 = getr regs0 3 /\ getr R 4 = Z_to_bv 64 0x31a20 /\
  rw_cells rsegs m (X + 2520) (saved_of regs0).

Definition P_R29 (X : Z) (regs0 : bvmap 5 word) (R : bvmap 5 word) (m : word -> option byte) : Prop :=
  getr R 2 = Z_to_bv 64 X /\ getr R 3 = getr regs0 3 /\ getr R 4 = Z_to_bv 64 0x31a20 /\
  rw_cells rsegs m (X + 2520) (saved_of regs0).

Definition P_RET (regs0 : bvmap 5 word) (R : bvmap 5 word) (m : word -> option byte) : Prop :=
  regs_preserved regs0 R /\ getr R 10 = Z_to_bv 64 0.

Definition junk8 (m : word -> option byte) (A : Z) : Prop := exists w : word, rw_cells rsegs m A [C8 w].
Definition junkb (m : word -> option byte) (A : Z) (n : nat) : Prop := exists bs, rw_cells rsegs m A [CB n bs].

Lemma stk_cb : forall m lo hi A n, Frame.stk rsegs m lo hi -> IMG_HI <= lo -> lo <= A -> 0 <= n -> A + n <= hi ->
  junkb m A (Z.to_nat n).
Proof.
  intros m lo hi A n (H0 & H1 & H2) Hl HA Hn Hh. apply rwc_present; [lia | lia | lia |].
  intros i Hi. assert (Hs : nseg (A + i)) by (right; lia). split; [exact Hs|].
  destruct (H2 (A + i) ltac:(lia)) as (W & _).
  rewrite (wview_nseg m (wa (A + i))) in W by (rewrite wa_unsigned by lia; exact Hs). exact W.
Qed.

Lemma stk_c8 : forall m lo hi A, Frame.stk rsegs m lo hi -> IMG_HI <= lo -> lo <= A -> A + 8 <= hi -> junk8 m A.
Proof.
  intros m lo hi A H Hl HA Hh. destruct (stk_cb m lo hi A 8 H Hl HA ltac:(lia) Hh) as [bs Hb].
  exact (rw_c8 m A bs Hb).
Qed.

Lemma stk_sub : forall m lo hi lo' hi', Frame.stk rsegs m lo hi -> lo <= lo' -> hi' <= hi -> 0 <= lo' ->
  Frame.stk rsegs m lo' hi'.
Proof.
  intros m lo hi lo' hi' (H0 & H1 & H2) Hl Hh H0'. split; [lia|]. split; [lia|].
  intros a Ha. apply H2. lia.
Qed.

Definition fenv (X : Z) (hb : list (Z * Z)) (m : word -> option byte) : Prop :=
  Frame.stk rsegs m (LO X) (X + SLOT_FRAME) /\
  forall a n, In (a, n) hb -> 4096 <= a /\ a + n <= LO X /\ (forall i, 0 <= i < n -> nseg (a + i)) /\
    (0 <= n -> forall x, a + n <= x < 8 * ((a + n + 7) / 8) -> nseg x /\ m (wa x) <> None).

Definition xok (X : Z) : Prop :=
  0 < X /\ X mod 16 = 0 /\ X + SLOT_FRAME <= 2 ^ 47 /\ IMG_HI + 8 <= LO X.

Definition dok (X d : Z) (pl : list byte) : Prop :=
  0 <= d /\ d + Z.of_nat (length pl) < 2 ^ 63 /\ d + Z.of_nat (length pl) <= LO X /\
  (pl <> [] -> forall i, 0 <= i < Z.of_nat (length pl) -> nseg (d + i)).

Definition hdr_mem (X d h : Z) (pl : list byte) (regs0 : bvmap 5 word) (m : word -> option byte) : Prop :=
  junkb m X 32 /\ rw_cells rsegs m (X + 32) [C8 (Z_to_bv 64 0xffff)] /\
  rw_cells rsegs m (X + 40) [C8 (Z_to_bv 64 INV9)] /\ junkb m (X + 48) 72 /\
  rw_cells rsegs m (X + 120) [C8 (Z_to_bv 64 STALE1)] /\ rw_cells rsegs m (X + 128) [C8 (Z_to_bv 64 0)] /\
  junk8 m (X + 136) /\ rw_cells rsegs m (X + 144) [C8 (Z_to_bv 64 MS_NS)] /\
  junk8 m (X + 152) /\ junk8 m (X + 160) /\ rw_cells rsegs m (X + 168) [C8 (Z_to_bv 64 h)] /\
  rw_cells rsegs m (X + 176) [C8 (Z_to_bv 64 (nt (X + 1056)))] /\
  rw_cells rsegs m (X + 184) [C8 (Z_to_bv 64 W0X0)] /\
  rw_cells rsegs m (X + 192) [C8 (Z_to_bv 64 (nt (X + 1024)))] /\
  rw_cells rsegs m (X + 200) [C8 (Z_to_bv 64 (nt (X + 544)))] /\
  junk8 m (X + 208) /\ rw_cells rsegs m (X + 216) [C8 (Z_to_bv 64 IMAX)] /\
  junk8 m (X + 224) /\ junk8 m (X + 232) /\ junk8 m (X + 240) /\ junk8 m (X + 248) /\
  rw_cells rsegs m (X + 256) [C8 (Z_to_bv 64 (nt (X + 280)))] /\ junkb m (X + 264) 4 /\
  junkb m (X + 268) 12 /\
  (exists Gt, rw_cells rsegs m (X + 280) [CB 264 Gt] /\ gate_ok Gt) /\
  (exists T, rw_cells rsegs m (X + 544) [CB 400 T] /\ table_ok T) /\
  junkb m (X + 944) 2 /\ rw_cells rsegs m (X + 946) [CB 6 (our_of pl)] /\
  junkb m (X + 952) 104 /\ junkb m (X + 1056) 24 /\ junkb m (X + 1080) 1440 /\
  rw_cells rsegs m (X + 2520) (saved_of regs0) /\
  (exists H, rw_cells rsegs m h [CB 480 H] /\ hunt_ok H /\ sub H 412 6 = our_of pl) /\
  bytes_at rsegs m d pl.

Ltac hdr_open H :=
  destruct H as ([j0 C0] & C32 & C40 & [j48 C48] & C120 & C128 & [j136 C136] & C144 & [j152 C152] & [j160 C160] &
    C168 & C176 & C184 & C192 & C200 & [j208 C208] & C216 & [j224 C224] & [j232 C232] & [j240 C240] &
    [j248 C248] & C256 & [j264 C264] & [Lk CLK] & (Gt & CGT & GOK) & (T & CT & TOK) & [j944 C944] & C946 &
    [j952 C952] & [j1056 C1056] & [j1080 C1080] & CSV & (Hunt & CH & HOK & OUR) & BD).

Ltac hdr_close := unfold hdr_mem, junk8, junkb; repeat first [eassumption | split | eexists].

Definition P_HDR (X d h : Z) (pl : list byte) (regs0 : bvmap 5 word) (i : Z) (R : bvmap 5 word)
    (m : word -> option byte) : Prop :=
  exists n now,
    1 <= n <= Z.of_nat (length pl) /\ 0 <= now < 2 ^ 64 /\ 0 <= i < MAX_OPS /\
    getr R 2 = Z_to_bv 64 X /\ getr R 3 = getr regs0 3 /\ getr R 4 = Z_to_bv 64 0x31a20 /\
    getr R 5 = Z_to_bv 64 i /\ getr R 9 = Z_to_bv 64 now /\ getr R 18 = Z_to_bv 64 WS_MASK /\
    getr R 21 = Z_to_bv 64 (d + (Z.of_nat (length pl) - n)) /\ getr R 23 = Z_to_bv 64 n /\
    getr R 24 = Z_to_bv 64 (X + 2368) /\ getr R 26 = Z_to_bv 64 32 /\ getr R 27 = Z_to_bv 64 1 /\
    hdr_mem X d h pl regs0 m.

Definition P_BASE (X d h : Z) (pl : list byte) (regs0 : bvmap 5 word) (i now : Z)
    (R : bvmap 5 word) (m : word -> option byte) : Prop :=
  0 <= i < MAX_OPS /\ 0 <= now < 2 ^ 64 /\
  getr R 2 = Z_to_bv 64 X /\ getr R 3 = getr regs0 3 /\ getr R 4 = Z_to_bv 64 0x31a20 /\
  getr R 18 = Z_to_bv 64 WS_MASK /\ getr R 24 = Z_to_bv 64 (X + 2368) /\ getr R 26 = Z_to_bv 64 32 /\
  rw_cells rsegs m (X + 160) [C8 (Z_to_bv 64 i)] /\ rw_cells rsegs m (X + 224) [C8 (Z_to_bv 64 now)] /\
  hdr_mem X d h pl regs0 m.

Definition P_LAT (X d h : Z) (pl : list byte) (regs0 : bvmap 5 word) (i : Z)
    (R : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists n now, 0 <= n <= Z.of_nat (length pl) /\
    getr R 9 = Z_to_bv 64 now /\ getr R 21 = Z_to_bv 64 (d + (Z.of_nat (length pl) - n)) /\
    getr R 23 = Z_to_bv 64 n /\ getr R 27 = Z_to_bv 64 1 /\ P_BASE X d h pl regs0 i now R m.

Definition P_NEXT (X d h : Z) (pl : list byte) (regs0 : bvmap 5 word) (i q : Z)
    (R : bvmap 5 word) (m : word -> option byte) : Prop :=
  (q = HDR /\ i + 1 < MAX_OPS /\ P_HDR X d h pl regs0 (i + 1) R m) \/
  (q = EXIT /\ P_EXIT X h regs0 R m).

Definition P_ENT (X d : Z) (pl : list byte) (regs0 : bvmap 5 word) (R : bvmap 5 word) (m : word -> option byte) : Prop :=
  (forall r, getr R r = getr regs0 r) /\ getr regs0 2 = Z_to_bv 64 (X + SLOT_FRAME) /\
  getr regs0 10 = Z_to_bv 64 d /\ getr regs0 11 = Z_to_bv 64 (Z.of_nat (length pl)) /\
  getr regs0 4 = Z_to_bv 64 0x31a20 /\ bytes_at rsegs m d pl.

Definition P_MAL0 (X d : Z) (pl : list byte) (regs0 : bvmap 5 word) (R : bvmap 5 word) (m : word -> option byte) : Prop :=
  getr R 1 = Z_to_bv 64 R2_RET /\ getr R 10 = Z_to_bv 64 HUNT_SIZE /\
  getr R 2 = Z_to_bv 64 X /\ getr R 3 = getr regs0 3 /\ getr R 4 = Z_to_bv 64 0x31a20 /\
  getr R 21 = Z_to_bv 64 (d + pre_take (Z.of_nat (length pl))) /\
  getr R 23 = Z_to_bv 64 (Z.of_nat (length pl) - pre_take (Z.of_nat (length pl))) /\
  getr R 24 = Z_to_bv 64 (X + 2368) /\
  rw_cells rsegs m (X + 2520) (saved_of regs0) /\ rw_cells rsegs m (X + 946) [CB 6 (our_of pl)] /\
  bytes_at rsegs m d pl.

Definition P_R2 (X d h : Z) (pl : list byte) (regs0 : bvmap 5 word) (R : bvmap 5 word) (m : word -> option byte) : Prop :=
  getr R 10 = Z_to_bv 64 h /\
  getr R 2 = Z_to_bv 64 X /\ getr R 3 = getr regs0 3 /\ getr R 4 = Z_to_bv 64 0x31a20 /\
  getr R 21 = Z_to_bv 64 (d + pre_take (Z.of_nat (length pl))) /\
  getr R 23 = Z_to_bv 64 (Z.of_nat (length pl) - pre_take (Z.of_nat (length pl))) /\
  getr R 24 = Z_to_bv 64 (X + 2368) /\
  rw_cells rsegs m (X + 2520) (saved_of regs0) /\ rw_cells rsegs m (X + 946) [CB 6 (our_of pl)] /\
  bytes_at rsegs m d pl /\ h mod 16 = 0 /\ junkb m h 480.
