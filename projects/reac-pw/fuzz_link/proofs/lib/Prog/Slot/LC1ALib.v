(* The slot LLVMFuzzerTestOneInput, plain image: the facts segment A of the op_write arm (LC1A.v) uses.

   - the two divisions by 6 the code does with a multiply (the dispatch's `b * 0xab >> 10` at
     0x13a2c-0x13a44 and name_of's `mulhu` by 0x2aaaaaaaaaaaaaab at 0x13f88-0x13f98), each checked for
     every byte value;
   - the odd table as read-only cells, the input bytes, the cursor cell the dispatch loads;
   - the loop memory lh_mem carried across the two cursor stores (sp + 0x40, sp + 0x48), the only
     stores of segment A, and the segment footprint they leave. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC1Defs.
Import ListNotations.
Local Open Scope Z_scope.

(* ==========================================================================
   1. The two divisions by 6
   ========================================================================== *)

(* a3 after 0x13a44 (andi a3, a3, 0xff), as the walk computes it from the op byte b *)
Definition c1a_opx (b : byte) : word :=
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (zxb b) +
     bv_swrap 32 (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.shiftr
                    (bv_unsigned (Z_to_bv 64 (bv_unsigned (zxb b) * 171))) 10))) 1)) -
                  bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.shiftr
                    (bv_unsigned (Z_to_bv 64 (bv_unsigned (zxb b) * 171))) 10))) 3)))))) 255).

(* a0 after 0x13f98 (add a0, a0, a1), as the walk computes it from the selector byte b *)
Definition c1a_m6x (b : byte) : word :=
  Z_to_bv 64 (bv_unsigned (zxb b) +
    (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64
        (Z.shiftr (bv_unsigned (zxb b) * 3074457345618258603) 64))) 1)) -
     bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64
        (Z.shiftr (bv_unsigned (zxb b) * 3074457345618258603) 64))) 3)))).

Lemma c1a_byte_self : forall b : byte, Z_to_bv 8 (bz b) = b.
Proof.
  intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma c1a_bz_range : forall b : byte, 0 <= bz b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. exact R. Qed.

Lemma c1a_in256 : forall z, 0 <= z < 256 -> In z (map Z.of_nat (seq 0 256)).
Proof. intros z Hz. replace z with (Z.of_nat (Z.to_nat z)) by lia. apply in_map. apply in_seq. lia. Qed.

Lemma c1a_bv_eqb_eq : forall x y : word, bv_eqb x y = true -> x = y.
Proof. intros x y H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.

Lemma c1a_opx_mod : forall b, c1a_opx b = Z_to_bv 64 (bz b mod 6).
Proof.
  intros b. rewrite <- (c1a_byte_self b) at 1.
  assert (H : forallb (fun z => bv_eqb (c1a_opx (Z_to_bv 8 z)) (Z_to_bv 64 (z mod 6))) (map Z.of_nat (seq 0 256))
              = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. apply c1a_bv_eqb_eq. apply H. apply c1a_in256, c1a_bz_range.
Qed.

Lemma c1a_opx_val : forall b, bz b mod 6 = 1 -> c1a_opx b = Z_to_bv 64 1.
Proof. intros b Hb. rewrite c1a_opx_mod, Hb. reflexivity. Qed.

Lemma c1a_m6x_val : forall b, c1a_m6x b = Z_to_bv 64 (bz b mod 6).
Proof.
  intros b. rewrite <- (c1a_byte_self b) at 1.
  assert (H : forallb (fun z => bv_eqb (c1a_m6x (Z_to_bv 8 z)) (Z_to_bv 64 (z mod 6))) (map Z.of_nat (seq 0 256))
              = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. apply c1a_bv_eqb_eq. apply H. apply c1a_in256, c1a_bz_range.
Qed.

Lemma c1a_six : forall r, 0 <= r < 6 -> r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5.
Proof. intros r Hr. lia. Qed.

(* ==========================================================================
   2. Reads: bytes, the odd table, the cursor cell
   ========================================================================== *)

Lemma c1a_ov1 : forall m a b, bytes_at rsegs m a [b] -> ov_read_bytes rsegs m (wa a) 1 = Some [b].
Proof.
  intros m a b H. pose proof (bytes_at_ov_read rsegs m a [b] 0 1 H ltac:(cbn; lia)) as R.
  change (Z.of_nat 0) with 0 in R. rewrite Z.add_0_r in R. exact R.
Qed.

Lemma c1a_pl_byte : forall m p0 pl k, bytes_at rsegs m p0 pl -> 0 <= k < Z.of_nat (length pl) ->
  exists b, nth_error pl (Z.to_nat k) = Some b /\ ov_read_bytes rsegs m (wa (p0 + k)) 1 = Some [b].
Proof.
  intros m p0 pl k H Hk.
  destruct (nth_error pl (Z.to_nat k)) as [b|] eqn:E; [|apply nth_error_None in E; lia].
  exists b. split; [reflexivity|].
  pose proof (bytes_at_read rsegs m p0 pl k 1 H ltac:(lia) ltac:(lia)) as R.
  rewrite <- (firstn_skipn_step pl (Z.to_nat k) 0 b E) in R. exact R.
Qed.

Lemma c1a_ba8 : forall m a x bs, bytes_at rsegs m a (le8 x) -> bytes_at rsegs m (a + 8) bs ->
  bytes_at rsegs m a (le8 x ++ bs).
Proof.
  intros m a x bs H1 H2. apply (proj2 (bytes_at_app rsegs m a (le8 x) bs)). split; [exact H1|].
  rewrite length_le8. exact H2.
Qed.

(* odd[] (0x207c0) as six read cells: the values odd_at gives *)
Definition c1a_odd_cells : list cell :=
  [C8 (Z_to_bv 64 0x10368); C8 (Z_to_bv 64 0x1039c); C8 (Z_to_bv 64 0x1056a); C8 (Z_to_bv 64 0x103bc);
   C8 (Z_to_bv 64 0x10598); C8 (Z_to_bv 64 0x102a2)].

Lemma c1a_odd_ro : forall m, odd_at m -> ro_cells rsegs m 0x207c0 c1a_odd_cells.
Proof.
  intros m H.
  assert (G : forall i, (i < 6)%nat ->
            bytes_at rsegs m (0x207c0 + 8 * Z.of_nat i) (le8 (Z_to_bv 64 (nth i odd_ptrs 0))))
    by (intros i Hi; exact (proj1 (H i Hi))).
  split; [cbn; tauto|]. cbn [c1a_odd_cells cells_bytes cbytes].
  apply c1a_ba8; [exact (G 0%nat ltac:(lia))|].
  apply c1a_ba8; [exact (G 1%nat ltac:(lia))|].
  apply c1a_ba8; [exact (G 2%nat ltac:(lia))|].
  apply c1a_ba8; [exact (G 3%nat ltac:(lia))|].
  apply c1a_ba8; [exact (G 4%nat ltac:(lia))|].
  apply c1a_ba8; [exact (G 5%nat ltac:(lia))|].
  apply bytes_at_nil. lia.
Qed.

Lemma c1a_ba_det : forall m a bs bs', bytes_at rsegs m a bs -> bytes_at rsegs m a bs' ->
  length bs = length bs' -> bs = bs'.
Proof.
  intros m a bs bs' (_ & _ & H1) (_ & _ & H2) L. apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length bs)) as [Li|Li].
  - rewrite <- (H1 i Li), <- (H2 i ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None bs i) Li), (proj2 (nth_error_None bs' i) ltac:(lia)). reflexivity.
Qed.

Lemma c1a_le8_inj : forall x y : word, le8 x = le8 y -> x = y.
Proof. intros x y H. rewrite <- (load_u64 x), <- (load_u64 y), H. reflexivity. Qed.

Lemma c1a_wz_inj : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> wz x = wz y -> x = y.
Proof.
  intros x y Hx Hy H. apply (f_equal bv_unsigned) in H. unfold wz in H.
  rewrite !unsigned_lit in H by lia. exact H.
Qed.

Lemma c1a_u64_det : forall m a p q, u64_at m a p -> u64_at m a q -> wz p = wz q.
Proof.
  intros m a p q Hp Hq. apply c1a_le8_inj. eapply c1a_ba_det; [exact Hp | exact Hq | rewrite !length_le8; reflexivity].
Qed.

(* ==========================================================================
   3. The frame cells
   ========================================================================== *)

Lemma c1a_rwc_split : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf Hb] (W0 & W1 & W2)].
  apply cells_wf_app in Hwf. destruct Hwf as [Hw1 Hw2].
  rewrite cells_bytes_app in Hb. apply (proj1 (bytes_at_app rsegs _ _ _ _)) in Hb. destruct Hb as [B1 B2].
  rewrite cells_bytes_length in B2 by exact Hw1.
  rewrite cells_size_app in W1, W2.
  split.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros j Hj. apply W2. lia.
  - split; [split; assumption|]. split; [lia|]. split; [lia|].
    intros j Hj. replace (A + Z.of_nat (cells_size cs1) + j) with (A + (Z.of_nat (cells_size cs1) + j)) by lia.
    apply W2. lia.
Qed.

Lemma c1a_rwc_join : forall m A cs1 cs2 B,
  rw_cells rsegs m A cs1 -> B = A + Z.of_nat (cells_size cs1) -> rw_cells rsegs m B cs2 ->
  rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 B [[Hw1 Hb1] (W0 & W1 & W2)] -> [[Hw2 Hb2] (V0 & V1 & V2)].
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply (proj2 (bytes_at_app rsegs _ _ _ _)). split; [exact Hb1|].
    rewrite cells_bytes_length by exact Hw1. exact Hb2.
  - rewrite cells_size_app. split; [lia|]. split; [lia|].
    intros j Hj. destruct (Z_lt_le_dec j (Z.of_nat (cells_size cs1))) as [L|L].
    + apply W2. lia.
    + replace (A + j) with (A + Z.of_nat (cells_size cs1) + (j - Z.of_nat (cells_size cs1))) by lia.
      apply V2. lia.
Qed.

(* the frame at the loop head, cut at the cursor cells sp + 0x40 / sp + 0x48 *)
Definition c1a_cs1 (j0 : list byte) (w1 w2 w3 w4 w5 w6 w7 : word) : list cell :=
  [CB 8 j0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7].

Lemma c1a_frame_split : forall m B j0 w1 w2 w3 w4 w5 w6 w7 x y j1 j2,
  rw_cells rsegs m B [CB 8 j0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 x; C8 y; CB 40 j1; CB 256 j2] ->
  rw_cells rsegs m B (c1a_cs1 j0 w1 w2 w3 w4 w5 w6 w7) /\ rw_cells rsegs m (B + 64) [C8 x; C8 y] /\
  rw_cells rsegs m (B + 80) [CB 40 j1; CB 256 j2].
Proof.
  intros m B j0 w1 w2 w3 w4 w5 w6 w7 x y j1 j2 H.
  change [CB 8 j0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 x; C8 y; CB 40 j1; CB 256 j2]
    with (c1a_cs1 j0 w1 w2 w3 w4 w5 w6 w7 ++ [C8 x; C8 y] ++ [CB 40 j1; CB 256 j2]) in H.
  destruct (c1a_rwc_split _ _ _ _ H) as [H1 H23].
  change (Z.of_nat (cells_size (c1a_cs1 j0 w1 w2 w3 w4 w5 w6 w7))) with 64 in H23.
  destruct (c1a_rwc_split _ _ _ _ H23) as [H2 H3].
  change (Z.of_nat (cells_size [C8 x; C8 y])) with 16 in H3.
  replace (B + 64 + 16) with (B + 80) in H3 by lia.
  split; [exact H1|]. split; [exact H2 | exact H3].
Qed.

Lemma c1a_frame_join : forall m B j0 w1 w2 w3 w4 w5 w6 w7 x y j1 j2,
  rw_cells rsegs m B (c1a_cs1 j0 w1 w2 w3 w4 w5 w6 w7) -> rw_cells rsegs m (B + 64) [C8 x; C8 y] ->
  rw_cells rsegs m (B + 80) [CB 40 j1; CB 256 j2] ->
  rw_cells rsegs m B [CB 8 j0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 x; C8 y; CB 40 j1; CB 256 j2].
Proof.
  intros m B j0 w1 w2 w3 w4 w5 w6 w7 x y j1 j2 H1 H2 H3.
  change [CB 8 j0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 x; C8 y; CB 40 j1; CB 256 j2]
    with (c1a_cs1 j0 w1 w2 w3 w4 w5 w6 w7 ++ [C8 x; C8 y] ++ [CB 40 j1; CB 256 j2]).
  eapply c1a_rwc_join; [exact H1 | reflexivity |].
  eapply c1a_rwc_join; [exact H2 | reflexivity |].
  change (Z.of_nat (cells_size (c1a_cs1 j0 w1 w2 w3 w4 w5 w6 w7))) with 64.
  change (Z.of_nat (cells_size [C8 x; C8 y])) with 16.
  replace (B + 64 + 16) with (B + 80) by lia. exact H3.
Qed.

(* the cursor cell the dispatch loads (sp + 0x40) holds the P of lh_mem *)
Lemma c1a_cur_eq : forall E i P N kbs mbs gbs m P1 b,
  lh_mem E i P N kbs mbs gbs m ->
  bytes_at rsegs m (e_S E - SLOT_FRAME + FO_P) (le8 (wz P1)) -> bytes_at rsegs m P1 [b] ->
  0 <= P < 2 ^ 64 -> P1 = P.
Proof.
  intros E i P N kbs mbs gbs m P1 b HL H1 Hb HP.
  destruct HL as ((j0 & j1 & j2 & nc & HF) & _).
  unfold lh_cells in HF. apply c1a_frame_split in HF. destruct HF as (_ & [[_ HC] _] & _).
  cbn [cells_bytes cbytes] in HC. apply (proj1 (bytes_at_app rsegs _ _ _ _)) in HC. destruct HC as [HC _].
  pose proof (bytes_at_bound rsegs _ _ _ Hb) as Bb. cbn [length] in Bb.
  apply c1a_wz_inj; [lia | exact HP |].
  apply c1a_le8_inj. eapply c1a_ba_det; [exact H1 | exact HC | rewrite !length_le8; reflexivity].
Qed.

(* ==========================================================================
   4. lh_mem across the cursor stores
   ========================================================================== *)

(* the cursor cells: the only bytes segment A stores *)
Definition c1a_W (E : lenv) : list ivl := [(e_S E - SLOT_FRAME + 64, e_S E - SLOT_FRAME + 80)].

Lemma c1a_img : forall E a n, lenv_ok E -> 0 <= n -> a + n <= 0x960e0 -> disjoint_from (c1a_W E) a n.
Proof.
  intros E a n HE Hn Ha. destruct HE as (HS1 & _). unfold c1a_W, SLOT_FRAME, SLOT_STACK_Z in *.
  cbn [disjoint_from]. split; [lia | exact I].
Qed.

Lemma c1a_heap : forall E a n, lenv_ok E -> 0 <= n -> a + n <= e_S E - SLOT_STACK_Z -> disjoint_from (c1a_W E) a n.
Proof.
  intros E a n HE Hn Ha. unfold c1a_W, SLOT_FRAME, SLOT_STACK_Z in *.
  cbn [disjoint_from]. split; [lia | exact I].
Qed.

Lemma c1a_ba_img : forall E m m' a bs, lenv_ok E -> munch (c1a_W E) m m' ->
  a + Z.of_nat (length bs) <= 0x960e0 -> bytes_at rsegs m a bs -> bytes_at rsegs m' a bs.
Proof.
  intros E m m' a bs HE MU Ha H. eapply bytes_at_transport; [exact H | exact MU |].
  apply c1a_img; [exact HE | lia | exact Ha].
Qed.

Lemma c1a_u64_img : forall E m m' a v, lenv_ok E -> munch (c1a_W E) m m' ->
  a + 8 <= 0x960e0 -> u64_at m a v -> u64_at m' a v.
Proof. intros E m m' a v HE MU Ha H. eapply c1a_ba_img; [exact HE | exact MU | rewrite length_le8; exact Ha | exact H]. Qed.

Lemma c1a_cstr_img : forall E m m' a s, lenv_ok E -> munch (c1a_W E) m m' ->
  a + Z.of_nat (length s) + 1 <= 0x960e0 -> cstr_at m a s -> cstr_at m' a s.
Proof.
  intros E m m' a s HE MU Ha [Hb Hn]. split; [|exact Hn].
  eapply c1a_ba_img; [exact HE | exact MU | rewrite length_app; cbn [length]; lia | exact Hb].
Qed.

Lemma c1a_link_ptrs_bd : forall i, (i < 64)%nat -> 0 <= nth i link_ptrs 0 < 0x75000.
Proof.
  intros i Hi.
  assert (L : length link_ptrs = 64%nat) by (vm_compute; reflexivity).
  assert (H : forallb (fun q => (0 <=? q) && (q <? 0x75000)) link_ptrs = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H (nth i link_ptrs 0) (@nth_In _ i link_ptrs 0 ltac:(lia))).
  apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma c1a_link_tab_len : forall i nm ix, nth_error link_tab i = Some (nm, ix) ->
  (i < 64)%nat /\ (length nm <= 16)%nat.
Proof.
  intros i nm ix H.
  assert (L : length link_tab = 64%nat) by (vm_compute; reflexivity).
  assert (Hi : (i < length link_tab)%nat) by (apply nth_error_Some; rewrite H; discriminate).
  split; [lia|].
  assert (A : forallb (fun p => Nat.leb (length (fst p)) 16) link_tab = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in A. apply nth_error_In in H. specialize (A _ H). cbn [fst] in A.
  apply Nat.leb_le in A. exact A.
Qed.

Lemma c1a_odd_bd : forall i, (i < 6)%nat ->
  nth i odd_ptrs 0 + Z.of_nat (length (nth i odd_strs [])) + 1 <= 0x960e0.
Proof.
  intros i Hi.
  do 6 (destruct i as [|i]; [apply Z.leb_le; vm_compute; reflexivity|]). lia.
Qed.

Ltac c1a_k :=
  unfold A_G_NL, NK_SIZE, NK_IF_NAME, NK_IF_INDEX, A_G_NAMES, A_ODD, A_TEXTS, A_LONG_ALIAS, LONG_ALIAS_SIZE,
    A_GOT_GUARD_S, A_GUARD_S, MD_SIZE, MK_SIZE, SLOT_FRAME, SLOT_STACK_Z in *.

Lemma c1a_lh_mem_move : forall (E : lenv) (i P N P' N' : Z) (kbs mbs gbs : list byte) (m m' : word -> option byte),
  lenv_ok E -> lh_mem E i P N kbs mbs gbs m ->
  munch (c1a_W E) m m' -> wmono rsegs m m' ->
  rw_cells rsegs m' (e_S E - SLOT_FRAME + 64) [C8 (wz P'); C8 (wz N')] ->
  (exists k, 0 <= k <= Z.of_nat (length (e_pl E)) /\ P' = e_p0 E + k /\ N' = Z.of_nat (length (e_pl E)) - k) ->
  lh_mem E i P' N' kbs mbs gbs m'.
Proof.
  intros E i P N P' N' kbs mbs gbs m m' HE HL MU WM HC HK.
  pose proof HE as (HS1 & HS2 & HS3 & (Hmd1 & Hmd2 & _) & (Hmk1 & Hmk2 & _) & _ & _ & _ & Hpl & (Hp1 & Hp2 & _)
                    & _ & _ & Hsav).
  destruct HL as ((j0 & j1 & j2 & nc & HF) & HSV & HNK & HNW & HIF & H6 & H7 & H8 & H9 & HGN & HOD & HPO & HLA &
                  HTX & HIP & HMD & HMW & HMK & HKW & HKA & (HPL & _) & HER & HGU).
  (* the frame *)
  assert (F' : exists j0 j1 j2 nc, rw_cells rsegs m' (e_S E - SLOT_FRAME) (lh_cells (e_md E) (e_mk E) P' nc j0 j1 j2)).
  { exists j0, j1, j2, N'. unfold lh_cells in HF |- *. apply c1a_frame_split in HF. destruct HF as (F1 & _ & F3).
    apply c1a_frame_join; [| exact HC |].
    - eapply rw_cells_transport; [exact F1 | exact MU | exact WM |].
      unfold c1a_W. cbn [disjoint_from]. change (Z.of_nat (cells_size (c1a_cs1 _ _ _ _ _ _ _ _))) with 64.
      split; [lia | exact I].
    - eapply rw_cells_transport; [exact F3 | exact MU | exact WM |].
      unfold c1a_W. cbn [disjoint_from]. split; [lia | exact I]. }
  assert (SV : bytes_at rsegs m' (e_S E - 104) (e_saved E)).
  { eapply bytes_at_transport; [exact HSV | exact MU |]. unfold c1a_W. cbn [disjoint_from].
    split; [|exact I]. right. unfold SLOT_FRAME. lia. }
  assert (NK : nlk_at m' kbs).
  { destruct HNK as (HU & HLn). split; [|exact HLn]. eapply u8arr_transport; [exact HU | exact MU | exact WM |].
    apply c1a_img; [exact HE | lia |]. rewrite HLn. c1a_k. lia. }
  assert (IP : ifptrs_at m').
  { intros j Hj. eapply c1a_u64_img; [exact HE | exact MU | | exact (HIP j Hj)]. c1a_k. lia. }
  assert (IF : iftab_at m' kbs link_tab).
  { destruct HIF as (Hn & Hlen & Hall). split; [exact Hn|]. split; [exact Hlen|].
    intros j nm ix Hj. destruct (Hall j nm ix Hj) as (Hix & p & Hu & Hp0 & Hc & Hu32).
    destruct (c1a_link_tab_len j nm ix Hj) as (Hj64 & Hnm).
    pose proof (c1a_link_ptrs_bd j Hj64) as Hq.
    assert (Ep : p = nth j link_ptrs 0).
    { destruct Hc as (Hcb & _). pose proof (bytes_at_bound rsegs _ _ _ Hcb) as Bc.
      rewrite length_app in Bc. cbn [length] in Bc.
      apply c1a_wz_inj; [lia | lia |]. eapply c1a_u64_det; [exact Hu | exact (HIP j Hj64)]. }
    split; [exact Hix|]. exists p. split; [|split; [exact Hp0|split]].
    - eapply c1a_u64_img; [exact HE | exact MU | | exact Hu]. c1a_k. lia.
    - eapply c1a_cstr_img; [exact HE | exact MU | | exact Hc]. subst p. lia.
    - unfold u32_at in *. eapply c1a_ba_img; [exact HE | exact MU | | exact Hu32].
      rewrite length_le4. c1a_k. lia. }
  assert (GN : gnames_at m').
  { intros k Hk. destruct (HGN k Hk) as (rest & Hb & Hl). exists rest. split; [|exact Hl].
    eapply c1a_ba_img; [exact HE | exact MU | | exact Hb]. rewrite Hl. c1a_k. lia. }
  assert (OD : odd_at m').
  { intros j Hj. destruct (HOD j Hj) as (Hu & Hc). split.
    - eapply c1a_u64_img; [exact HE | exact MU | | exact Hu]. c1a_k. lia.
    - eapply c1a_cstr_img; [exact HE | exact MU | exact (c1a_odd_bd j Hj) | exact Hc]. }
  assert (PO : policy_ro m').
  { destruct HPO as (C1 & C2 & C3 & C4).
    split; [|split; [|split]]; (eapply c1a_cstr_img; [exact HE | exact MU | | eassumption]);
      apply Z.leb_le; vm_compute; reflexivity. }
  assert (LA : la_ok m').
  { destruct HLA as (la & sl & Hr & Hb & Hl). exists la, sl. split; [|split; [|exact Hl]].
    - eapply rw_cells_transport; [exact Hr | exact MU | exact WM |]. apply c1a_img; [exact HE | lia |].
      replace (Z.of_nat (cells_size [CB (Z.to_nat 300) la; C1 (zb 0)])) with 301 by reflexivity. c1a_k. lia.
    - eapply c1a_ba_img; [exact HE | exact MU | | exact Hb]. rewrite Hl. c1a_k. lia. }
  assert (TX : texts_at m').
  { intros j Hj. eapply c1a_u64_img; [exact HE | exact MU | | exact (HTX j Hj)]. c1a_k. lia. }
  assert (MD : model_at m' (e_md E) mbs).
  { destruct HMD as (HU & HLn). split; [|exact HLn]. eapply u8arr_transport; [exact HU | exact MU | exact WM |].
    apply c1a_heap; [exact HE | lia |]. rewrite HLn. exact Hmd2. }
  assert (MK : marks_at m' (e_mk E) gbs).
  { destruct HMK as (HU & HLn). split; [|exact HLn]. eapply u8arr_transport; [exact HU | exact MU | exact WM |].
    apply c1a_heap; [exact HE | lia |]. rewrite HLn. exact Hmk2. }
  assert (CU : cursor_ok m' (e_p0 E) (e_pl E) P' N').
  { split; [|exact HK]. eapply bytes_at_transport; [exact HPL | exact MU |]. apply c1a_heap; [exact HE | lia | exact Hp2]. }
  assert (GU : guard_m m').
  { destruct HGU as (G1 & c & G2). split.
    - eapply c1a_ba_img; [exact HE | exact MU | | exact G1]. rewrite length_le8. c1a_k. lia.
    - exists c. eapply c1a_ba_img; [exact HE | exact MU | | exact G2]. rewrite length_le8. c1a_k. lia. }
  pose proof (wr_at_transport rsegs _ _ _ _ HER WM) as WR.
  exact (conj F' (conj SV (conj NK (conj HNW (conj IF (conj H6 (conj H7 (conj H8 (conj H9 (conj GN (conj OD
          (conj PO (conj LA (conj TX (conj IP (conj MD (conj HMW (conj MK (conj HKW (conj HKA (conj CU
          (conj WR GU)))))))))))))))))))))).
Qed.

Lemma c1a_task : forall E m m', MemNorm.task_mem rsegs m -> munch (c1a_W E) m m' -> e_S E <= 2 ^ 47 ->
  MemNorm.task_mem rsegs m'.
Proof.
  intros E m m' T MU HS a b Ha.
  assert (TS : TASK_SIZE = 2 ^ 47) by (vm_compute; reflexivity).
  destruct (Z_lt_le_dec (bv_unsigned a) (e_S E - SLOT_FRAME + 80)) as [L1|L1].
  - destruct (Z_lt_le_dec (bv_unsigned a) (e_S E - SLOT_FRAME + 64)) as [L2|L2].
    + rewrite (MU a ltac:(unfold c1a_W; cbn [outside]; split; [lia | exact I])) in Ha. exact (T a b Ha).
    + right. rewrite TS. unfold SLOT_FRAME in *. lia.
  - rewrite (MU a ltac:(unfold c1a_W; cbn [outside]; split; [lia | exact I])) in Ha. exact (T a b Ha).
Qed.

Lemma c1a_seg_fp : forall E m m', munch (c1a_W E) m m' -> wmono rsegs m m' -> seg_fp (e_S E) (c1_hp E) m m'.
Proof.
  intros E m m' MU WM. exists (c1a_W E). split; [exact MU|]. split; [exact WM|].
  intros x _ Hx. left. unfold c1a_W in Hx. cbn [outside] in Hx.
  destruct (Z_lt_le_dec x (e_S E - SLOT_FRAME + 64)) as [L|L];
    [exfalso; apply Hx; split; [lia | exact I]|].
  destruct (Z_lt_le_dec x (e_S E - SLOT_FRAME + 80)) as [L'|L'];
    [|exfalso; apply Hx; split; [lia | exact I]].
  unfold SLOT_FRAME, SLOT_STACK_Z in *. lia.
Qed.
