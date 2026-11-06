From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Image ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib DgnLink StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TImg TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import bcmp_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem TImgP TContract check_state_desk_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- values of registers and branch conditions ---- *)

Lemma csd_eqb_s32 : forall a b, -2^31 <= a < 2^31 -> -2^31 <= b < 2^31 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec a b) as [->|NE]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E. apply NE. Z.div_mod_to_equations. lia.
Qed.

Lemma csd_lts_s32 : forall a b, -2^31 <= a < 2^31 -> -2^31 <= b < 2^31 ->
  bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof.
  intros a b Ha Hb. unfold bv_lts.
  assert (S : forall z, -2^31 <= z < 2^31 -> bv_signed (Z_to_bv 64 z) = z).
  { intros z Hz. rewrite zb_signed, unsigned_lit_wrap.
    destruct (Z.ltb_spec 0 (z + 1)).
    - rewrite Z.mod_small by lia. destruct (Z.ltb_spec z (2^63)); lia.
    - replace (z mod 2^64) with (z + 2^64).
      + destruct (Z.ltb_spec (z + 2^64) (2^63)); lia.
      + symmetry. rewrite <- (Z.mod_add z 1 (2^64)) by lia. apply Z.mod_small. lia. }
  rewrite !S by assumption. reflexivity.
Qed.

Lemma csd_eqb_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit by assumption. reflexivity. Qed.

Lemma csd_seqz : forall x, 0 <= x < 2^64 -> v_sltiu (Z_to_bv 64 x) 1 = Z_to_bv 64 (Z.b2z (x =? 0)).
Proof.
  intros x Hx. unfold v_sltiu. rewrite unsigned_lit by exact Hx. change (bv_wrap 64 1) with 1.
  destruct (Z.ltb_spec x 1); destruct (Z.eqb_spec x 0); try reflexivity; lia.
Qed.

Lemma csd_snez : forall x, 0 <= x < 2^64 -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 x) = Z_to_bv 64 (Z.b2z (negb (x =? 0))).
Proof.
  intros x Hx. unfold v_sltu, c_ltu, bv_ltu. rewrite (unsigned_lit 0) by lia. rewrite unsigned_lit by exact Hx.
  destruct (Z.ltb_spec 0 x); destruct (Z.eqb_spec x 0); try reflexivity; lia.
Qed.

Lemma csd_eqb_b2z : forall x y : bool, bv_eqb (Z_to_bv 64 (Z.b2z x)) (Z_to_bv 64 (Z.b2z y)) = Bool.eqb x y.
Proof. intros [|] [|]; reflexivity. Qed.

Lemma csd_byte_rng : forall b : byte, 0 <= bz b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b). unfold bv_modulus, bz in *. change (Z.of_N 8) with 8 in *. lia.
Qed.

Lemma csd_eqb_byte : forall (b c : byte), bv_eqb (zxb b) (zxb c) = (bz b =? bz c).
Proof.
  intros b c. pose proof (csd_byte_rng b). pose proof (csd_byte_rng c).
  unfold bv_eqb, zxb, bz in *. rewrite !unsigned_lit by lia. reflexivity.
Qed.

Lemma csd_zxb0 : forall b : byte, bv_eqb (zxb b) (Z_to_bv 64 0) = (bz b =? 0).
Proof.
  intros b. pose proof (csd_byte_rng b).
  unfold bv_eqb, zxb, bz in *. rewrite !unsigned_lit by lia. reflexivity.
Qed.

(* ---- reads ---- *)

Lemma csd_firstn1 : forall (l : list byte) j d, (j < length l)%nat -> firstn 1 (skipn j l) = [nth j l d].
Proof.
  induction l as [|x l IH]; intros [|j] d H; cbn in H; try lia; cbn [skipn firstn nth]; [reflexivity|].
  apply IH. lia.
Qed.

Lemma csd_rd1 : forall m a bs (k : Z) addr, bytes_at rsegs m a bs -> 0 <= k -> (Z.to_nat k < length bs)%nat ->
  addr = a + k -> ov_read_bytes rsegs m (Z_to_bv 64 addr) 1 = Some [nth (Z.to_nat k) bs (b8 0)].
Proof.
  intros m a bs k addr H Hk Hn ->. change (Z_to_bv 64 (a + k)) with (wa (a + k)).
  rewrite (bytes_at_read rsegs m a bs k 1 H Hk ltac:(lia)). f_equal. apply csd_firstn1. exact Hn.
Qed.

Lemma csd_rd4 : forall m a bs (k : Z) addr, bytes_at rsegs m a bs -> 0 <= k -> (Z.to_nat k + 4 <= length bs)%nat ->
  addr = a + k -> ov_read_bytes rsegs m (Z_to_bv 64 addr) 4 = Some (sub bs k 4).
Proof.
  intros m a bs k addr H Hk Hn ->. change (Z_to_bv 64 (a + k)) with (wa (a + k)).
  apply (bytes_at_read rsegs m a bs k 4 H Hk Hn).
Qed.

Lemma csd_rd8 : forall m a bs (k : Z) addr, bytes_at rsegs m a bs -> 0 <= k -> (Z.to_nat k + 8 <= length bs)%nat ->
  addr = a + k -> ov_read_bytes rsegs m (Z_to_bv 64 addr) 8 = Some (sub bs k 8).
Proof.
  intros m a bs k addr H Hk Hn ->. change (Z_to_bv 64 (a + k)) with (wa (a + k)).
  apply (bytes_at_read rsegs m a bs k 8 H Hk Hn).
Qed.

(* ---- .data.rel.ro: the image bytes are still there, as bytes_at ---- *)

Lemma csd_img_nth : forall n a bs i, image_bytes rsegs a n = Some bs -> (i < n)%nat ->
  seg_rom rsegs (wa (a + Z.of_nat i)) = nth_error bs i.
Proof.
  induction n as [|n IH]; intros a bs i H Hi; cbn in H; [lia|].
  destruct (seg_rom rsegs (wa a)) as [b|] eqn:E1; [|discriminate].
  destruct (image_bytes rsegs (a + 1) n) as [bs'|] eqn:E2; [|discriminate].
  injection H as <-. destruct i as [|i]; cbn [nth_error].
  - rewrite Z.add_0_r. exact E1.
  - rewrite <- (IH (a + 1) bs' i E2 ltac:(lia)). f_equal. unfold wa. f_equal. lia.
Qed.

Lemma csd_relro_bytes : forall m a bs, relro_img m ->
  RELRO_BASE <= a -> a + Z.of_nat (length bs) <= RELRO_BASE + RELRO_LEN ->
  image_bytes rsegs a (length bs) = Some bs -> bytes_at rsegs m a bs.
Proof.
  intros m a bs RE H1 H2 HI. unfold RELRO_BASE, RELRO_LEN in H1, H2.
  split; [lia|]. split; [lia|].
  intros i Hi. rewrite <- (csd_img_nth (length bs) a bs i HI Hi).
  replace (a + Z.of_nat i) with (RELRO_BASE + (a + Z.of_nat i - RELRO_BASE)) by (unfold RELRO_BASE; lia).
  apply RE. unfold RELRO_BASE, RELRO_LEN. lia.
Qed.

Ltac csd_relro_pose H m RELRO a n :=
  let v := eval vm_compute in (image_bytes rsegs a n) in
  lazymatch v with
  | Some ?bs =>
      assert (H : bytes_at rsegs m a bs)
        by (apply (csd_relro_bytes m a bs RELRO);
            [ unfold RELRO_BASE; lia
            | unfold RELRO_BASE, RELRO_LEN; cbn [length]; lia
            | vm_compute; reflexivity ])
  end.

(* a 1-byte read at a + j of a byte span *)
Lemma csd_rd1j : forall m a bs (j : nat) addr, bytes_at rsegs m a bs -> (j < length bs)%nat ->
  addr = a + Z.of_nat j -> ov_read_bytes rsegs m (Z_to_bv 64 addr) 1 = Some [nth j bs (b8 0)].
Proof.
  intros m a bs j addr H Hj ->. change (Z_to_bv 64 (a + Z.of_nat j)) with (wa (a + Z.of_nat j)).
  rewrite (bytes_at_ov_read rsegs m a bs j 1 H ltac:(lia)). f_equal. apply csd_firstn1. exact Hj.
Qed.

(* a span inside a byte span *)
Lemma csd_bsub : forall m a bs (k : Z) q addr, bytes_at rsegs m a bs -> 0 <= k -> (Z.to_nat k + q <= length bs)%nat ->
  addr = a + k -> bytes_at rsegs m addr (sub bs k q).
Proof.
  intros m a bs k q addr (Ha & Hl & Hb) Hk Hn ->.
  assert (LS : length (sub bs k q) = q) by (apply length_sub; lia).
  split; [lia|]. split; [rewrite LS; lia|].
  intros i Hi. rewrite LS in Hi. rewrite ne_sub by lia.
  replace (i <? q)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  replace (a + k + Z.of_nat i) with (a + Z.of_nat (Z.to_nat k + i)) by lia.
  apply Hb. lia.
Qed.

Lemma csd_nth_skipn : forall j (l : list byte) i d, nth i (skipn j l) d = nth (j + i) l d.
Proof.
  induction j as [|j IH]; intros l i d; [reflexivity|].
  destruct l as [|x l].
  - rewrite !nth_overflow by (cbn [length skipn]; lia). reflexivity.
  - cbn [skipn]. replace (S j + i)%nat with (S (j + i))%nat by lia. cbn [nth]. apply IH.
Qed.

Lemma csd_nth_firstn : forall (l : list byte) q i d, (i < q)%nat -> nth i (firstn q l) d = nth i l d.
Proof.
  induction l as [|x l IH]; intros [|q] [|i] d H; cbn [firstn nth]; try lia; try reflexivity.
  apply IH. lia.
Qed.

(* what the inlined spec_strz_len loop (fuzz/spec.h:251-257) reads in the heap frame *)
Lemma csd_strz : forall (fr : tframe) (q : Z) (k : nat), frame_strz_len (Some fr) q = Some k ->
  0 <= q - tf_addr fr /\ (k <= 9)%nat /\
  (Z.to_nat (q - tf_addr fr) + Nat.min 9 (S k) <= length (tf_bytes fr))%nat /\
  (forall i, (i < k)%nat -> bz (nth (Z.to_nat (q - tf_addr fr) + i) (tf_bytes fr) (b8 0)) <> 0) /\
  ((k < 9)%nat -> bz (nth (Z.to_nat (q - tf_addr fr) + k) (tf_bytes fr) (b8 0)) = 0).
Proof.
  intros fr q k H. unfold frame_strz_len in H.
  destruct (Z.ltb_spec (q - tf_addr fr) 0) as [Hneg|Hpos]; [discriminate H|].
  unfold list_strz_len in H.
  destruct (Nat.ltb_spec (length (skipn (Z.to_nat (q - tf_addr fr)) (tf_bytes fr)))
                         (Nat.min 9 (S (strz_len (skipn (Z.to_nat (q - tf_addr fr)) (tf_bytes fr)))))) as [Hl|Hl];
    [discriminate H|].
  injection H as <-.
  pose proof (length_skipn (Z.to_nat (q - tf_addr fr)) (tf_bytes fr)) as LR.
  unfold strz_len in *.
  pose proof (nz_run_le (firstn 9 (skipn (Z.to_nat (q - tf_addr fr)) (tf_bytes fr)))) as NL.
  rewrite length_firstn in NL.
  split; [lia|]. split; [lia|]. split; [lia|]. split.
  - intros i Hi.
    pose proof (nz_run_nonzero (firstn 9 (skipn (Z.to_nat (q - tf_addr fr)) (tf_bytes fr))) i Hi) as NZ.
    unfold at8 in NZ. rewrite csd_nth_firstn in NZ by lia. rewrite csd_nth_skipn in NZ. exact NZ.
  - intros Hk.
    assert (LT : (nz_run (firstn 9 (skipn (Z.to_nat (q - tf_addr fr)) (tf_bytes fr)))
                  < length (firstn 9 (skipn (Z.to_nat (q - tf_addr fr)) (tf_bytes fr))))%nat)
      by (rewrite length_firstn; lia).
    pose proof (nz_run_zero (firstn 9 (skipn (Z.to_nat (q - tf_addr fr)) (tf_bytes fr))) LT) as NZ.
    unfold at8 in NZ. rewrite csd_nth_firstn in NZ by lia. rewrite csd_nth_skipn in NZ. exact NZ.
Qed.

(* the bytes frame_read gives, and where they are *)
Lemma csd_frame_read : forall m (fr : tframe) (q : Z) (k : nat) (bs : list byte),
  frame_read (Some fr) q (Z.of_nat k) = Some bs -> bytes_at rsegs m (tf_addr fr) (tf_bytes fr) ->
  0 <= q -> q <= 2 ^ 64 -> length bs = k /\ bytes_at rsegs m q bs.
Proof.
  intros m fr q k bs H HF Hq0 Hq1. unfold frame_read in H.
  destruct (Z.eqb_spec (Z.of_nat k) 0) as [E0|E0].
  - injection H as <-. assert (Ek : k = 0%nat) by lia. subst k. split; [reflexivity|]. apply bytes_at_nil. lia.
  - destruct ((q - tf_addr fr <? 0) || (Z.of_nat k <? 0)
              || (Z.of_nat (length (tf_bytes fr)) <? q - tf_addr fr + Z.of_nat k)) eqn:EB; [discriminate H|].
    apply orb_false_iff in EB. destruct EB as [EB EB3]. apply orb_false_iff in EB. destruct EB as [EB1 EB2].
    apply Z.ltb_ge in EB1. apply Z.ltb_ge in EB3.
    injection H as <-. rewrite Nat2Z.id. split.
    + apply length_sub; lia.
    + apply (csd_bsub m (tf_addr fr) (tf_bytes fr) (q - tf_addr fr) k);
        [exact HF | lia | lia | lia].
Qed.

(* memcmp of two spans that agree *)
Lemma csd_memcmp0 : forall q (l r : list byte), (q <= length l)%nat -> length r = q ->
  zs (firstn q l) = zs r -> memcmp_model l r q = Some 0.
Proof.
  induction q as [|q IH]; intros l r Hl Hr Hz; [reflexivity|].
  destruct l as [|x l]; [cbn [length] in Hl; lia|]. destruct r as [|y r]; [cbn [length] in Hr; lia|].
  cbn [memcmp_model]. unfold zs in Hz. cbn [firstn map] in Hz. injection Hz as Hxy Hz'.
  replace (bv_unsigned x =? bv_unsigned y) with true by (symmetry; apply Z.eqb_eq; exact Hxy).
  apply IH; [cbn [length] in Hl; lia | cbn [length] in Hr; lia | exact Hz'].
Qed.

Lemma csd_beq : forall a b, beq_bytes a b = true -> zs a = zs b.
Proof.
  intros a b H. unfold beq_bytes in H.
  destruct (list_eq_dec Z.eq_dec (zs a) (zs b)) as [E|E]; [exact E | discriminate H].
Qed.

Lemma csd_nth_sub0 : forall (l : list byte) q i d, (i < q)%nat -> nth i (sub l 0 q) d = nth i l d.
Proof. intros l q i d H. unfold sub. cbn [Z.to_nat skipn]. apply csd_nth_firstn. exact H. Qed.

Lemma csd_firstn_sub0 : forall (l : list byte) q i, (i <= q)%nat -> firstn i (sub l 0 q) = firstn i l.
Proof.
  intros l q i H. unfold sub. cbn [Z.to_nat skipn]. rewrite firstn_firstn. rewrite Nat.min_l by lia. reflexivity.
Qed.

Ltac cur_mem := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => mm end.
(* a branch whose condition tac proves false / true *)
Ltac brf tac := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota | symmetry; tac] end.
Ltac brt tac := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with true; [cbv iota | symmetry; tac] end.
(* a branch on a closed condition: compute it (no open value is in it) *)
Ltac brc := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
  end.

Ltac csd_rdb H HB j addr :=
  lazymatch type of HB with
  | bytes_at rsegs ?mm ?base ?bs =>
      assert (H : ov_read_bytes rsegs mm (Z_to_bv 64 addr) 1 = Some [nth j bs (b8 0)])
        by (apply (csd_rd1j mm base bs j addr HB); [cbn [length]; lia | lia])
  end.

Theorem check_state_desk_holds : bcmp_contract -> check_state_desk_contract.
Proof.
  intros BC. unfold check_state_desk_contract, check_state_desk_ENTRY, check_state_desk_FRAME.
  unfold bcmp_contract, BCMP in BC.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    B B' p n Fr -> NTC FRM RELRO WM HM S16 ST LO WOS MI.
  unfold w_off_stack in WOS.
  destruct NTC as (Pnz & Palign & PoffW & PoffWin & NB & HNB & LNB & Hkind & Hstate & Hold & Hreason & Hpers & Hmac
                   & Hblen & Hcnt & Hretry & HNbody & HboffW & HboffWin & Hann).
  unfold off_world, off_window in PoffW, PoffWin, HboffW, HboffWin.
  clear Hkind Hstate Hold Hreason Hblen Hcnt Hretry HNbody HboffW HboffWin.
  pose proof (bytes_at_bound rsegs m p NB HNB) as PB. rewrite LNB in PB.
  pose proof (u_at_range NB 32 8) as RNp. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in RNp.
  pose proof (u_at_range B 65552 8) as RNd. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in RNd.
  pose proof (u_at_range B 65560 8) as RNb. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in RNb.
  pose proof (u_at_range NB 24 8) as RNa. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in RNa.
  (* the model premise, in the machine's world offsets *)
  assert (EA1 : A_GOT_desk = 65292) by (vm_compute; reflexivity).
  assert (EA2 : A_OW_desk = 65520) by (vm_compute; reflexivity).
  assert (EA3 : A_OW_desk_off = 65544) by (vm_compute; reflexivity).
  assert (EA4 : A_OW_desk_p = 65552) by (vm_compute; reflexivity).
  assert (EA5 : A_OW_desk_body = 65560) by (vm_compute; reflexivity).
  unfold check_state_desk_m in HM.
  unfold GOT_desk, OW_desk, OW_desk_off, OW_desk_p, OW_desk_body in HM.
  rewrite ?EA1, ?EA2, ?EA3, ?EA4, ?EA5 in HM.
  rewrite <- Hmac, <- Hpers in HM.
  destruct ((s32_at B 65520 <? s32_at B 65292) || negb (s32_at NB 40 =? s32_at B 65544)
            || negb (Bool.eqb (u_at NB 32 8 =? 0) (u_at B 65552 8 =? 0))) eqn:C0; [discriminate HM|].
  apply orb_false_iff in C0. destruct C0 as [C0 C3]. apply orb_false_iff in C0. destruct C0 as [C1 C2].
  apply negb_false_iff in C2. apply negb_false_iff in C3. apply Bool.eqb_prop in C3.
  (* the model's announce / frame facts, with the device check resolved either way *)
  assert (MT : exists (va : tann) (vn nn : nat) (vb nb : list byte),
    n_ann n = Some va /\ (u_at B 65560 8 =? 0) = false /\
    frame_strz_len Fr (u_at B 65560 8 + 15) = Some vn /\
    frame_strz_len Fr (u_at B 65560 8 + 24) = Some nn /\
    frame_read Fr (u_at B 65560 8 + 15) (Z.of_nat vn) = Some vb /\
    frame_read Fr (u_at B 65560 8 + 24) (Z.of_nat nn) = Some nb /\
    beq_bytes (firstn vn (ta_version va)) vb = true /\ (vn < length (ta_version va))%nat /\
    bz (nth vn (ta_version va) (b8 0)) = 0 /\
    beq_bytes (firstn nn (ta_name va)) nb = true /\ (nn < length (ta_name va))%nat /\
    bz (nth nn (ta_name va) (b8 0)) = 0 /\ B' = B).
  { destruct (if u_at NB 32 8 =? 0 then Some false
              else match personality_ptr timg_plain (u_at NB 32 8) with
                   | Some pr => match spec_desk_at timg_plain (u_at B 65552 8) with
                                | Some dk => Some (negb (dp_device pr =? d_dev dk) || negb (dp_strips pr =? d_strips dk))
                                | None => None
                                end
                   | None => None
                   end) as [bad|] eqn:EB; [|discriminate HM].
    destruct bad; [discriminate HM|].
    destruct (n_ann n) as [va|] eqn:HVA; [|discriminate HM].
    destruct (u_at B 65560 8 =? 0) eqn:HDB; [discriminate HM|].
    unfold SPEC_ANN_VERSION, SPEC_ANN_NAME in HM.
    destruct (frame_strz_len Fr (u_at B 65560 8 + 15)) as [vn|] eqn:HVN; [|discriminate HM].
    destruct (frame_strz_len Fr (u_at B 65560 8 + 24)) as [nn|] eqn:HNN; [|discriminate HM].
    destruct (frame_read Fr (u_at B 65560 8 + 15) (Z.of_nat vn)) as [vb|] eqn:HVB; [|discriminate HM].
    destruct (frame_read Fr (u_at B 65560 8 + 24) (Z.of_nat nn)) as [nb|] eqn:HNB2; [|discriminate HM].
    destruct (beq_bytes (firstn vn (ta_version va)) vb) eqn:HBV; [|discriminate HM].
    destruct ((length (ta_version va) <=? vn)%nat) eqn:HLV; [discriminate HM|].
    destruct (truth (bz (nth vn (ta_version va) (b8 0)))) eqn:HZV; [discriminate HM|].
    destruct (beq_bytes (firstn nn (ta_name va)) nb) eqn:HBN; [|discriminate HM].
    destruct ((length (ta_name va) <=? nn)%nat) eqn:HLN; [discriminate HM|].
    destruct (truth (bz (nth nn (ta_name va) (b8 0)))) eqn:HZN; [discriminate HM|].
    unfold truth in HZV, HZN. apply negb_false_iff in HZV. apply negb_false_iff in HZN.
    apply Z.eqb_eq in HZV. apply Z.eqb_eq in HZN.
    apply Nat.leb_gt in HLV. apply Nat.leb_gt in HLN.
    cbv beta iota delta [negb] in HM.
    exists va, vn, nn, vb, nb.
    repeat split; try assumption. congruence. }
  destruct MT as (va & vn & nn & vb & nb & HVA & HDB & HVN & HNN & HVB & HNB2 & HBV & HLV & HZV & HBN & HLN & HZN & HBB).
  subst B'.
  apply Z.eqb_neq in HDB.
  (* the heap frame and the announce *)
  destruct Fr as [fr|]; [|discriminate HVN].
  unfold tframe_at in FRM. cbv iota in FRM.
  destruct FRM as (Fnz & HFB & FoffW & FoffWin). unfold off_world, off_window in FoffW, FoffWin.
  rewrite HVA in Hann. cbv iota in Hann.
  destruct Hann as (Anz & Aalign & HAV & HAN & AoffW & AoffWin). unfold off_world, off_window in AoffW, AoffWin.
  pose proof (bytes_at_bound rsegs m (tf_addr fr) (tf_bytes fr) HFB) as FBB.
  pose proof (bytes_at_bound rsegs m (u_at NB 24 8) (ta_version va) HAV) as AVB.
  pose proof (bytes_at_bound rsegs m (u_at NB 24 8 + 10) (ta_name va) HAN) as ANB.
  (* only the 10 bytes of each announce field are inside the span the contract gives *)
  pose proof (csd_bsub m (u_at NB 24 8) (ta_version va) 0 (Nat.min 10 (length (ta_version va))) (u_at NB 24 8)
                HAV ltac:(lia) ltac:(cbn [Z.to_nat]; lia) ltac:(lia)) as HAV10.
  pose proof (csd_bsub m (u_at NB 24 8 + 10) (ta_name va) 0 (Nat.min 10 (length (ta_name va))) (u_at NB 24 8 + 10)
                HAN ltac:(lia) ltac:(cbn [Z.to_nat]; lia) ltac:(lia)) as HAN10.
  assert (LAV : length (sub (ta_version va) 0 (Nat.min 10 (length (ta_version va))))
                = Nat.min 10 (length (ta_version va))) by (apply length_sub; cbn [Z.to_nat]; lia).
  assert (LAN : length (sub (ta_name va) 0 (Nat.min 10 (length (ta_name va))))
                = Nat.min 10 (length (ta_name va))) by (apply length_sub; cbn [Z.to_nat]; lia).
  clear HAV HAN.
  pose proof (csd_strz fr (u_at B 65560 8 + 15) vn HVN) as (SV1 & SV2 & SV3 & SV4 & SV5).
  pose proof (csd_strz fr (u_at B 65560 8 + 24) nn HNN) as (SN1 & SN2 & SN3 & SN4 & SN5).
  (* the two fields start inside the frame block, so neither address wraps *)
  assert (DBV : u_at B 65560 8 + 15 + 1 <= 2 ^ 64) by lia.
  assert (DBN : u_at B 65560 8 + 24 + 1 <= 2 ^ 64) by lia.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMo.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  wk_facts.
  (* the four .data.rel.ro bytes the device / strips checks read *)
  csd_relro_pose RP0 m RELRO 136240 2%nat.
  csd_relro_pose RP1 m RELRO 136264 2%nat.
  csd_relro_pose RD24 m RELRO 136176 2%nat.
  csd_relro_pose RDPC m RELRO 136192 2%nat.
  clear HVN HNN HVA Hpers Hmac EA1 EA2 EA3 EA4 EA5 RELRO PoffW FoffW AoffW Fnz.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  carve_frame 48%nat ST.
  do 6 step.
  lazymatch type of FR with rw_cells _ _ _ ?cs => set (FRC := cs) in FR end.
  clear PoffWin AoffWin FoffWin.
  (* ---- the epilogue at 0x15b38 ---- *)
  assert (EPI : forall (m' : word -> option byte)
                  (q1 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q28 q29 q30 q31 : word),
    rw_cells rsegs m' (bv_unsigned sp + -48) FRC ->
    stk rsegs m' lo (bv_unsigned sp + -48) ->
    munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    wmem rsegs m' B ->
    evt rsegs QQ (MS (mkR q1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17
                          q18 q19 s4 s5 s6 s7 s8 s9 s10 s11 q28 q29 q30 q31)
                     F (Z_to_bv 64 88888) fc None m' (seg_rom rsegs))).
  { intros m' q1 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q28 q29 q30 q31 FR' ST' MU' WM' MI' WB'.
    unfold FRC in FR'.
    do 7 step.
    release_frame FR' ST' (bv_unsigned sp).
    apply evt_done. unfold QQ. do 15 eexists. eexists. split; [reflexivity|].
    split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact ST'|].
    split; [reflexivity | exact WB']. }
  (* ---- 0x15af8: the two bcmp calls, the NUL after each field ---- *)
  let mm := cur_mem in
  assert (CMP : forall (q1 q5 q6 q7 q10 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 : word),
    evt rsegs QQ (MS (mkR q1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp q5 q6 q7
                          (Z_to_bv 64 (u_at NB 24 8)) (Z_to_bv 64 (Z.of_nat vn)) q10
                          (Z_to_bv 64 (u_at B 65560 8 + 15)) q12 q13 q14 q15 q16 q17
                          (Z_to_bv 64 (u_at B 65560 8 + 24)) (Z_to_bv 64 (Z.of_nat nn))
                          s4 s5 s6 s7 s8 s9 s10 s11 q28 q29 q30 q31)
                     F (Z_to_bv 64 88824) fc None mm (seg_rom rsegs))).
  { clear HM C1 C2 C3 RP0 RP1 RD24 RDPC Palign SV1 SV3 SV4 SV5 SN1 SN3 SN4 SN5 HNB LNB.
    intros q1 q5 q6 q7 q10 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31.
    let mm := cur_mem in
    pose proof (csd_frame_read mm fr (u_at B 65560 8 + 15) vn vb HVB HFB ltac:(lia) ltac:(lia)) as [LVB HVBB].
    let mm := cur_mem in
    pose proof (csd_frame_read mm fr (u_at B 65560 8 + 24) nn nb HNB2 HFB ltac:(lia) ltac:(lia)) as [LNB3 HNBB].
    do 3 step.
    let mm := cur_mem in
    eapply evt_cut;
      [ eapply BC with (ls := sub (ta_version va) 0 (Nat.min 10 (length (ta_version va)))) (rs := vb) (v := 0);
        [ rewrite unsigned_lit by lia; exact HAV10
        | rewrite unsigned_lit by lia; exact HVBB
        | rewrite unsigned_lit by lia; rewrite Nat2Z.id;
          apply csd_memcmp0; [lia | exact LVB | rewrite csd_firstn_sub0 by lia; exact (csd_beq _ _ HBV)]
        | assumption ]
      | wk_post_call rsegs mm ].
    step.
    brf ltac:(reflexivity).
    step.
    csd_rdb RD HAV10 vn (u_at NB 24 8 + Z.of_nat vn).
    step. clear RD.
    step.
    brf ltac:(rewrite csd_zxb0; rewrite csd_nth_sub0 by lia; rewrite HZV; reflexivity).
    do 5 step.
    let mm := cur_mem in
    eapply evt_cut;
      [ eapply BC with (ls := sub (ta_name va) 0 (Nat.min 10 (length (ta_name va)))) (rs := nb) (v := 0);
        [ rewrite unsigned_lit by lia; exact HAN10
        | rewrite unsigned_lit by lia; exact HNBB
        | rewrite unsigned_lit by lia; rewrite Nat2Z.id;
          apply csd_memcmp0; [lia | exact LNB3 | rewrite csd_firstn_sub0 by lia; exact (csd_beq _ _ HBN)]
        | assumption ]
      | wk_post_call rsegs mm ].
    step.
    brf ltac:(reflexivity).
    step.
    csd_rdb RD2 HAN10 nn (u_at NB 24 8 + 10 + Z.of_nat nn).
    step. clear RD2.
    step.
    brf ltac:(rewrite csd_zxb0; rewrite csd_nth_sub0 by lia; rewrite HZN; reflexivity).
    apply EPI; assumption. }
  (* ---- 0x15adc: the inlined spec_strz_len over the name field at OW.desk_body + 24 ---- *)
  let mm := cur_mem in
  assert (LOOP2 : forall (k i : nat), (k = nn - i)%nat -> (i <= nn)%nat -> (i < 9)%nat ->
    forall (q1 q5 q6 q7 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 : word),
    evt rsegs QQ (MS (mkR q1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp q5 q6 q7
                          (Z_to_bv 64 (u_at NB 24 8)) (Z_to_bv 64 (Z.of_nat vn)) (Z_to_bv 64 (Z.of_nat i))
                          (Z_to_bv 64 (u_at B 65560 8 + 15))
                          q12 q13 q14 q15 q16 q17
                          (Z_to_bv 64 (u_at B 65560 8 + 24)) (Z_to_bv 64 9)
                          s4 s5 s6 s7 s8 s9 s10 s11 q28 q29 q30 q31)
                     F (Z_to_bv 64 88796) fc None mm (seg_rom rsegs))).
  { clear HM C1 C2 C3 RP0 RP1 RD24 RDPC Palign HAV10 HAN10 LAV LAN HBV HBN HZV HZN HVB HNB2 HLV HLN Aalign AVB ANB
      SV1 SV3 SV4 SV5 HNB LNB Anz.
    induction k as [|k IH]; intros i Hk Hi H9 q1 q5 q6 q7 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31.
    - assert (Ei : i = nn) by lia. subst i.
      step.
      csd_rdb RD HFB (Z.to_nat (u_at B 65560 8 + 24 - tf_addr fr) + nn)%nat (u_at B 65560 8 + 24 + Z.of_nat nn).
      step. clear RD.
      step.
      brt ltac:(rewrite csd_zxb0; rewrite (SN5 ltac:(lia)); reflexivity).
      step. apply CMP.
    - step.
      csd_rdb RD HFB (Z.to_nat (u_at B 65560 8 + 24 - tf_addr fr) + i)%nat (u_at B 65560 8 + 24 + Z.of_nat i).
      step. clear RD.
      step.
      brf ltac:(rewrite csd_zxb0; apply Z.eqb_neq; exact (SN4 i ltac:(lia))).
      step. step.
      rewrite csd_eqb_lit by lia.
      destruct (Z.eqb_spec (Z.of_nat i + 1) 9) as [E9|E9]; cbn [negb]; cbv iota.
      + step. replace (Z_to_bv 64 9) with (Z_to_bv 64 (Z.of_nat nn)) by (f_equal; lia). apply CMP.
      + replace (Z_to_bv 64 (Z.of_nat i + 1)) with (Z_to_bv 64 (Z.of_nat (S i))) by (f_equal; lia).
        apply (IH (S i)); lia. }
  (* ---- 0x15ad0: the second field's set-up ---- *)
  let mm := cur_mem in
  assert (ENT2 : forall (q1 q5 q6 q7 q10 q12 q13 q14 q15 q16 q17 q19 q28 q29 q30 q31 : word),
    evt rsegs QQ (MS (mkR q1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp q5 q6 q7
                          (Z_to_bv 64 (u_at NB 24 8)) (Z_to_bv 64 (Z.of_nat vn)) q10
                          (Z_to_bv 64 (u_at B 65560 8 + 15)) q12 q13 q14 q15 q16 q17
                          (Z_to_bv 64 (u_at B 65560 8)) q19
                          s4 s5 s6 s7 s8 s9 s10 s11 q28 q29 q30 q31)
                     F (Z_to_bv 64 88784) fc None mm (seg_rom rsegs))).
  { clear HM C1 C2 C3 RP0 RP1 RD24 RDPC Palign HAV10 HAN10 LAV LAN HBV HBN HZV HZN HVB HNB2 HLV HLN Aalign AVB ANB
      SV1 SV3 SV4 SV5 SN4 SN5 HNB LNB.
    intros q1 q5 q6 q7 q10 q12 q13 q14 q15 q16 q17 q19 q28 q29 q30 q31.
    do 3 step.
    apply (LOOP2 nn 0%nat); lia. }
  (* ---- 0x15ab4: the inlined spec_strz_len over the version field at OW.desk_body + 15 ---- *)
  let mm := cur_mem in
  assert (LOOP1 : forall (k i : nat), (k = vn - i)%nat -> (i <= vn)%nat -> (i < 9)%nat ->
    forall (q1 q5 q6 q7 q12 q13 q14 q15 q16 q17 q19 q28 q29 q30 q31 : word),
    evt rsegs QQ (MS (mkR q1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp q5 q6 q7
                          (Z_to_bv 64 (u_at NB 24 8)) (Z_to_bv 64 9) (Z_to_bv 64 (Z.of_nat i))
                          (Z_to_bv 64 (u_at B 65560 8 + 15))
                          q12 q13 q14 q15 q16 q17
                          (Z_to_bv 64 (u_at B 65560 8)) q19
                          s4 s5 s6 s7 s8 s9 s10 s11 q28 q29 q30 q31)
                     F (Z_to_bv 64 88756) fc None mm (seg_rom rsegs))).
  { clear HM C1 C2 C3 RP0 RP1 RD24 RDPC Palign HAV10 HAN10 LAV LAN HBV HBN HZV HZN HVB HNB2 HLV HLN Aalign AVB ANB
      SN1 SN3 SN4 SN5 HNB LNB Anz.
    induction k as [|k IH]; intros i Hk Hi H9 q1 q5 q6 q7 q12 q13 q14 q15 q16 q17 q19 q28 q29 q30 q31.
    - assert (Ei : i = vn) by lia. subst i.
      step.
      csd_rdb RD HFB (Z.to_nat (u_at B 65560 8 + 15 - tf_addr fr) + vn)%nat (u_at B 65560 8 + 15 + Z.of_nat vn).
      step. clear RD.
      step.
      brt ltac:(rewrite csd_zxb0; rewrite (SV5 ltac:(lia)); reflexivity).
      step. apply ENT2.
    - step.
      csd_rdb RD HFB (Z.to_nat (u_at B 65560 8 + 15 - tf_addr fr) + i)%nat (u_at B 65560 8 + 15 + Z.of_nat i).
      step. clear RD.
      step.
      brf ltac:(rewrite csd_zxb0; apply Z.eqb_neq; exact (SV4 i ltac:(lia))).
      step. step.
      rewrite csd_eqb_lit by lia.
      destruct (Z.eqb_spec (Z.of_nat i + 1) 9) as [E9|E9]; cbn [negb]; cbv iota.
      + step. replace (Z_to_bv 64 9) with (Z_to_bv 64 (Z.of_nat vn)) by (f_equal; lia). apply ENT2.
      + replace (Z_to_bv 64 (Z.of_nat i + 1)) with (Z_to_bv 64 (Z.of_nat (S i))) by (f_equal; lia).
        apply (IH (S i)); lia. }
  (* ---- 0x15a9c: the announce, OW.desk_body, and the first field's set-up ---- *)
  let mm := cur_mem in
  assert (TAIL : forall (q1 q5 q6 q7 q8 q9 q12 q13 q14 q15 q16 q17 q18 q19 q28 q29 q30 q31 : word),
    evt rsegs QQ (MS (mkR q1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp q5 q6 q7 q8 q9
                          (Z_to_bv 64 p) (Z_to_bv 64 271704) q12 q13 q14 q15 q16 q17 q18 q19
                          s4 s5 s6 s7 s8 s9 s10 s11 q28 q29 q30 q31)
                     F (Z_to_bv 64 88732) fc None mm (seg_rom rsegs))).
  { clear HM C1 C2 C3 RP0 RP1 RD24 RDPC Palign HAV10 HAN10 LAV LAN HBV HBN HZV HZN HVB HNB2 HLV HLN Aalign AVB ANB
      SV4 SV5 SN1 SN3 SN4 SN5.
    intros q1 q5 q6 q7 q8 q9 q12 q13 q14 q15 q16 q17 q18 q19 q28 q29 q30 q31.
    let mm := cur_mem in
    pose proof (csd_rd8 mm p NB 24 (p + 24) HNB ltac:(lia) ltac:(rewrite LNB; lia) ltac:(reflexivity)) as RD.
    step. clear RD. rewrite wm_ld.
    step.
    brf ltac:(rewrite csd_eqb_lit by lia; apply Z.eqb_neq; lia).
    do 4 step.
    apply (LOOP1 vn 0%nat); lia. }
  (* ---- the head: GOT.desk <= OW.desk, the mac offset, the personality ---- *)
  clear HAV10 HAN10 LAV LAN HBV HBN HZV HZN HVB HNB2 HLV HLN Aalign AVB ANB SV1 SV3 SV4 SV5 SN1 SN3 SN4 SN5.
  do 5 step.
  brf ltac:(rewrite csd_lts_s32 by (apply s32_range); exact C1).
  let mm := cur_mem in
  pose proof (csd_rd4 mm p NB 40 (p + 40) HNB ltac:(lia) ltac:(rewrite LNB; lia) ltac:(reflexivity)) as RD.
  step. clear RD. rewrite wm_lw.
  step.
  step.
  brf ltac:(rewrite csd_eqb_s32 by (apply s32_range); rewrite C2; reflexivity).
  let mm := cur_mem in
  pose proof (csd_rd8 mm p NB 32 (p + 32) HNB ltac:(lia) ltac:(rewrite LNB; lia) ltac:(reflexivity)) as RD.
  step. clear RD. rewrite wm_ld.
  step.
  step. rewrite csd_seqz by lia.
  step. rewrite csd_snez by lia.
  step.
  brf ltac:(rewrite csd_eqb_b2z; rewrite C3; destruct (u_at B 65552 8 =? 0); reflexivity).
  step.
  rewrite csd_eqb_lit by lia.
  destruct (Z.eqb_spec (u_at NB 32 8) 0) as [PN0|PN0]; cbv iota.
  - apply TAIL.
  - (* the personality and OW.desk_p name records of .data.rel.ro *)
    replace (u_at NB 32 8 =? 0) with false in HM by (symmetry; apply Z.eqb_neq; exact PN0).
    cbv beta iota in HM.
    destruct (personality_ptr timg_plain (u_at NB 32 8)) as [pr|] eqn:PP; [|discriminate HM].
    destruct (spec_desk_at timg_plain (u_at B 65552 8)) as [dk|] eqn:PD; [|discriminate HM].
    destruct (negb (dp_device pr =? d_dev dk) || negb (dp_strips pr =? d_strips dk)) eqn:BADV;
      [cbv beta iota in HM; discriminate HM|].
    assert (EPERS : ti_personalities timg_plain = 136224) by (vm_compute; reflexivity).
    assert (EC24 : ti_spec_c24 timg_plain = 136168) by (vm_compute; reflexivity).
    assert (ESPC : ti_spec_pc timg_plain = 136184) by (vm_compute; reflexivity).
    unfold personality_ptr in PP. rewrite EPERS in PP.
    destruct ((u_at NB 32 8 - 136224 <? 0) || negb ((u_at NB 32 8 - 136224) mod 24 =? 0)) eqn:POK;
      [discriminate PP|].
    apply orb_false_iff in POK. destruct POK as [POK1 POK2].
    apply Z.ltb_ge in POK1. apply negb_false_iff in POK2. apply Z.eqb_eq in POK2.
    unfold personality_at in PP. unfold spec_desk_at in PD. rewrite EC24, ESPC in PD.
    destruct (Z.to_nat ((u_at NB 32 8 - 136224) / 24)) as [|[|kk]] eqn:EK.
    3: { exfalso.
         assert (HNE : nth_error personalities (S (S kk)) <> None) by (rewrite PP; discriminate).
         apply nth_error_Some in HNE. unfold personalities in HNE. cbn [length] in HNE. lia. }
    all: cbv beta iota delta [nth_error personalities] in PP.
    + assert (Epn : u_at NB 32 8 = 136224).
      { clear - POK1 POK2 EK.
        pose proof (Z.div_mod (u_at NB 32 8 - 136224) 24 ltac:(lia)) as DM. rewrite POK2 in DM.
        pose proof (Z.div_pos (u_at NB 32 8 - 136224) 24 ltac:(lia) ltac:(lia)) as DP. lia. }
      injection PP as <-.
      destruct (Z.eqb_spec (u_at B 65552 8) 136168) as [Epd|Epd]; cbv beta iota in PD.
      * injection PD as <-.
        rewrite Epn, Epd.
        csd_rdb RD1 RP0 0%nat 136240. step. clear RD1.
        csd_rdb RD2 RD24 0%nat 136176. step. clear RD2.
        step. cbn [nth].
        brc.
        csd_rdb RD3 RP0 1%nat 136241. step. clear RD3.
        csd_rdb RD4 RD24 1%nat 136177. step. clear RD4.
        step. cbn [nth].
        brc.
        apply TAIL.
      * destruct (Z.eqb_spec (u_at B 65552 8) 136184) as [Epd2|Epd2]; cbv beta iota in PD; [|discriminate PD].
        injection PD as <-. vm_compute in BADV. discriminate BADV.
    + assert (Epn : u_at NB 32 8 = 136248).
      { clear - POK1 POK2 EK.
        pose proof (Z.div_mod (u_at NB 32 8 - 136224) 24 ltac:(lia)) as DM. rewrite POK2 in DM.
        pose proof (Z.div_pos (u_at NB 32 8 - 136224) 24 ltac:(lia) ltac:(lia)) as DP. lia. }
      injection PP as <-.
      destruct (Z.eqb_spec (u_at B 65552 8) 136168) as [Epd|Epd]; cbv beta iota in PD.
      * injection PD as <-. vm_compute in BADV. discriminate BADV.
      * destruct (Z.eqb_spec (u_at B 65552 8) 136184) as [Epd2|Epd2]; cbv beta iota in PD; [|discriminate PD].
        injection PD as <-.
        rewrite Epn, Epd2.
        csd_rdb RD1 RP1 0%nat 136264. step. clear RD1.
        csd_rdb RD2 RDPC 0%nat 136192. step. clear RD2.
        step. cbn [nth].
        brc.
        csd_rdb RD3 RP1 1%nat 136265. step. clear RD3.
        csd_rdb RD4 RDPC 1%nat 136193. step. clear RD4.
        step. cbn [nth].
        brc.
        apply TAIL.
Qed.
