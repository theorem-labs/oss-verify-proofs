(* copy_strz_holds_F proves copy_strz_contract_F (copy_strz_F_c.v): the run of image B's copy_strz (fuzz_frame.asan-ubsan,
   entry 0x82db4, frame 16 bytes) as an ExecF.evtF run under the footprint RNG, so every data access of every step
   lies in RNG.
   The loop at 0x82de4 copies the bytes of s at src to the field at dst up to the first 0 byte, at most 9 of them;
   0x82e80 stores the 0 byte at dst + k. INVc is the state of memory at each loop head: the field holds i bytes of s,
   then the bytes i .. 9 of old; the frame holds ra at sp - 8.
   The five UBSan branches to the unimp word at 0x82e90 are not taken: src + i (0x82de4) and dst + i (0x82e10, 0x82e68)
   do not wrap (bytes_at gives src + 9 <= 2^64, rw_cells gives dst + 10 <= 2^64), src + i is not 0 (0x82df0) and src is
   not 0 (0x82df4). Before each byte access at x the code loads the shadow byte k at (x >> 3) + 0x7fff8000 and goes on
   at k = 0 or at (x & 7) < k, two paths that rejoin; each of the three checks is the lemma csb_chk_src / csb_chk_dst /
   csb_chk_nul below, which takes the rest of the walk as a continuation quantified over the registers its slow path
   writes. The addressable premises give k = 0 or (x mod 8) < k, so no call of errpath_load1 / errpath_store1 is
   reached. The walk works on sv = firstn 9 s, the bytes the code may read: copy_strz 10 9 reads only those. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA AsanKAProof.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import copy_strz_c copy_strz_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(** * Lists *)

Lemma csb_at8_ne : forall l i b, nth_error l i = Some b -> at8 l i = bz b.
Proof.
  induction l as [|x l IH]; intros [|i] b H; cbn in H; try discriminate.
  - injection H as E. subst. reflexivity.
  - unfold at8 in *. cbn [nth]. apply IH. exact H.
Qed.

Lemma csb_byte_at : forall (l : list byte) i, (i < length l)%nat -> exists b, nth_error l i = Some b.
Proof.
  intros l i Hi. destruct (nth_error l i) eqn:N; [eexists; reflexivity|].
  apply nth_error_None in N. lia.
Qed.

Lemma csb_ne_firstn : forall {A} (l : list A) n i, (i < n)%nat -> nth_error (firstn n l) i = nth_error l i.
Proof.
  intros A l n; revert l; induction n as [|n IH]; intros l i Hi; [lia|].
  destruct l as [|x l]; [destruct i; reflexivity|].
  destruct i as [|i]; [reflexivity|]. cbn [firstn nth_error]. apply IH. lia.
Qed.

Lemma csb_firstn_snoc_nth : forall (s : list byte) j b, nth_error s j = Some b -> firstn (S j) s = firstn j s ++ [b].
Proof.
  induction s as [|c s IH]; intros [|j] b H; cbn in H; try discriminate.
  - injection H as E. subst. reflexivity.
  - cbn [firstn]. rewrite (IH j b H). reflexivity.
Qed.

Lemma csb_upd_at_end : forall (P R : list byte) i z, length P = i -> upd_bytes (P ++ R) i [z] = P ++ z :: skipn 1 R.
Proof.
  intros P R i z <-. unfold upd_bytes. rewrite firstn_app, skipn_app, Nat.sub_diag, firstn_all.
  rewrite (skipn_all2 (n := (length P + length [z])%nat) P) by (cbn [length]; lia).
  cbn [length]. replace (length P + 1 - length P)%nat with 1%nat by lia.
  cbn [firstn app]. rewrite app_nil_r. reflexivity.
Qed.

(* One turn of the loop: the field holds j bytes of s, then byte j of s is stored. *)
Lemma csb_upd_snoc : forall (s X : list byte) j b, nth_error s j = Some b ->
  upd_bytes (firstn j s ++ skipn j X) j [b] = firstn (S j) s ++ skipn (S j) X.
Proof.
  intros s X j b Hn.
  assert (Hj : (j < length s)%nat) by (apply nth_error_Some; congruence).
  rewrite csb_upd_at_end by (rewrite length_firstn; lia).
  rewrite (csb_firstn_snoc_nth s j b Hn), skipn_skipn.
  replace (1 + j)%nat with (S j) by lia. rewrite <- app_assoc. reflexivity.
Qed.

Lemma csb_strz_len_le_len : forall l, (strz_len l <= length l)%nat.
Proof.
  intros l. unfold strz_len. pose proof (nz_run_le (firstn 9 l)) as H. rewrite length_firstn in H. lia.
Qed.

(* The 0 byte after the k = strz_len l bytes of l: the field is copy_strz 10 9 l old. *)
Lemma csb_nul : forall (l old : list byte) (z : byte), bz z = 0 ->
  upd_bytes (firstn (strz_len l) l ++ skipn (strz_len l) old) (strz_len l) [z] = copy_strz 10 9 l old.
Proof.
  intros l old z Hz. assert (Ez : z = b8 0) by (rewrite <- (b8_bz z), Hz; reflexivity). subst z.
  pose proof (csb_strz_len_le_len l) as H.
  rewrite csb_upd_at_end by (rewrite length_firstn; lia).
  unfold copy_strz. change (copy_len 10 9 l) with (strz_len l).
  rewrite skipn_skipn. replace (1 + strz_len l)%nat with (S (strz_len l)) by lia. reflexivity.
Qed.

(* copy_strz 10 9 reads only the first 9 bytes of its source. *)
Lemma csb_copy_firstn9 : forall (l old : list byte), copy_strz 10 9 l old = copy_strz 10 9 (firstn 9 l) old.
Proof.
  intros l old. unfold copy_strz, copy_len. change (Nat.min 9 (10 - 1)) with 9%nat.
  assert (E9 : firstn 9 (firstn 9 l) = firstn 9 l) by (rewrite firstn_firstn; reflexivity).
  rewrite E9.
  pose proof (nz_run_le (firstn 9 l)) as HK. rewrite length_firstn in HK.
  assert (EK : firstn (nz_run (firstn 9 l)) (firstn 9 l) = firstn (nz_run (firstn 9 l)) l)
    by (rewrite firstn_firstn; f_equal; lia).
  rewrite EK. reflexivity.
Qed.

(** * Memory *)

Lemma csb_firstn1_skipn : forall {X} (l : list X) i b, nth_error l i = Some b -> firstn 1 (skipn i l) = [b].
Proof.
  intros X l; induction l as [|c l IH]; intros [|i] b N; cbn in *; try discriminate.
  - injection N as ->. reflexivity.
  - apply IH; exact N.
Qed.

Lemma csb_rdb : forall m A l (i : nat) b, bytes_at rsegs m A l -> nth_error l i = Some b ->
  ov_read_bytes rsegs m (wa (A + Z.of_nat i)) 1 = Some [b].
Proof.
  intros m A l i b BL N. pose proof (nth_error_Some l i) as NS. rewrite N in NS.
  assert (Hi : (i < length l)%nat) by (apply NS; discriminate).
  rewrite (bytes_at_ov_read rsegs m A l i 1 BL ltac:(lia)). f_equal. apply csb_firstn1_skipn. exact N.
Qed.

Lemma csb_rd_all : forall m A bs, bytes_at rsegs m A bs ->
  ov_read_bytes rsegs m (Z_to_bv 64 A) (length bs) = Some bs.
Proof.
  intros m A bs H. change (Z_to_bv 64 A) with (wa A). replace A with (A + Z.of_nat 0) at 1 by lia.
  rewrite (bytes_at_ov_read rsegs m A bs 0 (length bs) H) by lia. cbn [skipn]. rewrite firstn_all. reflexivity.
Qed.

Lemma csb_bytes_firstn : forall m A (l : list byte) n, bytes_at rsegs m A l -> (n <= length l)%nat ->
  bytes_at rsegs m A (firstn n l).
Proof.
  intros m A l n (H0 & H1 & H) Hn.
  assert (LF : length (firstn n l) = n) by (rewrite length_firstn; lia).
  split; [lia|]. split; [rewrite LF; lia|].
  intros i Hi. rewrite LF in Hi. rewrite csb_ne_firstn by lia. apply H. lia.
Qed.

(** * ASan *)

Lemma csb_app_win : forall s d x, 0 < d <= 2^32 -> app_mem (s - d) -> app_mem (s - 1) -> s - d <= x < s -> app_mem x.
Proof. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. intros s d x Hd H1 H2 Hx. lia. Qed.

Lemma csb_shadow_not_app : forall a, app_mem a -> ~ app_mem (a / 8 + ASAN_K).
Proof.
  unfold app_mem, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. intros a Ha Hs. Z.div_mod_to_equations. lia.
Qed.

Lemma csb_shadow_range : forall a, app_mem a -> 0 <= a / 8 + ASAN_K < 2^64.
Proof.
  unfold app_mem, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. intros a Ha. Z.div_mod_to_equations. lia.
Qed.

Lemma csb_mrd_munch : forall W m m' a, munch W m m' -> 0 <= a < 2^64 -> outside W a ->
  mrd rsegs m' (wa a) = mrd rsegs m (wa a).
Proof.
  intros W m m' a MU Ha Ho. unfold mrd. rewrite MU; [reflexivity|]. rewrite wa_unsigned by exact Ha. exact Ho.
Qed.

Lemma csb_addr_munch : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W ((p + i) / 8 + ASAN_K)) -> addressable m' p n.
Proof.
  intros W m m' p n (H0 & H1 & H2 & H) MU D.
  split; [exact H0 | split; [exact H1 | split; [exact H2 | ]]].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hok). split; [exact Ha|]. exists b. split; [|exact Hok].
  unfold shadow_addr in *. rewrite (csb_mrd_munch W m m' _ MU (csb_shadow_range _ Ha) (D i Hi)). exact Hb.
Qed.

Lemma csb_addr_one : forall m p n i, addressable m p n -> 0 <= i < n ->
  app_mem (p + i) /\ exists k, mrd rsegs m (wa ((p + i) / 8 + ASAN_K)) = Some k /\
    (bv_signed k = 0 \/ (p + i) mod 8 < bv_signed k).
Proof.
  intros m p n i (H0 & H1 & H2 & H) Hi. destruct (H i Hi) as (Ha & k & Hk & Hok).
  split; [exact Ha|]. exists k. unfold shadow_addr in Hk. split; [exact Hk|].
  unfold shadow_ok in Hok. lia.
Qed.

Lemma csb_rng_one : forall RNG p n a, ExecF.rng RNG p n -> p <= a < p + n -> ExecF.rng RNG a 1.
Proof. intros RNG p n a H Ha. eapply ExecF.rng_sub; [exact H | lia | lia]. Qed.

Lemma csb_rng_shadow_one : forall RNG p n a,
  ExecF.rng RNG (shadow_addr p) (shadow_addr (p + n - 1) - shadow_addr p + 1) ->
  p <= a < p + n -> ExecF.rng RNG (a / 8 + ASAN_K) 1.
Proof.
  intros RNG p n a H Ha. unfold shadow_addr in H.
  assert (L1 : p / 8 <= a / 8) by (apply Z.div_le_mono; lia).
  assert (L2 : a / 8 <= (p + n - 1) / 8) by (apply Z.div_le_mono; lia).
  eapply ExecF.rng_sub; [exact H | lia | lia].
Qed.

(** * Words *)

Lemma csb_not : forall dst, 0 <= dst < 2^64 ->
  Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 dst)) 18446744073709551615) = Z_to_bv 64 (18446744073709551615 - dst).
Proof. intros dst H. rewrite unsigned_lit by lia. rewrite zb_lxor_ones by lia. reflexivity. Qed.

Lemma csb_snez : forall src, 0 < src < 2^64 -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 src) = Z_to_bv 64 1.
Proof.
  intros src H. rewrite v_sltu_b2z. rewrite !unsigned_lit by lia.
  replace (0 <? src) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma csb_seqz : forall x, 0 < x < 2^64 -> v_sltiu (Z_to_bv 64 x) 1 = Z_to_bv 64 0.
Proof.
  intros x H. rewrite v_sltiu_b2z. rewrite unsigned_lit by lia. change (bv_wrap 64 1) with 1.
  replace (x <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma csb_zb_eq0 : forall b : byte, bv_eqb (zxb b) (Z_to_bv 64 0) = (bz b =? 0).
Proof.
  intros b. pose proof (bz_range b) as R. unfold bz in *. unfold bv_eqb, zxb.
  rewrite !unsigned_lit by lia. reflexivity.
Qed.

Lemma csb_le1_0 : le1 (Z_to_bv 64 0) = [b8 0].
Proof. vm_compute. reflexivity. Qed.

(* The shadow address of P as the code computes it (srli by 3, add the shadow base). *)
Lemma csb_shr : forall P, 0 <= P < 2^64 -> Z.shiftr (bv_unsigned (Z_to_bv 64 P)) 3 + 2147450880 = P / 8 + ASAN_K.
Proof. intros P H. rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

(* Decide a branch whose condition holds by arithmetic, or whose condition is a closed term. *)
Ltac csb_br v := lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; unfold_cond; fold_lit_ux; rewrite ?unsigned_lit by lia; solve_cond_rec]
  end.
Ltac csb_brc := lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in replace c with v by (vm_compute; reflexivity); cbv iota
  end.

(** * The three one-byte shadow checks *)

(* 0x82df8 .. 0x82e04, slow path 0x82e48 .. 0x82e50: the shadow byte of src + i (a2), before the byte load at
   0x82e08. *)
Lemma csb_chk_src : forall (RNG : ExecF.footprint) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte)
    (Q : machine_state -> Prop) (k : byte) (P : Z)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x13 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  0 <= P < 2^64 ->
  mrd rsegs mm (wa (P / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ P mod 8 < bv_signed k) ->
  ExecF.rng RNG (P / 8 + ASAN_K) 1 ->
  (forall y7 y28 : word, evtF rsegs RNG Q
     (MS (mkR x1 x2 x3 x4 x5 x6 y7 x8 x9 x10 x11 (Z_to_bv 64 P) x13 (Z_to_bv 64 2147450880) x15 x16 x17
              x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y28 x29 x30 x31)
         F (Z_to_bv 64 0x8bfb0) fc None mm (seg_rom rsegs))) ->
  evtF rsegs RNG Q
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 P) x13 (Z_to_bv 64 2147450880) x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x8bfa0) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG F fc mm Q k P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x13 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 RP M SK RG CONT.
  rewrite <- (csb_shr P RP) in M, RG.
  pose proof (rd1 mm _ k M) as R. cbv delta [wa] in R.
  step. step.
  step. clear R.
  step.
  pose proof (Z.mod_pos_bound P 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step.
    rewrite land7. rewrite (unsigned_lit P) by lia.
    rewrite (lts_low (P mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* 0x82e14 .. 0x82e20, slow path 0x82e54 .. 0x82e58: the shadow byte of dst + i (a3), before the byte store at
   0x82e28. *)
Lemma csb_chk_dst : forall (RNG : ExecF.footprint) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte)
    (Q : machine_state -> Prop) (k : byte) (P : Z)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  0 <= P < 2^64 ->
  mrd rsegs mm (wa (P / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ P mod 8 < bv_signed k) ->
  ExecF.rng RNG (P / 8 + ASAN_K) 1 ->
  (forall y28 y29 : word, evtF rsegs RNG Q
     (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 P) (Z_to_bv 64 2147450880) x15 x16 x17
              x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y28 y29 x30 x31)
         F (Z_to_bv 64 0x8bfcc) fc None mm (seg_rom rsegs))) ->
  evtF rsegs RNG Q
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 P) (Z_to_bv 64 2147450880) x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x8bfbc) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG F fc mm Q k P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 RP M SK RG CONT.
  rewrite <- (csb_shr P RP) in M, RG.
  pose proof (rd1 mm _ k M) as R. cbv delta [wa] in R.
  step. step.
  step. clear R.
  step.
  pose proof (Z.mod_pos_bound P 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step.
    rewrite land7. rewrite (unsigned_lit P) by lia.
    rewrite (lts_low (P mod 8) k MB), (proj2 (Z.ltb_lt _ _) C).
    apply CONT.
Qed.

(* 0x82e70 .. 0x82e7c, slow path 0x82e94 .. 0x82e98: the shadow byte of dst + k (a0), before the store of the 0 byte
   at 0x82e80. *)
Lemma csb_chk_nul : forall (RNG : ExecF.footprint) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte)
    (Q : machine_state -> Prop) (k : byte) (P : Z)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  0 <= P < 2^64 ->
  mrd rsegs mm (wa (P / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ P mod 8 < bv_signed k) ->
  ExecF.rng RNG (P / 8 + ASAN_K) 1 ->
  (forall y11 y12 : word, evtF rsegs RNG Q
     (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 P) y11 y12 x13 (Z_to_bv 64 2147450880) x15 x16 x17
              x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
         F (Z_to_bv 64 0x8c028) fc None mm (seg_rom rsegs))) ->
  evtF rsegs RNG Q
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 P) x11 x12 x13 (Z_to_bv 64 2147450880) x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x8c018) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG F fc mm Q k P x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 RP M SK RG CONT.
  rewrite <- (csb_shr P RP) in M, RG.
  pose proof (rd1 mm _ k M) as R. cbv delta [wa] in R.
  step. step.
  step. clear R.
  step.
  pose proof (Z.mod_pos_bound P 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step.
    rewrite land7. rewrite (unsigned_lit P) by lia.
    rewrite (lts_low (P mod 8) k MB), (proj2 (Z.ltb_lt _ _) C).
    apply CONT.
Qed.

(** * The walk *)

Section CSB.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 : word).
Variables (s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word).
Variables (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Variables (sv old : list byte) (dst src lo : Z) (RNG : ExecF.footprint).

Local Notation SP := (bv_unsigned sp).

Hypothesis Hsrc : src <> 0.
Hypothesis Hsv : length sv = 9%nat.
Hypothesis HB : 0 < src /\ src + 9 <= 2^64 /\ 0 <= dst /\ dst + 10 <= 2^64.
Hypothesis DIS : dst + 10 <= src \/ src + 9 <= dst.
Hypothesis ST0 : stk rsegs m lo SP.
Hypothesis SPLO : lo + 16 <= SP.
Hypothesis OFFS : src + 9 <= SP - 16 \/ SP <= src.
Hypothesis OFFD : dst + 10 <= SP - 16 \/ SP <= dst.
Hypothesis APS1 : app_mem (SP - 16).
Hypothesis APS2 : app_mem (SP - 1).
Hypothesis CELLS : asan_cells m.
Hypothesis OFFG : GOT_CELL_K + 8 <= SP - 16 \/ SP <= GOT_CELL_K.
Hypothesis OFFK : CELL_K + 8 <= SP - 16 \/ SP <= CELL_K.
Hypothesis ADS : addressable m src 9.
Hypothesis ADD : addressable m dst 10.
Hypothesis RFR : ExecF.rng RNG (SP - 16) 16.
Hypothesis RGOT : ExecF.rng RNG GOT_CELL_K 8.
Hypothesis RCELL : ExecF.rng RNG CELL_K 8.
Hypothesis RS : ExecF.rng RNG src 9.
Hypothesis RSS : ExecF.rng RNG (shadow_addr src) (shadow_addr (src + 9 - 1) - shadow_addr src + 1).
Hypothesis RD : ExecF.rng RNG dst 10.
Hypothesis RDSH : ExecF.rng RNG (shadow_addr dst) (shadow_addr (dst + 10 - 1) - shadow_addr dst + 1).

(* The post of the contract, for the 9 bytes sv. *)
Definition PostC : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(SP - 16, SP); (dst, dst + 10)] m m' /\
    wmono rsegs m m' /\ stk rsegs m' lo SP /\
    rw_cells rsegs m' dst [CB 10 (copy_strz 10 9 sv old)].

(* The state of memory at a loop head: the field holds L, the source bytes are unchanged, the frame holds ra. *)
Definition INVc (jj : list byte) (m1 : word -> option byte) (L : list byte) : Prop :=
  rw_cells rsegs m1 dst [CB 10 L] /\
  munch [(SP - 16, SP); (dst, dst + 10)] m m1 /\ wmono rsegs m m1 /\
  bytes_at rsegs m1 src sv /\
  stk rsegs m1 lo (SP + -16) /\
  rw_cells rsegs m1 (SP + -16) [CB 8 jj; C8 ra].

(* The code writes only application memory (the frame and the field), so no shadow byte changes. *)
Lemma csb_INV_addr : forall jj m1 L p n, INVc jj m1 L -> addressable m p n -> addressable m1 p n.
Proof.
  intros jj m1 L p n (_ & MU & _) A.
  eapply csb_addr_munch; [exact A | exact MU |].
  intros i Hi. destruct A as (_ & _ & _ & HA). destruct (HA i Hi) as (Ha & _).
  pose proof (csb_shadow_not_app _ Ha) as NA. cbn [outside]. split; [|split; [|exact I]].
  - intros W. apply NA. apply (csb_app_win SP 16); [lia | exact APS1 | exact APS2 | lia].
  - intros W. apply NA. pose proof ADD as (_ & _ & _ & HO).
    destruct (HO ((p + i) / 8 + ASAN_K - dst) ltac:(lia)) as (Ho & _).
    replace (dst + ((p + i) / 8 + ASAN_K - dst)) with ((p + i) / 8 + ASAN_K) in Ho by lia. exact Ho.
Qed.

Lemma csb_INV_sok : forall jj m1 L (i : nat) (w : word),
  INVc jj m1 L -> (i < 10)%nat -> w = Z_to_bv 64 (dst + Z.of_nat i) -> store_ok rsegs m1 w 1 = true.
Proof.
  intros jj m1 L i w (CA & _) Hi ->. destruct CA as [_ Hw]. cbn [cells_size csize Nat.add] in Hw.
  change (Z_to_bv 64 (dst + Z.of_nat i)) with (wa (dst + Z.of_nat i)).
  exact (wr_at_store_ok rsegs m1 dst _ (Z.of_nat i) 1 Hw ltac:(lia) ltac:(lia)).
Qed.

(* A byte store at dst + i inside the field. *)
Lemma csb_INV_store : forall jj m1 L (i : nat) (w : word) (b : byte),
  INVc jj m1 L -> (i < 10)%nat -> w = Z_to_bv 64 (dst + Z.of_nat i) ->
  INVc jj (write_to_mem m1 w [b]) (upd_bytes L i [b]).
Proof.
  intros jj m1 L i w b ([[[Hl Hwf] Hb] Hw] & MU & WM & BS & STK & FR) Hi ->.
  pose proof HB as (B1 & B2 & B3 & B4).
  cbn [cells_bytes cbytes cells_size csize Nat.add] in Hb, Hw. cbn [cell_wf] in Hl.
  rewrite app_nil_r in Hb.
  change (Z_to_bv 64 (dst + Z.of_nat i)) with (wa (dst + Z.of_nat i)).
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
  - split; [split|].
    + cbn [cells_wf cell_wf]. split; [|exact I]. rewrite upd_bytes_length; cbn [length]; lia.
    + cbn [cells_bytes cbytes]. rewrite app_nil_r.
      pose proof (bytes_at_write_inside rsegs m1 dst L (Z.of_nat i) [b] Hb ltac:(lia)
                    ltac:(cbn [length]; lia)) as W1.
      rewrite Nat2Z.id in W1. exact W1.
    + cbn [cells_size csize Nat.add]. apply wr_at_write. exact Hw.
  - apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside length]; lia].
  - apply wmono_write. exact WM.
  - apply bytes_at_write_other; [exact BS | lia | cbn [length]; lia | rewrite Hsv; cbn [length]; lia].
  - apply stk_write; [exact STK | lia | cbn [length]; lia].
  - apply rw_cells_frame; [exact FR | lia | cbn [length]; lia | cbn [cells_size csize length Nat.add]; lia].
Qed.

(* After the store step of a byte at dst + i: the new memory is a fresh variable and I its INVc. *)
Ltac csb_stored I i :=
  rewrite ?le1_zxb, ?csb_le1_0;
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?w [?bv]) _) =>
      let I' := fresh "I" in
      pose proof (csb_INV_store _ mm _ i w bv I ltac:(lia) ltac:(first [reflexivity | f_equal; lia])) as I';
      let mn := fresh "m" in
      set (mn := write_to_mem mm w [bv]) in *; clearbody mn; clear I; rename I' into I
  end.

(* 0x82e68: dst + k does not wrap, the 0 byte at dst + k, the return. *)
Lemma csb_FIN : forall (jj : list byte) (m1 : word -> option byte)
    (x5 x6 x11 x12 x13 x15 x17 x28 x29 : word) (vk : Z),
  vk = Z.of_nat (strz_len sv) ->
  INVc jj m1 (firstn (strz_len sv) sv ++ skipn (strz_len sv) old) ->
  evtF rsegs RNG PostC
    (MS (mkR ra (Z_to_bv 64 (SP + -16)) gp tp x5 x6 (Z_to_bv 64 vk) s0 s1 (Z_to_bv 64 dst) x11 x12 x13
             (Z_to_bv 64 2147450880) x15 (Z_to_bv 64 (18446744073709551615 - dst)) x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 t5 t6)
        F (Z_to_bv 64 0x8c010) fc None m1 (seg_rom rsegs)).
Proof.
  intros jj m1 x5 x6 x11 x12 x13 x15 x17 x28 x29 vk Ek I.
  pose proof HB as (B1 & B2 & B3 & B4).
  pose proof (strz_len_le sv) as K9.
  pose proof (u64_range sp) as Rsp.
  assert (Hlo : 0 <= lo) by (destruct I as (_ & _ & _ & _ & (H & _) & _); lia).
  (* 0x82e68 bltu a6,t2: dst + k does not wrap *)
  step. csb_br false.
  (* 0x82e6c add a0,a0,t2 *)
  step.
  subst vk.
  pose proof (csb_INV_addr _ _ _ _ _ I ADD) as ADD1.
  destruct (csb_addr_one m1 dst 10 (Z.of_nat (strz_len sv)) ADD1 ltac:(lia)) as (_ & kk & MK & SK).
  eapply (csb_chk_nul RNG F fc m1 PostC kk (dst + Z.of_nat (strz_len sv)));
    [ lia | exact MK | exact SK | eapply csb_rng_shadow_one; [exact RDSH | lia] | intros y11 y12 ].
  (* 0x82e80 sb zero,0(a0) *)
  assert (HS : store_ok rsegs m1 (Z_to_bv 64 (dst + Z.of_nat (strz_len sv))) 1 = true)
    by (eapply (csb_INV_sok _ _ _ (strz_len sv)); [exact I | lia | reflexivity]).
  step. clear HS.
  csb_stored I (strz_len sv).
  rewrite (csb_nul sv old) in I by reflexivity.
  destruct I as (CA & MU & WM & _ & STK & FR).
  (* 0x82e84 ld ra,8(sp); 0x82e88 addi sp,sp,16; 0x82e8c ret *)
  step. step. step.
  apply evtF_done. unfold PostC.
  do 14 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [|exact CA].
  lazymatch type of STK with stk _ ?mf _ _ =>
    pose proof (stk_release rsegs mf lo (SP + -16) _ STK FR ltac:(lia)) as ST2 end.
  cbn [cells_size csize Nat.add] in ST2. replace (SP + -16 + Z.of_nat 16) with SP in ST2 by lia. exact ST2.
Qed.

(* 0x82de4: the loop; i bytes copied, k + 1 turns left at most. *)
Lemma csb_LOOP : forall (jj : list byte) (k i : nat) (m1 : word -> option byte) (x7 x28 x29 : word)
    (vp vq vi : Z),
  (i + S k = 9)%nat -> vp = src + Z.of_nat i -> vq = dst + Z.of_nat i -> vi = Z.of_nat i ->
  (forall j, (j < i)%nat -> at8 sv j <> 0) ->
  INVc jj m1 (firstn i sv ++ skipn i old) ->
  evtF rsegs RNG PostC
    (MS (mkR ra (Z_to_bv 64 (SP + -16)) gp tp (Z_to_bv 64 vp) (Z_to_bv 64 vq) x7 s0 s1
             (Z_to_bv 64 dst) (Z_to_bv 64 src) (Z_to_bv 64 vp) (Z_to_bv 64 vq) (Z_to_bv 64 2147450880)
             (Z_to_bv 64 vi) (Z_to_bv 64 (18446744073709551615 - dst)) (Z_to_bv 64 1)
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 t5 t6)
        F (Z_to_bv 64 0x8bf8c) fc None m1 (seg_rom rsegs)).
Proof.
  intros jj k. induction k as [|k IH]; intros i m1 x7 x28 x29 vp vq vi Hk Ep Eq Ei Hnz I.
  all: pose proof HB as (B1 & B2 & B3 & B4).
  all: destruct (csb_byte_at sv i ltac:(lia)) as [b Nb].
  all: pose proof (csb_at8_ne _ _ _ Nb) as Ab.
  all: pose proof (csb_INV_addr _ _ _ _ _ I ADS) as ADS1.
  all: pose proof (csb_INV_addr _ _ _ _ _ I ADD) as ADD1.
  (* 0x82de4 bltu a2,a1: src + i does not wrap *)
  all: step; csb_br false.
  (* 0x82de8 seqz t2,a2; 0x82dec xor t2,a7,t2; 0x82df0 beqz t2: (src <> 0) = (src + i = 0) is false *)
  all: step; rewrite (csb_seqz vp) by lia.
  all: step; step; csb_brc.
  (* 0x82df4 beqz a1: src <> 0 *)
  all: step; csb_br false.
  (* 0x82df8: the shadow byte of src + i *)
  all: destruct (csb_addr_one m1 src 9 (Z.of_nat i) ADS1 ltac:(lia)) as (_ & k0 & MK & SK).
  all: rewrite <- Ep in MK, SK.
  all: eapply (csb_chk_src RNG F fc m1 PostC k0 vp);
         [ lia | exact MK | exact SK | subst vp; eapply csb_rng_shadow_one; [exact RSS | lia] | intros y7 y28 ].
  (* 0x82e08 lbu t2,0(t0); 0x82e0c beqz t2 *)
  all: pose proof (proj1 (proj2 (proj2 (proj2 I)))) as BW.
  all: pose proof (csb_rdb m1 src sv i b BW Nb) as HR.
  all: rewrite <- Ep in HR.
  all: step.
  all: clear HR.
  all: step; rewrite csb_zb_eq0.
  all: destruct (Z.eqb_spec (bz b) 0) as [Z0|Z0]; cbv iota.
  (* byte i is 0: 0x82e64 mv t2,a5, then the 0 byte at dst + i *)
  1, 3: assert (Ek : strz_len sv = i) by (apply strz_len_char; [lia | lia | exact Hnz | intros; lia]);
        step; eapply csb_FIN; [ rewrite Ek; lia | rewrite Ek; exact I ].
  (* 0x82e10 bltu a6,a5: dst + i does not wrap *)
  all: step; csb_br false.
  (* 0x82e14: the shadow byte of dst + i *)
  all: destruct (csb_addr_one m1 dst 10 (Z.of_nat i) ADD1 ltac:(lia)) as (_ & k1 & MK1 & SK1).
  all: rewrite <- Eq in MK1, SK1.
  all: eapply (csb_chk_dst RNG F fc m1 PostC k1 vq);
         [ lia | exact MK1 | exact SK1 | subst vq; eapply csb_rng_shadow_one; [exact RDSH | lia] | intros z28 z29 ].
  (* 0x82e24 addi a5,a5,1; 0x82e28 sb t2,0(t1) *)
  all: step.
  all: assert (HS : store_ok rsegs m1 (Z_to_bv 64 vq) 1 = true)
         by (eapply (csb_INV_sok _ _ _ i); [exact I | lia | subst vq; reflexivity]).
  all: step; clear HS.
  all: csb_stored I i.
  all: rewrite (csb_upd_snoc sv old i b Nb) in I.
  (* 0x82e2c .. 0x82e3c: the pointers and the count step by 1, t2 = 9; 0x82e40 bne a5,t2 *)
  all: step; step; step; step; step; step.
  - (* the ninth byte is stored: 0x82e44 j 0x82e68 *)
    csb_br false. step.
    assert (Ek : strz_len sv = 9%nat).
    { apply strz_len_char; [lia | lia | | lia].
      intros j Hj. destruct (Nat.eq_dec j i) as [->|NE]; [lia | apply Hnz; lia]. }
    eapply csb_FIN; [rewrite Ek; reflexivity | rewrite Ek; replace (S i) with 9%nat in I by lia; exact I].
  - csb_br true.
    eapply (IH (S i)); [lia | lia | lia | lia | | exact I].
    intros j Hj. destruct (Nat.eq_dec j i) as [->|NE]; [lia | apply Hnz; lia].
Qed.

(* 0x82db4: the frame, the shadow base, i = 0, a6 = ~dst, a7 = (src <> 0), then the loop. The bytes_at and rw_cells
   premises are the lemma's own: the frame store transports them. *)
Lemma csb_ENTRY :
  bytes_at rsegs m src sv ->
  rw_cells rsegs m dst [CB 10 old] ->
  evtF rsegs RNG PostC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 dst) (Z_to_bv 64 src) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x8bf5c) fc None m (seg_rom rsegs)).
Proof.
  intros BS RW.
  pose proof HB as (B1 & B2 & B3 & B4).
  pose proof (u64_range sp) as Rsp.
  assert (Hlo : 0 <= lo) by (destruct ST0 as [H _]; lia).
  pose proof CELLS as (CK & GCK & _).
  pose proof OFFG as OFFGu. pose proof OFFK as OFFKu.
  pose proof RGOT as RGOTu. pose proof RCELL as RCELLu.
  unfold GOT_CELL_K, CELL_K, ASAN_K in CK, GCK, OFFGu, OFFKu, RGOTu, RCELLu.
  (* the frame [sp - 16, sp) *)
  destruct (stk_carve rsegs m lo SP 16%nat ST0 ltac:(lia)) as [STc [junk FR]].
  change (Z.of_nat 16) with 16 in STc, FR.
  replace (SP - 16) with (SP + -16) in STc, FR by lia.
  pose proof (munch_refl [(SP - 16, SP); (dst, dst + 10)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* 0x82db4 addi sp,sp,-16; 0x82db8 sd ra,8(sp) *)
  step. step.
  match goal with MU' : munch _ m ?m1 |- _ => rename m1 into m0 end.
  (* 0x82dbc li a5,0; 0x82dc0 auipc; 0x82dc4 ld a2 (GOT_CELL_K); 0x82dc8 ld a4 (CELL_K) *)
  step. step.
  pose proof (csb_rd_all _ _ _ GCK) as RDG. rewrite length_le8 in RDG.
  pose proof (csb_rd_all _ _ _ CK) as RDK. rewrite length_le8 in RDK.
  step. step. clear RDG RDK.
  (* 0x82dcc not a6,a0; 0x82dd0 snez a7,a1; 0x82dd4 .. 0x82de0 t0 = a2 = src, t1 = a3 = dst *)
  step. step. step. step. step. step.
  rewrite (csb_not dst) by lia. rewrite (csb_snez src) by lia.
  eapply (csb_LOOP _ 8%nat 0%nat); [lia | lia | lia | reflexivity | intros j Hj; lia |].
  unfold INVc. cbn [firstn skipn app].
  refine (conj _ (conj MU (conj WM (conj _ (conj STc FR))))); assumption.
Qed.

End CSB.

Theorem copy_strz_holds_F : copy_strz_contract_F.
Proof.
  unfold copy_strz_contract_F, COPY_STRZ, COPY_STRZ_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    s old dst src lo E0 E1 Hsrc Hlen BA RW DIS ST HLO OFFS OFFD APS1 APS2 CELLS OFFG OFFK ADS ADD
    RFR RGOT RCELL RS RSS RD RDSH.
  subst a0 a1.
  unfold off_stk in OFFS, OFFD, OFFG, OFFK.
  pose proof (bytes_at_bound rsegs _ _ _ BA) as HBA.
  pose proof (rw_cells_bound rsegs _ _ _ RW) as HRW. cbn [cells_size csize Nat.add] in HRW.
  assert (HB : 0 < src /\ src + 9 <= 2^64 /\ 0 <= dst /\ dst + 10 <= 2^64) by lia.
  pose proof (csb_bytes_firstn m src s 9 BA Hlen) as BA9.
  assert (Hsv : length (firstn 9 s) = 9%nat) by (rewrite length_firstn; lia).
  rewrite (csb_copy_firstn9 s old).
  eapply csb_ENTRY; eassumption.
Qed.
