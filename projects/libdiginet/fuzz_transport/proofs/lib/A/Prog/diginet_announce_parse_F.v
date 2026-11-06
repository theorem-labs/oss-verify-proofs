(* diginet_announce_parse_holds_F proves diginet_announce_parse_contract_F (diginet_announce_parse_F_c.v): the run
   of 0x82bbc .. 0x82da0 as an ExecF.evtF run under the footprint RNG, so every data access of every step lies in
   RNG. The walk is the plain image's walk of the same C source with the image-A shadow checks around each access:
   the two inlined copy_strz loops (0x82c80 and 0x82d10) each copy at most 9 bytes and stop at a NUL, and the 24
   bytes ap + 0 .. ap + 23 are one byte cell while the loops run.
   Before each access at x the code loads the shadow byte k at (x >> 3) + 0x7fff8000. The five 8-byte accesses go
   on only at k = 0, which addr_eight reads off the addressable premise, so each of those checks has one path and
   is in the walk itself. The seven 1-byte accesses go on at k = 0 or at (x & 7) < k, two paths that rejoin at the
   next instruction; each is the lemma sh30 / shv_src / shv_dst / shv_nul / shn_src / shn_dst / shn_nul below,
   which takes the rest of the walk as a continuation quantified over the registers its error block writes. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA AsanKAProof.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_announce_parse_c diginet_announce_parse_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(** * Lists *)

Lemma ne_skipn : forall {A} (l : list A) n i, nth_error (skipn n l) i = nth_error l (n + i).
Proof.
  intros A l n. revert l. induction n as [|n IH]; intros [|x l] i; cbn; try reflexivity.
  - destruct i; reflexivity.
  - apply IH.
Qed.

Lemma at8_ne : forall l i b, nth_error l i = Some b -> at8 l i = bz b.
Proof.
  induction l as [|x l IH]; intros [|i] b H; cbn in H; try discriminate.
  - injection H as E. subst. reflexivity.
  - unfold at8 in *. cbn [nth]. apply IH. exact H.
Qed.

Lemma byte_at : forall (l : list byte) i, (i < length l)%nat -> exists b, nth_error l i = Some b.
Proof.
  intros l i Hi. destruct (nth_error l i) eqn:N; [eexists; reflexivity|].
  apply nth_error_None in N. lia.
Qed.

Lemma firstn_snoc_nth : forall (s : list byte) j b, nth_error s j = Some b -> firstn (S j) s = firstn j s ++ [b].
Proof.
  induction s as [|c s IH]; intros [|j] b H; cbn in H; try discriminate.
  - injection H as E. subst. reflexivity.
  - cbn [firstn]. rewrite (IH j b H). reflexivity.
Qed.

Lemma upd_bytes_app_l : forall (xs ys bs : list byte) i, (i + length bs <= length xs)%nat ->
  upd_bytes (xs ++ ys) i bs = upd_bytes xs i bs ++ ys.
Proof.
  intros xs ys bs i H. unfold upd_bytes. rewrite firstn_app, skipn_app.
  replace (i - length xs)%nat with 0%nat by lia.
  replace (i + length bs - length xs)%nat with 0%nat by lia.
  cbn [firstn skipn]. rewrite app_nil_r. rewrite !app_assoc. reflexivity.
Qed.

Lemma upd_at_end : forall (P R : list byte) i z, length P = i -> upd_bytes (P ++ R) i [z] = P ++ z :: skipn 1 R.
Proof.
  intros P R i z <-. unfold upd_bytes. rewrite firstn_app, skipn_app, Nat.sub_diag, firstn_all.
  rewrite (skipn_all2 (n := (length P + length [z])%nat) P) by (cbn [length]; lia).
  cbn [length]. replace (length P + 1 - length P)%nat with 1%nat by lia.
  cbn [firstn app]. rewrite app_nil_r. reflexivity.
Qed.

(* One byte of a loop: the field at o holds j bytes of s, then byte j of s is stored. *)
Lemma upd_snoc : forall (V s X : list byte) (o j : nat) b, length V = o -> nth_error s j = Some b ->
  upd_bytes (V ++ firstn j s ++ skipn (o + j) X) (o + j) [b] = V ++ firstn (S j) s ++ skipn (o + S j) X.
Proof.
  intros V s X o j b HV Hn.
  assert (Hj : (j < length s)%nat) by (apply nth_error_Some; congruence).
  rewrite (app_assoc V (firstn j s) (skipn (o + j) X)).
  rewrite upd_at_end by (rewrite length_app, length_firstn; lia).
  rewrite (firstn_snoc_nth s j b Hn). rewrite skipn_skipn.
  replace (1 + (o + j))%nat with (o + S j)%nat by lia.
  rewrite <- !app_assoc. reflexivity.
Qed.

Lemma skipn_firstn_app : forall (l : list byte) a n, (a <= n)%nat -> (n <= length l)%nat ->
  skipn a l = skipn a (firstn n l) ++ skipn n l.
Proof.
  intros l a n H1 H2. rewrite <- (firstn_skipn n l) at 1. rewrite skipn_app, length_firstn.
  replace (a - Nat.min n (length l))%nat with 0%nat by lia. reflexivity.
Qed.

Lemma strz_len_le_len : forall src, (strz_len src <= length src)%nat.
Proof.
  intros src. unfold strz_len. pose proof (nz_run_le (firstn 9 src)) as H. rewrite length_firstn in H. lia.
Qed.

Lemma nul_byte : forall z : byte, bz z = 0 -> z = b8 0.
Proof. intros z H. rewrite <- (b8_bz z), H. reflexivity. Qed.

(* The 24 bytes after the NUL of the version. *)
Lemma ver_nul : forall (bb aj : list byte) (z : byte), bz z = 0 -> length aj = 40%nat ->
  upd_bytes (firstn (strz_len (skipn 15 bb)) (skipn 15 bb) ++ skipn (strz_len (skipn 15 bb)) (firstn 24 aj))
            (strz_len (skipn 15 bb)) [z]
  = ann_version bb (firstn 10 aj) ++ skipn 10 (firstn 24 aj).
Proof.
  intros bb aj z Hz Haj. rewrite (nul_byte z Hz).
  pose proof (strz_len_le (skipn 15 bb)) as Hk.
  pose proof (strz_len_le_len (skipn 15 bb)) as Hk2.
  rewrite upd_at_end by (rewrite length_firstn; lia).
  unfold ann_version, copy_strz. change (copy_len 10 9 (skipn 15 bb)) with (strz_len (skipn 15 bb)).
  rewrite <- app_assoc. cbn [app]. f_equal. f_equal.
  rewrite skipn_skipn. cbn [Nat.add].
  replace (firstn 10 aj) with (firstn 10 (firstn 24 aj)) by (rewrite firstn_firstn; reflexivity).
  apply skipn_firstn_app; [lia | rewrite length_firstn; lia].
Qed.

(* The 24 bytes after the NUL of the name: version, name, 4 bytes not written. *)
Lemma name_nul : forall (bb aj : list byte) (z : byte), bz z = 0 -> length aj = 40%nat ->
  upd_bytes (ann_version bb (firstn 10 aj) ++ firstn (strz_len (skipn 24 bb)) (skipn 24 bb)
               ++ skipn (10 + strz_len (skipn 24 bb)) (firstn 24 aj))
            (10 + strz_len (skipn 24 bb)) [z]
  = ann_version bb (firstn 10 aj) ++ ann_name bb (firstn 10 (skipn 10 aj)) ++ firstn 4 (skipn 20 aj).
Proof.
  intros bb aj z Hz Haj. rewrite (nul_byte z Hz).
  pose proof (strz_len_le (skipn 24 bb)) as Hk.
  pose proof (strz_len_le_len (skipn 24 bb)) as Hk2.
  assert (HV : length (ann_version bb (firstn 10 aj)) = 10%nat)
    by (apply length_copy_strz; rewrite length_firstn; lia).
  rewrite app_assoc.
  rewrite upd_at_end by (rewrite length_app, length_firstn; lia).
  rewrite <- app_assoc. f_equal.
  unfold ann_name, copy_strz. change (copy_len 10 9 (skipn 24 bb)) with (strz_len (skipn 24 bb)).
  rewrite <- app_assoc. cbn [app]. f_equal. f_equal.
  rewrite skipn_skipn.
  replace (1 + (10 + strz_len (skipn 24 bb)))%nat with (S (strz_len (skipn 24 bb)) + 10)%nat by lia.
  rewrite <- skipn_skipn. rewrite skipn_firstn_comm.
  replace (24 - 10)%nat with 14%nat by reflexivity.
  rewrite (skipn_firstn_app (firstn 14 (skipn 10 aj)) (S (strz_len (skipn 24 bb))) 10)
    by (try lia; rewrite length_firstn, length_skipn; lia).
  rewrite firstn_firstn. replace (Nat.min 10 14) with 10%nat by reflexivity.
  f_equal. rewrite skipn_firstn_comm, skipn_skipn. reflexivity.
Qed.

(** * Memory *)

Lemma ro_of_bytes : forall m A cs, cells_wf cs -> bytes_at rsegs m A (cells_bytes cs) -> ro_cells rsegs m A cs.
Proof. intros m A cs H1 H2. split; assumption. Qed.

Lemma firstn1_nth : forall {X} (l : list X) i b, nth_error l i = Some b -> firstn 1 (skipn i l) = [b].
Proof.
  intros X l; induction l as [|c l IH]; intros [|i] b N; cbn in *; try discriminate.
  - injection N as ->. reflexivity.
  - apply IH; exact N.
Qed.

Lemma rdb : forall m A l (i : nat) b, bytes_at rsegs m A l -> nth_error l i = Some b ->
  ov_read_bytes rsegs m (wa (A + Z.of_nat i)) 1 = Some [b].
Proof.
  intros m A l i b BL N. pose proof (nth_error_Some l i) as NS. rewrite N in NS.
  assert (Hi : (i < length l)%nat) by (apply NS; discriminate).
  rewrite (bytes_at_ov_read rsegs m A l i 1 BL ltac:(lia)). f_equal. apply firstn1_nth. exact N.
Qed.

Lemma rd_all : forall m A bs, bytes_at rsegs m A bs ->
  ov_read_bytes rsegs m (Z_to_bv 64 A) (length bs) = Some bs.
Proof.
  intros m A bs H. change (Z_to_bv 64 A) with (wa A). replace A with (A + Z.of_nat 0) at 1 by lia.
  rewrite (bytes_at_ov_read rsegs m A bs 0 (length bs) H) by lia. cbn [skipn]. rewrite firstn_all. reflexivity.
Qed.

Lemma ne_firstn : forall {A} (l : list A) n i, (i < n)%nat -> nth_error (firstn n l) i = nth_error l i.
Proof.
  intros A l n; revert l; induction n as [|n IH]; intros l i Hi; [lia|].
  destruct l as [|x l]; [destruct i; reflexivity|].
  destruct i as [|i]; [reflexivity|]. cbn [firstn nth_error]. apply IH. lia.
Qed.

Lemma bytes_window : forall m0 A (l : list byte) (p n : nat),
  (p + n <= length l)%nat ->
  bytes_at rsegs m0 A l -> bytes_at rsegs m0 (A + Z.of_nat p) (firstn n (skipn p l)).
Proof.
  intros m0 A l p n Hpn (H0 & H1 & H).
  assert (LF : length (firstn n (skipn p l)) = n)
    by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite LF; lia|].
  intros i Hi. rewrite LF in Hi.
  replace (A + Z.of_nat p + Z.of_nat i) with (A + Z.of_nat (p + i)) by lia.
  rewrite H by lia. rewrite ne_firstn by lia. rewrite ne_skipn. reflexivity.
Qed.

(* A byte store at A + i inside the byte cell that starts at A. *)
Lemma stb : forall W m0 m1 A n xs cs (i : nat) (b : byte),
  rw_cells rsegs m1 A (CB n xs :: cs) -> (i < n)%nat ->
  munch W m0 m1 -> inside W (A + Z.of_nat i) 1 -> wmono rsegs m0 m1 ->
  rw_cells rsegs (write_to_mem m1 (wa (A + Z.of_nat i)) [b]) A (CB n (upd_bytes xs i [b]) :: cs) /\
  munch W m0 (write_to_mem m1 (wa (A + Z.of_nat i)) [b]) /\
  wmono rsegs m0 (write_to_mem m1 (wa (A + Z.of_nat i)) [b]).
Proof.
  intros W m0 m1 A n xs cs i b [[[Hl Hwf] Hb] Hw] Hi MU Hin WM.
  cbn [cells_bytes cbytes cells_size csize] in Hb, Hw. cbn [cell_wf] in Hl.
  pose proof (bytes_at_bound rsegs _ _ _ Hb) as HB. rewrite length_app in HB.
  split; [|split].
  - split; [split|].
    + cbn [cells_wf cell_wf]. split; [|exact Hwf]. rewrite upd_bytes_length; cbn [length]; lia.
    + cbn [cells_bytes cbytes].
      pose proof (bytes_at_write_inside rsegs m1 A (xs ++ cells_bytes cs) (Z.of_nat i) [b] Hb ltac:(lia)
                    ltac:(rewrite length_app; cbn [length]; lia)) as W1.
      rewrite Nat2Z.id in W1. rewrite upd_bytes_app_l in W1 by (cbn [length]; lia). exact W1.
    + cbn [cells_size csize]. apply wr_at_write. exact Hw.
  - apply munch_write; [exact MU | lia | cbn [length]; lia | exact Hin].
  - apply wmono_write. exact WM.
Qed.

Lemma munch_extend : forall (m0 m1 : word -> option byte) a b c d,
  munch [(a, b)] m0 m1 -> munch [(a, b); (c, d)] m0 m1.
Proof.
  intros m0 m1 a b c d H. eapply munch_weaken; [|exact H].
  intros x Hx. cbn [outside] in *. tauto.
Qed.

Lemma rw_split3 : forall m A (V N T : list byte) cs, length V = 10%nat -> length N = 10%nat -> length T = 4%nat ->
  rw_cells rsegs m A (CB 24 (V ++ N ++ T) :: cs) -> rw_cells rsegs m A (CB 10 V :: CB 10 N :: CB 4 T :: cs).
Proof.
  intros m A V N T cs HV HN HT [[[_ Hwf] Hb] Hw]. split; [split|].
  - cbn [cells_wf cell_wf]. tauto.
  - cbn [cells_bytes cbytes] in *. rewrite <- !app_assoc in Hb. exact Hb.
  - cbn [cells_size csize] in *. replace (10 + (10 + (4 + cells_size cs)))%nat with (24 + cells_size cs)%nat by lia.
    exact Hw.
Qed.

(** * ASan *)

Lemma eqb_lit : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma ltu_lit : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma eqb_nz : forall x, x <> 0 -> -2^64 < x < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = false.
Proof.
  intros x H1 H2. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2^64). apply Z.eqb_neq. rewrite Z.mod_0_l by lia.
  Z.div_mod_to_equations. lia.
Qed.

Lemma zb_eq0 : forall b : byte, bv_eqb (zxb b) (Z_to_bv 64 0) = (bz b =? 0).
Proof.
  intros b. pose proof (bz_range b) as R. unfold bz in *. unfold bv_eqb, zxb.
  rewrite !unsigned_lit by lia. reflexivity.
Qed.

Lemma le1_0 : le1 (Z_to_bv 64 0) = [b8 0].
Proof. vm_compute. reflexivity. Qed.

Lemma byte_signed0 : forall k : byte, bv_signed k = 0 -> bv_unsigned k = 0.
Proof.
  intros k H. pose proof (bv_unsigned_in_range 8 k) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8) with 256 in R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. change (256 / 2) with 128 in H.
  Z.div_mod_to_equations. lia.
Qed.

Lemma cmd_test : forall cmd, 0 <= cmd < 2^8 ->
  bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (zxb (b8 cmd))) 254)) (Z_to_bv 64 224) = ann_cmd cmd.
Proof.
  assert (G : forall cmd, 0 <= cmd < 2^8 ->
    Bool.eqb (bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (zxb (b8 cmd))) 254)) (Z_to_bv 64 224)) (ann_cmd cmd) = true).
  { apply (byte_forall (fun cmd =>
      Bool.eqb (bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (zxb (b8 cmd))) 254)) (Z_to_bv 64 224)) (ann_cmd cmd))).
    vm_compute. reflexivity. }
  intros cmd Hc. apply Bool.eqb_prop. exact (G cmd Hc).
Qed.

Lemma lts_sm : forall (x : Z) (k : byte), 0 <= x < 2^63 -> bv_lts (Z_to_bv 64 x) (sxb k) = (x <? bv_signed k).
Proof.
  intros x k Hx. unfold bv_lts, sxb. pose proof (byte_signed_range k).
  rewrite !signed_lit by lia. reflexivity.
Qed.

Lemma app_win : forall s d x, 0 < d <= 2^32 -> app_mem (s - d) -> app_mem (s - 1) -> s - d <= x < s -> app_mem x.
Proof. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. intros s d x Hd H1 H2 Hx. lia. Qed.

Lemma shadow_not_app : forall a, app_mem a -> ~ app_mem (a / 8 + ASAN_K).
Proof.
  unfold app_mem, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. intros a Ha Hs. Z.div_mod_to_equations. lia.
Qed.

Lemma shadow_range : forall a, app_mem a -> 0 <= a / 8 + ASAN_K < 2^64.
Proof.
  unfold app_mem, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. intros a Ha. Z.div_mod_to_equations. lia.
Qed.

Lemma mrd_munch : forall W m m' a, munch W m m' -> 0 <= a < 2^64 -> outside W a ->
  mrd rsegs m' (wa a) = mrd rsegs m (wa a).
Proof.
  intros W m m' a MU Ha Ho. unfold mrd. rewrite MU; [reflexivity|]. rewrite wa_unsigned by exact Ha. exact Ho.
Qed.

Lemma addr_munch : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W ((p + i) / 8 + ASAN_K)) -> addressable m' p n.
Proof.
  intros W m m' p n (H0 & H1 & H2 & H) MU D.
  split; [exact H0 | split; [exact H1 | split; [exact H2 | ]]].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hok). split; [exact Ha|]. exists b. split; [|exact Hok].
  unfold shadow_addr in *. rewrite (mrd_munch W m m' _ MU (shadow_range _ Ha) (D i Hi)). exact Hb.
Qed.

Lemma asan_cells_munch : forall m m' lo hi, asan_cells m -> munch [(lo, hi)] m m' ->
  MIDEND + 8 <= lo \/ hi <= GOT_CELL_K -> asan_cells m'.
Proof.
  unfold asan_cells, MIDEND, GOT_CELL_K.
  intros m m' lo hi (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17) MU D.
  unfold CELL_K, GOT_CELL_K, INITED, REPLACE, GOT_REPLACE, UAR, GOT_UAR, CANPOISON, HIEND, GOT_HIEND, MIDBEG,
    GOT_MIDBEG, MIDEND, GOT_MIDEND, REAL_MEMCPY, REAL_MEMSET, GOT_REAL_MEMSET in *.
  repeat (match goal with |- _ /\ _ => split end);
    (eapply bytes_tp; [exact MU | | eassumption]); rewrite ?length_le8, ?length_le4; cbn [length]; lia.
Qed.

Lemma addr_one : forall m p n i, addressable m p n -> 0 <= i < n ->
  app_mem (p + i) /\ exists k, mrd rsegs m (wa ((p + i) / 8 + ASAN_K)) = Some k /\
    (bv_signed k = 0 \/ (p + i) mod 8 < bv_signed k).
Proof.
  intros m p n i (H0 & H1 & H2 & H) Hi. destruct (H i Hi) as (Ha & k & Hk & Hok).
  split; [exact Ha|]. exists k. unfold shadow_addr in Hk. split; [exact Hk|].
  unfold shadow_ok in Hok. lia.
Qed.

Lemma addr_bound : forall m p n, addressable m p n -> 0 <= p /\ 0 <= n /\ p + n <= 0x800000000000.
Proof. intros m p n (H0 & H1 & H2 & _). unfold APPMEM_END in H2. lia. Qed.

(* An 8-byte access goes on only at shadow 0: the last byte of the group of a is one of the n usable bytes, and
   its own shadow_ok forces 7 < k <= 7. *)
Lemma addr_eight : forall m p n a, addressable m p n -> p <= a -> a + 8 <= p + n ->
  exists k, mrd rsegs m (wa (a / 8 + ASAN_K)) = Some k /\ bv_signed k = 0.
Proof.
  intros m p n a (H0 & H1 & H2 & H) Ha Hn.
  pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Mb.
  destruct (H (a + (7 - a mod 8) - p) ltac:(lia)) as (Hap & k & Hk & Hok).
  replace (p + (a + (7 - a mod 8) - p)) with (a + (7 - a mod 8)) in Hk, Hok by lia.
  assert (E1 : (a + (7 - a mod 8)) / 8 = a / 8) by (Z.div_mod_to_equations; lia).
  assert (E2 : (a + (7 - a mod 8)) mod 8 = 7) by (Z.div_mod_to_equations; lia).
  unfold shadow_addr in Hk. rewrite E1 in Hk. unfold shadow_ok in Hok. rewrite E2 in Hok.
  exists k. split; [exact Hk | lia].
Qed.

(* A one-byte window of a buffer, and of the shadow bytes of a buffer, out of the buffer's own rng premise. *)
Lemma rng_one : forall RNG p n a, ExecF.rng RNG p n -> p <= a < p + n -> ExecF.rng RNG a 1.
Proof. intros RNG p n a H Ha. eapply ExecF.rng_sub; [exact H | lia | lia]. Qed.

Lemma rng_shadow_one : forall RNG p n a,
  ExecF.rng RNG (shadow_addr p) (shadow_addr (p + n - 1) - shadow_addr p + 1) ->
  p <= a < p + n -> ExecF.rng RNG (a / 8 + ASAN_K) 1.
Proof.
  intros RNG p n a H Ha. unfold shadow_addr in H.
  assert (L1 : p / 8 <= a / 8) by (apply Z.div_le_mono; lia).
  assert (L2 : a / 8 <= (p + n - 1) / 8) by (apply Z.div_le_mono; lia).
  eapply ExecF.rng_sub; [exact H | lia | lia].
Qed.

(** * The seven one-byte shadow checks *)

(* 0x82bdc .. 0x82bf0: the byte cmd at f + 30 (error block 0x82da4). *)
Lemma sh30 : forall (RNG : ExecF.footprint) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte)
    (Q : machine_state -> Prop) (k : byte) (ff : Z)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  0 <= ff + 30 < 2^64 ->
  mrd rsegs mm (wa ((ff + 30) / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ (ff + 30) mod 8 < bv_signed k) ->
  ExecF.rng RNG ((ff + 30) / 8 + ASAN_K) 1 ->
  (forall y14 y15 : word, evtF rsegs RNG Q
     (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 ff) x11 (Z_to_bv 64 (ff + 30)) (Z_to_bv 64 2147450880)
              y14 y15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
         F (Z_to_bv 64 0x8c26c) fc None mm (seg_rom rsegs))) ->
  evtF rsegs RNG Q
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 ff) x11 x12 (Z_to_bv 64 2147450880)
             x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x8c258) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG F fc mm Q k ff x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 RA M SK RGS CONT.
  unfold ASAN_K in M, RGS.
  step.
  step. gen_shr (Z_to_bv 64 (ff + 30)) g G. rewrite (unsigned_lit (ff + 30)) in G by lia.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound (ff + 30) 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step.
    rewrite land7. rewrite (unsigned_lit (ff + 30)) by lia.
    rewrite (lts_low ((ff + 30) mod 8) k MB), (proj2 (Z.ltb_lt _ _) C).
    apply CONT.
Qed.

(* 0x82c80 .. 0x82c94: the byte of the version at a7 + a6 (error block 0x82cc4). *)
Lemma shv_src : forall (RNG : ExecF.footprint) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte)
    (Q : machine_state -> Prop) (k : byte) (P I : Z)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x14 x15 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  0 <= P + I < 2^64 ->
  mrd rsegs mm (wa ((P + I) / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ (P + I) mod 8 < bv_signed k) ->
  ExecF.rng RNG ((P + I) / 8 + ASAN_K) 1 ->
  (forall y5 y6 : word, evtF rsegs RNG Q
     (MS (mkR x1 x2 x3 x4 y5 y6 x7 x8 x9 x10 x11 (Z_to_bv 64 (P + I)) (Z_to_bv 64 2147450880) x14 x15
              (Z_to_bv 64 I) (Z_to_bv 64 P) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
         F (Z_to_bv 64 0x8c310) fc None mm (seg_rom rsegs))) ->
  evtF rsegs RNG Q
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 2147450880) x14 x15
             (Z_to_bv 64 I) (Z_to_bv 64 P) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x8c2fc) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG F fc mm Q k P I x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x14 x15 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 RA M SK RGS CONT.
  unfold ASAN_K in M, RGS.
  step.
  step. gen_shr (Z_to_bv 64 (P + I)) g G. rewrite (unsigned_lit (P + I)) in G by lia.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound (P + I) 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step.
    rewrite land7. rewrite (unsigned_lit (P + I)) by lia.
    rewrite (lts_low ((P + I) mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* 0x82c9c .. 0x82cb0: the byte of the version field at a1 + a6 (error block 0x82cd0). *)
Lemma shv_dst : forall (RNG : ExecF.footprint) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte)
    (Q : machine_state -> Prop) (k : byte) (A I : Z)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x12 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  0 <= A + I < 2^64 ->
  mrd rsegs mm (wa ((A + I) / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ (A + I) mod 8 < bv_signed k) ->
  ExecF.rng RNG ((A + I) / 8 + ASAN_K) 1 ->
  (forall y6 y7 : word, evtF rsegs RNG Q
     (MS (mkR x1 x2 x3 x4 x5 y6 y7 x8 x9 x10 (Z_to_bv 64 A) (Z_to_bv 64 (A + I)) (Z_to_bv 64 2147450880) x14 x15
              (Z_to_bv 64 I) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
         F (Z_to_bv 64 0x8c32c) fc None mm (seg_rom rsegs))) ->
  evtF rsegs RNG Q
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 A) x12 (Z_to_bv 64 2147450880) x14 x15
             (Z_to_bv 64 I) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x8c318) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG F fc mm Q k A I x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x12 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 RA M SK RGS CONT.
  unfold ASAN_K in M, RGS.
  step.
  step. gen_shr (Z_to_bv 64 (A + I)) g G. rewrite (unsigned_lit (A + I)) in G by lia.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound (A + I) 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step.
    rewrite land7. rewrite (unsigned_lit (A + I)) by lia.
    rewrite (lts_low ((A + I) mod 8) k MB), (proj2 (Z.ltb_lt _ _) C).
    apply CONT.
Qed.

(* 0x82ce4 .. 0x82cf8: the NUL of the version field at a1 + t1 (error block 0x82db4). *)
Lemma shv_nul : forall (RNG : ExecF.footprint) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte)
    (Q : machine_state -> Prop) (k : byte) (A I : Z)
    (x1 x2 x3 x4 x5 x7 x8 x9 x10 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  0 <= A + I < 2^64 ->
  mrd rsegs mm (wa ((A + I) / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ (A + I) mod 8 < bv_signed k) ->
  ExecF.rng RNG ((A + I) / 8 + ASAN_K) 1 ->
  (forall y15 y16 : word, evtF rsegs RNG Q
     (MS (mkR x1 x2 x3 x4 x5 (Z_to_bv 64 I) x7 x8 x9 x10 (Z_to_bv 64 A) (Z_to_bv 64 (A + I))
              (Z_to_bv 64 2147450880) x14 y15 y16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
         F (Z_to_bv 64 0x8c374) fc None mm (seg_rom rsegs))) ->
  evtF rsegs RNG Q
    (MS (mkR x1 x2 x3 x4 x5 (Z_to_bv 64 I) x7 x8 x9 x10 (Z_to_bv 64 A) x12 (Z_to_bv 64 2147450880) x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x8c360) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG F fc mm Q k A I x1 x2 x3 x4 x5 x7 x8 x9 x10 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 RA M SK RGS CONT.
  unfold ASAN_K in M, RGS.
  step.
  step. gen_shr (Z_to_bv 64 (A + I)) g G. rewrite (unsigned_lit (A + I)) in G by lia.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound (A + I) 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step.
    rewrite land7. rewrite (unsigned_lit (A + I)) by lia.
    rewrite (lts_low ((A + I) mod 8) k MB), (proj2 (Z.ltb_lt _ _) C).
    apply CONT.
Qed.

(* 0x82d10 .. 0x82d24: the byte of the name at a5 + a2 (error block 0x82d54). *)
Lemma shn_src : forall (RNG : ExecF.footprint) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte)
    (Q : machine_state -> Prop) (k : byte) (P J : Z)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x14 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  0 <= P + J < 2^64 ->
  mrd rsegs mm (wa ((P + J) / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ (P + J) mod 8 < bv_signed k) ->
  ExecF.rng RNG ((P + J) / 8 + ASAN_K) 1 ->
  (forall y5 y17 : word, evtF rsegs RNG Q
     (MS (mkR x1 x2 x3 x4 y5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 J) (Z_to_bv 64 2147450880) x14 (Z_to_bv 64 P)
              (Z_to_bv 64 (P + J)) y17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
         F (Z_to_bv 64 0x8c3a0) fc None mm (seg_rom rsegs))) ->
  evtF rsegs RNG Q
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 J) (Z_to_bv 64 2147450880) x14 (Z_to_bv 64 P)
             x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x8c38c) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG F fc mm Q k P J x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x14 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 RA M SK RGS CONT.
  unfold ASAN_K in M, RGS.
  step.
  step. gen_shr (Z_to_bv 64 (P + J)) g G. rewrite (unsigned_lit (P + J)) in G by lia.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound (P + J) 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step.
    rewrite land7. rewrite (unsigned_lit (P + J)) by lia.
    rewrite (lts_low ((P + J) mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* 0x82d2c .. 0x82d40: the byte of the name field at a0 + a2 (error block 0x82d60). *)
Lemma shn_dst : forall (RNG : ExecF.footprint) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte)
    (Q : machine_state -> Prop) (k : byte) (D J : Z)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  0 <= D + J < 2^64 ->
  mrd rsegs mm (wa ((D + J) / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ (D + J) mod 8 < bv_signed k) ->
  ExecF.rng RNG ((D + J) / 8 + ASAN_K) 1 ->
  (forall y5 y6 : word, evtF rsegs RNG Q
     (MS (mkR x1 x2 x3 x4 y5 y6 x7 x8 x9 (Z_to_bv 64 D) x11 (Z_to_bv 64 J) (Z_to_bv 64 2147450880) x14 x15 x16
              (Z_to_bv 64 (D + J)) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
         F (Z_to_bv 64 0x8c3bc) fc None mm (seg_rom rsegs))) ->
  evtF rsegs RNG Q
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 D) x11 (Z_to_bv 64 J) (Z_to_bv 64 2147450880) x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x8c3a8) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG F fc mm Q k D J x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 RA M SK RGS CONT.
  unfold ASAN_K in M, RGS.
  step.
  step. gen_shr (Z_to_bv 64 (D + J)) g G. rewrite (unsigned_lit (D + J)) in G by lia.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound (D + J) 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step.
    rewrite land7. rewrite (unsigned_lit (D + J)) by lia.
    rewrite (lts_low ((D + J) mod 8) k MB), (proj2 (Z.ltb_lt _ _) C).
    apply CONT.
Qed.

(* 0x82d78 .. 0x82d8c: the NUL of the name field at a0 + t0 (error block 0x82dc4). *)
Lemma shn_nul : forall (RNG : ExecF.footprint) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte)
    (Q : machine_state -> Prop) (k : byte) (D J : Z)
    (x1 x2 x3 x4 x6 x7 x8 x9 x11 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  0 <= D + J < 2^64 ->
  mrd rsegs mm (wa ((D + J) / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ (D + J) mod 8 < bv_signed k) ->
  ExecF.rng RNG ((D + J) / 8 + ASAN_K) 1 ->
  (forall y11 y12 : word, evtF rsegs RNG Q
     (MS (mkR x1 x2 x3 x4 (Z_to_bv 64 J) x6 x7 x8 x9 (Z_to_bv 64 (D + J)) y11 y12 (Z_to_bv 64 2147450880)
              x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
         F (Z_to_bv 64 0x8c408) fc None mm (seg_rom rsegs))) ->
  evtF rsegs RNG Q
    (MS (mkR x1 x2 x3 x4 (Z_to_bv 64 J) x6 x7 x8 x9 (Z_to_bv 64 D) x11 x12 (Z_to_bv 64 2147450880)
             x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x8c3f4) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG F fc mm Q k D J x1 x2 x3 x4 x6 x7 x8 x9 x11 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 RA M SK RGS CONT.
  unfold ASAN_K in M, RGS.
  step.
  step. gen_shr (Z_to_bv 64 (D + J)) g G. rewrite (unsigned_lit (D + J)) in G by lia.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound (D + J) 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step.
    rewrite land7. rewrite (unsigned_lit (D + J)) by lia.
    rewrite (lts_low ((D + J) mod 8) k MB), (proj2 (Z.ltb_lt _ _) C).
    apply CONT.
Qed.

(** * The walk *)

Section ANN.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 : word).
Variables (s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word).
Variables (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Variables (bb aj : list byte) (f ap cmd body lo : Z) (RNG : ExecF.footprint).

Local Notation SP := (bv_unsigned sp).

Hypothesis Hf : 0 < f < 2^64.
Hypothesis Hap : 0 < ap < 2^64.
Hypothesis Hcmd : 0 <= cmd < 2^8.
Hypothesis Hbody : 0 < body < 2^64.
Hypothesis ST0 : stk rsegs m lo SP.
Hypothesis SPLO : lo + 16 <= SP.
Hypothesis DF30 : off_stk sp 16 (f + 30) 18.
Hypothesis DB15 : ann_ok cmd bb = true -> off_stk sp 16 (body + 15) 18.
Hypothesis HOK : ann_ok cmd bb = true ->
  rw_cells rsegs m ap [CB 40 aj] /\ (ap + 40 <= f + 30 \/ f + 48 <= ap) /\
  (ap + 40 <= body + 15 \/ body + 33 <= ap) /\ off_stk sp 16 ap 40.
Hypothesis APS1 : app_mem (SP - 16).
Hypothesis APS2 : app_mem (SP - 1).
Hypothesis CELLS0 : asan_cells m.
Hypothesis DGOT : off_stk sp 16 GOT_CELL_K (MIDEND + 8 - GOT_CELL_K).
Hypothesis A30 : addressable m (f + 30) 1.
Hypothesis A40 : ann_cmd cmd = true -> addressable m (f + 40) 8.
Hypothesis A32 : ann_ok cmd bb = true -> addressable m (f + 32) 8.
Hypothesis AB : ann_ok cmd bb = true -> addressable m (body + 15) 18.
Hypothesis AAP : ann_ok cmd bb = true -> addressable m ap 40.
Hypothesis RGW : ExecF.rng RNG (SP - 16) 16.
Hypothesis RGC : ExecF.rng RNG GOT_CELL_K 8.
Hypothesis RCK : ExecF.rng RNG CELL_K 8.
Hypothesis R30 : ExecF.rng RNG (f + 30) 1.
Hypothesis R30s : ExecF.rng RNG (shadow_addr (f + 30)) (shadow_addr (f + 30 + 1 - 1) - shadow_addr (f + 30) + 1).
Hypothesis R40 : ann_cmd cmd = true -> ExecF.rng RNG (f + 40) 8.
Hypothesis R40s : ann_cmd cmd = true ->
  ExecF.rng RNG (shadow_addr (f + 40)) (shadow_addr (f + 40 + 8 - 1) - shadow_addr (f + 40) + 1).
Hypothesis R32 : ann_ok cmd bb = true -> ExecF.rng RNG (f + 32) 8.
Hypothesis R32s : ann_ok cmd bb = true ->
  ExecF.rng RNG (shadow_addr (f + 32)) (shadow_addr (f + 32 + 8 - 1) - shadow_addr (f + 32) + 1).
Hypothesis RB : ann_ok cmd bb = true -> ExecF.rng RNG (body + 15) 18.
Hypothesis RBs : ann_ok cmd bb = true ->
  ExecF.rng RNG (shadow_addr (body + 15)) (shadow_addr (body + 15 + 18 - 1) - shadow_addr (body + 15) + 1).
Hypothesis RAP : ann_ok cmd bb = true -> ExecF.rng RNG ap 40.
Hypothesis RAPs : ann_ok cmd bb = true ->
  ExecF.rng RNG (shadow_addr ap) (shadow_addr (ap + 40 - 1) - shadow_addr ap + 1).

(* The post of the contract. *)
Definition PostA : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (ann_code cmd (Z.of_nat (length bb))))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    wmono rsegs m m' /\ stk rsegs m' lo SP /\
    (if ann_ok cmd bb
     then munch [(SP - 16, SP); (ap, ap + 40)] m m' /\ rw_cells rsegs m' ap (PAnn.ann_cells body bb aj)
     else munch [(SP - 16, SP)] m m').

Lemma ann_ok_true : ann_ok cmd bb = true -> ann_cmd cmd = true /\ 33 <= Z.of_nat (length bb).
Proof.
  unfold ann_ok, ann_code. intros H.
  destruct (ann_cmd cmd) eqn:AC; cbn [negb] in H.
  - destruct (Z.ltb_spec (Z.of_nat (length bb)) 33) as [L|L]; [cbn in H; discriminate|].
    split; [reflexivity | lia].
  - cbn in H. discriminate.
Qed.

Lemma ann_code0 : ann_ok cmd bb = true -> ann_code cmd (Z.of_nat (length bb)) = 0.
Proof. unfold ann_ok. intros H. apply Z.eqb_eq. exact H. Qed.

(* The 18 bytes of the body the code reads. *)
Definition bb18 : list byte := firstn 18 (skipn 15 bb).

Lemma bb18_len : ann_ok cmd bb = true -> length bb18 = 18%nat.
Proof.
  intros OK. destruct (ann_ok_true OK) as (_ & L).
  unfold bb18. rewrite length_firstn, length_skipn. lia.
Qed.

Lemma bb18_nth : forall (i : nat) b, (i < 18)%nat -> nth_error bb18 i = Some b ->
  nth_error (skipn 15 bb) i = Some b.
Proof.
  intros i b Hi H. unfold bb18 in H. rewrite nth_error_firstn in H.
  destruct (Nat.ltb_spec i 18) as [E|E]; [exact H | lia].
Qed.

Lemma bb18_nth15 : forall (i : nat) b, (i < 9)%nat -> nth_error bb18 (9 + i) = Some b ->
  nth_error (skipn 24 bb) i = Some b.
Proof.
  intros i b Hi H. apply bb18_nth in H; [|lia]. rewrite ne_skipn in H.
  rewrite ne_skipn. replace (24 + i)%nat with (15 + (9 + i))%nat by lia. exact H.
Qed.

Lemma strz24 : strz_len (skipn 9 bb18) = strz_len (skipn 24 bb).
Proof.
  unfold strz_len, bb18. rewrite skipn_firstn_comm, firstn_firstn.
  replace (Nat.min 9 (18 - 9)) with 9%nat by reflexivity.
  rewrite skipn_skipn. replace (9 + 15)%nat with 24%nat by lia. reflexivity.
Qed.

(* The state of memory at a loop head. *)
Definition INVa (jj : list byte) (m1 : word -> option byte) (L : list byte) : Prop :=
  rw_cells rsegs m1 ap [CB 24 L; C8 (Z_to_bv 64 body); C8 (Z_to_bv 64 15)] /\
  munch [(SP - 16, SP); (ap, ap + 40)] m m1 /\ wmono rsegs m m1 /\
  bytes_at rsegs m1 (body + 15) bb18 /\
  ro_cells rsegs m1 (f + 32) [C8 (Z_to_bv 64 body); C8 (Z_to_bv 64 (Z.of_nat (length bb)))] /\
  stk rsegs m1 lo (SP + -16) /\
  rw_cells rsegs m1 (SP + -16) [CB 8 jj; C8 ra].

(* Every byte the code writes is application memory, so no shadow byte is in the written window. *)
Lemma INV_addr : forall jj m1 L p n, ann_ok cmd bb = true -> INVa jj m1 L ->
  addressable m p n -> addressable m1 p n.
Proof.
  intros jj m1 L p n OK (_ & MU & _) A.
  eapply addr_munch; [exact A | exact MU |].
  intros i Hi. destruct A as (_ & _ & _ & HA). destruct (HA i Hi) as (Ha & _).
  pose proof (shadow_not_app _ Ha) as NA. cbn [outside]. split; [|split; [|exact I]].
  - intros W. apply NA. apply (app_win SP 16); [lia | exact APS1 | exact APS2 | lia].
  - intros W. apply NA. destruct (AAP OK) as (_ & _ & _ & HO).
    destruct (HO ((p + i) / 8 + ASAN_K - ap) ltac:(lia)) as (Ho & _).
    replace (ap + ((p + i) / 8 + ASAN_K - ap)) with ((p + i) / 8 + ASAN_K) in Ho by lia. exact Ho.
Qed.

Lemma INV_sok : forall jj m1 L (i : nat) (w : word),
  INVa jj m1 L -> (i < 24)%nat -> w = Z_to_bv 64 (ap + Z.of_nat i) -> store_ok rsegs m1 w 1 = true.
Proof.
  intros jj m1 L i w (CA & _) Hi ->. destruct CA as [_ Hw]. cbn [cells_size csize Nat.add] in Hw.
  change (Z_to_bv 64 (ap + Z.of_nat i)) with (wa (ap + Z.of_nat i)).
  exact (wr_at_store_ok rsegs m1 ap _ (Z.of_nat i) 1 Hw ltac:(lia) ltac:(lia)).
Qed.

Lemma INV_store : forall jj m1 L (i : nat) (w : word) (b : byte),
  ann_ok cmd bb = true -> INVa jj m1 L -> (i < 24)%nat -> w = Z_to_bv 64 (ap + Z.of_nat i) ->
  INVa jj (write_to_mem m1 w [b]) (upd_bytes L i [b]).
Proof.
  intros jj m1 L i w b OK (CA & MU & WM & BW & RF & STK & FR) Hi ->.
  destruct (HOK OK) as (_ & DFA & DBA & DSA). unfold off_stk in DSA.
  pose proof (rw_cells_bound rsegs m1 ap _ CA) as HA. cbn [cells_size csize Nat.add] in HA.
  pose proof (length_firstn 18 (skipn 15 bb)) as LB. fold bb18 in LB.
  change (Z_to_bv 64 (ap + Z.of_nat i)) with (wa (ap + Z.of_nat i)).
  destruct (stb [(SP - 16, SP); (ap, ap + 40)] m m1 ap 24 L [C8 (Z_to_bv 64 body); C8 (Z_to_bv 64 15)] i b
             CA Hi MU ltac:(cbn [inside]; lia) WM) as (CA' & MU' & WM').
  split; [exact CA'|]. split; [exact MU'|]. split; [exact WM'|].
  split. { apply bytes_at_write_other; [exact BW | lia | cbn [length]; lia | cbn [length]; lia]. }
  split. { apply ro_cells_frame; [exact RF | lia | cbn [length]; lia | cbn [cells_size csize length]; lia]. }
  split. { apply stk_write; [exact STK | lia | cbn [length]; lia]. }
  apply rw_cells_frame; [exact FR | lia | cbn [length]; lia | cbn [cells_size csize length]; lia].
Qed.

Ltac stored OKh I i :=
  rewrite ?le1_zxb, ?le1_0;
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?w [?bv]) _) =>
      let I' := fresh "I" in
      pose proof (INV_store _ mm _ i w bv OKh I ltac:(lia) ltac:(first [reflexivity | f_equal; lia])) as I';
      let mn := fresh "mw" in
      set (mn := write_to_mem mm w [bv]) in *; clearbody mn; clear I; rename I' into I
  end.

(* 0x82d94: the three exits. *)
Lemma ann_exit : forall (m1 : word -> option byte) (r : Z) (jj : list byte)
    (x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 : word),
  rw_cells rsegs m1 (SP + -16) [CB 8 jj; C8 ra] ->
  stk rsegs m1 lo (SP + -16) ->
  wmono rsegs m m1 ->
  r = ann_code cmd (Z.of_nat (length bb)) ->
  (if ann_ok cmd bb
   then munch [(SP - 16, SP); (ap, ap + 40)] m m1 /\ rw_cells rsegs m1 ap (PAnn.ann_cells body bb aj)
   else munch [(SP - 16, SP)] m m1) ->
  evtF rsegs RNG PostA
    (MS (mkR x1 (Z_to_bv 64 (SP + -16)) gp tp x5 x6 x7 s0 s1 x10 x11 (Z_to_bv 64 r) x13 x14 x15 x16 x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x8c410) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 r jj x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 FR STK WM Er HM.
  pose proof (u64_range sp) as Rsp.
  assert (Hlo : 0 <= lo) by (destruct STK as [H _]; lia).
  step. step. step. step.
  apply evtF_done. unfold PostA.
  exists x5, x6, x7, x11, (Z_to_bv 64 r), x13, x14, x15, x16, x17, m1.
  split; [subst r; reflexivity|]. split; [exact WM|]. split.
  - pose proof (stk_release rsegs m1 lo (SP + -16) _ STK FR ltac:(lia)) as ST2.
    cbn [cells_size csize Nat.add] in ST2. replace (SP + -16 + Z.of_nat 16) with SP in ST2 by lia. exact ST2.
  - exact HM.
Qed.

(* 0x82d78: the NUL of the name, then the exit with the code 0. *)
Lemma FIN2 : forall (jj : list byte) (m1 : word -> option byte) (K : nat)
    (x6 x7 x11 x12 x14 x15 x16 x17 : word),
  ann_ok cmd bb = true -> length aj = 40%nat -> strz_len (skipn 24 bb) = K ->
  INVa jj m1 (ann_version bb (firstn 10 aj) ++ firstn K (skipn 24 bb) ++ skipn (10 + K) (firstn 24 aj)) ->
  evtF rsegs RNG PostA
    (MS (mkR ra (Z_to_bv 64 (SP + -16)) gp tp (Z_to_bv 64 (Z.of_nat K)) x6 x7 s0 s1
             (Z_to_bv 64 (ap + 10)) x11 x12 (Z_to_bv 64 2147450880) x14 x15 x16 x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x8c3f4) fc None m1 (seg_rom rsegs)).
Proof.
  intros jj m1 K x6 x7 x11 x12 x14 x15 x16 x17 OK Laj EK I. subst K.
  destruct (ann_ok_true OK) as (AC & L33).
  destruct (HOK OK) as (CA0 & DFA & DBA & DSA). unfold off_stk in DSA.
  pose proof (strz_len_le (skipn 24 bb)) as K2le.
  pose proof (AAP OK) as AAP1. pose proof (INV_addr _ _ _ _ _ OK I AAP1) as AAP2.
  pose proof (addr_bound m ap 40 AAP1) as BAP. pose proof (RAP OK) as RGAP.
  destruct (addr_one m1 ap 40 (10 + Z.of_nat (strz_len (skipn 24 bb))) AAP2 ltac:(lia)) as (_ & kk & MK & SK).
  eapply (shn_nul RNG F fc m1 PostA kk (ap + 10) (Z.of_nat (strz_len (skipn 24 bb))));
    [ lia
    | replace (ap + 10 + Z.of_nat (strz_len (skipn 24 bb))) with (ap + (10 + Z.of_nat (strz_len (skipn 24 bb)))) by lia; exact MK
    | replace (ap + 10 + Z.of_nat (strz_len (skipn 24 bb))) with (ap + (10 + Z.of_nat (strz_len (skipn 24 bb)))) by lia; exact SK
    | replace (ap + 10 + Z.of_nat (strz_len (skipn 24 bb))) with (ap + (10 + Z.of_nat (strz_len (skipn 24 bb)))) by lia;
      eapply rng_shadow_one; [exact (RAPs OK) | lia]
    | intros y11 y12 ].
  step.
  assert (HS : store_ok rsegs m1 (Z_to_bv 64 (ap + 10 + Z.of_nat (strz_len (skipn 24 bb)))) 1 = true)
    by (eapply (INV_sok _ _ _ (10 + (strz_len (skipn 24 bb)))%nat); [exact I | lia | f_equal; lia]).
  step. clear HS.
  stored OK I (10 + (strz_len (skipn 24 bb)))%nat.
  rewrite (name_nul bb aj (Z_to_bv 8 0) ltac:(reflexivity) Laj) in I.
  destruct I as (CA & MU & WM & _ & _ & STK & FR).
  eapply (ann_exit _ 0 jj); [exact FR | exact STK | exact WM | symmetry; apply ann_code0; exact OK |].
  rewrite OK. split; [exact MU|]. unfold PAnn.ann_cells.
  apply rw_split3; [ | | | exact CA].
  - apply length_copy_strz. rewrite length_firstn. lia.
  - apply length_copy_strz. rewrite length_firstn, length_skipn. lia.
  - rewrite length_firstn, length_skipn. lia.
Qed.

(* 0x82d10: the loop of the name; j bytes copied. *)
Lemma LOOP2 : forall (jj : list byte) (k j : nat) (m1 : word -> option byte) (x5 x6 x7 x16 x17 : word),
  ann_ok cmd bb = true -> length aj = 40%nat ->
  (j + S k = 9)%nat ->
  (forall i, (i < j)%nat -> at8 (skipn 24 bb) i <> 0) ->
  INVa jj m1 (ann_version bb (firstn 10 aj) ++ firstn j (skipn 24 bb) ++ skipn (10 + j) (firstn 24 aj)) ->
  evtF rsegs RNG PostA
    (MS (mkR ra (Z_to_bv 64 (SP + -16)) gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 (ap + 10))
             (Z_to_bv 64 ap) (Z_to_bv 64 (Z.of_nat j)) (Z_to_bv 64 2147450880) (Z_to_bv 64 body)
             (Z_to_bv 64 (body + 24)) x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x8c38c) fc None m1 (seg_rom rsegs)).
Proof.
  intros jj k. induction k as [|k IH]; intros j m1 x5 x6 x7 x16 x17 OK Laj Hk Hnz I.
  all: destruct (ann_ok_true OK) as (AC & L33).
  all: pose proof (AB OK) as AB1; pose proof (INV_addr _ _ _ _ _ OK I AB1) as AB2.
  all: pose proof (AAP OK) as AAP1; pose proof (INV_addr _ _ _ _ _ OK I AAP1) as AAP2.
  all: pose proof (addr_bound m ap 40 AAP1) as BAP; pose proof (addr_bound m (body + 15) 18 AB1) as BBD.
  all: pose proof (RAP OK) as RGAP; pose proof (RB OK) as RGBD.
  all: pose proof (bb18_len OK) as LB18.
  all: assert (L24 : (9 <= length (skipn 24 bb))%nat) by (rewrite length_skipn; lia).
  all: destruct (byte_at bb18 (9 + j) ltac:(lia)) as [b Nb].
  all: assert (Nb' : nth_error (skipn 24 bb) j = Some b) by (apply bb18_nth15; [lia | exact Nb]).
  all: pose proof (at8_ne _ _ _ Nb') as Ab.
  all: destruct (addr_one m1 (body + 15) 18 (9 + Z.of_nat j) AB2 ltac:(lia)) as (_ & k0 & MK & SK).
  all: eapply (shn_src RNG F fc m1 PostA k0 (body + 24) (Z.of_nat j));
         [ lia
         | replace (body + 24 + Z.of_nat j) with (body + 15 + (9 + Z.of_nat j)) by lia; exact MK
         | replace (body + 24 + Z.of_nat j) with (body + 15 + (9 + Z.of_nat j)) by lia; exact SK
         | replace (body + 24 + Z.of_nat j) with (body + 15 + (9 + Z.of_nat j)) by lia;
           eapply rng_shadow_one; [exact (RBs OK) | lia]
         | intros y5 y17 ].
  all: pose proof (proj1 (proj2 (proj2 (proj2 I)))) as BW.
  all: pose proof (rdb m1 (body + 15) bb18 (9 + j) b BW Nb) as HR.
  all: replace (body + 15 + Z.of_nat (9 + j)) with (body + 24 + Z.of_nat j) in HR by lia.
  all: step; [idtac].
  all: clear HR.
  all: step.
  all: rewrite zb_eq0.
  all: destruct (Z.eqb_spec (bz b) 0) as [Z0|Z0]; cbv iota.
  1, 3: assert (Ek : strz_len (skipn 24 bb) = j)
          by (apply strz_len_char; [lia | lia | exact Hnz | intros; lia]);
        step; eapply (FIN2 jj _ j); [exact OK | exact Laj | exact Ek | exact I].
  all: destruct (addr_one m1 ap 40 (10 + Z.of_nat j) AAP2 ltac:(lia)) as (_ & k1 & MK1 & SK1).
  all: eapply (shn_dst RNG F fc m1 PostA k1 (ap + 10) (Z.of_nat j));
         [ lia
         | replace (ap + 10 + Z.of_nat j) with (ap + (10 + Z.of_nat j)) by lia; exact MK1
         | replace (ap + 10 + Z.of_nat j) with (ap + (10 + Z.of_nat j)) by lia; exact SK1
         | replace (ap + 10 + Z.of_nat j) with (ap + (10 + Z.of_nat j)) by lia;
           eapply rng_shadow_one; [exact (RAPs OK) | lia]
         | intros z5 z6 ].
  all: step; step.
  all: assert (HS : store_ok rsegs m1 (Z_to_bv 64 (ap + 10 + Z.of_nat j)) 1 = true)
         by (eapply (INV_sok _ _ _ (10 + j)%nat); [exact I | lia | f_equal; lia]).
  all: step; clear HS.
  all: stored OK I (10 + j)%nat.
  all: assert (HV : length (ann_version bb (firstn 10 aj)) = 10%nat)
         by (apply length_copy_strz; rewrite length_firstn; lia).
  all: rewrite (upd_snoc (ann_version bb (firstn 10 aj)) (skipn 24 bb) (firstn 24 aj) 10 j b HV Nb') in I.
  all: step.
  all: rewrite (eqb_lit (Z.of_nat j + 1) 9) by lia.
  - replace (Z.of_nat j + 1 =? 9) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb]. cbv iota.
    step.
    assert (Ek : strz_len (skipn 24 bb) = 9%nat).
    { apply strz_len_char; [lia | lia | | lia].
      intros i Hi. destruct (Nat.eq_dec i j) as [->|NE]; [lia | apply Hnz; lia]. }
    eapply (FIN2 jj _ 9%nat); [exact OK | exact Laj | exact Ek |
      replace (S j) with 9%nat in I by lia; exact I].
  - replace (Z.of_nat j + 1 =? 9) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv iota.
    replace (Z_to_bv 64 (Z.of_nat j + 1)) with (Z_to_bv 64 (Z.of_nat (S j))) by (f_equal; lia).
    eapply (IH (S j)); [exact OK | exact Laj | lia | | exact I].
    intros i Hi. destruct (Nat.eq_dec i j) as [->|NE]; [lia | apply Hnz; lia].
Qed.

(* 0x82ce4: the NUL of the version, the body address again, then the loop of the name. *)
Lemma MID1 : forall (jj : list byte) (m1 : word -> option byte) (K : nat) (x5 x7 x12 x15 x16 x17 : word),
  ann_ok cmd bb = true -> length aj = 40%nat -> strz_len (skipn 15 bb) = K ->
  INVa jj m1 (firstn K (skipn 15 bb) ++ skipn K (firstn 24 aj)) ->
  evtF rsegs RNG PostA
    (MS (mkR ra (Z_to_bv 64 (SP + -16)) gp tp x5 (Z_to_bv 64 (Z.of_nat K)) x7 s0 s1
             (Z_to_bv 64 (f + 32)) (Z_to_bv 64 ap) x12 (Z_to_bv 64 2147450880)
             (Z_to_bv 64 ((f + 32) / 8 + 2147450880)) x15 x16 x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x8c360) fc None m1 (seg_rom rsegs)).
Proof.
  intros jj m1 K x5 x7 x12 x15 x16 x17 OK Laj EK I. subst K.
  destruct (ann_ok_true OK) as (AC & L33).
  pose proof (strz_len_le (skipn 15 bb)) as K1le.
  pose proof (AAP OK) as AAP1. pose proof (INV_addr _ _ _ _ _ OK I AAP1) as AAP2.
  pose proof (A32 OK) as A321.
  pose proof (addr_bound m ap 40 AAP1) as BAP. pose proof (addr_bound m (f + 32) 8 A321) as BF32.
  pose proof (RAP OK) as RGAP. pose proof (R32 OK) as RG32.
  destruct (addr_one m1 ap 40 (Z.of_nat (strz_len (skipn 15 bb))) AAP2 ltac:(lia)) as (_ & kk & MK & SK).
  eapply (shv_nul RNG F fc m1 PostA kk ap (Z.of_nat (strz_len (skipn 15 bb))));
    [ lia | exact MK | exact SK
    | eapply rng_shadow_one; [exact (RAPs OK) | lia]
    | intros y15 y16 ].
  assert (HS : store_ok rsegs m1 (Z_to_bv 64 (ap + Z.of_nat (strz_len (skipn 15 bb)))) 1 = true)
    by (eapply (INV_sok _ _ _ (strz_len (skipn 15 bb))); [exact I | lia | reflexivity]).
  step. clear HS.
  stored OK I (strz_len (skipn 15 bb)).
  rewrite (ver_nul bb aj (Z_to_bv 8 0) ltac:(reflexivity) Laj) in I.
  (* the shadow byte of f + 32 again *)
  pose proof (INV_addr _ _ _ _ _ OK I A321) as A322.
  destruct (addr_eight _ (f + 32) 8 (f + 32) A322 ltac:(lia) ltac:(lia)) as (k2 & MK2 & SK2).
  pose proof (rdw0 _ (Z_to_bv 64 ((f + 32) / 8 + 2147450880)) _ _ MK2
                ltac:(unfold ASAN_K; apply unsigned_lit; Z.div_mod_to_equations; lia)) as R2.
  pose proof (rng_shadow_one RNG (f + 32) 8 (f + 32) (R32s OK) ltac:(lia)) as RG32s.
  unfold ASAN_K in RG32s.
  step. clear R2.
  replace (zxb k2) with (Z_to_bv 64 0) by (unfold zxb; rewrite (byte_signed0 k2 SK2); reflexivity).
  step. if_false.
  (* 0x82d04: the body field again *)
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 I))))) as RF.
  step. step. step.
  eapply (LOOP2 jj 8%nat 0%nat); [exact OK | exact Laj | lia | intros i Hi; lia |].
  cbn [firstn app]. replace (10 + 0)%nat with 10%nat by lia. exact I.
Qed.

(* 0x82c80: the loop of the version; i bytes copied. *)
Lemma LOOP1 : forall (jj : list byte) (k i : nat) (m1 : word -> option byte) (x5 x6 x7 x12 : word),
  ann_ok cmd bb = true -> length aj = 40%nat ->
  (i + S k = 9)%nat ->
  (forall j, (j < i)%nat -> at8 (skipn 15 bb) j <> 0) ->
  INVa jj m1 (firstn i (skipn 15 bb) ++ skipn i (firstn 24 aj)) ->
  evtF rsegs RNG PostA
    (MS (mkR ra (Z_to_bv 64 (SP + -16)) gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 ap) x12
             (Z_to_bv 64 2147450880) (Z_to_bv 64 ((f + 32) / 8 + 2147450880)) (Z_to_bv 64 body)
             (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 (body + 15))
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x8c2fc) fc None m1 (seg_rom rsegs)).
Proof.
  intros jj k. induction k as [|k IH]; intros i m1 x5 x6 x7 x12 OK Laj Hk Hnz I.
  all: destruct (ann_ok_true OK) as (AC & L33).
  all: pose proof (AB OK) as AB1; pose proof (INV_addr _ _ _ _ _ OK I AB1) as AB2.
  all: pose proof (AAP OK) as AAP1; pose proof (INV_addr _ _ _ _ _ OK I AAP1) as AAP2.
  all: pose proof (addr_bound m ap 40 AAP1) as BAP; pose proof (addr_bound m (body + 15) 18 AB1) as BBD.
  all: pose proof (RAP OK) as RGAP; pose proof (RB OK) as RGBD.
  all: pose proof (bb18_len OK) as LB18.
  all: assert (L15 : (18 <= length (skipn 15 bb))%nat) by (rewrite length_skipn; lia).
  all: destruct (byte_at bb18 i ltac:(lia)) as [b Nb].
  all: assert (Nb' : nth_error (skipn 15 bb) i = Some b) by (apply bb18_nth; [lia | exact Nb]).
  all: pose proof (at8_ne _ _ _ Nb') as Ab.
  all: destruct (addr_one m1 (body + 15) 18 (Z.of_nat i) AB2 ltac:(lia)) as (_ & k0 & MK & SK).
  all: eapply (shv_src RNG F fc m1 PostA k0 (body + 15) (Z.of_nat i));
         [ lia | exact MK | exact SK
         | eapply rng_shadow_one; [exact (RBs OK) | lia]
         | intros y5 y6 ].
  all: pose proof (proj1 (proj2 (proj2 (proj2 I)))) as BW.
  all: pose proof (rdb m1 (body + 15) bb18 i b BW Nb) as HR.
  all: step; [idtac].
  all: clear HR.
  all: step.
  all: rewrite zb_eq0.
  all: destruct (Z.eqb_spec (bz b) 0) as [Z0|Z0]; cbv iota.
  1, 3: assert (Ek : strz_len (skipn 15 bb) = i)
          by (apply strz_len_char; [lia | lia | exact Hnz | intros; lia]);
        step; eapply (MID1 jj _ i); [exact OK | exact Laj | exact Ek | exact I].
  all: destruct (addr_one m1 ap 40 (Z.of_nat i) AAP2 ltac:(lia)) as (_ & k1 & MK1 & SK1).
  all: eapply (shv_dst RNG F fc m1 PostA k1 ap (Z.of_nat i));
         [ lia | exact MK1 | exact SK1
         | eapply rng_shadow_one; [exact (RAPs OK) | lia]
         | intros z6 z7 ].
  all: step; step.
  all: assert (HS : store_ok rsegs m1 (Z_to_bv 64 (ap + Z.of_nat i)) 1 = true)
         by (eapply (INV_sok _ _ _ i); [exact I | lia | reflexivity]).
  all: step; clear HS.
  all: stored OK I i.
  all: replace (upd_bytes (firstn i (skipn 15 bb) ++ skipn i (firstn 24 aj)) i [b])
         with (firstn (S i) (skipn 15 bb) ++ skipn (S i) (firstn 24 aj)) in I
         by (symmetry; exact (upd_snoc [] (skipn 15 bb) (firstn 24 aj) 0 i b eq_refl Nb')).
  all: step.
  all: rewrite (eqb_lit (Z.of_nat i + 1) 9) by lia.
  - replace (Z.of_nat i + 1 =? 9) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb]. cbv iota.
    step.
    assert (Ek : strz_len (skipn 15 bb) = 9%nat).
    { apply strz_len_char; [lia | lia | | lia].
      intros j Hj. destruct (Nat.eq_dec j i) as [->|NE]; [lia | apply Hnz; lia]. }
    eapply (MID1 jj _ 9%nat); [exact OK | exact Laj | exact Ek |
      replace (S i) with 9%nat in I by lia; exact I].
  - replace (Z.of_nat i + 1 =? 9) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv iota.
    replace (Z_to_bv 64 (Z.of_nat i + 1)) with (Z_to_bv 64 (Z.of_nat (S i))) by (f_equal; lia).
    eapply (IH (S i)); [exact OK | exact Laj | lia | | exact I].
    intros j Hj. destruct (Nat.eq_dec j i) as [->|NE]; [lia | apply Hnz; lia].
Qed.

Lemma addr_win1 : forall (m1 : word -> option byte) p n,
  addressable m p n -> munch [(SP - 16, SP)] m m1 -> addressable m1 p n.
Proof.
  intros m1 p n A MU. eapply addr_munch; [exact A | exact MU |].
  intros i Hi. destruct A as (_ & _ & _ & HA). destruct (HA i Hi) as (Ha & _).
  pose proof (shadow_not_app _ Ha) as NA. cbn [outside]. split; [|exact I].
  intros W. apply NA. apply (app_win SP 16); [lia | exact APS1 | exact APS2 | lia].
Qed.

Lemma addr_win2 : forall (m1 : word -> option byte) p n,
  ann_ok cmd bb = true -> addressable m p n ->
  munch [(SP - 16, SP); (ap, ap + 40)] m m1 -> addressable m1 p n.
Proof.
  intros m1 p n OK A MU. eapply addr_munch; [exact A | exact MU |].
  intros i Hi. destruct A as (_ & _ & _ & HA). destruct (HA i Hi) as (Ha & _).
  pose proof (shadow_not_app _ Ha) as NA. cbn [outside]. split; [|split; [|exact I]].
  - intros W. apply NA. apply (app_win SP 16); [lia | exact APS1 | exact APS2 | lia].
  - intros W. apply NA. destruct (AAP OK) as (_ & _ & _ & HO).
    destruct (HO ((p + i) / 8 + ASAN_K - ap) ltac:(lia)) as (Ho & _).
    replace (ap + ((p + i) / 8 + ASAN_K - ap)) with ((p + i) / 8 + ASAN_K) in Ho by lia. exact Ho.
Qed.

Ltac curmemF k := lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => k mm end.

(* (x >> 3) of a literal address, as x / 8. *)
Ltac shr_norm E :=
  rewrite (unsigned_lit E) by lia; rewrite (Z.shiftr_div_pow2 E 3) by lia; change (2 ^ 3) with 8.

(* An 8-byte access: its shadow byte is 0, so the check has one path. *)
Ltac shadow8 MK SK :=
  let RR := fresh "RR" in
  pose proof (rd1 _ _ _ MK) as RR; unfold ASAN_K in RR;
  step; clear RR;
  lazymatch type of MK with mrd _ _ _ = Some ?kb =>
    replace (zxb kb) with (Z_to_bv 64 0) by (unfold zxb; rewrite (byte_signed0 _ SK); reflexivity)
  end;
  step; if_false.

(* 0x82bbc: the whole run.  The three bytes_at premises are the lemma's own, not the section's: the walk stores
   into the frame and into ap, and each store transports (or forgets) the bytes_at facts of the context. *)
Lemma ENTRY :
  bytes_at rsegs m (f + 30) [b8 cmd] ->
  bytes_at rsegs m (f + 32) (le8 (Z_to_bv 64 body) ++ le8 (Z_to_bv 64 (Z.of_nat (length bb)))) ->
  bytes_at rsegs m body bb ->
  evtF rsegs RNG PostA
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 ap) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x8c238) fc None m (seg_rom rsegs)).
Proof.
  intros BC BF BB.
  pose proof (u64_range sp) as Rsp.
  assert (Hlo : 0 <= lo) by (destruct ST0 as [H _]; lia).
  pose proof (bytes_at_bound rsegs m body bb BB) as HBB.
  pose proof (addr_bound m (f + 30) 1 A30) as B30.
  pose proof DF30 as DF30u. unfold off_stk in DF30u.
  pose proof DGOT as DGOTu. unfold off_stk, GOT_CELL_K, MIDEND in DGOTu.
  pose proof RGC as RGCu. unfold GOT_CELL_K in RGCu.
  pose proof RCK as RCKu. unfold CELL_K in RCKu.
  assert (RC : ro_cells rsegs m (f + 30) [C1 (b8 cmd)]).
  { apply ro_of_bytes; [repeat split|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact BC. }
  assert (RF : ro_cells rsegs m (f + 32) [C8 (Z_to_bv 64 body); C8 (Z_to_bv 64 (Z.of_nat (length bb)))]).
  { apply ro_of_bytes; [repeat split|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact BF. }
  pose proof (conj BB CELLS0) as PK. clear BB BC BF.
  (* the frame [sp - 16, sp) *)
  destruct (stk_carve rsegs m lo SP 16 ST0 ltac:(lia)) as [STc [junk FR]].
  change (Z.of_nat 16) with 16 in STc, FR.
  replace (SP - 16) with (SP + -16) in STc, FR by lia.
  pose proof (munch_refl [(SP - 16, SP)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step.
  destruct PK as (BB & CELLSm).
  step.
  step. rewrite (eqb_nz f) by lia; cbv iota.
  step. rewrite (eqb_nz ap) by lia; cbv iota.
  step.
  curmemF ltac:(fun mm => assert (CELLS1 : asan_cells mm)
    by (eapply asan_cells_munch; [exact CELLSm | exact MU | unfold MIDEND, GOT_CELL_K; lia])).
  pose proof CELLS1 as (CK & GCK & _). clear CELLS1.
  unfold CELL_K, GOT_CELL_K, ASAN_K in CK, GCK.
  pose proof (rd_all _ _ _ GCK) as RDG. rewrite length_le8 in RDG.
  pose proof (rd_all _ _ _ CK) as RDS. rewrite length_le8 in RDS.
  step. step. clear RDG RDS CK GCK.
  (* 0x82bdc: the shadow byte of f + 30 *)
  curmemF ltac:(fun mm =>
    destruct (addr_one mm (f + 30) 1 0 (addr_win1 mm (f + 30) 1 A30 MU) ltac:(lia))
      as (_ & k30 & MK30 & SK30)).
  replace (f + 30 + 0) with (f + 30) in MK30, SK30 by lia.
  eapply (sh30 RNG F fc _ PostA k30 f);
    [ lia | exact MK30 | exact SK30
    | eapply rng_shadow_one; [exact R30s | lia]
    | intros y14 y15 ].
  (* 0x82bf0: the byte cmd *)
  step. step. step. step.
  rewrite cmd_test by lia.
  assert (ACd : ann_cmd cmd = true \/ ann_cmd cmd = false) by (destruct (ann_cmd cmd); auto).
  destruct ACd as [AC|AC]; rewrite AC; cbn [negb]; cbv iota.
  2:{ (* the command is not e0 / e1: the code is -9 *)
      step. step.
      assert (ANO : ann_ok cmd bb = false) by (unfold ann_ok, ann_code; rewrite AC; reflexivity).
      eapply (ann_exit _ (-9));
        [ exact FR | exact STc | exact WM
        | unfold ann_code; rewrite AC; reflexivity
        | rewrite ANO; exact MU ]. }
  (* 0x82c00: the shadow bytes of f + 40 *)
  pose proof (A40 AC) as A401. pose proof (addr_bound m (f + 40) 8 A401) as B40.
  pose proof (R40 AC) as RG40.
  curmemF ltac:(fun mm =>
    destruct (addr_eight mm (f + 40) 8 (f + 40) (addr_win1 mm (f + 40) 8 A401 MU) ltac:(lia) ltac:(lia))
      as (k40 & MK40 & SK40)).
  step.
  step. shr_norm (f + 40).
  step.
  pose proof (rng_shadow_one RNG (f + 40) 8 (f + 40) (R40s AC) ltac:(lia)) as RG40s. unfold ASAN_K in RG40s.
  shadow8 MK40 SK40.
  (* 0x82c14: the length *)
  step. step. step.
  assert (OKd : ann_ok cmd bb = true \/ ann_ok cmd bb = false) by (destruct (ann_ok cmd bb); auto).
  destruct OKd as [OK|OK].
  2:{ (* a body under 33 bytes: the code is -4 *)
      assert (L33 : Z.of_nat (length bb) < 33).
      { unfold ann_ok, ann_code in OK. rewrite AC in OK. cbn [negb] in OK.
        destruct (Z.ltb_spec (Z.of_nat (length bb)) 33) as [L|L]; [lia | cbn in OK; discriminate]. }
      rewrite (ltu_lit (Z.of_nat (length bb)) 33 ltac:(lia) ltac:(lia)).
      replace (Z.of_nat (length bb) <? 33) with true by (symmetry; apply Z.ltb_lt; lia).
      cbn [negb]. cbv iota.
      step. step.
      eapply (ann_exit _ (-4));
        [ exact FR | exact STc | exact WM
        | unfold ann_code; rewrite AC; cbn [negb];
          replace (Z.of_nat (length bb) <? 33) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity
        | rewrite OK; exact MU ]. }
  (* the announce parses: the code is 0 *)
  destruct (HOK OK) as (CA0 & DFA & DBA & DSA). pose proof DSA as DSAu. unfold off_stk in DSAu.
  pose proof (rw_cells_bound rsegs m ap _ CA0) as HAB. cbn [cells_size csize] in HAB.
  destruct (ann_ok_true OK) as (_ & L33).
  rewrite (ltu_lit (Z.of_nat (length bb)) 33 ltac:(lia) ltac:(lia)).
  replace (Z.of_nat (length bb) <? 33) with false by (symmetry; apply Z.ltb_ge; lia).
  cbn [negb]. cbv iota.
  pose proof (DB15 OK) as DB15u. unfold off_stk in DB15u.
  assert (Laj : length aj = 40%nat) by (destruct CA0 as [[[Hl _] _] _]; exact Hl).
  pose proof (AAP OK) as AAP1. pose proof (addr_bound m ap 40 AAP1) as BAP.
  pose proof (A32 OK) as A321. pose proof (addr_bound m (f + 32) 8 A321) as BF32.
  pose proof (AB OK) as AB1. pose proof (addr_bound m (body + 15) 18 AB1) as BBD.
  pose proof (RAP OK) as RGAP. pose proof (R32 OK) as RG32. pose proof (RB OK) as RGBD.
  pose proof (bb18_len OK) as LB18.
  pose proof (bytes_window m body bb 15 18 ltac:(lia) BB) as BW0. fold bb18 in BW0.
  curmemF ltac:(fun mm =>
    assert (CA : rw_cells rsegs mm ap [CB 40 aj])
      by (eapply rw_cells_transport;
          [exact CA0 | exact MU | exact WM | cbn [disjoint_from cells_size csize]; split; [lia | exact I]]);
    assert (BW : bytes_at rsegs mm (body + 15) bb18)
      by (eapply bytes_at_transport; [exact BW0 | exact MU | cbn [disjoint_from]; split; [lia | exact I]])).
  clear BW0 CA0 BB.
  apply (munch_extend _ _ _ _ ap (ap + 40)) in MU.
  (* 0x82c30: the shadow byte of f + 32 *)
  curmemF ltac:(fun mm =>
    destruct (addr_eight mm (f + 32) 8 (f + 32) (addr_win2 mm (f + 32) 8 OK A321 MU) ltac:(lia) ltac:(lia))
      as (k32 & MK32 & SK32)).
  pose proof (rng_shadow_one RNG (f + 32) 8 (f + 32) (R32s OK) ltac:(lia)) as RG32s. unfold ASAN_K in RG32s.
  step.
  step. shr_norm (f + 32).
  step.
  shadow8 MK32 SK32.
  (* 0x82c44: the shadow byte of ap + 24 *)
  pose proof (rng_shadow_one RNG ap 40 (ap + 24) (RAPs OK) ltac:(lia)) as RGs24. unfold ASAN_K in RGs24.
  curmemF ltac:(fun mm =>
    destruct (addr_eight mm ap 40 (ap + 24) (addr_win2 mm ap 40 OK AAP1 MU) ltac:(lia) ltac:(lia))
      as (k24 & MK24 & SK24)).
  step.
  step. shr_norm (ap + 24).
  step.
  shadow8 MK24 SK24.
  (* 0x82c58: the body field, the store of unknown, the shadow byte of ap + 32 *)
  pose proof (rng_shadow_one RNG ap 40 (ap + 32) (RAPs OK) ltac:(lia)) as RGs32. unfold ASAN_K in RGs32.
  step. step.
  step. shr_norm (ap + 32).
  step.
  step.
  curmemF ltac:(fun mm =>
    destruct (addr_eight mm ap 40 (ap + 32) (addr_win2 mm ap 40 OK AAP1 MU) ltac:(lia) ltac:(lia))
      as (k32b & MK32b & SK32b)).
  shadow8 MK32b SK32b.
  (* 0x82c74: the store of unknown_len, then the loop of the version from 0 *)
  step. step. step.
  eapply (LOOP1 _ 8%nat 0%nat); [exact OK | exact Laj | lia | intros j Hj; lia |].
  unfold INVa. cbn [firstn skipn app].
  refine (conj _ (conj MU (conj WM (conj BW (conj RF (conj STc FR)))))).
  exact CA.
Qed.

End ANN.

Theorem diginet_announce_parse_holds_F : diginet_announce_parse_contract_F.
Proof.
  unfold diginet_announce_parse_contract_F, DIGINET_ANNOUNCE_PARSE, DIGINET_ANNOUNCE_PARSE_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m bb aj f ap cmd body lo E0 E1 Hf Hap Hcmd Hbody BC BF BB ST0 SPLO DF30 DB15 HOK APS1 APS2 CELLS0
    DGOT A30 A40 A32 AB AAP RGW RGC RCK R30 R30s R40 R40s R32 R32s RB RBs RAP RAPs.
  subst a0 a1.
  apply (ENTRY ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m bb aj f ap cmd body lo RNG); assumption.
Qed.
