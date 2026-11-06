(* reac-pw/fuzz_link, PLAIN build: memory facts the walks of __fseeko_unlocked and rewind share.
   - a field of link's memory FILE (lib/MemFile.v `val_mem` at f + off) read as bytes for the walk
     tactics, and back; two readings of one field agree;
   - a field, a byte run, `memfile_at` and the stack protector's words kept across a write set
     (Frame.v `munch`) that misses them;
   - `memfile_at` built again after the stores of the path: the bytes outside the words the path
     changes are as they were, and each changed word is in its range. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem memfile_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YH02 YI04 YI14 YO0f YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Spec Require StrFun.
Local Open Scope Z_scope.

Lemma mbyte_mrd : forall m z, YP09.mbyte rsegs m z = mrd rsegs m (wa z).
Proof. reflexivity. Qed.

Lemma nth_Z_to_le_bytes : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|].
  destruct k as [|k]; cbn [Z_to_le_bytes nth_error].
  - change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
  - rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. f_equal. lia.
Qed.

Lemma le8_bytes : forall bs, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs Hl. unfold le8, word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 ?x) with (x mod 2^64).
  rewrite Z_to_le_bytes_mod by (cbn; lia). rewrite <- Hl. apply StrFun.Z_to_le_bytes_to_Z.
Qed.

(* ---------- a field as bytes, and back ---------- *)

Lemma bytes_of_val8 : forall m a v, YI04.val_mem rsegs m a 8 v -> 0 <= a -> a + 8 <= 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  bytes_at rsegs m a (le8 (Z_to_bv 64 v)).
Proof.
  intros m a v H Ha Hb Hv. split; [lia|]. split; [rewrite length_le8; lia|].
  intros i Hi. rewrite length_le8 in Hi.
  rewrite <- mbyte_mrd, (H i Hi). rewrite <- store_bytes_8'. rewrite unsigned_lit by lia.
  rewrite nth_Z_to_le_bytes by exact Hi. f_equal.
  apply YI04.le_byte_small; [change (8 * Z.of_nat 8) with 64; lia | exact Hi].
Qed.

Lemma val_of_bytes8 : forall m a w, bytes_at rsegs m a (le8 w) -> YI04.val_mem rsegs m a 8 (bv_unsigned w).
Proof.
  intros m a w (Ha & Hb & H) k Hk. rewrite mbyte_mrd, (H k ltac:(rewrite length_le8; exact Hk)).
  rewrite <- store_bytes_8', nth_Z_to_le_bytes by exact Hk. f_equal. symmetry.
  pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2 ^ 64) in R.
  apply YI04.le_byte_small; [change (8 * Z.of_nat 8) with 64; lia | exact Hk].
Qed.

Lemma bytes_of_val4 : forall m a v, YI04.val_mem rsegs m a 4 v -> 0 <= a -> a + 4 <= 2 ^ 64 -> 0 <= v < 2 ^ 32 ->
  bytes_at rsegs m a (le4 (Z_to_bv 64 v)).
Proof.
  intros m a v H Ha Hb Hv. split; [lia|]. split; [rewrite length_le4; lia|].
  intros i Hi. rewrite length_le4 in Hi.
  rewrite <- mbyte_mrd, (H i Hi). unfold le4. rewrite unsigned_lit by lia.
  rewrite nth_Z_to_le_bytes by exact Hi. f_equal.
  apply YI04.le_byte_small; [change (8 * Z.of_nat 4) with 32; lia | exact Hi].
Qed.

Lemma val_of_bytes4 : forall m a w, bytes_at rsegs m a (le4 w) -> bv_unsigned w < 2 ^ 32 ->
  YI04.val_mem rsegs m a 4 (bv_unsigned w).
Proof.
  intros m a w (Ha & Hb & H) Hw k Hk. rewrite mbyte_mrd, (H k ltac:(rewrite length_le4; exact Hk)).
  unfold le4. rewrite nth_Z_to_le_bytes by exact Hk. f_equal. symmetry.
  pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2 ^ 64) in R.
  apply YI04.le_byte_small; [change (8 * Z.of_nat 4) with 32; lia | exact Hk].
Qed.

Lemma bytes_at_det : forall m a bs1 bs2, bytes_at rsegs m a bs1 -> bytes_at rsegs m a bs2 ->
  length bs1 = length bs2 -> bs1 = bs2.
Proof.
  intros m a bs1 bs2 (_ & _ & H1) (_ & _ & H2) HL. apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length bs1)) as [Hi | Hi].
  - rewrite <- (H1 i Hi), <- (H2 i ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None bs1 i) Hi), (proj2 (nth_error_None bs2 i) ltac:(lia)). reflexivity.
Qed.

Lemma val8_inj : forall m a v1 v2, YI04.val_mem rsegs m a 8 v1 -> YI04.val_mem rsegs m a 8 v2 ->
  0 <= a -> a + 8 <= 2 ^ 64 -> 0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 -> v1 = v2.
Proof.
  intros m a v1 v2 H1 H2 Ha Hb R1 R2.
  pose proof (bytes_at_det m a _ _ (bytes_of_val8 m a v1 H1 Ha Hb R1) (bytes_of_val8 m a v2 H2 Ha Hb R2)
                (eq_trans (length_le8 _) (eq_sym (length_le8 _)))) as E.
  apply (f_equal le_bytes_to_word) in E. rewrite !le_bytes_to_word_le8 in E.
  apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. exact E.
Qed.

Lemma val4_inj : forall m a v1 v2, YI04.val_mem rsegs m a 4 v1 -> YI04.val_mem rsegs m a 4 v2 ->
  0 <= a -> a + 4 <= 2 ^ 64 -> 0 <= v1 < 2 ^ 32 -> 0 <= v2 < 2 ^ 32 -> v1 = v2.
Proof.
  intros m a v1 v2 H1 H2 Ha Hb R1 R2.
  pose proof (bytes_at_det m a _ _ (bytes_of_val4 m a v1 H1 Ha Hb R1) (bytes_of_val4 m a v2 H2 Ha Hb R2)
                (eq_trans (length_le4 _) (eq_sym (length_le4 _)))) as E.
  apply (f_equal le_bytes_to_word) in E. apply (f_equal bv_unsigned) in E.
  rewrite !le_bytes_to_word_le4 in E. rewrite !unsigned_lit in E by lia.
  rewrite !Z.mod_small in E by lia. exact E.
Qed.

(* ---------- kept across a write set that misses them ---------- *)

Lemma munch_mbyte : forall W m m' z, munch W m m' -> 0 <= z < 2 ^ 64 -> outside W z ->
  YP09.mbyte rsegs m' z = YP09.mbyte rsegs m z.
Proof.
  intros W m m' z MU Hz Ho. unfold YP09.mbyte. rewrite (MU (Z_to_bv 64 z)); [reflexivity|].
  rewrite unsigned_lit by lia. exact Ho.
Qed.

Lemma val_munch : forall W m m' a n v, YI04.val_mem rsegs m a n v -> munch W m m' ->
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (forall z, a <= z < a + Z.of_nat n -> outside W z) ->
  YI04.val_mem rsegs m' a n v.
Proof.
  intros W m m' a n v H MU H0 H1 HO k Hk.
  rewrite (munch_mbyte W m m' (a + Z.of_nat k) MU ltac:(lia) (HO (a + Z.of_nat k) ltac:(lia))). exact (H k Hk).
Qed.

Lemma bytes_munch : forall W m m' a bs, bytes_at rsegs m a bs -> munch W m m' ->
  (forall z, a <= z < a + Z.of_nat (length bs) -> outside W z) -> bytes_at rsegs m' a bs.
Proof.
  intros W m m' a bs (H0 & H1 & H) MU HO. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (H i Hi). unfold mrd. rewrite (MU (wa (a + Z.of_nat i))); [reflexivity|].
  rewrite wa_unsigned by lia. apply HO. lia.
Qed.

Lemma memfile_at_munch : forall W m m' f,
  MemFile.memfile_at YH02.src0_msyms MemFile.link_mf m f -> munch W m m' ->
  (forall z, f <= z < f + MemFile.MF_ZEROED -> outside W z) ->
  MemFile.memfile_at YH02.src0_msyms MemFile.link_mf m' f.
Proof.
  intros W m m' f H MU HO. eapply MemFile.memfile_at_frame; [|exact H].
  intros x Hx. destruct H as (H0 & H1 & _).
  exact (munch_mbyte W m m' x MU ltac:(unfold MemFile.MF_ZEROED, MemFile.MF_BLOCK in *; lia) (HO x Hx)).
Qed.

(* GUARD (0x95878) is .bss: the image gives a byte at each of its 8 addresses, so some word is there in
   every memory; the GOT slot GOT_GUARD (0x208d8) is writable in the image, so it is kept only by a write
   set that misses it *)
Lemma guard_rom_ok :
  forallb (fun i => match seg_rom rsegs (wa (GUARD + Z.of_nat i)) with Some _ => true | None => false end)
          (seq 0 8) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma guard_any : forall m, exists g : word, bytes_at rsegs m GUARD (le8 g).
Proof.
  intros m.
  set (bs := map (fun i => match mrd rsegs m (wa (GUARD + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end)
                 (seq 0 8)).
  assert (HL : length bs = 8%nat) by (unfold bs; rewrite length_map, length_seq; reflexivity).
  exists (le_bytes_to_word bs). rewrite le8_bytes by exact HL.
  split; [unfold GUARD; lia|]. split; [rewrite HL; unfold GUARD; lia|].
  intros i Hi. rewrite HL in Hi. unfold bs. rewrite nth_error_map.
  replace (nth_error (seq 0 8) i) with (Some i)
    by (symmetry; rewrite nth_error_seq; destruct (Nat.ltb_spec i 8); [reflexivity | lia]).
  cbn [option_map].
  pose proof guard_rom_ok as G. rewrite forallb_forall in G. specialize (G i ltac:(apply in_seq; lia)).
  unfold mrd. destruct (m (wa (GUARD + Z.of_nat i))) as [b|]; [reflexivity|].
  destruct (seg_rom rsegs (wa (GUARD + Z.of_nat i))) as [b|]; [reflexivity | discriminate G].
Qed.

Lemma guard_keep : forall W m m', guard_words m -> munch W m m' ->
  (forall z, GOT_GUARD <= z < GOT_GUARD + 8 -> outside W z) -> guard_words m'.
Proof.
  intros W m m' (HG & _) MU HO. split; [|exact (guard_any m')].
  apply (bytes_munch W m m' GOT_GUARD _ HG MU). rewrite length_le8. exact HO.
Qed.

(* ---------- the FILE kept across a write set that misses its block ---------- *)

Ltac fld_munch MU HO :=
  eapply val_munch;
  [ eassumption | exact MU | unfold MemFile.MF_COOKIE in *; lia
  | cbn [Z.of_nat Pos.of_succ_nat Pos.succ];
    unfold MemFile.MF_COOKIE, MemFile.MF_BUF, MemFile.MF_BUFSIZ, MemFile.MF_BLOCK in *; lia
  | let z := fresh "z" in let Hz := fresh "Hz" in
    intros z Hz; apply HO; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hz;
    unfold MemFile.MF_COOKIE, MemFile.MF_BUF, MemFile.MF_BUFSIZ, MemFile.MF_BLOCK in *; lia ].

Lemma mf_dyn_munch : forall W m m' f fl om wend wpos wbase pos len,
  mf_dyn m f fl om wend wpos wbase pos len -> munch W m m' -> 0 < f -> f + MemFile.MF_BLOCK <= 2 ^ 64 ->
  (forall z, f <= z < f + MemFile.MF_BLOCK -> outside W z) -> mf_dyn m' f fl om wend wpos wbase pos len.
Proof.
  intros W m m' f fl om wend wpos wbase pos len H MU H0 H1 HO. unfold mf_dyn, mf_fld in *.
  destruct H as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & D1 & D2 & D3 & D4 & D5 & D6 & D7).
  refine (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj R6 (conj R7 _))))))).
  repeat split; fld_munch MU HO.
Qed.

Lemma memfile_k_munch : forall W m m' f k, memfile_k m f k -> munch W m m' -> wmono rsegs m m' ->
  (forall z, f <= z < f + MemFile.MF_BLOCK -> outside W z) -> memfile_k m' f k.
Proof.
  intros W m m' f k (HA & HW & HB & HS & HP) MU WM HO.
  pose proof HA as (H0 & H1 & _).
  split; [apply (memfile_at_munch W m m' f HA MU); intros z Hz; apply HO;
          unfold MemFile.MF_ZEROED, MemFile.MF_BLOCK in *; lia|].
  split; [|split; [exact (wr_at_transport rsegs m m' _ _ HB WM)
                  |split; [exact (wr_at_transport rsegs m m' _ _ HS WM) | exact HP]]].
  unfold mf_win, mf_fld in *.
  destruct HW as [(Hk & W1 & W2 & W3) | (Hk & W1 & W2 & W3)]; [left | right];
    (split; [exact Hk|]); repeat split; fld_munch MU HO.
Qed.

Lemma pend_munch : forall W m m' f pb, mf_pend_bytes m f pb -> munch W m m' ->
  Z.of_nat (length pb) <= MemFile.MF_BUFSIZ ->
  (forall z, f <= z < f + MemFile.MF_BLOCK -> outside W z) -> mf_pend_bytes m' f pb.
Proof.
  intros W m m' f pb H MU HL HO. unfold mf_pend_bytes in *. apply (bytes_munch W m m' _ pb H MU).
  intros z Hz. apply HO. unfold MemFile.MF_BUF, MemFile.MF_BUFSIZ, MemFile.MF_BLOCK in *. lia.
Qed.

(* the fields of the FILE the two walks read *)
Lemma memfile_at_fields : forall m f, MemFile.memfile_at YH02.src0_msyms MemFile.link_mf m f ->
  0 < f /\ f + MemFile.MF_BLOCK <= 2 ^ 64 /\
  mf_fld m f 8 8 0 /\ mf_fld m f 16 8 0 /\ mf_fld m f 48 8 0 /\
  mf_fld m f 72 8 MWRITE /\ mf_fld m f 80 8 MSEEK /\ mf_fld m f 140 4 YI14.U32M1 /\
  mf_fld m f 152 8 (f + MemFile.MF_COOKIE) /\ mf_fld m f (MemFile.MF_COOKIE + 16) 8 SAID_SIZE /\
  (mf_fld m f 0 4 MemFile.F_NORD \/ mf_fld m f 0 4 (MemFile.F_NORD + MemFile.F_ERR)).
Proof.
  intros m f (H0 & H1 & _ & HS & HF & _ & HW & _). unfold MemFile.memfile_static in HS.
  destruct HS as (_ & S48 & _ & S72 & S80 & _ & _ & _ & _ & _ & _ & _ & S140 & _ & S152 &
                  _ & _ & _ & _ & _ & _ & _ & _ & _ & S248 & _ & _).
  destruct HW as (W8 & W16 & _).
  split; [exact H0|]. split; [exact H1|].
  split; [exact W8|]. split; [exact W16|]. split; [exact S48|]. split; [exact S72|]. split; [exact S80|].
  split; [exact S140|]. split; [exact S152|]. split; [exact S248|]. exact HF.
Qed.

(* building cells from consecutive fields *)
Lemma bytes_cons8 : forall m a w rest, bytes_at rsegs m a (le8 w) -> bytes_at rsegs m (a + 8) rest ->
  bytes_at rsegs m a (le8 w ++ rest).
Proof.
  intros m a w rest H1 H2. apply (proj2 (bytes_at_app rsegs m a (le8 w) rest)).
  split; [exact H1|]. rewrite length_le8. exact H2.
Qed.

Lemma rw_cells_intro : forall m A cs, cells_wf cs -> bytes_at rsegs m A (cells_bytes cs) ->
  wr_at rsegs m A (Z.of_nat (cells_size cs)) -> rw_cells rsegs m A cs.
Proof. intros m A cs H1 H2 H3. split; [split; assumption | exact H3]. Qed.

Lemma wr_at_sub : forall m a n b k, wr_at rsegs m a n -> a <= b -> 0 <= k -> b + k <= a + n -> wr_at rsegs m b k.
Proof.
  intros m a n b k (H0 & H1 & H) Hb Hk Hbk. split; [lia|]. split; [lia|]. intros i Hi.
  replace (b + i) with (a + (b - a + i)) by lia. apply H. lia.
Qed.

Lemma rw_cells_bytes : forall m A cs, rw_cells rsegs m A cs -> bytes_at rsegs m A (cells_bytes cs).
Proof. intros m A cs [[_ H] _]. exact H. Qed.

Lemma val_mod8 : forall m a v, YI04.val_mem rsegs m a 8 v -> YI04.val_mem rsegs m a 8 (v mod 2 ^ 64).
Proof.
  intros m a v H k Hk. rewrite (H k Hk). f_equal. f_equal. unfold YO0f.le_byte.
  change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* the window as the walks read it: wpos = wbase exactly when nothing is pending, and an active window
   starts at the buffer *)
Lemma win_facts : forall m f k fl om wend wpos wbase pos len,
  memfile_k m f k -> mf_dyn m f fl om wend wpos wbase pos len ->
  (wpos = wbase <-> k = 0) /\ (k = 0 \/ wbase = f + MemFile.MF_BUF) /\ 0 <= k <= MemFile.MF_BUFSIZ.
Proof.
  intros m f k fl om wend wpos wbase pos len (HA & HW & _) HD.
  destruct HA as (H0 & H1 & _).
  destruct HD as (_ & _ & _ & R4 & R5 & _ & _ & _ & _ & _ & D4 & D5 & _).
  unfold mf_win, mf_fld in *. unfold MemFile.MF_BUF, MemFile.MF_BUFSIZ, MemFile.MF_BLOCK in *.
  destruct HW as [(-> & _ & W2 & W3) | (Hk & _ & W2 & W3)].
  - pose proof (val8_inj m _ _ _ D4 W2 ltac:(lia) ltac:(lia) R4 ltac:(lia)) as E4.
    pose proof (val8_inj m _ _ _ D5 W3 ltac:(lia) ltac:(lia) R5 ltac:(lia)) as E5.
    subst wpos wbase. split; [split; intros; reflexivity|]. lia.
  - pose proof (val8_inj m _ _ _ D5 W3 ltac:(lia) ltac:(lia) R5 ltac:(lia)) as E5.
    apply val_mod8 in W2.
    pose proof (val8_inj m _ _ _ D4 W2 ltac:(lia) ltac:(lia) R4 (Z.mod_pos_bound (f + 280 + k) (2 ^ 64) ltac:(lia)))
      as E4.
    subst wpos wbase.
    destruct (Z.lt_ge_cases (f + 280 + k) (2 ^ 64)) as [Hl | Hl].
    + rewrite Z.mod_small by lia. split; [split; intros; lia|]. lia.
    + replace (f + 280 + k) with (2 ^ 64) by lia. rewrite Z.mod_same by lia. split; [split; intros; lia|]. lia.
Qed.

(* ---------- the fields the walks load and store, as cells ---------- *)

Lemma cells_win : forall m f k fl om wend wpos wbase pos len,
  memfile_k m f k -> mf_dyn m f fl om wend wpos wbase pos len ->
  rw_cells rsegs m (f + 32) [C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase)].
Proof.
  intros m f k fl om wend wpos wbase pos len HK HD.
  pose proof (memfile_at_fields _ _ (memfile_k_at _ _ _ HK)) as (F0 & F1 & _ & _ & S48 & _).
  destruct HD as (_ & _ & Rwend & Rwpos & Rwbase & _ & _ & _ & _ & Dwend & Dwpos & Dwbase & _).
  destruct HK as (_ & _ & HB & _).
  unfold mf_fld, MemFile.MF_BLOCK in *.
  apply rw_cells_intro; [cbn; tauto | | ].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r.
    apply bytes_cons8; [apply bytes_of_val8; [exact Dwend | lia | lia | lia]|].
    replace (f + 32 + 8) with (f + 40) by lia.
    apply bytes_cons8; [apply bytes_of_val8; [exact Dwpos | lia | lia | lia]|].
    replace (f + 40 + 8) with (f + 48) by lia.
    apply bytes_cons8; [apply bytes_of_val8; [exact S48 | lia | lia | lia]|].
    replace (f + 48 + 8) with (f + 56) by lia.
    apply bytes_of_val8; [exact Dwbase | lia | lia | lia].
  - cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
    apply (wr_at_sub m f 1304); [exact HB | lia | lia | lia].
Qed.

Lemma cells_ptrs : forall m f k, memfile_k m f k ->
  rw_cells rsegs m (f + 72) [C8 (Z_to_bv 64 103748); C8 (Z_to_bv 64 104024)].
Proof.
  intros m f k HK.
  pose proof (memfile_at_fields _ _ (memfile_k_at _ _ _ HK)) as (F0 & F1 & _ & _ & _ & S72 & S80 & _).
  destruct HK as (_ & _ & HB & _).
  unfold mf_fld, MWRITE, MSEEK, MemFile.MF_BLOCK in *.
  apply rw_cells_intro; [cbn; tauto | | ].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r.
    apply bytes_cons8; [apply bytes_of_val8; [exact S72 | lia | lia | lia]|].
    replace (f + 72 + 8) with (f + 80) by lia.
    apply bytes_of_val8; [exact S80 | lia | lia | lia].
  - cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
    apply (wr_at_sub m f 1304); [exact HB | lia | lia | lia].
Qed.

Lemma cells_seek : forall m f k, memfile_k m f k -> rw_cells rsegs m (f + 80) [C8 (Z_to_bv 64 104024)].
Proof.
  intros m f k HK.
  pose proof (memfile_at_fields _ _ (memfile_k_at _ _ _ HK)) as (F0 & F1 & _ & _ & _ & _ & S80 & _).
  destruct HK as (_ & _ & HB & _).
  unfold mf_fld, MSEEK, MemFile.MF_BLOCK in *.
  apply rw_cells_intro; [cbn; tauto | | ].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_of_val8; [exact S80 | lia | lia | lia].
  - cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
    apply (wr_at_sub m f 1304); [exact HB | lia | lia | lia].
Qed.

Lemma cells_rd : forall m f k, memfile_k m f k -> rw_cells rsegs m (f + 8) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof.
  intros m f k HK.
  pose proof (memfile_at_fields _ _ (memfile_k_at _ _ _ HK)) as (F0 & F1 & S8 & S16 & _).
  destruct HK as (_ & _ & HB & _).
  unfold mf_fld, MemFile.MF_BLOCK in *.
  apply rw_cells_intro; [cbn; tauto | | ].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r.
    apply bytes_cons8; [apply bytes_of_val8; [exact S8 | lia | lia | lia]|].
    replace (f + 8 + 8) with (f + 16) by lia.
    apply bytes_of_val8; [exact S16 | lia | lia | lia].
  - cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
    apply (wr_at_sub m f 1304); [exact HB | lia | lia | lia].
Qed.

Lemma cells_flags : forall m f k fl om wend wpos wbase pos len,
  memfile_k m f k -> mf_dyn m f fl om wend wpos wbase pos len -> rw_cells rsegs m f [C4 (Z_to_bv 64 fl)].
Proof.
  intros m f k fl om wend wpos wbase pos len HK HD.
  pose proof (memfile_at_fields _ _ (memfile_k_at _ _ _ HK)) as (F0 & F1 & _).
  destruct HD as (Rfl & _ & _ & _ & _ & _ & _ & Dfl & _).
  destruct HK as (_ & _ & HB & _).
  unfold mf_fld, MemFile.MF_BLOCK in *.
  pose proof (bytes_of_val4 m (f + 0) fl Dfl ltac:(lia) ltac:(lia) Rfl) as B. rewrite Z.add_0_r in B.
  apply rw_cells_intro; [cbn; tauto | | ].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
    apply (wr_at_sub m f 1304); [exact HB | lia | lia | lia].
Qed.

Lemma cells_lock : forall m f k, memfile_k m f k -> rw_cells rsegs m (f + 140) [C4 (Z_to_bv 64 YI14.U32M1)].
Proof.
  intros m f k HK.
  pose proof (memfile_at_fields _ _ (memfile_k_at _ _ _ HK)) as (F0 & F1 & _ & _ & _ & _ & _ & S140 & _).
  destruct HK as (_ & _ & HB & _).
  unfold mf_fld, MemFile.MF_BLOCK in *.
  pose proof (bytes_of_val4 m (f + 140) YI14.U32M1 S140 ltac:(lia) ltac:(lia) ltac:(unfold YI14.U32M1; lia)) as B.
  apply rw_cells_intro; [cbn; tauto | | ].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
    apply (wr_at_sub m f 1304); [exact HB | lia | lia | lia].
Qed.

(* the flags as the code leaves them: F_NORD, with F_ERR or not *)
Lemma flags_val : forall m f k fl om wend wpos wbase pos len,
  memfile_k m f k -> mf_dyn m f fl om wend wpos wbase pos len -> fl = 4 \/ fl = 36.
Proof.
  intros m f k fl om wend wpos wbase pos len HK HD.
  pose proof (memfile_at_fields _ _ (memfile_k_at _ _ _ HK)) as (F0 & F1 & _ & _ & _ & _ & _ & _ & _ & _ & SF).
  destruct HD as (Rfl & _ & _ & _ & _ & _ & _ & Dfl & _).
  unfold mf_fld, MemFile.MF_BLOCK, MemFile.F_NORD, MemFile.F_ERR in *.
  destruct SF as [SF | SF]; [left | right];
    exact (val4_inj m (f + 0) fl _ Dfl SF ltac:(lia) ltac:(lia) Rfl ltac:(lia)).
Qed.

(* reading the fields back out of cells after the stores *)
Lemma val_of_cell8 : forall m a w rest, bytes_at rsegs m a (le8 w ++ rest) ->
  YI04.val_mem rsegs m a 8 (bv_unsigned w) /\ bytes_at rsegs m (a + 8) rest.
Proof.
  intros m a w rest H. apply (proj1 (bytes_at_app rsegs m a (le8 w) rest)) in H. destruct H as [H1 H2].
  rewrite length_le8 in H2. split; [exact (val_of_bytes8 _ _ _ H1) | exact H2].
Qed.

Lemma val_of_cell4 : forall m a v, rw_cells rsegs m a [C4 (Z_to_bv 64 v)] -> 0 <= v < 2 ^ 32 ->
  YI04.val_mem rsegs m a 4 v.
Proof.
  intros m a v H Hv. pose proof (rw_cells_bytes _ _ _ H) as B. cbn [cells_bytes cbytes] in B.
  rewrite app_nil_r in B. pose proof (val_of_bytes4 _ _ _ B) as V. rewrite unsigned_lit in V by lia.
  apply V. lia.
Qed.

Lemma val_of_cells_z2 : forall m a, rw_cells rsegs m a [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  YI04.val_mem rsegs m a 8 0 /\ YI04.val_mem rsegs m (a + 8) 8 0.
Proof.
  intros m a H. pose proof (rw_cells_bytes _ _ _ H) as B. cbn [cells_bytes cbytes] in B.
  apply val_of_cell8 in B as [V0 B]. rewrite app_nil_r in B. apply val_of_bytes8 in B.
  change (bv_unsigned (Z_to_bv 64 0)) with 0 in *. split; assumption.
Qed.

Lemma val_of_cells_z4 : forall m a,
  rw_cells rsegs m a [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  YI04.val_mem rsegs m a 8 0 /\ YI04.val_mem rsegs m (a + 8) 8 0 /\
  YI04.val_mem rsegs m (a + 16) 8 0 /\ YI04.val_mem rsegs m (a + 24) 8 0.
Proof.
  intros m a H. pose proof (rw_cells_bytes _ _ _ H) as B. cbn [cells_bytes cbytes] in B.
  apply val_of_cell8 in B as [V0 B]. apply val_of_cell8 in B as [V1 B]. apply val_of_cell8 in B as [V2 B].
  rewrite app_nil_r in B. apply val_of_bytes8 in B.
  change (bv_unsigned (Z_to_bv 64 0)) with 0 in *.
  replace (a + 8 + 8) with (a + 16) in V2 by lia. replace (a + 8 + 8 + 8) with (a + 24) in B by lia.
  split; [exact V0|]. split; [exact V1|]. split; [exact V2 | exact B].
Qed.

(* ---------- memfile_at built again after the path's stores ---------- *)

(* the bytes of the FILE header the path changes: flags, rpos, rend, wend, wpos, wbase, the orientation,
   and the cookie's pos and len *)
Definition in_dyn (f z : Z) : Prop :=
  (f <= z < f + 4) \/ (f + 8 <= z < f + 24) \/ (f + 32 <= z < f + 48) \/ (f + 56 <= z < f + 64) \/
  (f + 136 <= z < f + 140) \/ (f + 232 <= z < f + 248).

Lemma memfile_static_keep : forall m m' f,
  (forall z, f <= z < f + MemFile.MF_ZEROED -> ~ in_dyn f z -> YP09.mbyte rsegs m' z = YP09.mbyte rsegs m z) ->
  MemFile.memfile_static YH02.src0_msyms MemFile.link_mf m f ->
  MemFile.memfile_static YH02.src0_msyms MemFile.link_mf m' f.
Proof.
  intros m m' f HK HS. unfold MemFile.memfile_static in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat split;
    (eapply YI14.val_mem_frame; [|eassumption]);
    intros x Hx; apply HK;
    cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; unfold in_dyn, MemFile.MF_COOKIE, MemFile.MF_ZEROED in *; lia.
Qed.

Lemma memfile_at_rebuild : forall m m' f,
  MemFile.memfile_at YH02.src0_msyms MemFile.link_mf m f ->
  (forall z, f <= z < f + MemFile.MF_ZEROED -> ~ in_dyn f z -> YP09.mbyte rsegs m' z = YP09.mbyte rsegs m z) ->
  MemFile.memfile_flags YH02.src0_msyms m' f -> MemFile.memfile_omode YH02.src0_msyms m' f ->
  MemFile.memfile_window YH02.src0_msyms m' f -> MemFile.memfile_cookie YH02.src0_msyms MemFile.link_mf m' f ->
  MemFile.memfile_at YH02.src0_msyms MemFile.link_mf m' f.
Proof.
  intros m m' f (H0 & H1 & H2 & HS & _) HK Hfl Hom Hw Hc.
  split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  split; [exact (memfile_static_keep m m' f HK HS)|]. tauto.
Qed.

(* memfile_at after a store to the flags alone: every other byte of the header is as it was *)
Lemma memfile_at_reflag : forall W m m' f,
  MemFile.memfile_at YH02.src0_msyms MemFile.link_mf m f -> munch W m m' ->
  (forall z, f + 4 <= z < f + MemFile.MF_ZEROED -> outside W z) ->
  MemFile.memfile_flags YH02.src0_msyms m' f ->
  MemFile.memfile_at YH02.src0_msyms MemFile.link_mf m' f.
Proof.
  intros W m m' f HA MU HO HF. pose proof HA as (H0 & H1 & _ & _ & _ & HOM & HW & HC).
  assert (K : forall a n v, f + 4 <= a -> a + Z.of_nat n <= f + MemFile.MF_ZEROED ->
                YI04.val_mem rsegs m a n v -> YI04.val_mem rsegs m' a n v).
  { intros a n v Ha Hn H. apply (val_munch W m m' a n v H MU); [lia | unfold MemFile.MF_ZEROED, MemFile.MF_BLOCK in *; lia |].
    intros z Hz. apply HO. lia. }
  apply (memfile_at_rebuild m m' f HA).
  - intros z Hz Hd. apply (munch_mbyte W m m' z MU); [unfold MemFile.MF_ZEROED, MemFile.MF_BLOCK in *; lia|].
    apply HO. unfold in_dyn in Hd. lia.
  - exact HF.
  - unfold MemFile.memfile_omode in *.
    destruct HOM as [HOM | HOM]; [left | right]; apply K; try exact HOM; cbn [Z.of_nat Pos.of_succ_nat Pos.succ];
      unfold MemFile.MF_ZEROED; lia.
  - unfold MemFile.memfile_window in *. destruct HW as (W8 & W16 & HW).
    split; [apply K; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold MemFile.MF_ZEROED; lia | exact W8]|].
    split; [apply K; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold MemFile.MF_ZEROED; lia | exact W16]|].
    destruct HW as [(W1 & W2 & W3) | (kk & Hk & W1 & W2 & W3)]; [left | right; exists kk; split; [exact Hk|]];
      (split; [apply K; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold MemFile.MF_ZEROED; lia | exact W1]|]);
      (split; [apply K; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold MemFile.MF_ZEROED; lia | exact W2]|]);
      (apply K; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold MemFile.MF_ZEROED; lia | exact W3]).
  - unfold MemFile.memfile_cookie in *. destruct HC as (p & l & Hp & Hl & C1 & C2). exists p, l.
    split; [exact Hp|]. split; [exact Hl|].
    split; (apply K; [unfold MemFile.MF_COOKIE; lia
                     | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold MemFile.MF_COOKIE, MemFile.MF_ZEROED; lia
                     | assumption]).
Qed.
