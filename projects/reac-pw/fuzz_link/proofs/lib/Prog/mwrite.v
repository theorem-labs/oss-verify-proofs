(* mwrite (musl src/stdio/fmemopen.c), PLAIN build: the walk of its contract (lib/Prog/mwrite_c.v) on
   link's plain image, 0x19544 (276 bytes, 69 instructions; link/pf/dis/plain/mwrite.s). Each step decodes
   the instruction at its pc from the image the proofs load (lib/Lib/Step.v `step`).

   The walk works on cells of the FILE block (flags at f, wend / wpos at f + 32, wbase at f + 56, the
   cookie pointer at f + 152, the cookie's pos / len / size / buf / mode at f + 232), on g_said, errno and
   the frame:
   - mw_t2 (+0xb0 .. ret): memcpy of the bytes that fit, pos / len, the NUL after len, the epilogue;
   - mw_tail (+0x5c .. ret): the mode test, size - pos, and on a store past g_said's end errno = ENOSPC,
     F_ERR and the empty window (+0x84 .. +0xac), then mw_t2;
   - mw_k0 (entry, k = 0 pending bytes, one frame of 48): the prologue, wpos = wbase, mw_tail;
   - mw_gen (entry, any k, frame 96): k = 0 is mw_k0; else wpos = wbase (+0x3c), the inner call
     mwrite(f, wbase, k) (+0x4c) through mw_k0 at sp - 48, then return 0 (+0x54) or mw_tail;
   - mwrite_proof: mwrite_contract, from mw_gen through mk_leaf's leaf_intro, reading the cells from
     memfile_k / mf_dyn and giving memfile_at back (memfile_at_upd: only the dynamic words changed);
   - mwrite_flush: the instance buf = 0, len = 0 that __fseeko_unlocked (+0x70) and close_file make. *)
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem memfile_c mwrite_c mk_leaf memcpy_c __errno_location_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require memcpy __errno_location.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YK1j YO0f YI04 YP09 YH02.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Memory views: writable bytes, little-endian values, val_mem
   ========================================================================== *)

(* every segment of link's plain image is readable, so a writable address has a byte *)
Lemma rsegs_readable : forallb (fun s => seg_readable s) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma wv_mrd : forall m x, wview rsegs m x <> None -> exists b, mrd rsegs m x = Some b.
Proof.
  intros m x H. unfold wview in H. unfold mrd, PropExec.seg_rom, memory_read.
  destruct (m x) as [b|]; [exists b; reflexivity|].
  change (Z.of_N 1) with 1.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [sg|] eqn:E; [|congruence].
  pose proof (YK1j.find_segment_in _ _ _ _ E) as I.
  pose proof rsegs_readable as R. rewrite forallb_forall in R. rewrite (R sg I).
  destruct (seg_writable sg); [|congruence].
  cbv zeta. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
  destruct (segment_byte_at (seg_bytes sg) (Z.to_N (bv_unsigned x - Z.of_N (seg_base sg)))) as [b|];
    [exists b; reflexivity | congruence].
Qed.

Lemma wr_at_bytes : forall m a n, wr_at rsegs m a n -> 0 <= n ->
  exists bs, length bs = Z.to_nat n /\ bytes_at rsegs m a bs.
Proof.
  intros m a n (H1 & H2 & H) Hn.
  assert (G : forall k, (k <= Z.to_nat n)%nat -> exists bs, length bs = k /\
            forall i, (i < k)%nat -> mrd rsegs m (wa (a + Z.of_nat i)) = nth_error bs i).
  { induction k as [|k IH]; intros Hk.
    - exists []. split; [reflexivity|]. intros i Hi; lia.
    - destruct (IH ltac:(lia)) as (bs & Hlen & Hbs).
      destruct (wv_mrd m (wa (a + Z.of_nat k)) (H (Z.of_nat k) ltac:(lia))) as (b & Hb).
      exists (bs ++ [b]). split. { rewrite length_app; cbn; lia. }
      intros i Hi. destruct (Nat.eqb_spec i k).
      + subst i. rewrite nth_error_app2 by lia. rewrite Hlen, Nat.sub_diag. exact Hb.
      + rewrite nth_error_app1 by lia. apply Hbs. lia. }
  destruct (G (Z.to_nat n) ltac:(lia)) as (bs & Hlen & Hbs). exists bs. split; [exact Hlen|].
  split; [lia|]. split; [lia|]. intros i Hi. apply Hbs. lia.
Qed.

Lemma wr_at_cells : forall m a n i j, wr_at rsegs m a n -> 0 <= i -> 0 <= j -> i + j <= n ->
  exists junk, rw_cells rsegs m (a + i) [CB (Z.to_nat j) junk].
Proof.
  intros m a n i j (H0 & H1 & H) Hi Hj Hij.
  assert (W : wr_at rsegs m (a + i) j).
  { split; [lia|]. split; [lia|]. intros t Ht. replace (a + i + t) with (a + (i + t)) by lia. apply H. lia. }
  destruct (wr_at_bytes m (a + i) j W Hj) as (bs & Hl & Hb).
  exists bs. split.
  - split. { cbn. split; [exact Hl | exact I]. } cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact W.
Qed.

Lemma wr_at_sub : forall m a n i j, wr_at rsegs m a n -> 0 <= i -> 0 <= j -> i + j <= n -> wr_at rsegs m (a + i) j.
Proof.
  intros m a n i j (H0 & H1 & H) Hi Hj Hij. split; [lia|]. split; [lia|].
  intros t Ht. replace (a + i + t) with (a + (i + t)) by lia. apply H. lia.
Qed.

Lemma le_nth : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|]. destruct k as [|k]; cbn [Z_to_le_bytes nth_error].
  - replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r. reflexivity.
  - rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. do 3 f_equal. lia.
Qed.

Lemma le_byte_shiftr : forall z n k, (k < n)%nat ->
  Z_to_bv 8 (YO0f.le_byte z n k) = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
  intros z n k Hk. unfold YO0f.le_byte. apply Z_to_bv8_mod.
  change 256 with (2 ^ 8). rewrite Z.mod_mod by lia.
  apply shiftr_mod_mod8; lia.
Qed.

Lemma vm_bytes : forall m a n v, YI04.val_mem rsegs m a n v -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  bytes_at rsegs m a (Z_to_le_bytes n v).
Proof.
  intros m a n v H H0 H1. split; [lia|]. rewrite length_Z_to_le_bytes. split; [lia|].
  intros i Hi. rewrite le_nth by lia. rewrite <- (le_byte_shiftr v n i) by lia. exact (H i Hi).
Qed.

Lemma bytes_vm : forall m a n v, bytes_at rsegs m a (Z_to_le_bytes n v) -> YI04.val_mem rsegs m a n v.
Proof.
  intros m a n v (H0 & H1 & H) k Hk. rewrite length_Z_to_le_bytes in H.
  change (YP09.mbyte rsegs m (a + Z.of_nat k)) with (mrd rsegs m (wa (a + Z.of_nat k))).
  rewrite (H k Hk), le_nth by lia. rewrite le_byte_shiftr by lia. reflexivity.
Qed.

Lemma le_byte_bit : forall v n i, 0 <= i < 8 * Z.of_nat n ->
  Z.testbit v i = Z.testbit (YO0f.le_byte v n (Z.to_nat (i / 8))) (i mod 8).
Proof.
  intros v n i Hi. unfold YO0f.le_byte.
  assert (H8 : 0 <= i mod 8 < 8) by (apply Z.mod_pos_bound; lia).
  assert (Hd : 0 <= i / 8) by (apply Z.div_pos; lia).
  pose proof (Z.div_mod i 8 ltac:(lia)) as DM.
  change 256 with (2 ^ 8). rewrite Z.mod_pow2_bits_low by lia.
  rewrite Z.shiftr_spec by lia. rewrite Z2Nat.id by lia.
  rewrite Z.mod_pow2_bits_low by lia.
  f_equal. lia.
Qed.

Lemma vm_inj : forall m a n v1 v2, YI04.val_mem rsegs m a n v1 -> YI04.val_mem rsegs m a n v2 ->
  0 <= v1 < 2 ^ (8 * Z.of_nat n) -> 0 <= v2 < 2 ^ (8 * Z.of_nat n) -> v1 = v2.
Proof.
  intros m a n v1 v2 H1 H2 R1 R2. apply Z.bits_inj'. intros i Hi.
  destruct (Z.lt_ge_cases i (8 * Z.of_nat n)) as [Hl|Hg].
  - rewrite (le_byte_bit v1 n i), (le_byte_bit v2 n i) by lia.
    assert (Hk : (Z.to_nat (i / 8) < n)%nat).
    { apply Nat2Z.inj_lt. rewrite Z2Nat.id by (apply Z.div_pos; lia). apply Z.div_lt_upper_bound; lia. }
    specialize (H1 _ Hk). specialize (H2 _ Hk).
    assert (E : bv_unsigned (Z_to_bv 8 (YO0f.le_byte v1 n (Z.to_nat (i / 8)))) =
                bv_unsigned (Z_to_bv 8 (YO0f.le_byte v2 n (Z.to_nat (i / 8))))) by congruence.
    rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
    change (bv_modulus 8) with 256 in E.
    assert (M : forall v, YO0f.le_byte v n (Z.to_nat (i / 8)) mod 256 = YO0f.le_byte v n (Z.to_nat (i / 8)))
      by (intros v; unfold YO0f.le_byte; apply Z.mod_mod; lia).
    rewrite !M in E. rewrite E. reflexivity.
  - rewrite <- (Z.mod_small v1 (2 ^ (8 * Z.of_nat n))) by lia.
    rewrite <- (Z.mod_small v2 (2 ^ (8 * Z.of_nat n))) by lia.
    rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* a one-cell rw_cells from the value's bytes and the writable range *)
Lemma rw1 : forall m a c, cell_wf c -> bytes_at rsegs m a (cbytes c) -> wr_at rsegs m a (Z.of_nat (csize c)) ->
  rw_cells rsegs m a [c].
Proof.
  intros m a c Hw Hb Hr. split; [split|].
  - cbn. split; [exact Hw | exact I].
  - cbn [cells_bytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size]. rewrite Nat.add_0_r. exact Hr.
Qed.

Lemma rw1_bytes : forall m a c, rw_cells rsegs m a [c] -> bytes_at rsegs m a (cbytes c).
Proof. intros m a c [[_ Hb] _]. cbn [cells_bytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

Lemma rw_cells_app2 : forall m a c cs, rw_cells rsegs m a [c] -> cell_wf c ->
  rw_cells rsegs m (a + Z.of_nat (csize c)) cs -> rw_cells rsegs m a (c :: cs).
Proof.
  intros m a c cs [[_ H1] (W0 & W1 & W)] Hc [[Hw2 H2] (V0 & V1 & V)]. cbn [cells_bytes] in H1. rewrite app_nil_r in H1.
  cbn [cells_size] in W1, W. rewrite Nat.add_0_r in W1, W.
  split; [split|].
  - cbn. split; assumption.
  - cbn [cells_bytes]. apply bytes_at_app. rewrite (cbytes_length c Hc). split; assumption.
  - cbn [cells_size]. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat (csize c))); [apply W; lia|].
    replace (a + i) with (a + Z.of_nat (csize c) + (i - Z.of_nat (csize c))) by lia. apply V. lia.
Qed.

Lemma vm_cell8 : forall m a v, YI04.val_mem rsegs m a 8 v -> 0 <= v < 2 ^ 64 -> wr_at rsegs m a 8 ->
  rw_cells rsegs m a [C8 (wz v)].
Proof.
  intros m a v H R W. pose proof W as (W0 & W1 & _). apply rw1; [exact I | | exact W].
  cbn [cbytes]. unfold le8, word_to_le_bytes, wz. rewrite unsigned_lit by lia. apply vm_bytes; [exact H | lia | lia].
Qed.

Lemma vm_cell4 : forall m a v, YI04.val_mem rsegs m a 4 v -> 0 <= v < 2 ^ 32 -> wr_at rsegs m a 4 ->
  rw_cells rsegs m a [C4 (wz v)].
Proof.
  intros m a v H R W. pose proof W as (W0 & W1 & _). apply rw1; [exact I | | exact W].
  cbn [cbytes]. unfold le4, wz. rewrite unsigned_lit by lia. apply vm_bytes; [exact H | lia | lia].
Qed.

Lemma cell8_vm : forall m a w, rw_cells rsegs m a [C8 w] -> YI04.val_mem rsegs m a 8 (bv_unsigned w).
Proof. intros m a w H. apply bytes_vm. exact (rw1_bytes m a (C8 w) H). Qed.

Lemma cell4_vm : forall m a w, rw_cells rsegs m a [C4 w] -> YI04.val_mem rsegs m a 4 (bv_unsigned w).
Proof. intros m a w H. apply bytes_vm. exact (rw1_bytes m a (C4 w) H). Qed.

(* munch at the level of mbyte *)
Lemma munch_mbyte : forall W m m' x, munch W m m' -> 0 <= x < 2 ^ 64 -> outside W x ->
  YP09.mbyte rsegs m' x = YP09.mbyte rsegs m x.
Proof.
  intros W m m' x H Hx Ho. unfold YP09.mbyte. rewrite H; [reflexivity|].
  rewrite unsigned_lit by lia. exact Ho.
Qed.

(* ==========================================================================
   2. The FILE after a call that writes only its dynamic words
   ========================================================================== *)

Definition dynw (f x : Z) : Prop :=
  f <= x < f + 4 \/ f + 32 <= x < f + 48 \/ f + 56 <= x < f + 64 \/ f + 232 <= x < f + 248.

Lemma memfile_at_upd : forall m m' f fl wend wpos wbase pos len,
  MemFile.memfile_at YH02.src0_msyms MemFile.link_mf m f ->
  (forall x, f <= x < f + MemFile.MF_ZEROED -> ~ dynw f x -> YP09.mbyte rsegs m' x = YP09.mbyte rsegs m x) ->
  YI04.val_mem rsegs m' (f + 0) 4 fl -> (fl = MemFile.F_NORD \/ fl = MemFile.F_NORD + MemFile.F_ERR) ->
  YI04.val_mem rsegs m' (f + 32) 8 wend -> YI04.val_mem rsegs m' (f + 40) 8 wpos ->
  YI04.val_mem rsegs m' (f + 56) 8 wbase ->
  ((wend = 0 /\ wpos = 0 /\ wbase = 0) \/
   (exists k, 0 <= k <= MemFile.MF_BUFSIZ /\ wend = f + MemFile.MF_BUF + MemFile.MF_BUFSIZ /\
      wpos = f + MemFile.MF_BUF + k /\ wbase = f + MemFile.MF_BUF)) ->
  YI04.val_mem rsegs m' (f + MemFile.MF_COOKIE) 8 pos -> YI04.val_mem rsegs m' (f + (MemFile.MF_COOKIE + 8)) 8 len ->
  0 <= pos <= len -> len <= 4096 ->
  MemFile.memfile_at YH02.src0_msyms MemFile.link_mf m' f.
Proof.
  intros m m' f fl wend wpos wbase pos len (Hf0 & Hf1 & Hf2 & Hs & Hfl & Hom & Hw & Hc) Hfr
    Vfl Efl Vwe Vwp Vwb Ew Vpos Vlen Hp Hl.
  assert (HV : forall off n v, 0 <= off -> off + Z.of_nat n <= MemFile.MF_ZEROED ->
    (forall x, f + off <= x < f + off + Z.of_nat n -> ~ dynw f x) ->
    YI04.val_mem rsegs m (f + off) n v -> YI04.val_mem rsegs m' (f + off) n v).
  { intros off n v H0 H1 Hd Hv k Hk. rewrite Hfr; [exact (Hv k Hk) | lia | apply Hd; lia]. }
  unfold MemFile.MF_ZEROED, MemFile.MF_COOKIE in *.
  split; [exact Hf0|]. split; [exact Hf1|]. split; [exact Hf2|].
  split; [|split; [|split; [|split]]].
  - unfold MemFile.memfile_static in *. unfold MemFile.MF_COOKIE in *.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    repeat match goal with |- _ /\ _ => split end;
      (apply HV; [lia | cbn; lia | intros x Hx; unfold dynw; cbn in Hx; lia | assumption]).
  - destruct Efl as [-> | ->]; [left | right]; exact Vfl.
  - destruct Hom as [H|H]; [left|right]; (apply HV; [lia | cbn; lia | intros x Hx; unfold dynw; cbn in Hx; lia | exact H]).
  - destruct Hw as (H8 & H16 & _).
    split; [apply HV; [lia | cbn; lia | intros x Hx; unfold dynw; cbn in Hx; lia | exact H8]|].
    split; [apply HV; [lia | cbn; lia | intros x Hx; unfold dynw; cbn in Hx; lia | exact H16]|].
    destruct Ew as [(-> & -> & ->) | (k & Hk & -> & -> & ->)].
    + left. split; [exact Vwe|]. split; [exact Vwp | exact Vwb].
    + right. exists k. split; [exact Hk|]. split; [exact Vwe|]. split; [exact Vwp | exact Vwb].
  - exists pos, len. split; [exact Hp|]. split; [cbn; exact Hl|]. split; [exact Vpos | exact Vlen].
Qed.

Definition ccells (posw lenw : word) : list cell :=
  [C8 posw; C8 lenw; C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 A_G_SAID); C4 (Z_to_bv 64 119)].
Definition frcells (o0 o1 o2 o3 o4 ora : word) : list cell :=
  [C8 o4; C8 o3; C8 o2; C8 o1; C8 o0; C8 ora].

Lemma stk_wmono : forall m m' lo hi, stk rsegs m lo hi -> wmono rsegs m m' -> stk rsegs m' lo hi.
Proof.
  intros m m' lo hi (H1 & H2 & H) W. split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as [Hw _]. pose proof (W _ Hw) as Hw'. split; [exact Hw'|].
  destruct (wv_mrd m' (wa a) Hw') as (b & Hb). exists b. exact Hb.
Qed.

Lemma mw_t2 : memcpy_contract -> forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo C : Z)
    (sp0 o0 o1 o2 o3 o4 ora lenw : word) (ds : list byte),
  sp = Z_to_bv 64 (bv_unsigned sp0 + -48) -> s4 = Z_to_bv 64 C ->
  rw_cells rsegs m (bv_unsigned sp0 + -48) (frcells o0 o1 o2 o3 o4 ora) ->
  stk rsegs m lo (bv_unsigned sp0 + -48) -> lo <= bv_unsigned sp0 + -48 -> 48 <= bv_unsigned sp0 ->
  rw_cells rsegs m C (ccells a0 lenw) ->
  bytes_at rsegs m (bv_unsigned s1) ds -> bv_unsigned s0 <= Z.of_nat (length ds) ->
  wr_at rsegs m A_G_SAID 4096 -> mem_inv rsegs m ->
  bv_unsigned a0 + bv_unsigned s0 <= 4096 -> bv_unsigned lenw <= 4096 ->
  (bv_unsigned s1 + bv_unsigned s0 <= A_G_SAID + bv_unsigned a0 \/ A_G_SAID + bv_unsigned a0 + bv_unsigned s0 <= bv_unsigned s1) ->
  (C + 36 <= A_G_SAID \/ A_G_SAID + 4096 <= C) ->
  (bv_unsigned sp0 <= A_G_SAID \/ A_G_SAID + 4096 <= bv_unsigned sp0 - 48) ->
  (bv_unsigned sp0 <= C \/ C + 36 <= bv_unsigned sp0 - 48) ->
  evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' posw' lenw',
      ms' = MS (mkR ora sp0 gp tp t0' t1' t2' o0 o1 s0 a1' a2' a3' a4' a5' a6' a7' o2 o3 o4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ora) fc None m' (seg_rom rsegs) /\
      munch [(C, C + 16); (A_G_SAID + bv_unsigned a0, A_G_SAID + 4096)] m m' /\
      wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp0) /\
      rw_cells rsegs m' C (ccells posw' lenw') /\
      bv_unsigned posw' = bv_unsigned a0 + bv_unsigned s0 /\
      bv_unsigned lenw' = Z.max (bv_unsigned lenw) (bv_unsigned a0 + bv_unsigned s0) /\
      bytes_at rsegs m' (A_G_SAID + bv_unsigned a0) (firstn (Z.to_nat (bv_unsigned s0)) ds))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x195f4) fc None m (seg_rom rsegs)).
Proof.
  intros MC. intros until ds. intros -> -> FR ST LOS S48 HC DS NL SAID MI PL LL SEP1 SEP2 SEP3 SEP4.
  unfold ccells, frcells in *.
  assert (STK : forall m', wmono rsegs m m' -> stk rsegs m' lo (bv_unsigned sp0 + -48))
    by (intros m' W; exact (stk_wmono m m' _ _ ST W)).
  pose proof (rw_cells_bound _ _ _ _ HC) as BC. cbn [cells_size csize Nat.add] in BC.
  pose proof (zr_word sp0) as Rsp. pose proof (zr_word s0) as Rs0. pose proof (zr_word a0) as Ra0.
  pose proof (zr_word s1) as Rs1. pose proof (zr_word lenw) as Rlen. unfold inr64 in *.
  pose proof (munch_refl [(C, C + 16); (A_G_SAID + bv_unsigned a0, A_G_SAID + 4096)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct (wr_at_cells m A_G_SAID 4096 (bv_unsigned a0) (bv_unsigned s0) SAID ltac:(lia) ltac:(lia) ltac:(lia)) as [junk DST].
  assert (SRC : bytes_at rsegs m (bv_unsigned s1) (firstn (Z.to_nat (bv_unsigned s0)) ds)).
  { rewrite <- (firstn_skipn (Z.to_nat (bv_unsigned s0)) ds) in DS. apply bytes_at_app in DS. destruct DS as [D1 _]. exact D1. }
  zstep. zstep. zstep. zstep. zstep.
  remember (Z_to_bv 64 (A_G_SAID + bv_unsigned a0)) as dw eqn:Edw.
  assert (Ud : bv_unsigned dw = A_G_SAID + bv_unsigned a0) by (subst dw; apply unsigned_lit; unfold A_G_SAID in *; lia).
  clear Edw. rewrite <- Ud in DST.
  call MC; [ exact SRC | rewrite length_firstn; lia | exact DST | lia | exact MI | ].
  zstep. zstep. zstep.
  remember (Z_to_bv 64 (bv_unsigned a0 + bv_unsigned s0)) as pw eqn:Epw.
  assert (Upw : bv_unsigned pw = bv_unsigned a0 + bv_unsigned s0) by (subst pw; apply unsigned_lit; lia).
  clear Epw.
  zstep. zstep.
  if_cases BR1; zify_cond BR1.
  - (* len >= new pos: len stays *)
    do 9 zstep.
    pose proof (STK _ WM) as ST. release_frame FR ST (bv_unsigned sp0).
    apply evt_done. do 17 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
    split; [exact HC|]. split; [exact Upw|]. split; [lia|].
    rewrite <- Ud. exact (rw1_bytes _ _ _ PC).
  - zstep. zstep. zstep.
    if_cases BR2; zify_cond BR2.
    + (* new pos at the size: no NUL *)
      do 9 zstep.
      pose proof (STK _ WM) as ST. release_frame FR ST (bv_unsigned sp0).
      apply evt_done. do 17 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
      split; [exact HC|]. split; [exact Upw|]. split; [lia|].
      rewrite <- Ud. exact (rw1_bytes _ _ _ PC).
    + (* NUL after the new len *)
      destruct (wr_at_cells _ A_G_SAID 4096 (bv_unsigned pw) 1 SAID ltac:(lia) ltac:(lia) ltac:(lia)) as [nj NUL].
      change (Z.to_nat 1) with 1%nat in NUL.
      zstep. zstep.
      remember (A_G_SAID + bv_unsigned pw) as na eqn:Ena.
      zstep. change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0]. mem_after_store.
      do 9 zstep.
      pose proof (STK _ WM) as ST. release_frame FR ST (bv_unsigned sp0).
      apply evt_done. do 17 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
      split; [exact HC|]. split; [exact Upw|]. split; [lia|].
      rewrite <- Ud. exact (rw1_bytes _ _ _ PC).
Qed.

Ltac call_t2 MC xsp0 xlo xC xlenw xds x0 x1 x2 x3 x4 xra :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (mw_t2 MC) with (sp0 := xsp0) (lo := xlo) (C := xC) (lenw := xlenw) (ds := xds)
        (o0 := x0) (o1 := x1) (o2 := x2) (o3 := x3) (o4 := x4) (ora := xra)
    | post_call rsegs mm ]
  end.

Lemma mw_tail : memcpy_contract -> __errno_location_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo Fz C fl : Z)
    (sp0 o0 o1 o2 o3 o4 ora posw lenw wendw wposw wbasew : word) (ds : list byte),
  sp = Z_to_bv 64 (bv_unsigned sp0 + -48) -> s2 = Z_to_bv 64 Fz -> s4 = Z_to_bv 64 C -> C = Fz + 232 ->
  rw_cells rsegs m (bv_unsigned sp0 + -48) (frcells o0 o1 o2 o3 o4 ora) ->
  stk rsegs m lo (bv_unsigned sp0 + -48) -> lo <= bv_unsigned sp0 + -48 -> 48 <= bv_unsigned sp0 ->
  rw_cells rsegs m Fz [C4 (Z_to_bv 64 fl)] -> (fl = 4 \/ fl = 36) ->
  rw_cells rsegs m (Fz + 32) [C8 wendw; C8 wposw] -> rw_cells rsegs m (Fz + 56) [C8 wbasew] ->
  rw_cells rsegs m C (ccells posw lenw) ->
  wr_at rsegs m (bv_unsigned tp + -164) 4 ->
  bytes_at rsegs m (bv_unsigned s1) ds -> bv_unsigned s0 = Z.of_nat (length ds) ->
  wr_at rsegs m A_G_SAID 4096 -> mem_inv rsegs m ->
  bv_unsigned posw <= 4096 -> bv_unsigned lenw <= 4096 -> 0 <= Fz -> Fz + 1304 <= 2 ^ 64 ->
  (bv_unsigned s1 + bv_unsigned s0 <= A_G_SAID \/ A_G_SAID + 4096 <= bv_unsigned s1) ->
  (bv_unsigned s1 + bv_unsigned s0 <= Fz \/ Fz + 272 <= bv_unsigned s1) ->
  (bv_unsigned tp + -164 + 4 <= bv_unsigned s1 \/ bv_unsigned s1 + bv_unsigned s0 <= bv_unsigned tp + -164) ->
  (Fz + 1304 <= A_G_SAID \/ A_G_SAID + 4096 <= Fz) ->
  (bv_unsigned tp + -164 + 4 <= Fz \/ Fz + 1304 <= bv_unsigned tp + -164) ->
  (bv_unsigned tp + -164 + 4 <= A_G_SAID \/ A_G_SAID + 4096 <= bv_unsigned tp + -164) ->
  (bv_unsigned sp0 <= Fz \/ Fz + 1304 <= bv_unsigned sp0 - 48) ->
  (bv_unsigned sp0 <= A_G_SAID \/ A_G_SAID + 4096 <= bv_unsigned sp0 - 48) ->
  (bv_unsigned sp0 <= bv_unsigned tp + -164 \/ bv_unsigned tp + -164 + 4 <= bv_unsigned sp0 - 48) ->
  let N := bv_unsigned s0 in let P := bv_unsigned posw in let L := bv_unsigned lenw in
  let E := bv_unsigned tp + -164 in let n2 := Z.min N (4096 - P) in
  evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' rw flw' wendw' wposw' wbasew' posw' lenw',
      ms' = MS (mkR ora sp0 gp tp t0' t1' t2' o0 o1 rw a1' a2' a3' a4' a5' a6' a7' o2 o3 o4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ora) fc None m' (seg_rom rsegs) /\
      munch [(Fz, Fz + 4); (Fz + 32, Fz + 48); (Fz + 56, Fz + 64); (C, C + 16); (A_G_SAID + P, A_G_SAID + 4096); (E, E + 4)] m m' /\
      wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp0) /\
      rw_cells rsegs m' Fz [C4 flw'] /\ rw_cells rsegs m' (Fz + 32) [C8 wendw'; C8 wposw'] /\
      rw_cells rsegs m' (Fz + 56) [C8 wbasew'] /\ rw_cells rsegs m' C (ccells posw' lenw') /\
      bv_unsigned rw = n2 /\ bv_unsigned posw' = P + n2 /\ bv_unsigned lenw' = Z.max L (P + n2) /\
      bytes_at rsegs m' (A_G_SAID + P) (firstn (Z.to_nat n2) ds) /\
      (N <= 4096 - P -> flw' = Z_to_bv 64 fl /\ wendw' = wendw /\ wposw' = wposw /\ wbasew' = wbasew) /\
      (4096 - P < N -> flw' = Z_to_bv 64 36 /\ wendw' = Z_to_bv 64 0 /\ wposw' = Z_to_bv 64 0 /\ wbasew' = Z_to_bv 64 0))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x195a0) fc None m (seg_rom rsegs)).
Proof.
  intros MC EC. intros until ds.
  intros -> -> -> ECk FR ST LOS S48 HFl FL HW HB HC ERRW DS NL SAID MI PL LL F0 F1 SEP1 SEP2 SEP3 SEP4 SEP5 SEP6 SEP7 SEP8 SEP9.
  intros N P L E n2. subst N P L E n2. subst C.
  unfold ccells, frcells in *.
  assert (STK : forall m', wmono rsegs m m' -> stk rsegs m' lo (bv_unsigned sp0 + -48))
    by (intros m' W; exact (stk_wmono m m' _ _ ST W)).
  pose proof (zr_word sp0) as Rsp. pose proof (zr_word s0) as Rs0. pose proof (zr_word posw) as Rp.
  pose proof (zr_word s1) as Rs1. pose proof (zr_word lenw) as Rlen. pose proof (zr_word tp) as Rtp. unfold inr64 in *.
  pose proof ERRW as (BE0 & BE1 & _).
  pose proof (munch_refl [(Fz, Fz + 4); (Fz + 32, Fz + 48); (Fz + 56, Fz + 64); (Fz + 232, Fz + 232 + 16);
     (A_G_SAID + bv_unsigned posw, A_G_SAID + 4096); (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  zstep. zstep. zstep. if_true.
  zstep. zstep. zstep.
  remember (Z_to_bv 64 (4096 - bv_unsigned posw)) as r3 eqn:Er3.
  assert (Ur3 : bv_unsigned r3 = 4096 - bv_unsigned posw) by (subst r3; apply unsigned_lit; lia).
  clear Er3.
  zstep. if_cases BR; zify_cond BR.
  - (* the data fits *)
    call_t2 MC sp0 lo (Fz + 232) lenw ds o0 o1 o2 o3 o4 ora;
      [ reflexivity | reflexivity | exact FR | exact (STK _ WM) | lia | lia | exact HC | exact DS | lia
      | exact SAID | assumption | lia | lia | lia | lia | lia | lia | ].
    apply evt_done. do 22 eexists. split; [reflexivity|].
    split; [eapply munch_weaken; [|exact MU]; unfold sub_fp; cbn [outside]; intros; lia|].
    split; [exact WM|]. split; [assumption|]. split; [assumption|].
    split; [exact HFl|]. split; [exact HW|]. split; [exact HB|]. split; [eassumption|].
    split; [lia|]. split; [lia|]. split; [lia|].
    split; [replace (Z.min (bv_unsigned s0) (4096 - bv_unsigned posw)) with (bv_unsigned s0) by lia; assumption|].
    split; [intros _; repeat split; reflexivity | intros; lia].
  - (* past the end: errno, F_ERR, empty window, then the bytes that fit *)
    zstep.
    eapply evt_cut; [apply EC | intros ms' ->].
    replace (ret_pc (Z_to_bv 64 103884)) with (Z_to_bv 64 103884) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    unfold __errno_location_c.ERRNO_TP_OFF.
    destruct (wr_at_cells _ (bv_unsigned tp + -164) 4 0 4 ERRW ltac:(lia) ltac:(lia) ltac:(lia)) as [ej ERR].
    rewrite Z.add_0_r in ERR. change (Z.to_nat 4) with 4%nat in ERR.
    zstep. zstep.
    destruct FL as [-> | ->]; zstep; zstep; zstep; zstep; zstep; zstep; zstep; zstep;
    (call_t2 MC sp0 lo (Fz + 232) lenw ds o0 o1 o2 o3 o4 ora;
      [ reflexivity | reflexivity | exact FR | exact (STK _ WM) | lia | lia | exact HC | exact DS | lia
      | exact SAID | assumption | lia | lia | lia | lia | lia | lia | ]);
    (apply evt_done; do 22 eexists; split; [reflexivity|];
     split; [eapply munch_weaken; [|exact MU]; unfold sub_fp; cbn [outside]; intros; lia|];
     split; [exact WM|]; split; [assumption|]; split; [assumption|];
     split; [exact HFl|]; split; [exact HW|]; split; [exact HB|]; split; [eassumption|];
     split; [lia|]; split; [lia|]; split; [lia|];
     split; [replace (Z.min (bv_unsigned s0) (4096 - bv_unsigned posw)) with (bv_unsigned r3) by lia; assumption|];
     split; [intros; lia | intros _; repeat split; vm_compute; reflexivity]).
Qed.

Ltac call_tail MC EC xsp0 xlo xFz xfl xpos xlen xwe xwp xwb xds x0 x1 x2 x3 x4 xra :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (mw_tail MC EC) with (sp0 := xsp0) (lo := xlo) (Fz := xFz) (C := xFz + 232) (fl := xfl)
        (posw := xpos) (lenw := xlen) (wendw := xwe) (wposw := xwp) (wbasew := xwb) (ds := xds)
        (o0 := x0) (o1 := x1) (o2 := x2) (o3 := x3) (o4 := x4) (ora := xra)
    | post_call rsegs mm ]
  end.

(* the no-flush call: k = 0 (wpos = wbase), one frame of 48 *)
Lemma mw_k0 : memcpy_contract -> __errno_location_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo Fz fl : Z)
    (posw lenw wendw wbasew : word) (ds : list byte),
  a0 = Z_to_bv 64 Fz ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> bv_unsigned sp < 2 ^ 63 ->
  rw_cells rsegs m Fz [C4 (Z_to_bv 64 fl)] -> (fl = 4 \/ fl = 36) ->
  rw_cells rsegs m (Fz + 32) [C8 wendw; C8 wbasew] -> rw_cells rsegs m (Fz + 56) [C8 wbasew] ->
  rw_cells rsegs m (Fz + 152) [C8 (Z_to_bv 64 (Fz + 232))] ->
  rw_cells rsegs m (Fz + 232) (ccells posw lenw) ->
  wr_at rsegs m (bv_unsigned tp + -164) 4 ->
  bytes_at rsegs m (bv_unsigned a1) ds -> bv_unsigned a2 = Z.of_nat (length ds) ->
  wr_at rsegs m A_G_SAID 4096 -> mem_inv rsegs m ->
  bv_unsigned posw <= 4096 -> bv_unsigned lenw <= 4096 -> 0 <= Fz -> Fz + 1304 <= 2 ^ 64 ->
  (bv_unsigned a1 + bv_unsigned a2 <= A_G_SAID \/ A_G_SAID + 4096 <= bv_unsigned a1) ->
  (bv_unsigned a1 + bv_unsigned a2 <= Fz \/ Fz + 272 <= bv_unsigned a1) ->
  (bv_unsigned tp + -164 + 4 <= bv_unsigned a1 \/ bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned tp + -164) ->
  (Fz + 1304 <= A_G_SAID \/ A_G_SAID + 4096 <= Fz) ->
  (bv_unsigned tp + -164 + 4 <= Fz \/ Fz + 1304 <= bv_unsigned tp + -164) ->
  (bv_unsigned tp + -164 + 4 <= A_G_SAID \/ A_G_SAID + 4096 <= bv_unsigned tp + -164) ->
  (bv_unsigned sp <= Fz \/ Fz + 1304 <= bv_unsigned sp - 48) ->
  (bv_unsigned sp <= A_G_SAID \/ A_G_SAID + 4096 <= bv_unsigned sp - 48) ->
  (bv_unsigned sp <= bv_unsigned tp + -164 \/ bv_unsigned tp + -164 + 4 <= bv_unsigned sp - 48) ->
  (bv_unsigned sp <= bv_unsigned a1 \/ bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned sp - 48) ->
  let N := bv_unsigned a2 in let P := bv_unsigned posw in let L := bv_unsigned lenw in
  let E := bv_unsigned tp + -164 in let n2 := Z.min N (4096 - P) in
  evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' rw flw' wendw' wposw' wbasew' posw' lenw',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 rw a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned sp - 48, bv_unsigned sp); (Fz, Fz + 4); (Fz + 32, Fz + 48); (Fz + 56, Fz + 64);
             (Fz + 232, Fz + 248); (A_G_SAID + P, A_G_SAID + 4096); (E, E + 4)] m m' /\
      wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
      rw_cells rsegs m' Fz [C4 flw'] /\ rw_cells rsegs m' (Fz + 32) [C8 wendw'; C8 wposw'] /\
      rw_cells rsegs m' (Fz + 56) [C8 wbasew'] /\ rw_cells rsegs m' (Fz + 232) (ccells posw' lenw') /\
      bv_unsigned rw = n2 /\ bv_unsigned posw' = P + n2 /\ bv_unsigned lenw' = Z.max L (P + n2) /\
      bytes_at rsegs m' (A_G_SAID + P) (firstn (Z.to_nat n2) ds) /\
      (N <= 4096 - P -> flw' = Z_to_bv 64 fl /\ wendw' = wendw /\ wposw' = wbasew /\ wbasew' = wbasew) /\
      (4096 - P < N -> flw' = Z_to_bv 64 36 /\ wendw' = Z_to_bv 64 0 /\ wposw' = Z_to_bv 64 0 /\ wbasew' = Z_to_bv 64 0))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x19544) fc None m (seg_rom rsegs)).
Proof.
  intros MC EC. intros until ds.
  intros -> ST LO SPH HFl FL HW HB HK HC ERRW DS NL SAID MI PL LL F0 F1
    SEP1 SEP2 SEP3 SEP4 SEP5 SEP6 SEP7 SEP8 SEP9 SEP10.
  intros N P L E n2. subst N P L E n2.
  unfold ccells in *.
  pose proof (zr_word sp) as Rsp. pose proof (zr_word a2) as Ra2. pose proof (zr_word posw) as Rp.
  pose proof (zr_word a1) as Ra1. pose proof (zr_word lenw) as Rlen. pose proof (zr_word tp) as Rtp. unfold inr64 in *.
  pose proof ERRW as (BE0 & BE1 & _).
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (Fz, Fz + 4); (Fz + 32, Fz + 48); (Fz + 56, Fz + 64);
     (Fz + 232, Fz + 248); (A_G_SAID + bv_unsigned posw, A_G_SAID + 4096);
     (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  do 14 zstep.
  if_true.
  call_tail MC EC sp lo Fz fl posw lenw wendw wbasew wbasew ds s0 s1 s2 s3 s4 ra;
    [ reflexivity | reflexivity | reflexivity | reflexivity | exact FR | exact ST | lia | lia
    | exact HFl | exact FL | exact HW | exact HB | exact HC | exact ERRW | exact DS | exact NL
    | exact SAID | exact MI | lia | lia | lia | lia
    | lia | lia | lia | lia | lia | lia | lia | lia | lia | ].
  apply evt_done. do 22 eexists. split; [reflexivity|].
  split; [eapply munch_weaken; [|exact MU]; unfold sub_fp; cbn [outside]; intros; lia|].
  split; [exact WM|]. split; [assumption|]. split; [assumption|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; assumption.
Qed.

Ltac call_k0 MC EC xlo xFz xfl xpos xlen xwe xwb xds :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (mw_k0 MC EC) with (lo := xlo) (Fz := xFz) (fl := xfl) (posw := xpos) (lenw := xlen)
        (wendw := xwe) (wbasew := xwb) (ds := xds)
    | post_call rsegs mm ]
  end.

(* the general call: k = length pb pending bytes, flushed by the inner call at sp - 48 *)
Lemma mw_gen : memcpy_contract -> __errno_location_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo Fz fl : Z)
    (posw lenw wendw wposw wbasew : word) (pb ds : list byte),
  a0 = Z_to_bv 64 Fz ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 96 <= bv_unsigned sp -> bv_unsigned sp < 2 ^ 63 ->
  rw_cells rsegs m Fz [C4 (Z_to_bv 64 fl)] -> (fl = 4 \/ fl = 36) ->
  rw_cells rsegs m (Fz + 32) [C8 wendw; C8 wposw] -> rw_cells rsegs m (Fz + 56) [C8 wbasew] ->
  rw_cells rsegs m (Fz + 152) [C8 (Z_to_bv 64 (Fz + 232))] ->
  rw_cells rsegs m (Fz + 232) (ccells posw lenw) ->
  wr_at rsegs m (bv_unsigned tp + -164) 4 ->
  bytes_at rsegs m (bv_unsigned a1) ds -> bv_unsigned a2 = Z.of_nat (length ds) ->
  bytes_at rsegs m (Fz + 280) pb -> Z.of_nat (length pb) <= 1024 ->
  ((pb = [] /\ wposw = wbasew) \/
   (pb <> [] /\ bv_unsigned wbasew = Fz + 280 /\ bv_unsigned wposw = Fz + 280 + Z.of_nat (length pb))) ->
  wr_at rsegs m A_G_SAID 4096 -> mem_inv rsegs m ->
  bv_unsigned posw <= 4096 -> bv_unsigned lenw <= 4096 -> 0 <= Fz -> Fz + 1304 <= 2 ^ 64 ->
  (bv_unsigned a1 + bv_unsigned a2 <= A_G_SAID \/ A_G_SAID + 4096 <= bv_unsigned a1) ->
  (bv_unsigned a1 + bv_unsigned a2 <= Fz \/ Fz + 272 <= bv_unsigned a1) ->
  (bv_unsigned tp + -164 + 4 <= bv_unsigned a1 \/ bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned tp + -164) ->
  (Fz + 1304 <= A_G_SAID \/ A_G_SAID + 4096 <= Fz) ->
  (bv_unsigned tp + -164 + 4 <= Fz \/ Fz + 1304 <= bv_unsigned tp + -164) ->
  (bv_unsigned tp + -164 + 4 <= A_G_SAID \/ A_G_SAID + 4096 <= bv_unsigned tp + -164) ->
  (bv_unsigned sp <= Fz \/ Fz + 1304 <= bv_unsigned sp - 96) ->
  (bv_unsigned sp <= A_G_SAID \/ A_G_SAID + 4096 <= bv_unsigned sp - 96) ->
  (bv_unsigned sp <= bv_unsigned tp + -164 \/ bv_unsigned tp + -164 + 4 <= bv_unsigned sp - 96) ->
  (bv_unsigned sp <= bv_unsigned a1 \/ bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned sp - 96) ->
  let k := Z.of_nat (length pb) in
  let N := bv_unsigned a2 in let P := bv_unsigned posw in let L := bv_unsigned lenw in
  let E := bv_unsigned tp + -164 in
  let n1 := Z.min k (4096 - P) in let P1 := P + n1 in let n2 := Z.min N (4096 - P1) in
  evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' rw flw' wendw' wposw' wbasew' posw' lenw',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 rw a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned sp - 96, bv_unsigned sp); (Fz, Fz + 4); (Fz + 32, Fz + 48); (Fz + 56, Fz + 64);
             (Fz + 232, Fz + 248); (A_G_SAID + P, A_G_SAID + 4096); (E, E + 4)] m m' /\
      wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
      rw_cells rsegs m' Fz [C4 flw'] /\ rw_cells rsegs m' (Fz + 32) [C8 wendw'; C8 wposw'] /\
      rw_cells rsegs m' (Fz + 56) [C8 wbasew'] /\ rw_cells rsegs m' (Fz + 232) (ccells posw' lenw') /\
      (n1 < k ->
         bv_unsigned rw = 0 /\ flw' = Z_to_bv 64 36 /\ wendw' = Z_to_bv 64 0 /\ wposw' = Z_to_bv 64 0 /\
         wbasew' = Z_to_bv 64 0 /\ bv_unsigned posw' = P1 /\ bv_unsigned lenw' = Z.max L P1 /\
         bytes_at rsegs m' (A_G_SAID + P) (firstn (Z.to_nat n1) pb)) /\
      (n1 = k ->
         bv_unsigned rw = n2 /\ bv_unsigned posw' = P1 + n2 /\ bv_unsigned lenw' = Z.max L (P1 + n2) /\
         bytes_at rsegs m' (A_G_SAID + P) (pb ++ firstn (Z.to_nat n2) ds) /\
         (n2 < N -> flw' = Z_to_bv 64 36 /\ wendw' = Z_to_bv 64 0 /\ wposw' = Z_to_bv 64 0 /\ wbasew' = Z_to_bv 64 0) /\
         (n2 = N -> flw' = Z_to_bv 64 fl /\ wendw' = wendw /\ wposw' = wbasew /\ wbasew' = wbasew)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x19544) fc None m (seg_rom rsegs)).
Proof.
  intros MC EC. intros until ds.
  intros -> ST LO SPH HFl FL HW HB HK HC ERRW DS NL PB KB WIN SAID MI PL LL F0 F1
    SEP1 SEP2 SEP3 SEP4 SEP5 SEP6 SEP7 SEP8 SEP9 SEP10.
  intros k N P L E n1 P1 n2. subst k N P L E n1 P1 n2.
  pose proof (zr_word sp) as Rsp. pose proof (zr_word a2) as Ra2. pose proof (zr_word posw) as Rp.
  pose proof (zr_word a1) as Ra1. pose proof (zr_word lenw) as Rlen. pose proof (zr_word tp) as Rtp. unfold inr64 in *.
  pose proof ERRW as (BE0 & BE1 & _).
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  destruct WIN as [(-> & ->) | (PNE & Uwb & Uwp)].
  - (* nothing pending: the no-flush lemma, in the lower 48 bytes of the window *)
    eapply evt_mono;
    [ eapply (mw_k0 MC EC) with (lo := lo) (Fz := Fz) (fl := fl) (posw := posw) (lenw := lenw)
        (wendw := wendw) (wbasew := wbasew) (ds := ds);
        first [ reflexivity | eassumption | lia ] | ].
    intros ms' (x0' & x1' & x2' & x3' & x4' & x5' & x6' & x7' & x8' & x9' & x10' & x11' & x12' & x13' & m' & rw &
      flw' & wendw' & wposw' & wbasew' & posw' & lenw' & -> & MU' & WM' & MI' & ST' & C1 & C2 & C3 & C4 & R1 & R2 & R3 & BY & I1 & I2).
    cbn [length Z.of_nat] in *.
    do 22 eexists. split; [reflexivity|].
    split; [eapply munch_weaken; [|exact MU']; unfold sub_fp; cbn [outside]; intros; lia|].
    split; [exact WM'|]. split; [exact MI'|]. split; [exact ST'|].
    split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|].
    split; [intros; lia|].
    intros _. change (Z.of_nat (length (@nil byte))) with 0 in *. change (Z.of_nat 0) with 0 in *.
    replace (Z.min 0 (4096 - bv_unsigned posw)) with 0 by lia. rewrite Z.add_0_r. cbn [app].
    split; [lia|]. split; [lia|]. split; [lia|].
    split; [exact BY|].
    split; [intros; apply I2; lia | intros; apply I1; lia].
  - (* k bytes pending: flush them first *)
    unfold ccells in *.
    pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (Fz, Fz + 4); (Fz + 32, Fz + 48); (Fz + 56, Fz + 64);
       (Fz + 232, Fz + 248); (A_G_SAID + bv_unsigned posw, A_G_SAID + 4096);
       (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    carve_frame 48%nat ST.
    assert (STK : forall m', wmono rsegs m m' -> stk rsegs m' lo (bv_unsigned sp + -48))
      by (intros m' W; exact (stk_wmono m m' _ _ ST W)).
    assert (KP : 0 < Z.of_nat (length pb)) by (destruct pb; [congruence | cbn; lia]).
    do 14 zstep.
    if_cases BQ; zify_cond BQ; [exfalso; lia|].
    zstep.
    remember (Z_to_bv 64 (bv_unsigned wposw - bv_unsigned wbasew)) as r3 eqn:Er3.
    assert (Ur3 : bv_unsigned r3 = Z.of_nat (length pb)) by (subst r3; rewrite unsigned_lit by lia; lia).
    clear Er3.
    do 5 zstep.
    assert (Usp1 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
    (* the inner call: mwrite(f, wbase, k), the no-flush lemma at sp - 48 *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply (mw_k0 MC EC) with (lo := lo) (Fz := Fz) (fl := fl) (posw := posw) (lenw := lenw)
          (wendw := wendw) (wbasew := wbasew) (ds := pb);
        first [ reflexivity | eassumption | (rewrite Usp1; exact (STK _ WM)) | (rewrite Uwb; exact PB) | lia ]
      | rename mm into m1 ] end.
    intros ms' (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m2 & rw &
      flw2 & wendw2 & wposw2 & wbasew2 & posw2 & lenw2 & -> & MUc & WMc & MI2 & ST2 & C1 & C2 & C3 & C4 &
      R1 & R2 & R3 & BY & I1 & I2).
    replace (ret_pc (Z_to_bv 64 103828)) with (Z_to_bv 64 103828) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    rewrite Ur3, Usp1 in *.
    assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -48) (frcells s0 s1 s2 s3 s4 ra))
      by (unfold frcells; apply (rw_cells_transport rsegs _ m1 m2 _ _ FR MUc WMc);
          clear - SEP7 SEP8 SEP9 Rsp Rtp Rp F0 F1 BE0 BE1; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    assert (DS2 : bytes_at rsegs m2 (bv_unsigned a1) ds)
      by (apply (bytes_at_transport rsegs _ m1 m2 _ _ DS MUc);
          clear - SEP1 SEP2 SEP3 SEP10 NL Rsp Ra1 Ra2 Rp Rtp F0 F1 BE0 BE1; cbn [disjoint_from]; lia).
    assert (MU2 : munch [(bv_unsigned sp - 96, bv_unsigned sp); (Fz, Fz + 4); (Fz + 32, Fz + 48); (Fz + 56, Fz + 64);
       (Fz + 232, Fz + 248); (A_G_SAID + bv_unsigned posw, A_G_SAID + 4096);
       (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] m m2)
      by (apply (munch_trans _ _ _ _ MU); eapply munch_weaken; [|exact MUc];
          clear - Rsp; unfold sub_fp; cbn [outside]; intros; lia).
    pose proof (wmono_trans _ _ _ _ WM WMc) as WM2.
    pose proof (wr_at_transport _ _ _ _ _ ERRW WMc) as ERRW2.
    pose proof (wr_at_transport _ _ _ _ _ SAID WMc) as SAID2.
    clear FR DS MU WM WMc MUc ERRW SAID HK PB HFl HW HB HC MI ST2.
    zstep.
    if_cases BR; zify_cond BR.
    + (* the flush stored all k: the tail at the new pos *)
      destruct (I1 ltac:(lia)) as (-> & -> & -> & ->).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply evt_cut;
        [ eapply (mw_tail MC EC) with (sp0 := sp) (lo := lo) (Fz := Fz) (C := Fz + 232) (fl := fl)
            (posw := posw2) (lenw := lenw2) (wendw := wendw) (wposw := wbasew) (wbasew := wbasew) (ds := ds)
            (o0 := s0) (o1 := s1) (o2 := s2) (o3 := s3) (o4 := s4) (ora := ra);
          first [ reflexivity | eassumption | exact (STK _ WM2) | lia ]
        | ] end.
      intros ms' (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m3 & rw3 &
        flw3 & wendw3 & wposw3 & wbasew3 & posw3 & lenw3 & -> & MUt & WMt & MI3 & ST3 & D1 & D2 & D3 & D4 &
        Q1 & Q2 & Q3 & BY3 & J1 & J2).
      replace (Z.to_nat (Z.min (Z.of_nat (length pb)) (4096 - bv_unsigned posw))) with (length pb) in BY by lia.
      rewrite firstn_all in BY.
      assert (BY2 : bytes_at rsegs m3 (A_G_SAID + bv_unsigned posw) pb)
        by (apply (bytes_at_transport rsegs _ m2 m3 _ _ BY MUt);
            clear - SEP4 SEP6 R1 R2 BR Ur3 Rp BE0 BE1 F0 F1 KB; cbn [disjoint_from]; lia).
      assert (MU3 : munch [(bv_unsigned sp - 96, bv_unsigned sp); (Fz, Fz + 4); (Fz + 32, Fz + 48); (Fz + 56, Fz + 64);
         (Fz + 232, Fz + 248); (A_G_SAID + bv_unsigned posw, A_G_SAID + 4096);
         (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] m m3)
        by (apply (munch_trans _ _ _ _ MU2); eapply munch_weaken; [|exact MUt];
            clear - R1 R2 BR Ur3 Rp; unfold sub_fp; cbn [outside]; intros; lia).
      apply evt_done. do 22 eexists. split; [reflexivity|].
      split; [eapply munch_weaken; [|exact MU3]; clear; unfold sub_fp; cbn [outside]; intros; lia|].
      split; [exact (wmono_trans _ _ _ _ WM2 WMt)|]. split; [exact MI3|]. split; [exact ST3|].
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split; [intros; lia|].
      intros _.
      replace (bv_unsigned posw + Z.min (Z.of_nat (length pb)) (4096 - bv_unsigned posw)) with (bv_unsigned posw2) by lia.
      split; [lia|]. split; [lia|]. split; [lia|].
      split.
      { apply bytes_at_app. split; [exact BY2|].
        replace (A_G_SAID + bv_unsigned posw + Z.of_nat (length pb)) with (A_G_SAID + bv_unsigned posw2) by lia.
        exact BY3. }
      split; [intros; apply J2; lia | intros; apply J1; lia].
    + (* the flush passed g_said's end: return 0 *)
      unfold frcells in FR2. zstep. zstep. do 9 zstep.
      pose proof (STK _ WM2) as ST4. release_frame FR2 ST4 (bv_unsigned sp).
      apply evt_done. do 22 eexists. split; [reflexivity|].
      split; [eapply munch_weaken; [|exact MU2]; clear; unfold sub_fp; cbn [outside]; intros; lia|].
      split; [exact WM2|]. split; [exact MI2|]. split; [exact ST4|].
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split; [|intros; lia].
      intros _. destruct (I2 ltac:(lia)) as (E1 & E2 & E3 & E4).
      split; [reflexivity|]. split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|].
      split; [lia|]. split; [lia|]. exact BY.
Qed.

Lemma vm_munch : forall W m m' a n v, YI04.val_mem rsegs m a n v -> munch W m m' ->
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (forall j, 0 <= j < Z.of_nat n -> outside W (a + j)) ->
  YI04.val_mem rsegs m' a n v.
Proof.
  intros W m m' a n v H MU A0 A1 HO k Hk.
  rewrite (munch_mbyte W m m'); [exact (H k Hk) | exact MU | lia | apply HO; lia].
Qed.

Lemma cells_vm88 : forall m a x y cs, rw_cells rsegs m a (C8 x :: C8 y :: cs) ->
  YI04.val_mem rsegs m a 8 (bv_unsigned x) /\ YI04.val_mem rsegs m (a + 8) 8 (bv_unsigned y).
Proof.
  intros m a x y cs [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb.
  apply bytes_at_app in Hb as [H1 H2]. apply bytes_at_app in H2 as [H2 _].
  rewrite length_le8 in H2. change (Z.of_nat 8) with 8 in H2.
  split; apply bytes_vm; [exact H1 | exact H2].
Qed.

Lemma rw_cells_cons : forall m a b c cs, rw_cells rsegs m a [c] -> cell_wf c -> rw_cells rsegs m b cs ->
  b = a + Z.of_nat (csize c) -> rw_cells rsegs m a (c :: cs).
Proof. intros m a b c cs H1 Hc H2 ->. apply rw_cells_app2; assumption. Qed.

Lemma memfile_static_need : forall m f, MemFile.memfile_static YH02.src0_msyms MemFile.link_mf m f ->
  YI04.val_mem rsegs m (f + 152) 8 (f + 232) /\ YI04.val_mem rsegs m (f + 248) 8 4096 /\
  YI04.val_mem rsegs m (f + 256) 8 A_G_SAID /\ YI04.val_mem rsegs m (f + 264) 4 119.
Proof.
  intros m f H. unfold MemFile.memfile_static, MemFile.MF_COOKIE, MemFile.MF_BUF in H.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat split; assumption.
Qed.

(* the FILE after the call, from the state the walk leaves *)
Lemma memfile_k_after : forall m m' f k flv wev wpv wbv pv lv,
  memfile_k m f k ->
  (forall x, f <= x < f + MemFile.MF_ZEROED -> ~ dynw f x -> YP09.mbyte rsegs m' x = YP09.mbyte rsegs m x) ->
  YI04.val_mem rsegs m' (f + 0) 4 flv -> (flv = 4 \/ flv = 36) ->
  YI04.val_mem rsegs m' (f + 32) 8 wev -> YI04.val_mem rsegs m' (f + 40) 8 wpv ->
  YI04.val_mem rsegs m' (f + 56) 8 wbv ->
  ((wev = 0 /\ wpv = 0 /\ wbv = 0) \/ (wev = f + 1304 /\ wpv = f + 280 /\ wbv = f + 280)) ->
  YI04.val_mem rsegs m' (f + 232) 8 pv -> YI04.val_mem rsegs m' (f + 240) 8 lv ->
  0 <= pv <= lv -> lv <= 4096 ->
  wr_at rsegs m' f MemFile.MF_BLOCK -> wr_at rsegs m' A_G_SAID SAID_SIZE ->
  memfile_k m' f 0.
Proof.
  intros m m' f k flv wev wpv wbv pv lv (MA & _ & _ & _ & MP) AG Vfl Efl Vwe Vwp Vwb Ew Vp Vl Hp Hl W1 W2.
  split; [|split; [|split; [exact W1 | split; [exact W2 | exact MP]]]].
  - apply (memfile_at_upd m m' f flv wev wpv wbv pv lv MA AG Vfl Efl Vwe Vwp Vwb); try assumption.
    destruct Ew as [E|(-> & -> & ->)]; [left; exact E | right].
    exists 0. unfold MemFile.MF_BUF, MemFile.MF_BUFSIZ. split; [lia|]. split; [lia|]. split; lia.
  - unfold mf_win, mf_fld. destruct Ew as [(-> & -> & ->) | (-> & -> & ->)].
    + left. split; [reflexivity|]. split; [exact Vwe|]. split; [exact Vwp | exact Vwb].
    + right. unfold MemFile.MF_BUF, MemFile.MF_BUFSIZ. split; [lia|].
      replace (f + 280 + 1024) with (f + 1304) by lia. replace (f + 280 + 0) with (f + 280) by lia.
      split; [exact Vwe|]. split; [exact Vwp | exact Vwb].
Qed.

Lemma f_top : forall f, f mod 16 = 0 -> f + 1304 <= 2 ^ 64 -> f + 1304 < 2 ^ 64.
Proof.
  intros f H1 H2. destruct (Z.eq_dec (f + 1304) (2 ^ 64)) as [E|E]; [|lia].
  exfalso. assert (f = 2 ^ 64 - 1304) by lia. subst f. vm_compute in H1. discriminate.
Qed.

Theorem mwrite_proof : mwrite_contract.
Proof.
  unfold mwrite_contract. intros f k fl om wend wpos wbase pos len pb ds.
  apply leaf_intro.
  - intros r1 r2 m E H. unfold getr_same in E.
    assert (Ea0 : arg r1 0 = arg r2 0) by (unfold arg; rewrite E; reflexivity).
    assert (Ea1 : arg r1 1 = arg r2 1) by (unfold arg; rewrite E; reflexivity).
    assert (Ea2 : arg r1 2 = arg r2 2) by (unfold arg; rewrite E; reflexivity).
    assert (Eer : errno_at r1 = errno_at r2) by (unfold errno_at; rewrite E; reflexivity).
    assert (Esp : spZ r1 = spZ r2) by (unfold spZ; f_equal; exact (E 2%bv)).
    unfold errno_ok in *. unfold apart_frame in *. rewrite <- Ea0, <- Ea1, <- Ea2, <- Eer, <- Esp. exact H.
  - intros r1 r2 m E. unfold getr_same in E. unfold errno_at. rewrite E. reflexivity.
  - intros r1 r2 m q1 q2 m' E1 E2 H. unfold getr_same in E2. unfold res in *. rewrite <- E2. exact H.
  - unfold leaf_walk.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
    cbv zeta. intros PRE MI ST LO SPH.
    unfold errno_ok in PRE. unfold apart_frame in PRE.
    rewrite ?mkR_a0, ?mkR_a1, ?mkR_a2, ?mkR_sp, ?mkR_errno in PRE.
    destruct PRE as (A0 & A2 & MK & MD & PBY & KL & DSB & R1 & R2 & R3 & AF1 & AF2 & AF3 & ITOP & EOK).
    destruct EOK as (ERRW & EAF & ERF & ERS & ERG & ERY).
    pose proof MK as (MA & MW & WRB & WRS & MP).
    destruct MD as (Rfl & Rom & Rwe & Rwp & Rwb & Rpos & Rlen & Vfl & Vom & Vwe & Vwp & Vwb & Vpos & Vlen).
    pose proof MA as (Hf0 & Hf1 & Hf2 & Hst & Hfl & Hom & Hwin & Hck).
    destruct (memfile_static_need _ _ Hst) as (Vck & Vsz & Vbuf & Vmode).
    pose proof (f_top f Hf2 Hf1) as FQ.
    pose proof (memfile_k_range _ _ _ MK) as KR.
    unfold link_mem.ERRNO_TP_OFF, mf_place_ok, rapart, IMG_LO, IMG_TOP, SAID_SIZE, MemFile.MF_BLOCK,
      MemFile.MF_ZEROED, MWRITE_K, MemFile.MF_COOKIE, MemFile.MF_BUF, MemFile.MF_BUFSIZ,
      MemFile.F_NORD, MemFile.F_ERR, mf_pend_bytes, mf_fld in *.
    unfold MemFile.MF_BUF, MemFile.MF_COOKIE, MemFile.MF_BUFSIZ, MemFile.MF_BLOCK, MemFile.MF_ZEROED in *.
    pose proof (zr_word sp) as Rsp. pose proof (zr_word a1) as Ra1. pose proof (zr_word a2) as Ra2.
    pose proof (zr_word tp) as Rtp. pose proof (zr_word a0) as Ra0. unfold inr64 in *.
    assert (FL : fl = 4 \/ fl = 36).
    { destruct Hfl as [H|H]; [left|right]; (apply (vm_inj m (f + 0) 4); [exact Vfl | exact H | cbn; lia | cbn; lia]). }
    assert (WINZ : (k = 0 /\ wend = 0 /\ wpos = 0 /\ wbase = 0) \/
                   (0 <= k <= 1024 /\ wend = f + 1304 /\ wpos = f + 280 + k /\ wbase = f + 280)).
    { unfold mf_win, mf_fld, MemFile.MF_BUF, MemFile.MF_BUFSIZ in MW.
      destruct MW as [(-> & H1 & H2 & H3) | (Hk & H1 & H2 & H3)]; [left | right].
      - split; [reflexivity|].
        split; [apply (vm_inj m (f + 32) 8); [exact Vwe | exact H1 | cbn; lia | cbn; lia]|].
        split; [apply (vm_inj m (f + 40) 8); [exact Vwp | exact H2 | cbn; lia | cbn; lia]|].
        apply (vm_inj m (f + 56) 8); [exact Vwb | exact H3 | cbn; lia | cbn; lia].
      - split; [exact Hk|]. replace (f + 280 + 1024) with (f + 1304) in H1 by lia.
        split; [apply (vm_inj m (f + 32) 8); [exact Vwe | exact H1 | cbn; lia | cbn; lia]|].
        split; [apply (vm_inj m (f + 40) 8); [exact Vwp | exact H2 | cbn; lia | cbn; lia]|].
        apply (vm_inj m (f + 56) 8); [exact Vwb | exact H3 | cbn; lia | cbn; lia]. }
    assert (WRF : forall off n, 0 <= off -> 0 <= n -> off + n <= 1304 -> wr_at rsegs m (f + off) n)
      by (intros off n Ho Hn Hon; apply (wr_at_sub _ _ _ _ _ WRB); lia).
    pose proof (vm_cell4 m (f + 0) fl Vfl ltac:(lia) (WRF 0 4 ltac:(lia) ltac:(lia) ltac:(lia))) as HFl.
    rewrite Z.add_0_r in HFl.
    pose proof (rw_cells_cons _ _ _ _ _ (vm_cell8 m (f + 32) wend Vwe Rwe (WRF 32 8 ltac:(lia) ltac:(lia) ltac:(lia))) I
                 (vm_cell8 m (f + 40) wpos Vwp Rwp (WRF 40 8 ltac:(lia) ltac:(lia) ltac:(lia))) ltac:(cbn; lia)) as HW.
    pose proof (vm_cell8 m (f + 56) wbase Vwb Rwb (WRF 56 8 ltac:(lia) ltac:(lia) ltac:(lia))) as HB.
    pose proof (vm_cell8 m (f + 152) (f + 232) Vck ltac:(lia) (WRF 152 8 ltac:(lia) ltac:(lia) ltac:(lia))) as HK.
    pose proof (vm_cell4 m (f + 264) 119 Vmode ltac:(lia) (WRF 264 4 ltac:(lia) ltac:(lia) ltac:(lia))) as K5.
    pose proof (rw_cells_cons _ _ _ _ _ (vm_cell8 m (f + 256) A_G_SAID Vbuf ltac:(unfold A_G_SAID; lia)
                 (WRF 256 8 ltac:(lia) ltac:(lia) ltac:(lia))) I K5 ltac:(cbn; lia)) as K4.
    pose proof (rw_cells_cons _ _ _ _ _ (vm_cell8 m (f + 248) 4096 Vsz ltac:(lia)
                 (WRF 248 8 ltac:(lia) ltac:(lia) ltac:(lia))) I K4 ltac:(cbn; lia)) as K3.
    pose proof (rw_cells_cons _ _ _ _ _ (vm_cell8 m (f + (232 + 8)) len Vlen ltac:(lia)
                 (WRF 240 8 ltac:(lia) ltac:(lia) ltac:(lia))) I K3 ltac:(cbn; lia)) as K2.
    pose proof (rw_cells_cons _ _ _ _ _ (vm_cell8 m (f + 232) pos Vpos ltac:(lia)
                 (WRF 232 8 ltac:(lia) ltac:(lia) ltac:(lia))) I K2 ltac:(cbn; lia)) as HC.
    clear K2 K3 K4 K5.
    assert (WIN : (pb = [] /\ wz wpos = wz wbase) \/
                  (pb <> [] /\ bv_unsigned (wz wbase) = f + 280 /\ bv_unsigned (wz wpos) = f + 280 + Z.of_nat (length pb))).
    { destruct WINZ as [(-> & _ & -> & ->) | (Hk & _ & -> & ->)].
      - left. split; [destruct pb; [reflexivity | cbn in KL; lia] | reflexivity].
      - destruct pb as [|b pb'].
        + left. split; [reflexivity|]. cbn in KL. subst k. unfold wz. f_equal. lia.
        + right. split; [congruence|]. rewrite KL. unfold wz. rewrite !unsigned_lit by lia. split; lia. }
    eapply evt_mono.
    { eapply (mw_gen memcpy.memcpy_holds __errno_location.__errno_location_holds) with (lo := lo) (Fz := f) (fl := fl)
        (posw := wz pos) (lenw := wz len) (wendw := wz wend) (wposw := wz wpos) (wbasew := wz wbase) (pb := pb) (ds := ds);
      first [ (rewrite <- A0; symmetry; apply Z_to_bv_bv_unsigned) | eassumption
            | (unfold wz; rewrite !unsigned_lit by lia; lia) | lia | (unfold A_G_SAID; lia) ]. }
    intros ms' (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & m' & rw &
      flw' & wendw' & wposw' & wbasew' & posw' & lenw' & -> & MU' & WM' & MI' & ST' & C1 & C2 & C3 & C4 & I1 & I2).
    clear R1 R2 R3 AF1 AF3 ITOP EAF ERS ERG ERY Hfl Hom Hwin Hck Hst MW WIN.
    exists (mkR ra sp gp tp x0 x1 x2 s0 s1 rw x3 x4 x5 x6 x7 x8 x9 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x10 x11 x12 x13), m'.
    split; [reflexivity|].
    split; [apply regs_preserved_mkR|].
    assert (UP : bv_unsigned (wz pos) = pos) by (unfold wz; apply unsigned_lit; lia).
    assert (UL : bv_unsigned (wz len) = len) by (unfold wz; apply unsigned_lit; lia).
    rewrite UP, UL in *. rewrite KL in *. rewrite A2 in *.
    split.
    { cbv beta. rewrite mkR_errno. unfold mf_hdr, mf_said, link_mem.ERRNO_TP_OFF, MemFile.MF_ZEROED, SAID_SIZE, MWRITE_K.
      eapply munch_weaken; [|exact MU']. clear - Rpos. unfold sub_fp; cbn [outside fst snd]; intros; lia. }
    split; [exact WM'|]. split; [exact MI'|]. split; [exact ST'|].
    pose proof (wr_at_transport _ _ _ _ _ WRB WM') as WRB'.
    pose proof (wr_at_transport _ _ _ _ _ WRS WM') as WRS'.
    assert (PB' : bytes_at rsegs m' (f + 280) pb).
    { apply (bytes_at_transport rsegs _ m m' _ _ PBY MU').
      clear - AF2 MP ERF Rpos KR KL FQ Hf0 Rsp Rtp. cbn [disjoint_from]. unfold A_G_SAID.

      lia. }
    assert (AG : forall x, f <= x < f + MemFile.MF_ZEROED -> ~ dynw f x ->
                 YP09.mbyte rsegs m' x = YP09.mbyte rsegs m x).
    { intros x Hx Hd. unfold dynw, MemFile.MF_ZEROED in Hx, Hd. apply (munch_mbyte _ m m' x MU'); [lia|].
      clear - Hx Hd AF2 MP ERF Rpos Rsp Rtp FQ Hf0.
      cbn [outside]. unfold A_G_SAID. lia. }
    assert (VOM : YI04.val_mem rsegs m' (f + 136) 4 om).
    { apply (vm_munch _ m m' _ _ _ Vom MU'); [lia | cbn; lia |].
      intros j Hj. cbn in Hj. clear - Hj AF2 MP ERF Rpos Rsp Rtp FQ Hf0. cbn [outside]. unfold A_G_SAID. lia. }
    pose proof (cell4_vm _ _ _ C1) as VF'.
    assert (VF0 : YI04.val_mem rsegs m' (f + 0) 4 (bv_unsigned flw')) by (rewrite Z.add_0_r; exact VF').
    clear VF'.
    destruct (cells_vm88 _ _ _ _ _ C2) as (VWE' & VWP').
    replace (f + 32 + 8) with (f + 40) in VWP' by lia.
    pose proof (cell8_vm _ _ _ C3) as VWB'.
    unfold ccells in C4. destruct (cells_vm88 _ _ _ _ _ C4) as (VP' & VL').
    replace (f + 232 + 8) with (f + 240) in VL' by lia.
    pose proof (zr_word posw') as Rp'. pose proof (zr_word lenw') as Rl'. unfold inr64 in *.
    cbv zeta. unfold mw_n2. unfold mw_pos1. unfold mf_n1, SAID_SIZE.
    destruct (Z.lt_ge_cases (Z.min k (4096 - pos)) k) as [HN1 | HN1].
    + (* the flush passed the end *)
      destruct (I1 HN1) as (RW & -> & -> & -> & -> & UP' & UL' & BYS).
      rewrite !unsigned_lit in VF0, VWE', VWP', VWB' by lia.
      assert (MK' : memfile_k m' f 0).
      { apply (memfile_k_after m m' f k 36 0 0 0 (bv_unsigned posw') (bv_unsigned lenw') MK AG VF0
                 ltac:(right; reflexivity) VWE' VWP' VWB' ltac:(left; lia) VP' VL'); try assumption; lia. }
      split; [exact MK'|]. split; [exact PB'|].
      split; [|intros; lia].
      intros _. split; [exact RW|]. split; [|exact BYS].
      unfold mf_dyn, mf_fld. unfold MemFile.MF_COOKIE, SAID_SIZE.
      assert (LOR : Z.lor fl 32 = 36) by (destruct FL as [-> | ->]; reflexivity).
      rewrite LOR.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [exact VF0|]. split; [exact VOM|]. split; [exact VWE'|]. split; [exact VWP'|]. split; [exact VWB'|].
      rewrite <- UL', <- UP'. split; [exact VP' | exact VL'].
    + (* the flush stored all k *)
      assert (HN1' : Z.min k (4096 - pos) = k) by lia.
      destruct (I2 HN1') as (RW & UP' & UL' & BYS & J1 & J2).
      rewrite HN1' in *.
      destruct (Z.lt_ge_cases (Z.min (Z.of_nat (length ds)) (4096 - (pos + k))) (Z.of_nat (length ds))) as [HN2 | HN2].
      * destruct (J1 HN2) as (-> & -> & -> & ->).
        rewrite !unsigned_lit in VF0, VWE', VWP', VWB' by lia.
        assert (MK' : memfile_k m' f 0).
        { apply (memfile_k_after m m' f k 36 0 0 0 (bv_unsigned posw') (bv_unsigned lenw') MK AG VF0
                   ltac:(right; reflexivity) VWE' VWP' VWB' ltac:(left; lia) VP' VL'); try assumption; lia. }
        split; [exact MK'|]. split; [exact PB'|].
        split; [intros; lia|].
        intros _. split; [exact RW|].
        exists 36, 0, 0, 0.
        split.
        { unfold mf_dyn, mf_fld. unfold MemFile.MF_COOKIE, SAID_SIZE.
          split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
          split; [exact VF0|]. split; [exact VOM|]. split; [exact VWE'|]. split; [exact VWP'|]. split; [exact VWB'|].
          rewrite <- UL', <- UP'. split; [exact VP' | exact VL']. }
        split; [intros _; destruct FL as [-> | ->]; repeat split; reflexivity|].
        split; [intros; lia|].
        exact BYS.
      * destruct (J2 ltac:(lia)) as (-> & -> & -> & ->).
        unfold wz in VF0, VWE', VWP', VWB'. rewrite !unsigned_lit in VF0, VWE', VWP', VWB' by lia.
        assert (MK' : memfile_k m' f 0).
        { apply (memfile_k_after m m' f k fl wend wbase wbase (bv_unsigned posw') (bv_unsigned lenw') MK AG VF0
                   ltac:(exact FL) VWE' VWP' VWB'); try assumption; lia. }
        split; [exact MK'|]. split; [exact PB'|].
        split; [intros; lia|].
        intros _. split; [exact RW|].
        exists fl, wend, wbase, wbase.
        split.
        { unfold mf_dyn, mf_fld. unfold MemFile.MF_COOKIE, SAID_SIZE.
          split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
          split; [exact VF0|]. split; [exact VOM|]. split; [exact VWE'|]. split; [exact VWP'|]. split; [exact VWB'|].
          rewrite <- UL', <- UP'. split; [exact VP' | exact VL']. }
        split; [intros; lia|].
        split; [intros _; repeat split; reflexivity|].
        exact BYS.
Qed.

(* the flush __fseeko_unlocked (+0x70) and close_file make: f->write(f, 0, 0) *)
Lemma mwrite_flush : forall (f k fl om wend wpos wbase pos len : Z) (pb : list byte),
  leaf MWRITE MWRITE_K
    (fun regs m =>
       arg regs 0 = f /\ arg regs 1 = 0 /\ arg regs 2 = 0 /\
       memfile_k m f k /\ mf_dyn m f fl om wend wpos wbase pos len /\
       mf_pend_bytes m f pb /\ Z.of_nat (length pb) = k /\
       apart_frame regs MWRITE_K f MemFile.MF_BLOCK /\ apart_frame regs MWRITE_K A_G_SAID SAID_SIZE /\
       IMG_TOP <= spZ regs - MWRITE_K /\
       errno_ok regs m MWRITE_K f)
    (fun regs m => [mf_hdr f; mf_said; (errno_at regs, errno_at regs + 4)])
    (fun regs m regs' m' =>
       let n1 := mf_n1 k pos in
       memfile_k m' f 0 /\ mf_pend_bytes m' f pb /\
       bytes_at rsegs m' (A_G_SAID + pos) (firstn (Z.to_nat n1) pb) /\
       (n1 < k ->
          res regs' = 0 /\ mf_dyn m' f (Z.lor fl MemFile.F_ERR) om 0 0 0 (pos + n1) (Z.max len (pos + n1))) /\
       (n1 = k ->
          res regs' = 0 /\ mf_dyn m' f fl om wend wbase wbase (pos + k) (Z.max len (pos + k)))).
Proof.
  intros f k fl om wend wpos wbase pos len pb.
  unfold leaf. intros regs F fc m lo PRE MI ST LO SPH.
  destruct PRE as (A0 & A1 & A2 & MK & MD & PBY & KL & AF2 & AF3 & ITOP & EOK).
  pose proof EOK as (ERRW & _).
  pose proof ERRW as (E0 & E1 & _).
  pose proof MD as (_ & _ & _ & _ & _ & Rpos & Rlen & _).
  pose proof (memfile_k_at _ _ _ MK) as (Hf0 & _).
  eapply evt_mono.
  { apply (mwrite_proof f k fl om wend wpos wbase pos len pb [] regs F fc m lo); try assumption.
    split; [exact A0|]. split; [rewrite A2; reflexivity|]. split; [exact MK|]. split; [exact MD|].
    split; [exact PBY|]. split; [exact KL|]. rewrite A1. cbn [length Z.of_nat].
    split; [apply bytes_at_nil; lia|].
    split; [unfold rapart, A_G_SAID; lia|]. split; [unfold rapart; lia|]. split; [unfold rapart; lia|].
    split; [unfold apart_frame, IMG_TOP, MWRITE_K in *; lia|].
    split; [exact AF2|]. split; [exact AF3|]. split; [exact ITOP | exact EOK].
  }
  intros ms' (regs' & m' & E & RP & MU & WM & MI' & ST' & PO).
  exists regs', m'. split; [exact E|]. split; [exact RP|]. split; [exact MU|]. split; [exact WM|].
  split; [exact MI'|]. split; [exact ST'|].
  cbv zeta in PO |- *. unfold mw_n2 in PO. unfold mw_pos1 in PO. cbn [length Z.of_nat] in PO.
  destruct PO as (MK' & PB' & P1 & P2).
  split; [exact MK'|]. split; [exact PB'|].
  unfold mf_n1, SAID_SIZE in *.
  destruct (Z.lt_ge_cases (Z.min k (4096 - pos)) k) as [H|H].
  - destruct (P1 H) as (R & D & B). split; [exact B|].
    split; [intros _; split; assumption | intros; lia].
  - assert (H' : Z.min k (4096 - pos) = k) by lia.
    destruct (P2 H') as (R & fl' & wend' & wpos' & wbase' & D & _ & J & B).
    rewrite H' in *. change (Z.of_nat 0) with 0 in *. replace (Z.min 0 (4096 - (pos + k))) with 0 in * by lia.
    try rewrite Z.add_0_r in *. rewrite firstn_nil, app_nil_r in B.
    split.
    { rewrite <- KL, Nat2Z.id, firstn_all. exact B. }
    split; [intros; lia|].
    intros _. split; [exact R|].
    destruct (J eq_refl) as (-> & -> & -> & ->). exact D.
Qed.
