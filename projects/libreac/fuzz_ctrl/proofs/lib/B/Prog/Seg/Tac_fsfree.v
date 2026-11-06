(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 803 of its 886 lines of code are new or changed and 3770 lines of the source are left out. *)
(* The class-generic side-stack fact FSFREE of the fuzz_ctrl LLVMFuzzerTestOneInput slot proof (asan-ubsan,
   image B), and the lemmas that rebuild a callee's side-stack package from it. rule 24: no function proved.

   A callee that takes side-stack frames of the classes cs (reac_ctrl_build_as: [0; 1]; reac_ctrl_parse,
   reac_ctrl_identity_reply: [1]) asks at its call for the package
     FP.fp cs m tp FS (sp - K) sp W D /\ <callee>_tls m tp FS (sp - K) sp
   (lib/B/Prog/RcAsanFP.v, reac_ctrl_parse_c.v ...). Every part of it is a fact about the side stack FS (the word at
   tp), the thread cells asan_tls_cells names, and where the caller's writes W and data ranges D lie. FSFREE g fr m
   states those facts once, for the frame fr and the slot window [S - SLOT_STACK, S):
   - the base FS, its runtime state a_fs_ok, its placement (GT <= FS, page-aligned, in AppMem, below the slot
     window) and the bound FS + 6328320 <= fr (the side stack's metadata and the classes 0 .. 5 are below the frame);
   - one asan_tls_cells instance in m whose cells are apart from [FS, FS + FS_SIZE), the slot window and the frame,
     each cell range nonempty and in AppMem.
   No flag value is part of it: the frame-allocation contracts read the flags (each 0 or 1, a_fs_ok) and return 0
   when a class is full, so a package needs no free frame.

   FRA (and FRAH) imply FSFREE (fra_fsfree, frah_fsfree): the runtime invariant RT names the cells at fixed
   addresses (tp - 8, tp + 8, tp - 88, the TSD key, ...), and the allocator laws of AH pin the two pointers read out
   of memory (C at RT_TSDMAIN and T at C + 152, a_laws_thread; DB at tp + 8, a_laws_fs_state) and put their cells
   among the allocator's bytes or below stklo and outside FS (a_laws_not_owned, a_laws_fs_state). So every FRA cut
   carries FSFREE without a conjunct of its own, and a call site rebuilds its callee's package from FRA (fra_fp)
   instead of threading it cut by cut. fsfree_post carries FSFREE across a callee whose post has the fp form
   directly, and fp_post_fs_ok gives the side stack's state a_fs_ok after such a callee (for AH by
   AC.a_laws_fs_store). fra_rbe_tls gives RBE's thread-cell conjunct from FRA at any cut; fsfree_tls is the
   reference instance (prover a Theorem Labs lane's R12TLS) in that form. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState PropExec.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLay.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require RcAsanFP asan_stack_malloc_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_fs.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module FP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.RcAsanFP.
Module SMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_stack_malloc_c.
Module RLay := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcLay.

(* ==== The fact. *)
Definition FSFREE (g : ghost) (fr : Z) (m : word -> option byte) : Prop :=
  exists FS, word_mem rsegs m (AC.as_tp AC.ASYMS) FS /\ 0 <= FS < 2 ^ 64 /\ AC.a_fs_ok m FS /\
    AC.GT <= FS /\ FS mod 4096 = 0 /\ (forall a, FS <= a < FS + AC.FS_SIZE -> app_mem a) /\
    FS + AC.FS_SIZE <= g_S g - AF.SLOT_STACK /\ FS + 6328320 <= fr /\
    exists DT TS C T DB k,
      SMC.asan_tls_cells m (AC.as_tp AC.ASYMS) DT TS C T DB k /\
      FP.fp_dj [(FS, FS + AC.FS_SIZE); (g_S g - AF.SLOT_STACK, g_S g); (fr, fr + FRAME_BYTES)]
        (FP.fp_tls (AC.as_tp AC.ASYMS) DT TS C T DB k) /\
      Forall (fun r => fst r < snd r /\ forall x, fst r <= x < snd r -> app_mem x)
        (FP.fp_tls (AC.as_tp AC.ASYMS) DT TS C T DB k).

(* ==== Interval and byte helpers. *)
Lemma fsf_urange : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H. exact H. Qed.

Lemma fsf_mbyte_mrd : forall m a, mbyte rsegs m a = mrd rsegs m (wa a).
Proof.
  intros m a. unfold mbyte, mrd, wa. destruct (m (Z_to_bv 64 a)); [reflexivity|].
  unfold YK11.seg_rom, PropExec.seg_rom. reflexivity.
Qed.

Lemma fsf_ly_dj_by : forall a b c d, a < b -> c < d -> (forall x, a <= x < b -> c <= x < d -> False) ->
  RLay.ly_dj a b c d.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros a b c d H1 H2 H. unfold RLay.ly_dj.
  destruct (Z_le_gt_dec b c) as [E|E]; [left; exact E|].
  destruct (Z_le_gt_dec d a) as [E'|E']; [right; exact E'|].
  exfalso. apply (H (Z.max a c)); lia.
Qed.

Lemma fsf_ly_dj_sub_l : forall a b c d a' b', RLay.ly_dj a b c d -> a <= a' -> b' <= b -> RLay.ly_dj a' b' c d.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv. intros a b c d a' b' H H1 H2. unfold RLay.ly_dj in *. lia. Qed.

Lemma fsf_ly_dj_sym : forall a b c d, RLay.ly_dj a b c d -> RLay.ly_dj c d a b.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv. intros a b c d H. unfold RLay.ly_dj in *. lia. Qed.

Lemma fsf_dj_intro : forall W D, (forall w d, In w W -> In d D -> RLay.ly_dj (fst w) (snd w) (fst d) (snd d)) ->
  FP.fp_dj W D.
Proof.
  intros W D H. unfold FP.fp_dj. apply Forall_forall. intros w Hw. apply Forall_forall. intros d Hd.
  exact (H w d Hw Hd).
Qed.

Lemma fsf_dj_elim : forall W D w d, FP.fp_dj W D -> In w W -> In d D -> RLay.ly_dj (fst w) (snd w) (fst d) (snd d).
Proof.
  intros W D w d H Hw Hd. unfold FP.fp_dj in H. rewrite Forall_forall in H. pose proof (H w Hw) as H1.
  rewrite Forall_forall in H1. exact (H1 d Hd).
Qed.

(* A byte of a range of X is outside every range of L when fp_dj L X, and conversely. *)
Lemma fsf_dj_out : forall L X a b x, FP.fp_dj L X -> In (a, b) X -> a <= x < b -> Frame.outside L x.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros L. induction L as [|[lo hi] L IH]; intros X a b x H Hin Hx; cbn [Frame.outside]; [exact I|].
  unfold FP.fp_dj in H. apply Forall_cons_iff in H as [H1 H2]. split.
  - rewrite Forall_forall in H1. pose proof (H1 (a, b) Hin) as Hd. cbn [fst snd] in Hd. unfold RLay.ly_dj in Hd. lia.
  - exact (IH X a b x H2 Hin Hx).
Qed.

Lemma fsf_dj_out_r : forall L X a b x, FP.fp_dj L X -> In (a, b) L -> a <= x < b -> Frame.outside X x.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros L X a b x H Hin Hx. unfold FP.fp_dj in H. rewrite Forall_forall in H. pose proof (H _ Hin) as H1.
  cbn [fst snd] in H1. clear H Hin. induction X as [|[lo hi] X IH]; cbn [Frame.outside]; [exact I|].
  apply Forall_cons_iff in H1 as [H2 H3]. cbn [fst snd] in H2. unfold RLay.ly_dj in H2. split; [lia | exact (IH H3)].
Qed.

Lemma fsf_out_app : forall A C x, Frame.outside A x -> Frame.outside C x -> Frame.outside (A ++ C) x.
Proof.
  induction A as [|[lo hi] A IH]; intros C x HA HC; cbn [app Frame.outside] in *; [exact HC|].
  destruct HA as [H1 H2]. split; [exact H1 | exact (IH C x H2 HC)].
Qed.

(* A byte of the shadow of an application range is a shadow byte (so never an application byte). *)
Lemma fsf_sh_in : forall lo hi x, 0 <= lo -> (forall y, 8 * (lo / 8) <= y < hi -> app_mem y) ->
  shadow_addr lo <= x < shadow_addr hi -> in_shadow x.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros lo hi x Hlo Happ Hx.
  assert (Ey : shadow_addr (8 * (x - ASAN_K)) = x).
  { unfold shadow_addr. rewrite Z.mul_comm, Z.div_mul by lia. lia. }
  rewrite <- Ey. apply shadow_of_app, Happ.
  unfold shadow_addr in Hx. pose proof (Z.mul_div_le hi 8 ltac:(lia)). lia.
Qed.

(* The same for a window [lo, hi) of application bytes that need not start on a granule. *)
Lemma fsf_sh_in_win : forall lo hi x, 0 <= lo -> (forall a, lo <= a < hi -> app_mem a) ->
  shadow_addr lo <= x < shadow_addr hi -> in_shadow x.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros lo hi x Hlo Happ Hx.
  assert (Hlt : lo < hi).
  { destruct (Z_lt_le_dec lo hi) as [E|E]; [exact E|].
    pose proof (Z.div_le_mono hi lo 8 ltac:(lia) E). unfold shadow_addr in Hx. lia. }
  pose proof (Happ lo ltac:(lia)) as Hl.
  apply (fsf_sh_in lo hi x Hlo); [|exact Hx].
  intros y Hy. destruct (Z_lt_le_dec y lo) as [E|E]; [|apply Happ; lia].
  pose proof (Z.mul_div_le lo 8 ltac:(lia)).
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *.
  destruct Hl as [Hl|Hl]; [left; lia|right].
  assert (8 * (17594333495296 / 8) <= 8 * (lo / 8)) by (apply Z.mul_le_mono_nonneg_l; [lia | apply Z.div_le_mono; lia]).
  change (17594333495296 / 8) with 2199291686912 in *. lia.
Qed.

Lemma fsf_wm_mod : forall m a v, word_mem rsegs m a v -> word_mem rsegs m a (v mod 2 ^ 64).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros m a v H k Hk. rewrite (H k Hk). unfold le_byte.
  replace (8 * Z.of_nat 8) with 64 by reflexivity.
  rewrite Z.mod_mod by (apply Z.pow_nonzero; lia). reflexivity.
Qed.

Lemma fsf_wm_uniq : forall m a v v', word_mem rsegs m a v -> word_mem rsegs m a v' ->
  0 <= v < 2 ^ 64 -> 0 <= v' < 2 ^ 64 -> 0 <= a -> a + 8 <= 2 ^ 64 -> v = v'.
Proof.
  intros m a v v' H H' Hv Hv' Ha Hb.
  pose proof (word_mem_le8 rsegs m a v H Hv Ha Hb) as B1.
  pose proof (word_mem_le8 rsegs m a v' H' Hv' Ha Hb) as B2.
  assert (E : Z_to_bv 64 v = Z_to_bv 64 v').
  { apply (fl_le8_eq [] m m a _ _ B1 B2 (munch_refl [] m)). intros x _. exact I. }
  apply (f_equal bv_unsigned) in E. rewrite !MState.unsigned_lit in E by assumption. exact E.
Qed.

(* Present bytes make a byte list (a copy of image A's rd8_le8 helpers, reac_box_model_block.v). *)
Lemma fsf_bytes_of : forall m (P : byte -> Prop) k a, 0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat k -> exists b, mbyte rsegs m (a + i) = Some b /\ P b) ->
  exists bs, bytes_at rsegs m a bs /\ length bs = k /\ Forall P bs.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros m P k. induction k as [|k IH]; intros a Ha Hk H.
  - exists []. split; [|split; [reflexivity | constructor]].
    split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi. lia.
  - destruct (H 0 ltac:(lia)) as (b0 & Hb0 & HP0).
    destruct (IH (a + 1) ltac:(lia) ltac:(lia)) as (bs & (Ha1 & Hl1 & Hr) & Hlen & HP).
    { intros i Hi. replace (a + 1 + i) with (a + (i + 1)) by lia. apply H. lia. }
    exists (b0 :: bs). split; [|split; [cbn [length]; lia | constructor; assumption]].
    split; [lia|]. split; [cbn [length]; lia|].
    intros i Hi. destruct i as [|i].
    + cbn [nth_error]. rewrite <- fsf_mbyte_mrd. replace (a + Z.of_nat 0) with (a + 0) by lia. exact Hb0.
    + cbn [nth_error]. cbn [length] in Hi. rewrite <- (Hr i) by lia. f_equal. f_equal. lia.
Qed.

Lemma fsf_ble_nonneg : forall bs, 0 <= bytes_le_to_Z bs.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z]; [lia|].
  apply Z.lor_nonneg. split; [apply bv_unsigned_in_range | apply Z.shiftl_nonneg; exact IH].
Qed.

Lemma fsf_ble_cons : forall (b : byte) bs, bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros b bs. cbn [bytes_le_to_Z]. pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb.
  change (2 ^ Z.of_N 8) with 256 in Hb.
  pose proof (fsf_ble_nonneg bs) as Hr.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  assert (D : Z.land (bv_unsigned b) (bytes_le_to_Z bs * 256) = 0).
  { apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite <- (Z.mod_small (bv_unsigned b) (2 ^ 8)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
  rewrite <- Z.lxor_lor by exact D. rewrite Z.add_nocarry_lxor by exact D. reflexivity.
Qed.

Lemma fsf_le_bytes_to_Z : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes]. rewrite fsf_ble_cons.
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with 256 in Hb.
  pose proof (fsf_ble_nonneg bs) as Hr.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace ((bv_unsigned b + bytes_le_to_Z bs * 256) / 256) with (bytes_le_to_Z bs) by (Z.div_mod_to_equations; lia).
    exact IH.
Qed.

Lemma fsf_le8_of_bytes : forall bs, length bs = 8%nat -> le8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros bs Hl. rewrite <- store_bytes_8. cbn [width_bytes]. rewrite MState.unsigned_lit_wrap.
  rewrite Z_to_le_bytes_mod by (cbn; lia). rewrite <- Hl at 1. exact (fsf_le_bytes_to_Z bs).
Qed.

(* ==== The thread cells: two instances in one memory are the same (le8 / le4 determinism), and an instance
   moves across a run that writes none of its cells. *)
Lemma tls_uniq : forall m TP DT TS C T DB k DT' TS' C' T' DB' k',
  SMC.asan_tls_cells m TP DT TS C T DB k -> SMC.asan_tls_cells m TP DT' TS' C' T' DB' k' ->
  DT = DT' /\ TS = TS' /\ C = C' /\ T = T' /\ DB = DB' /\ k = k'.
Proof.
  intros m TP DT TS C T DB k DT' TS' C' T' DB' k' HA HB.
  destruct HA as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 &
    A18 & A19).
  destruct HB as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & B17 &
    B18 & B19).
  pose proof (munch_refl [] m) as MU.
  assert (EDT : DT = DT') by (apply (fl_le8_eq [] m m (TP - 8) DT DT' A3 B3 MU); intros; exact I).
  assert (Ek : k = k') by (apply (fl_le4_eq [] m m SMC.TSD_KEY k k' A6 B6 A7 B7 MU); intros; exact I).
  assert (ETS : TS = TS') by (apply (fl_le8_eq [] m m (TP - 88) TS TS' A8 B8 MU); intros; exact I).
  subst DT' k' TS'.
  assert (EC : C = C') by (apply (fl_le8_eq [] m m (bv_unsigned TS + 8 * k) C C' A9 B9 MU); intros; exact I).
  subst C'.
  assert (ET : T = T') by (apply (fl_le8_eq [] m m (bv_unsigned C + 152) T T' A10 B10 MU); intros; exact I).
  assert (EDB : DB = DB') by (apply (fl_le8_eq [] m m (TP + 8) DB DB' A17 B17 MU); intros; exact I).
  subst T' DB'. repeat split.
Qed.

Ltac fsf_inl := solve [cbn [FP.fp_tls In]; repeat (first [left; reflexivity | right])].

Lemma tls_keep : forall m m' W TP DT TS C T DB k,
  SMC.asan_tls_cells m TP DT TS C T DB k -> Frame.munch W m m' ->
  (forall r x, In r (FP.fp_tls TP DT TS C T DB k) -> fst r <= x < snd r -> Frame.outside W x) ->
  SMC.asan_tls_cells m' TP DT TS C T DB k.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros m m' W TP DT TS C T DB k HT MU HO.
  destruct HT as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 &
    A18 & A19).
  Local Ltac tk HO MU lo hi :=
    eapply fl_bytes; [eassumption | exact MU |
      let x := fresh "x" in let Hx := fresh "Hx" in
      intros x Hx; apply (HO (lo, hi) x); [fsf_inl |
        cbn [fst snd]; rewrite ?length_app, ?length_le8, ?length_le4 in Hx; cbn [length] in Hx; lia]].
  unfold SMC.asan_tls_cells.
  split; [tk HO MU SMC.TLS_INDEX (SMC.TLS_INDEX + 16)|].
  split; [tk HO MU SMC.REAL_TLS_GET_ADDR (SMC.REAL_TLS_GET_ADDR + 8)|].
  split; [tk HO MU (TP - 8) (TP + 16)|].
  split; [tk HO MU (bv_unsigned DT + 8) (bv_unsigned DT + 16)|].
  split; [tk HO MU SMC.TSD_KEY_INITED (SMC.TSD_KEY_INITED + 1)|].
  split; [exact A6|].
  split; [tk HO MU SMC.TSD_KEY (SMC.TSD_KEY + 4)|].
  split; [tk HO MU (TP - 88) (TP - 80)|].
  split; [tk HO MU (bv_unsigned TS + 8 * k) (bv_unsigned TS + 8 * k + 8)|].
  split; [tk HO MU (bv_unsigned C + 152) (bv_unsigned C + 160)|].
  split; [destruct A11 as (tb & te & A11); exists tb, te; tk HO MU (bv_unsigned T + 48) (bv_unsigned T + 64)|].
  split; [tk HO MU SMC.GOT_CF (SMC.GOT_CF + 8)|].
  split; [tk HO MU (SMC.CF + 137) (SMC.CF + 138)|].
  split; [tk HO MU SMC.GOT_VERBOSITY (SMC.GOT_VERBOSITY + 8)|].
  split; [tk HO MU SMC.VERBOSITY (SMC.VERBOSITY + 4)|].
  split; [tk HO MU SMC.DTLS_TPOFF (SMC.DTLS_TPOFF + 8)|].
  split; [tk HO MU (TP - 8) (TP + 16)|].
  split; [exact A18|].
  tk HO MU (bv_unsigned DB + 24) (bv_unsigned DB + 32).
Qed.

(* ==== Side-stack layout facts for the classes 0 .. 5. *)
Lemma fsf_pow : forall c, (c <= 5)%nat ->
  1 <= 2 ^ Z.of_nat c <= 32 /\ 2 ^ (15 - Z.of_nat c) = 2 * 2 ^ (14 - Z.of_nat c) /\
  2 ^ (14 - Z.of_nat c) * (64 * 2 ^ Z.of_nat c) = 2 ^ 20 /\ 512 <= 2 ^ (14 - Z.of_nat c) <= 16384.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv. intros c Hc. destruct c as [|[|[|[|[|[|c]]]]]]; [..|lia]; cbn; lia. Qed.

(* The ranges of fp_w1 FS c for c <= 5: the hint word, the flag bytes and the class frames lie in
   [FS, FS + 6328320); the fourth is the shadow of the class frames [lo, hi), lo a multiple of 8. *)
Lemma fsf_w1_parts : forall FS c f, 0 <= FS -> FS mod 8 = 0 -> (c <= 5)%nat -> In f (FP.fp_w1 FS c) ->
  fst f < snd f /\
  ((FS <= fst f /\ snd f <= FS + 6328320) \/
   (exists lo hi, FS <= lo /\ lo + 8 <= hi /\ hi <= FS + 6328320 /\ lo mod 8 = 0 /\
      fst f = shadow_addr lo /\ snd f = shadow_addr hi)).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros FS c f H0 H8 Hc Hf.
  destruct (fsf_pow c Hc) as (Hp & H15 & Hpq & Hq).
  assert (P20 : 2 ^ 20 = 1048576) by reflexivity.
  assert (P15 : 2 ^ 15 = 32768) by reflexivity.
  assert (Hc' : 0 <= Z.of_nat c <= 5) by lia.
  unfold FP.fp_w1, SMC.fs_hint, SMC.fs_flag, SMC.fs_frame, SMC.fs_M, SMC.fs_B in Hf.
  cbn [In] in Hf. destruct Hf as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd].
  - split; [lia | left; lia].
  - split; [lia | left; lia].
  - split; [lia | left; lia].
  - assert (Hlo8 : (FS + 36864 + Z.of_nat c * 2 ^ 20 + 0 * (64 * 2 ^ Z.of_nat c)) mod 8 = 0)
      by (Z.div_mod_to_equations; lia).
    split.
    + unfold shadow_addr. Z.div_mod_to_equations. lia.
    + right. exists (FS + 36864 + Z.of_nat c * 2 ^ 20 + 0 * (64 * 2 ^ Z.of_nat c)),
        (FS + 36864 + Z.of_nat c * 2 ^ 20 + 2 ^ (14 - Z.of_nat c) * (64 * 2 ^ Z.of_nat c)).
      split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hlo8|]. split; reflexivity.
Qed.

(* The class-c state the frame-allocation contracts read, from a_fs_ok. *)
Lemma fsf_cls : forall m FS c, (c <= 6)%nat -> AC.a_fs_ok m FS -> 0 <= FS -> FS + AC.FS_SIZE <= 2 ^ 64 ->
  FP.fp_cls m FS c.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros m FS c Hc Hok H0 Hsz. destruct Hok as (_ & _ & _ & Hhint & Hflag).
  assert (HSZ : AC.FS_SIZE = 11571200) by reflexivity.
  assert (P15 : 2 ^ 15 = 32768) by reflexivity.
  assert (Hc' : 0 <= Z.of_nat c <= 6) by lia.
  assert (Hq : 1 <= 2 ^ (14 - Z.of_nat c) /\ 2 ^ (15 - Z.of_nat c) = 2 * 2 ^ (14 - Z.of_nat c) /\
               2 ^ (14 - Z.of_nat c) <= 16384).
  { destruct c as [|[|[|[|[|[|[|c]]]]]]]; [..|lia]; cbn; lia. }
  destruct Hq as (Hq1 & Hq2 & Hq3).
  split; [exact Hc|].
  destruct (Hhint c ltac:(lia)) as (h & Hh).
  destruct (fsf_bytes_of m (fun b => b = Z_to_bv 8 0 \/ b = Z_to_bv 8 1) (Z.to_nat (SMC.fs_M c))
              (SMC.fs_flag FS c 0)) as (flags & Hfl & Hlen & HP).
  { unfold SMC.fs_flag. lia. }
  { unfold SMC.fs_flag, SMC.fs_M. rewrite Z2Nat.id by lia. lia. }
  { intros i Hi. unfold SMC.fs_M in Hi. rewrite Z2Nat.id in Hi by lia.
    replace (SMC.fs_flag FS c 0 + i) with (AC.a_fs_flag FS c i) by (unfold SMC.fs_flag, AC.a_fs_flag; lia).
    destruct (Hflag c i ltac:(lia) ltac:(unfold AC.a_fs_M; lia)) as [E|E];
      [exists (Z_to_bv 8 0); split; [exact E | left; reflexivity]
      |exists (Z_to_bv 8 1); split; [exact E | right; reflexivity]]. }
  exists (Z_to_bv 64 (h mod 2 ^ 64)), flags.
  split; [|split; [exact Hfl | split; [rewrite Hlen; unfold SMC.fs_M; rewrite Z2Nat.id by lia; reflexivity | exact HP]]].
  apply (word_mem_le8 rsegs m (SMC.fs_hint FS c) (h mod 2 ^ 64)).
  - exact (fsf_wm_mod m (AC.a_fs_hint FS c) h Hh).
  - apply Z.mod_pos_bound. lia.
  - unfold SMC.fs_hint. lia.
  - unfold SMC.fs_hint. lia.
Qed.

(* ==== FSFREE gives the package of any callee taking frames of classes cs (c <= 5) whose window [S0 - K, S0)
   (K >= 8) lies inside the slot window, whose write list W lies in the slot window, the frame or the frame's 392
   shadow bytes, and whose data ranges D lie in the image below GT, in the frame, or in application bytes outside
   FS (a live block: fra_fp). *)
Lemma fsfree_fp : forall g fr m cs S0 K W D,
  FSFREE g fr m ->
  (forall c, In c cs -> (c <= 5)%nat) ->
  8 <= K -> g_S g - AF.SLOT_STACK <= S0 - K -> S0 <= g_S g ->
  HIGHMEM_BEG <= g_S g - AF.SLOT_STACK -> g_S g <= APPMEM_END ->
  fr mod 8 = 0 -> (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
  (forall w, In w W ->
     (g_S g - AF.SLOT_STACK <= fst w /\ snd w <= g_S g) \/ (fr <= fst w /\ snd w <= fr + FRAME_BYTES) \/
     (Sfr fr <= fst w /\ snd w <= Sfr fr + FRAME_SHADOW)) ->
  (forall d, In d D ->
     snd d <= AC.GT \/ (fr <= fst d /\ snd d <= fr + FRAME_BYTES) \/
     (fst d < snd d /\ forall x, fst d <= x < snd d -> app_mem x /\ ~ AC.a_in_fs AC.ASYMS m x)) ->
  exists FS,
    FP.fp cs m (AC.as_tp AC.ASYMS) FS (S0 - K) S0 W D /\
    (forall DT TS C T DB k, SMC.asan_tls_cells m (AC.as_tp AC.ASYMS) DT TS C T DB k ->
       FP.fp_dj (FP.fp_tls (AC.as_tp AC.ASYMS) DT TS C T DB k)
         (FP.fp_w cs FS ++ [(shadow_addr (S0 - K), shadow_addr S0)])) /\
    FP.fp_dj [(fr, fr + FRAME_BYTES); (Sfr fr, Sfr fr + FRAME_SHADOW)] (FP.fp_w cs FS) /\
    SMC.fs_frame FS 1 (SMC.fs_M 1) <= fr.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr m cs S0 K W D
    (FS & Hwtp & HFSr & Hok & HGT & HAl & HFSapp & HFSend & Hfr & DT0 & TS0 & C0 & T0 & DB0 & k0 & HT0 & Hdj0 & Hap0)
    Hcs HK Hlo Hhi HHB HSE Hfr8 Hfapp HW HD.
  assert (HSZ : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HGTv : AC.GT = 0x5fe000) by reflexivity.
  assert (HHBv : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (HAEv : APPMEM_END = 140737488355328) by reflexivity.
  assert (HFS0 : 0 <= FS) by lia.
  assert (HFS8 : FS mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (Hfr0 : 0 <= fr) by (pose proof (Hfapp fr ltac:(lia)) as Ha; unfold app_mem in Ha; lia).
  assert (HSfr : Sfr fr + FRAME_SHADOW = shadow_addr (fr + FRAME_BYTES)) by (unfold Sfr, shadow_addr; Z.div_mod_to_equations; lia).
  assert (Hfsh : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> in_shadow x).
  { intros x Hx. apply (fsf_sh_in fr (fr + FRAME_BYTES) x Hfr0).
    - intros y Hy. apply Hfapp. assert (8 * (fr / 8) = fr) by (Z.div_mod_to_equations; lia). lia.
    - rewrite <- HSfr. unfold Sfr in Hx. exact Hx. }
  rewrite Forall_forall in Hap0.
  exists FS. split.
  { exists DT0, TS0, C0, T0, DB0, k0.
    split; [exact HT0|].
    split; [apply (word_mem_le8 rsegs m (AC.as_tp AC.ASYMS) FS Hwtp HFSr); unfold AC.as_tp, AC.ASYMS; cbn; lia|].
    split.
    { unfold SMC.fs_place. destruct Hok as (Hrw & _).
      split; [unfold AC.GT in HGT; lia|]. split; [exact HAl|]. split; [unfold SMC.ASAN_GT; lia|].
      split; [intros a Ha; apply HFSapp; unfold SMC.FS_SIZE in Ha; lia|].
      split; [lia|]. split; [unfold SMC.FS_SIZE; lia|].
      intros a Ha. destruct (Hrw a ltac:(unfold SMC.FS_SIZE in Ha; lia)) as (Hw & b & Hb).
      split; [exact Hw|]. exists b. rewrite <- fsf_mbyte_mrd. exact Hb. }
    split.
    { destruct Hok as (_ & H88 & _). apply (word_mem_le8 rsegs m (FS + 88) 20 H88); lia. }
    split.
    { destruct Hok as (_ & _ & H96 & _). split; [lia|]. split; [cbn [length]; lia|].
      intros i Hi. cbn [length] in Hi. destruct i as [|i]; [|lia]. cbn [nth_error].
      replace (FS + 96 + Z.of_nat 0) with (FS + 96) by lia. rewrite <- fsf_mbyte_mrd. exact H96. }
    split.
    { apply Forall_forall. intros c Hc. pose proof (Hcs c Hc) as Hc5. apply (fsf_cls m FS c); [lia | exact Hok | lia | lia]. }
    split; [unfold SMC.FS_SIZE; lia|].
    split; [intros a Ha; unfold app_mem; right; lia|].
    split.
    { apply fsf_dj_intro. intros w d Hw Hd. apply in_app_or in Hd.
      destruct (HW w Hw) as [Hwin | [Hwfr | Hwsh]].
      - destruct Hd as [Hd | [<- | []]].
        + apply (fsf_ly_dj_sub_l (g_S g - AF.SLOT_STACK) (g_S g)); [| lia | lia].
          exact (fsf_dj_elim _ _ _ _ Hdj0 (or_intror (or_introl eq_refl)) Hd).
        + cbn [fst snd]. unfold RLay.ly_dj, SMC.fs_frame. cbn [Z.of_nat]. right. lia.
      - destruct Hd as [Hd | [<- | []]].
        + apply (fsf_ly_dj_sub_l fr (fr + FRAME_BYTES)); [| lia | lia].
          exact (fsf_dj_elim _ _ _ _ Hdj0 (or_intror (or_intror (or_introl eq_refl))) Hd).
        + cbn [fst snd]. unfold RLay.ly_dj, SMC.fs_frame. cbn [Z.of_nat]. right. lia.
      - apply (fsf_ly_dj_sub_l (Sfr fr) (Sfr fr + FRAME_SHADOW)); [| lia | lia].
        destruct Hd as [Hd | [<- | []]].
        + destruct (Hap0 d Hd) as (Hdne & Hdapp).
          apply fsf_ly_dj_by; [lia | exact Hdne |]. intros x Hx1 Hx2.
          exact (app_not_shadow x (Hdapp x Hx2) (Hfsh x Hx1)).
        + cbn [fst snd]. unfold SMC.fs_frame. cbn [Z.of_nat].
          apply fsf_ly_dj_by; [lia | lia |]. intros x Hx1 Hx2.
          apply (app_not_shadow x); [apply HFSapp; lia | exact (Hfsh x Hx1)]. }
    { apply fsf_dj_intro. intros d f Hd Hf.
      apply in_flat_map in Hf. destruct Hf as (c & Hc & Hf).
      destruct (fsf_w1_parts FS c f HFS0 HFS8 (Hcs c Hc) Hf)
        as (Hfne & [Hpart | (lo & hi & Hlo' & Hlohi & Hhi' & Hlo8 & Ef1 & Ef2)]).
      - destruct (HD d Hd) as [HdGT | [Hdfr | (Hdne & Hdpt)]].
        + unfold RLay.ly_dj. left. lia.
        + unfold RLay.ly_dj. right. lia.
        + apply fsf_ly_dj_by; [lia | lia |]. intros x Hx1 Hx2. apply (proj2 (Hdpt x Hx1)).
          exists FS. split; [exact HFSr|]. split; [exact Hwtp | lia].
      - assert (E8 : 8 * (lo / 8) = lo) by (pose proof (Z.div_mod lo 8 ltac:(lia)); lia).
        assert (Hshf : forall x, fst f <= x < snd f -> in_shadow x).
        { intros x Hx. rewrite Ef1, Ef2 in Hx. apply (fsf_sh_in lo hi x); [lia | | exact Hx].
          intros y Hy. apply HFSapp. lia. }
        destruct (HD d Hd) as [HdGT | [Hdfr | (Hdne & Hdpt)]].
        + unfold RLay.ly_dj. left. rewrite Ef1. unfold shadow_addr, ASAN_K.
          assert (0 <= lo / 8) by (apply Z.div_pos; lia). lia.
        + apply (fsf_ly_dj_sub_l fr (fr + FRAME_BYTES)); [| lia | lia].
          apply fsf_ly_dj_by; [lia | lia |]. intros x Hx1 Hx2.
          exact (app_not_shadow x (Hfapp x Hx1) (Hshf x Hx2)).
        + apply fsf_ly_dj_by; [lia | lia |]. intros x Hx1 Hx2.
          exact (app_not_shadow x (proj1 (Hdpt x Hx1)) (Hshf x Hx2)). } }
  split.
  { intros DT TS C T DB k HT.
    destruct (tls_uniq m _ _ _ _ _ _ _ _ _ _ _ _ _ HT0 HT) as (<- & <- & <- & <- & <- & <-).
    apply fsf_dj_intro. intros r f Hr Hf. destruct (Hap0 r Hr) as (Hrne & Hrapp).
    apply in_app_or in Hf. destruct Hf as [Hf | [<- | []]].
    - apply in_flat_map in Hf. destruct Hf as (c & Hc & Hf).
      destruct (fsf_w1_parts FS c f HFS0 HFS8 (Hcs c Hc) Hf)
        as (Hfne & [Hpart | (lo & hi & Hlo' & Hlohi & Hhi' & Hlo8 & Ef1 & Ef2)]).
      + apply fsf_ly_dj_sym. apply (fsf_ly_dj_sub_l FS (FS + AC.FS_SIZE)); [| lia | lia].
        exact (fsf_dj_elim _ _ _ _ Hdj0 (or_introl eq_refl) Hr).
      + assert (E8 : 8 * (lo / 8) = lo) by (pose proof (Z.div_mod lo 8 ltac:(lia)); lia).
        apply fsf_ly_dj_by; [exact Hrne | lia |]. intros x Hx1 Hx2.
        apply (app_not_shadow x (Hrapp x Hx1)). rewrite Ef1, Ef2 in Hx2.
        apply (fsf_sh_in lo hi x); [lia | | exact Hx2]. intros y Hy. apply HFSapp. lia.
    - cbn [fst snd]. apply fsf_ly_dj_by; [exact Hrne | unfold shadow_addr; Z.div_mod_to_equations; lia |].
      intros x Hx1 Hx2. apply (app_not_shadow x (Hrapp x Hx1)).
      apply (fsf_sh_in_win (S0 - K) S0 x); [lia | | exact Hx2].
      intros a Ha. unfold app_mem. right. lia. }
  split.
  { apply fsf_dj_intro. intros w f Hw Hf. apply in_flat_map in Hf. destruct Hf as (c & Hc & Hf).
    destruct (fsf_w1_parts FS c f HFS0 HFS8 (Hcs c Hc) Hf)
      as (Hfne & [Hpart | (lo & hi & Hlo' & Hlohi & Hhi' & Hlo8 & Ef1 & Ef2)]);
      cbn [In] in Hw; destruct Hw as [<- | [<- | []]]; cbn [fst snd].
    - unfold RLay.ly_dj. right. lia.
    - apply fsf_ly_dj_by; [lia | lia |]. intros x Hx1 Hx2.
      apply (app_not_shadow x); [apply HFSapp; lia | exact (Hfsh x Hx1)].
    - assert (E8 : 8 * (lo / 8) = lo) by (pose proof (Z.div_mod lo 8 ltac:(lia)); lia).
      apply fsf_ly_dj_by; [lia | lia |]. intros x Hx1 Hx2.
      apply (app_not_shadow x (Hfapp x Hx1)). rewrite Ef1, Ef2 in Hx2.
      apply (fsf_sh_in lo hi x); [lia | intros y Hy; apply HFSapp; lia | exact Hx2].
    - unfold RLay.ly_dj. right. rewrite Ef2. unfold Sfr, shadow_addr.
      pose proof (Z.div_le_mono hi fr 8 ltac:(lia) ltac:(lia)). lia. }
  unfold SMC.fs_frame, SMC.fs_M, SMC.fs_B. cbn. lia.
Qed.

(* ==== After a callee whose post has the fp form, the side stack's state is a_fs_ok again: the header word and
   byte and the class-cs hint / flag cells are the ones the post's fp states; every other metadata cell is
   outside the run's writes. With AC.a_laws_fs_store this re-establishes AH. *)
Lemma fsf_flag_apart : forall FS c c' j, (c <= 10)%nat -> (c' <= 5)%nat -> c <> c' -> 0 <= j < AC.a_fs_M c ->
  ~ (SMC.fs_flag FS c' 0 <= AC.a_fs_flag FS c j < SMC.fs_flag FS c' 0 + SMC.fs_M c').
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros FS c c' j Hc Hc' Hne Hj.
  unfold SMC.fs_flag, SMC.fs_M, AC.a_fs_flag, AC.a_fs_M in *.
  assert (S1 : 2 ^ (15 - Z.of_nat c) = 2 * 2 ^ (14 - Z.of_nat c)).
  { replace (15 - Z.of_nat c) with (Z.succ (14 - Z.of_nat c)) by lia. rewrite Z.pow_succ_r by lia. reflexivity. }
  assert (S2 : 2 ^ (15 - Z.of_nat c') = 2 * 2 ^ (14 - Z.of_nat c')).
  { replace (15 - Z.of_nat c') with (Z.succ (14 - Z.of_nat c')) by lia. rewrite Z.pow_succ_r by lia. reflexivity. }
  destruct (Nat.lt_total c c') as [Hlt | [Heq | Hgt]]; [| exfalso; exact (Hne Heq) |].
  - assert (2 ^ (15 - Z.of_nat c') <= 2 ^ (14 - Z.of_nat c)) by (apply Z.pow_le_mono_r; lia). lia.
  - assert (2 ^ (15 - Z.of_nat c) <= 2 ^ (14 - Z.of_nat c')) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma fp_post_fs_ok : forall m m' cs TP FS lo hi W D Wall,
  (forall c, In c cs -> (c <= 5)%nat) ->
  AC.a_fs_ok m FS -> 0 <= FS -> FS + AC.FS_SIZE <= 2 ^ 64 ->
  FP.fp cs m' TP FS lo hi W D ->
  Frame.munch Wall m m' -> Frame.wmono rsegs m m' ->
  (forall q, FS <= q < FS + 36864 ->
     (forall c, In c cs -> ~ (SMC.fs_hint FS c <= q < SMC.fs_hint FS c + 8) /\
                          ~ (SMC.fs_flag FS c 0 <= q < SMC.fs_flag FS c 0 + SMC.fs_M c)) ->
     Frame.outside Wall q) ->
  AC.a_fs_ok m' FS.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros m m' cs TP FS lo hi W D Wall Hcs Hok H0 Hsz Hfp MU WM Hkeep.
  destruct Hok as (P1 & P2 & P3 & P4 & P5).
  destruct Hfp as (DT & TS & C & T & DB & k & _ & _ & HP & H88 & H96 & HCL & _).
  assert (HSZ : AC.FS_SIZE = 11571200) by reflexivity.
  assert (P15 : 2 ^ 15 = 32768) by reflexivity.
  unfold SMC.fs_place in HP. destruct HP as (_ & _ & _ & _ & (_ & _ & Hstk)).
  rewrite Forall_forall in HCL.
  (* a hint cell of a class outside cs, or a flag cell of such a class, is in the header and is none of the cs
     classes' hint / flag cells *)
  assert (Hcs' : forall c c', In c' cs -> ~ In c cs -> c <> c').
  { intros c c' Hin Hnin E. subst. exact (Hnin Hin). }
  split.
  { intros a Ha. split; [exact (WM _ (proj1 (P1 a Ha)))|].
    destruct (Hstk a ltac:(unfold SMC.FS_SIZE; lia)) as (_ & b & Hb). exists b. rewrite fsf_mbyte_mrd. exact Hb. }
  split.
  { pose proof (bytes_at_le8_word rsegs m' (FS + 88) _ H88) as Hw. rewrite MState.unsigned_lit in Hw by lia.
    exact Hw. }
  split.
  { destruct H96 as (_ & _ & H). pose proof (H 0%nat ltac:(cbn; lia)) as E. cbn [nth_error] in E.
    rewrite fsf_mbyte_mrd. replace (FS + 96) with (FS + 96 + Z.of_nat 0) by lia. exact E. }
  split.
  { intros c Hc. destruct (in_dec Nat.eq_dec c cs) as [Hin | Hnin].
    - destruct (HCL c Hin) as (_ & h & flags & Hh & _).
      exists (bv_unsigned h). exact (bytes_at_le8_word rsegs m' _ h Hh).
    - destruct (P4 c Hc) as (h & Hh). exists h.
      apply (kb_word_munch rsegs m m' Wall _ h Hh MU). intros k0 Hk0.
      split; [unfold AC.a_fs_hint; lia|].
      apply Hkeep; [unfold AC.a_fs_hint; lia|]. intros c' Hc'.
      pose proof (Hcs' c c' Hc' Hnin) as Hne. pose proof (Hcs c' Hc') as Hc5.
      destruct (fsf_pow c' Hc5) as (_ & H15 & _ & Hq).
      unfold SMC.fs_hint, SMC.fs_flag, SMC.fs_M, AC.a_fs_hint. split; lia. }
  { intros c j Hc Hj. destruct (in_dec Nat.eq_dec c cs) as [Hin | Hnin].
    - destruct (HCL c Hin) as (_ & h & flags & _ & Hfl & Hlen & HPf).
      destruct Hfl as (_ & _ & Hr).
      assert (Hj' : (Z.to_nat j < length flags)%nat) by (unfold AC.a_fs_M in Hj; unfold SMC.fs_M in Hlen; lia).
      pose proof (Hr (Z.to_nat j) Hj') as E.
      destruct (nth_error flags (Z.to_nat j)) as [b|] eqn:Eb; [|apply nth_error_None in Eb; lia].
      rewrite Forall_forall in HPf. pose proof (HPf b (nth_error_In _ _ Eb)) as Hb.
      replace (SMC.fs_flag FS c 0 + Z.of_nat (Z.to_nat j)) with (AC.a_fs_flag FS c j) in E
        by (unfold SMC.fs_flag, AC.a_fs_flag; lia).
      rewrite fsf_mbyte_mrd, E. destruct Hb as [-> | ->]; [left | right]; reflexivity.
    - pose proof (Tac_fs.a_fs_flag_range FS c j Hc Hj) as Hrng.
      assert (Hx : 0 <= AC.a_fs_flag FS c j < 2 ^ 64) by lia.
      unfold mbyte. rewrite (MU (Z_to_bv 64 (AC.a_fs_flag FS c j))); [exact (P5 c j Hc Hj)|].
      rewrite MState.unsigned_lit by exact Hx.
      apply Hkeep; [lia|]. intros c' Hc'.
      pose proof (Hcs' c c' Hc' Hnin) as Hne. pose proof (Hcs c' Hc') as Hc5.
      split.
      { unfold SMC.fs_hint, AC.a_fs_flag.
        assert (2 ^ (15 - Z.of_nat c) <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia). lia. }
      exact (fsf_flag_apart FS c c' j Hc Hc5 Hne Hj). }
Qed.

(* A byte of the side stack's header that is no class-cs hint / flag cell is outside fp_w cs FS. *)
Lemma fsf_out_fpw : forall cs FS q, (forall c, In c cs -> (c <= 5)%nat) -> 0 <= FS -> FS mod 8 = 0 ->
  FS <= q < FS + 36864 -> (forall a, FS <= a < FS + AC.FS_SIZE -> app_mem a) ->
  (forall c, In c cs -> ~ (SMC.fs_hint FS c <= q < SMC.fs_hint FS c + 8) /\
                       ~ (SMC.fs_flag FS c 0 <= q < SMC.fs_flag FS c 0 + SMC.fs_M c)) ->
  Frame.outside (FP.fp_w cs FS) q.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros cs. induction cs as [|c cs IH]; intros FS q Hcs H0 H8 Hq Happ Hx; [exact I|].
  assert (HSZ : AC.FS_SIZE = 11571200) by reflexivity.
  change (FP.fp_w (c :: cs) FS) with (FP.fp_w1 FS c ++ FP.fp_w cs FS).
  apply fsf_out_app.
  - pose proof (Hcs c (or_introl eq_refl)) as Hc5.
    destruct (Hx c (or_introl eq_refl)) as (Hnh & Hnf).
    cbn [FP.fp_w1 Frame.outside]. split; [exact Hnh|]. split; [exact Hnf|].
    destruct (fsf_pow c Hc5) as (Hpw & H15 & Hpq & Hqw).
    assert (P20 : 2 ^ 20 = 1048576) by reflexivity.
    assert (Elo : SMC.fs_frame FS c 0 = FS + 36864 + Z.of_nat c * 1048576)
      by (unfold SMC.fs_frame, SMC.fs_B; lia).
    assert (Ehi : SMC.fs_frame FS c (SMC.fs_M c) = FS + 36864 + Z.of_nat c * 1048576 + 1048576)
      by (unfold SMC.fs_frame, SMC.fs_M, SMC.fs_B; lia).
    rewrite Elo, Ehi.
    split; [lia|].
    split; [|exact I]. intros Hin.
    assert (Hlo8 : (FS + 36864 + Z.of_nat c * 1048576) mod 8 = 0) by (Z.div_mod_to_equations; lia).
    assert (E8 : 8 * ((FS + 36864 + Z.of_nat c * 1048576) / 8) = FS + 36864 + Z.of_nat c * 1048576)
      by (pose proof (Z.div_mod (FS + 36864 + Z.of_nat c * 1048576) 8 ltac:(lia)); lia).
    apply (app_not_shadow q (Happ q ltac:(lia))).
    apply (fsf_sh_in (FS + 36864 + Z.of_nat c * 1048576) (FS + 36864 + Z.of_nat c * 1048576 + 1048576) q);
      [lia | intros y Hy; apply Happ; lia | exact Hin].
  - apply IH; auto. intros c' Hc'. apply Hcs. right. exact Hc'.
    intros c' Hc'. apply Hx. right. exact Hc'.
Qed.

(* FSFREE across a callee whose pre and post have the fp form: the callee's write list is Wx (inside its W),
   the class-cs side-stack bytes and the shadow of its window; its pre puts its W apart from the thread cells and
   the side stack's header, its tls premise puts the rest apart from the thread cells, so the thread cells and
   the tp word are kept, and its post's fp gives the side stack's state (fp_post_fs_ok). *)
Lemma fsfree_post : forall g fr m m' cs FS lo hi W D Wx,
  FSFREE g fr m ->
  (forall c, In c cs -> (c <= 5)%nat) ->
  FP.fp cs m (AC.as_tp AC.ASYMS) FS lo hi W D ->
  (forall DT TS C T DB k, SMC.asan_tls_cells m (AC.as_tp AC.ASYMS) DT TS C T DB k ->
     FP.fp_dj (FP.fp_tls (AC.as_tp AC.ASYMS) DT TS C T DB k)
       (FP.fp_w cs FS ++ [(shadow_addr lo, shadow_addr hi)])) ->
  Frame.munch (Wx ++ FP.fp_w cs FS ++ [(shadow_addr lo, shadow_addr hi)]) m m' -> Frame.sub_fp Wx W ->
  Frame.wmono rsegs m m' ->
  FP.fp cs m' (AC.as_tp AC.ASYMS) FS lo hi W D ->
  FSFREE g fr m'.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr m m' cs FS lo hi W D Wx
    (FS0 & Hwtp & HFSr & Hok & HGT & HAl & HFSapp & HFSend & Hfr & DT0 & TS0 & C0 & T0 & DB0 & k0 & HT0 & Hdj0 & Hap0)
    Hcs Hpre Htls MU Hsub WM Hpost.
  assert (HSZ : AC.FS_SIZE = 11571200) by reflexivity.
  pose proof Hpre as (DT1 & TS1 & C1 & T1 & DB1 & k1 & HT1 & HTP1 & HP1 & _ & _ & _ & HFSlo & Happw & HWdj & _).
  destruct (tls_uniq m _ _ _ _ _ _ _ _ _ _ _ _ _ HT1 HT0) as (-> & -> & -> & -> & -> & ->).
  (* the pre's side stack is FSFREE's *)
  destruct HP1 as (HFSpos & _ & _ & _ & (_ & HFSb & _)).
  assert (EFS : FS0 = FS).
  { apply (fsf_wm_uniq m (AC.as_tp AC.ASYMS)); [exact Hwtp | | exact HFSr | unfold SMC.FS_SIZE in HFSb; lia
      | unfold AC.as_tp, AC.ASYMS; cbn; lia | unfold AC.as_tp, AC.ASYMS; cbn; lia].
    pose proof (bytes_at_le8_word rsegs m _ _ HTP1) as Hw. rewrite MState.unsigned_lit in Hw by (unfold SMC.FS_SIZE in HFSb; lia).
    exact Hw. }
  subst FS0.
  assert (HFS8 : FS mod 8 = 0) by (Z.div_mod_to_equations; lia).
  set (Wall := Wx ++ FP.fp_w cs FS ++ [(shadow_addr lo, shadow_addr hi)]).
  (* every byte of a thread cell is outside the run's writes *)
  assert (OUTT : forall r x, In r (FP.fp_tls (AC.as_tp AC.ASYMS) DT0 TS0 C0 T0 DB0 k0) -> fst r <= x < snd r ->
                   Frame.outside Wall x).
  { intros [a b] x Hr Hx. cbn [fst snd] in Hx. apply fsf_out_app.
    - apply Hsub. apply (fsf_dj_out W _ a b x HWdj); [apply in_or_app; left; exact Hr | exact Hx].
    - exact (fsf_dj_out_r _ _ a b x (Htls _ _ _ _ _ _ HT0) Hr Hx). }
  exists FS. split.
  { apply (kb_word_munch rsegs m m' Wall _ FS Hwtp MU). intros k Hk.
    split; [unfold AC.as_tp, AC.ASYMS; cbn; lia|].
    apply (OUTT (AC.as_tp AC.ASYMS - 8, AC.as_tp AC.ASYMS + 16)); [fsf_inl | cbn [fst snd]; lia]. }
  split; [exact HFSr|].
  split.
  { assert (HFSb' : FS + AC.FS_SIZE <= 2 ^ 64) by (unfold SMC.FS_SIZE in HFSb; lia).
    apply (fp_post_fs_ok m m' cs (AC.as_tp AC.ASYMS) FS lo hi W D Wall Hcs Hok ltac:(lia) HFSb' Hpost MU WM).
    intros q Hq Hx. apply fsf_out_app; [|apply fsf_out_app].
    - apply Hsub. apply (fsf_dj_out W _ FS (SMC.fs_frame FS 0 0) q HWdj).
      + apply in_or_app. right. left. reflexivity.
      + unfold SMC.fs_frame. cbn [Z.of_nat]. lia.
    - apply fsf_out_fpw; auto; lia.
    - cbn [Frame.outside]. split; [|exact I]. intros Hin.
      apply (app_not_shadow q (HFSapp q ltac:(lia))).
      apply (fsf_sh_in_win lo hi q); [unfold SMC.FS_SIZE in HFSlo; lia | exact Happw | exact Hin]. }
  split; [exact HGT|]. split; [exact HAl|]. split; [exact HFSapp|]. split; [exact HFSend|]. split; [exact Hfr|].
  exists DT0, TS0, C0, T0, DB0, k0.
  split; [exact (tls_keep m m' Wall _ _ _ _ _ _ _ HT0 MU OUTT)|].
  split; [exact Hdj0 | exact Hap0].
Qed.

(* The reference thread-cell instance in prover a Theorem Labs lane's R12TLS form. *)
Lemma fsfree_tls : forall g fr m, FSFREE g fr m ->
  exists DT TS C T DB k, SMC.asan_tls_cells m (AC.as_tp AC.ASYMS) DT TS C T DB k /\
    FP.fp_dj [(g_S g - AF.SLOT_STACK, g_S g); (fr, fr + FRAME_BYTES)] (FP.fp_tls (AC.as_tp AC.ASYMS) DT TS C T DB k).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr m (FS & _ & _ & _ & _ & _ & _ & _ & _ & DT & TS & C & T & DB & k & HT & Hdj & _).
  exists DT, TS, C, T, DB, k. split; [exact HT|].
  apply fsf_dj_intro. intros w d Hw Hd. apply (fsf_dj_elim _ _ _ _ Hdj); [|exact Hd]. cbn [In] in *. tauto.
Qed.

(* ==== The facts of the generated laws (lib/B/Contract.v, generation N.1b) that fs_tls_core reads, each by its
   statement (a Theorem Labs lane 15:18Z: a generated conjunction is never destructed by position at a use; the twin of a Theorem Labs lane's
   thr_fields, fuzz_manifest's lib/B/SlotTies.v (a version not in this delivery; from a working branch 3d75efd5ce9)). Each field is matched
   to a conjunct of AC.a_laws_thread / AC.a_laws_fs_state by `eassumption`, so a conjunct that a later generation adds
   or moves does not change these lemmas or their users. The fields that fix an existential come first. *)
Record fsf_thr_fields (API : AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT) (H : list (Z * Z))
    (mem : word -> option byte) (md : Model) (C T : Z) : Prop := {
  fthr_tsd_owned : forall i, 0 <= i < 8 -> AC.aa_owned AC.ASYMS AsanRTInv.RT API H mem md (RT_TSDMAIN + i);
  fthr_tsd_word : word_mem rsegs mem RT_TSDMAIN C;
  fthr_thr_word : word_mem rsegs mem (C + 152) T;
  fthr_tsd_range : 0 < C < 2 ^ 64;
  fthr_thr_range : 0 < T < 2 ^ 64;
  fthr_thr_cell : forall i, 0 <= i < 8 ->
    AC.aa_owned AC.ASYMS AsanRTInv.RT API H mem md (C + 152 + i) /\ app_mem (C + 152 + i);
  fthr_t48 : forall i, 0 <= i < 16 ->
    AC.aa_owned AC.ASYMS AsanRTInv.RT API H mem md (T + 48 + i) /\ exists b, mbyte rsegs mem (T + 48 + i) = Some b }.

Lemma fsf_thread_fields : forall API H mem md, AC.aa_AH AC.ASYMS AsanRTInv.RT API H mem md ->
  exists C T, fsf_thr_fields API H mem md C T.
Proof.
  intros API H mem md HAH.
  decompose [and ex] (AC.a_laws_thread _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT API) H mem md HAH).
  do 2 eexists. constructor; first [eassumption | split; eassumption].
Qed.

Record fsf_fs_fields (API : AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT) (mem : word -> option byte) (md : Model)
    (FS DB : Z) : Prop := {
  ffs_ok : AC.a_fs_ok mem FS;
  ffs_db_word : word_mem rsegs mem (AC.as_tp AC.ASYMS + 8) DB;
  ffs_db_range : 0 <= DB < 2 ^ 64;
  ffs_db_nz : DB <> 0;
  ffs_db24 : word_mem rsegs mem (DB + 24) (AC.as_tp AC.ASYMS);
  ffs_db_cells : forall a, DB + 24 <= a < DB + 32 ->
    app_mem a /\ a < AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md /\ ~ AC.a_in_fs AC.ASYMS mem a;
  ffs_t48_app : forall C T, word_mem rsegs mem RT_TSDMAIN C -> 0 <= C < 2 ^ 64 -> word_mem rsegs mem (C + 152) T ->
    0 <= T < 2 ^ 64 -> forall i, 0 <= i < 16 -> app_mem (T + 48 + i) }.

Lemma fsf_fs_state_fields : forall API H mem md FS, AC.aa_AH AC.ASYMS AsanRTInv.RT API H mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 -> exists DB, fsf_fs_fields API mem md FS DB.
Proof.
  intros API H mem md FS HAH Hw Hr.
  decompose [and ex] (AC.a_laws_fs_state _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT API) H mem md FS HAH Hw Hr).
  eexists. constructor;
    first [ eassumption | split; eassumption
          | intros a Ha; match goal with Hx : forall a, _ -> app_mem a /\ _ |- _ =>
              let Hc := fresh "Hc" in pose proof (Hx a Ha) as Hc; decompose [and] Hc; repeat split; assumption end ].
Qed.

(* ==== FRA / FRAH imply FSFREE. *)
Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.

(* The canonical thread-cell instance of a state with RT and AH: DT = tp + 32, TS = RT_TSDMAIN, k = 0 (RT's
   cells), C at RT_TSDMAIN and T at C + 152 (a_laws_thread), DB at tp + 8 (RT, a_laws_fs_state). Each cell range
   is an image range below GT, or its bytes are application bytes outside FS and below stklo (C + 152 and T + 48
   are the allocator's: a_laws_not_owned; DB + 24: a_laws_fs_state). *)
Lemma fs_tls_core : forall H sp mem md,
  AsanRTInv.RT sp mem md -> AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  exists DT TS C T DB k,
    SMC.asan_tls_cells mem (AC.as_tp AC.ASYMS) DT TS C T DB k /\
    forall r, In r (FP.fp_tls (AC.as_tp AC.ASYMS) DT TS C T DB k) ->
      fst r < snd r /\
      ((0 <= fst r /\ snd r <= AC.GT) \/
       (forall x, fst r <= x < snd r -> app_mem x /\ ~ AC.a_in_fs AC.ASYMS mem x /\
          ~ (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= x < APPMEM_END))).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros H sp mem md HRT HAH.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  destruct HRT as (HC & HSW & HO & HCF & HU & HR & HI & HX & HFS).
  destruct HFS as (F1 & F2 & F3 & F4 & (FSw & F5 & F5v) & (DBw & F6 & F6nz & F6app)).
  destruct HU as (U1 & U2 & U3 & U4 & c & U5).
  destruct HCF as (CF1 & CF2 & CF3 & CF4 & CF5 & CF6 & CF7 & CF8).
  destruct HO as (O1 & O2 & O3 & O4).
  assert (ETP : AC.as_tp AC.ASYMS = RT_TP) by reflexivity.
  assert (Hwtp : word_mem rsegs mem (AC.as_tp AC.ASYMS) (bv_unsigned FSw))
    by (rewrite ETP; exact (bytes_at_le8_word rsegs mem RT_TP FSw F5)).
  pose proof (fsf_urange FSw) as HFSr.
  destruct (fsf_fs_state_fields (APIf rc) H mem md (bv_unsigned FSw) HAH Hwtp HFSr)
    as (DB0 & [Hok HDB0w HDB0r HDB0nz HDB24 HDBpl HT48app]).
  destruct (fsf_thread_fields (APIf rc) H mem md HAH) as (C0 & T0 & [Hown HC0 HT0 HC0r HT0r HC152 HT48]).
  pose proof (lw_not_owned (APIf rc)) as NOWN.
  assert (EC : C0 = bv_unsigned c).
  { apply (fsf_wm_uniq mem RT_TSDMAIN); [exact HC0 | exact (bytes_at_le8_word rsegs mem RT_TSDMAIN c U5) | lia
      | apply fsf_urange | unfold RT_TSDMAIN; lia | unfold RT_TSDMAIN; lia]. }
  subst C0.
  assert (EDB : DB0 = bv_unsigned DBw).
  { apply (fsf_wm_uniq mem (AC.as_tp AC.ASYMS + 8)); [exact HDB0w | | exact HDB0r | apply fsf_urange
      | rewrite ETP; unfold RT_TP; lia | rewrite ETP; unfold RT_TP; lia].
    rewrite ETP. exact (bytes_at_le8_word rsegs mem (RT_TP + 8) DBw F6). }
  subst DB0.
  assert (Hap48 : forall i, 0 <= i < 16 -> app_mem (T0 + 48 + i))
    by exact (HT48app (bv_unsigned c) T0 HC0 ltac:(lia) HT0 ltac:(lia)).
  pose proof (Hap48 15 ltac:(lia)) as Hap15.
  pose proof (HC152 7 ltac:(lia)) as (_ & HC7).
  pose proof (HDBpl (bv_unsigned DBw + 31) ltac:(lia)) as (HDB31 & _).
  assert (HT48b : exists tb te : word, bytes_at rsegs mem (bv_unsigned (Z_to_bv 64 T0) + 48) (le8 tb ++ le8 te)).
  { rewrite MState.unsigned_lit by lia.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hap15.
    destruct (fsf_bytes_of mem (fun _ => True) 16 (T0 + 48) ltac:(lia) ltac:(cbn; lia)) as (bs & Hbs & Hlen & _).
    { intros i Hi. cbn in Hi. destruct (proj2 (HT48 i ltac:(lia))) as (b & Hb). exists b. split; [exact Hb | exact I]. }
    exists (Z_to_bv 64 (bytes_le_to_Z (firstn 8 bs))), (Z_to_bv 64 (bytes_le_to_Z (skipn 8 bs))).
    rewrite !fsf_le8_of_bytes by (rewrite ?length_firstn, ?length_skipn; lia).
    rewrite firstn_skipn. exact Hbs. }
  exists (Z_to_bv 64 (RT_TP + 32)), (Z_to_bv 64 RT_TSDMAIN), c, (Z_to_bv 64 T0), DBw, 0.
  assert (EDT : bv_unsigned (Z_to_bv 64 (RT_TP + 32)) = RT_TP + 32) by (apply MState.unsigned_lit; unfold RT_TP; lia).
  assert (ETS : bv_unsigned (Z_to_bv 64 RT_TSDMAIN) = RT_TSDMAIN) by (apply MState.unsigned_lit; unfold RT_TSDMAIN; lia).
  assert (ET : bv_unsigned (Z_to_bv 64 T0) = T0) by (apply MState.unsigned_lit; lia).
  pose proof (fsf_urange c) as Hcr. pose proof (fsf_urange DBw) as Hdbr.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HC7, HDB31.
  split.
  { unfold SMC.asan_tls_cells. rewrite ETP.
    split; [exact F1|].
    split; [exact (real_cell_of mem SMC.REAL_TLS_GET_ADDR SMC.MUSL_TLS_GET_ADDR HR ltac:(vm_compute; reflexivity))|].
    split; [exact F3|].
    split; [rewrite EDT; replace (RT_TP + 32 + 8) with (RT_TP + 40) by lia; exact F4|].
    split; [exact U1|].
    split; [lia|].
    split; [exact U2|].
    split; [exact U4|].
    split; [rewrite ETS; replace (RT_TSDMAIN + 8 * 0) with RT_TSDMAIN by lia; exact U5|].
    split; [apply (word_mem_le8 rsegs mem (bv_unsigned c + 152) T0 HT0); lia|].
    split; [exact HT48b|].
    split; [exact CF1|].
    split; [exact CF6|].
    split; [exact O3|].
    split; [exact O4|].
    split; [exact F2|].
    split; [exact F6|].
    split; [exact F6nz|].
    rewrite <- ETP. apply (word_mem_le8 rsegs mem (bv_unsigned DBw + 24) (AC.as_tp AC.ASYMS) HDB24);
      unfold AC.as_tp, AC.ASYMS; cbn; lia. }
  intros r Hr. cbn [FP.fp_tls In] in Hr. rewrite ?ETP, ?EDT, ?ETS, ?ET in Hr.
  assert (HGT : AC.GT = 0x5fe000) by reflexivity.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]];
    cbn [fst snd];
    try (split; [|left]; unfold SMC.TLS_INDEX, SMC.REAL_TLS_GET_ADDR, SMC.TSD_KEY_INITED, SMC.TSD_KEY, SMC.GOT_CF,
           SMC.CF, SMC.GOT_VERBOSITY, SMC.VERBOSITY, SMC.DTLS_TPOFF, RT_TP, RT_TSDMAIN, AC.GT in *; lia).
  - (* C + 152: the allocator's bytes *)
    split; [lia | right]. intros x Hx.
    destruct (HC152 (x - (bv_unsigned c + 152)) ltac:(lia)) as (Hown' & Happ').
    assert (Ex : bv_unsigned c + 152 + (x - (bv_unsigned c + 152)) = x) by lia.
    rewrite Ex in Hown', Happ'.
    split; [exact Happ'|]. split.
    + intros Hfs. exact (lwn_byte (NOWN H mem md x HAH (or_intror (or_intror (or_introl Hfs)))) Hown').
    + intros Hst. exact (lwn_byte (NOWN H mem md x HAH (or_intror (or_intror (or_intror Hst)))) Hown').
  - (* T + 48: the allocator's bytes *)
    split; [lia | right]. intros x Hx.
    destruct (HT48 (x - (T0 + 48)) ltac:(lia)) as (Hown' & _).
    pose proof (Hap48 (x - (T0 + 48)) ltac:(lia)) as Happ'.
    assert (Ex : T0 + 48 + (x - (T0 + 48)) = x) by lia.
    rewrite Ex in Hown', Happ'.
    split; [exact Happ'|]. split.
    + intros Hfs. exact (lwn_byte (NOWN H mem md x HAH (or_intror (or_intror (or_introl Hfs)))) Hown').
    + intros Hst. exact (lwn_byte (NOWN H mem md x HAH (or_intror (or_intror (or_intror Hst)))) Hown').
  - (* DB + 24: below stklo, outside FS *)
    split; [lia | right]. intros x Hx.
    destruct (HDBpl x Hx) as (Happ' & Hlt & Hnfs).
    split; [exact Happ'|]. split; [exact Hnfs | lia].
Qed.

(* FSFREE from RT, AH, the slot window above stklo, and the frame's location (each frame byte on the real stack
   or in FS, the side stack's classes 0 .. 5 below the frame). *)
Lemma fsfree_core : forall g fr H sp mem md,
  AsanRTInv.RT sp mem md -> AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= g_S g - AF.SLOT_STACK -> g_S g < APPMEM_END ->
  (forall a, fr <= a < fr + FRAME_BYTES ->
     AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= a < APPMEM_END \/ AC.a_in_fs AC.ASYMS mem a) ->
  (forall FS, word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 -> FS + 6328320 <= fr) ->
  FSFREE g fr mem.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr H sp mem md HRT HAH Hstk HSe Hloc Hfsb.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  destruct (fs_tls_core H sp mem md HRT HAH) as (DT & TS & C & T & DB & k & HT & Hr).
  pose proof HRT as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & (FSw & F5 & _) & _)).
  assert (Hwtp : word_mem rsegs mem (AC.as_tp AC.ASYMS) (bv_unsigned FSw))
    by exact (bytes_at_le8_word rsegs mem RT_TP FSw F5).
  pose proof (fsf_urange FSw) as HFSr.
  destruct (lw_fs_place (APIf rc) H mem md (bv_unsigned FSw) HAH Hwtp HFSr) as [HGT HEnd HAl HApp].
  pose proof (lw_fs_ok (APIf rc) H mem md (bv_unsigned FSw) HAH Hwtp HFSr) as Hok.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS H mem md HAH) as Hhigh.
  pose proof (Hfsb (bv_unsigned FSw) Hwtp HFSr) as Hfr.
  assert (HSZ : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HGTv : AC.GT = 0x5fe000) by reflexivity.
  assert (HHBv : HIGHMEM_BEG = 17594333495296) by reflexivity.
  exists (bv_unsigned FSw). split; [exact Hwtp|]. split; [exact HFSr|]. split; [exact Hok|]. split; [exact HGT|].
  split; [exact HAl|]. split; [exact HApp|]. split; [lia|]. split; [exact Hfr|].
  exists DT, TS, C, T, DB, k. split; [exact HT|]. split.
  - apply fsf_dj_intro. intros w d Hw Hd. destruct (Hr d Hd) as (Hdne & [(Hd0 & HdGT) | Hpt]).
    + cbn [In] in Hw. destruct Hw as [<-|[<-|[<-|[]]]]; cbn [fst snd]; unfold RLay.ly_dj; right; lia.
    + cbn [In] in Hw.
      destruct Hw as [<-|[<-|[<-|[]]]]; cbn [fst snd]; apply fsf_ly_dj_by; try lia;
        intros x Hx1 Hx2; destruct (Hpt x Hx2) as (_ & Hnfs & Hnst).
      * apply Hnfs. exists (bv_unsigned FSw). split; [exact HFSr|]. split; [exact Hwtp | lia].
      * apply Hnst. lia.
      * destruct (Hloc x Hx1) as [Hs|Hs]; [exact (Hnst Hs) | exact (Hnfs Hs)].
  - apply Forall_forall. intros d Hd. destruct (Hr d Hd) as (Hdne & [(Hd0 & HdGT) | Hpt]);
      (split; [exact Hdne|]).
    + intros x Hx. unfold app_mem, LOWMEM_END. left. lia.
    + intros x Hx. exact (proj1 (Hpt x Hx)).
Qed.

Lemma fra_fsfree : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md -> FSFREE g fr mem.
Proof.
  intros g fr hb regs mem md HFRA.
  pose proof (fra_frame B APIf ra g fr hb regs mem md HFRA) as (_ & _ & Hfsb & _).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & _).
  apply (fsfree_core g fr (hb ++ g_H g) sp mem md HRT HAH Hstklo HAPP); [|exact Hfsb].
  intros a Ha. destruct Hloc as [(_ & _ & Hreal) | (_ & _ & Hfs & _)];
    [left; exact (Hreal a Ha) | right; exact (Hfs a Ha)].
Qed.

Lemma frah_fsfree : forall g fr hb regs mem md sel hdr,
  FRAH B APIf ra g fr hb regs mem md sel hdr -> FSFREE g fr mem.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem md sel hdr HF.
  destruct HF as (A & sp & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz & Hstklo & Hr4 & Hr8 & Hr9 &
    Hr3 & Hr19 & Hr26 & Hfrm & Hsel & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP & Hspill & Hloc & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  apply (fsfree_core g fr (hb ++ g_H g) sp mem md HRT HAH Hstklo HAPP).
  - intros a Ha. destruct Hloc as [(_ & _ & Hreal) | (_ & _ & Hfs & _)];
      [left; exact (Hreal a Ha) | right; exact (Hfs a Ha)].
  - intros FS Hw HFSr. destruct Hloc as [(_ & _ & Hreal) | (_ & Hb & _)]; [|exact (Hb FS Hw HFSr)].
    destruct (lw_fs_place (APIf rc) (hb ++ g_H g) mem md FS HAH Hw HFSr) as [_ Hend _].
    pose proof (Hreal fr ltac:(lia)) as (Hlo & _). assert (AC.FS_SIZE = 11571200) by reflexivity. lia.
Qed.

(* The thread cells of every asan_tls_cells instance of an FRA state are apart from the slot window and the frame
   (prover a Theorem Labs lane's r13_tls_fra, lib/B/Prog/Seg/R13.v (a version not in this delivery) on a working branch 6a3ed3e194, in the slot-window form):
   the instance is FSFREE's (tls_uniq). So no cut carries this clause; a segment rebuilds it from FRA. *)
Lemma tls_fra : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md ->
  forall DT TS C T DB k, SMC.asan_tls_cells mem (AC.as_tp AC.ASYMS) DT TS C T DB k ->
    FP.fp_dj [(g_S g - AF.SLOT_STACK, g_S g); (fr, fr + FRAME_BYTES)] (FP.fp_tls (AC.as_tp AC.ASYMS) DT TS C T DB k).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem md HFRA DT TS C T DB k HT.
  destruct (fra_fsfree g fr hb regs mem md HFRA)
    as (FS & _ & _ & _ & _ & _ & _ & _ & _ & DT0 & TS0 & C0 & T0 & DB0 & k0 & HT0 & Hdj0 & _).
  destruct (tls_uniq mem _ _ _ _ _ _ _ _ _ _ _ _ _ HT0 HT) as (<- & <- & <- & <- & <- & <-).
  apply fsf_dj_intro. intros w d Hw Hd. apply (fsf_dj_elim _ _ _ _ Hdj0); [|exact Hd]. cbn [In] in *. tauto.
Qed.

(* RBE's thread-cell conjunct at any FRA cut: out[] [fr + 544, fr + 2036) is inside the frame. *)
Lemma fra_rbe_tls : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md ->
  forall DT TS C T DB k, SMC.asan_tls_cells mem (AC.as_tp AC.ASYMS) DT TS C T DB k ->
    FP.fp_dj [(fr + 544, fr + 544 + 1492)] (FP.fp_tls (AC.as_tp AC.ASYMS) DT TS C T DB k).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem md HFRA DT TS C T DB k HT.
  destruct (fra_fsfree g fr hb regs mem md HFRA)
    as (FS & _ & _ & _ & _ & _ & _ & _ & _ & DT0 & TS0 & C0 & T0 & DB0 & k0 & HT0 & Hdj0 & _).
  destruct (tls_uniq mem _ _ _ _ _ _ _ _ _ _ _ _ _ HT0 HT) as (<- & <- & <- & <- & <- & <-).
  apply fsf_dj_intro. intros w d Hw Hd. cbn [In] in Hw. destruct Hw as [<- | []]. cbn [fst snd].
  apply (fsf_ly_dj_sub_l fr (fr + FRAME_BYTES));
    [exact (fsf_dj_elim _ _ _ _ Hdj0 (or_intror (or_intror (or_introl eq_refl))) Hd) | lia | lia].
Qed.

(* THE call-site lemma: the side-stack package of a callee with classes cs (c <= 5) and window K
   (8 <= K <= FN_STACK) at any FRA cut, for a write list W in the slot window, the frame or the frame's shadow,
   and data ranges D in the image below GT, in the frame, or inside a live block of the cut. *)
Lemma fra_fp : forall g fr hb regs mem md cs K W D,
  FRA B APIf ra g fr hb regs mem md ->
  (forall c, In c cs -> (c <= 5)%nat) -> 8 <= K <= FN_STACK ->
  (forall w, In w W ->
     (g_S g - AF.SLOT_STACK <= fst w /\ snd w <= g_S g) \/ (fr <= fst w /\ snd w <= fr + FRAME_BYTES) \/
     (Sfr fr <= fst w /\ snd w <= Sfr fr + FRAME_SHADOW)) ->
  (forall d, In d D -> snd d <= AC.GT \/ (fr <= fst d /\ snd d <= fr + FRAME_BYTES) \/
     (fst d < snd d /\ exists p n, In (p, n) (hb ++ g_H g) /\ p <= fst d /\ snd d <= p + n)) ->
  exists FS,
    FP.fp cs mem (AC.as_tp AC.ASYMS) FS (AC.aspZ regs - K) (AC.aspZ regs) W D /\
    (forall DT TS C T DB k, SMC.asan_tls_cells mem (AC.as_tp AC.ASYMS) DT TS C T DB k ->
       FP.fp_dj (FP.fp_tls (AC.as_tp AC.ASYMS) DT TS C T DB k)
         (FP.fp_w cs FS ++ [(shadow_addr (AC.aspZ regs - K), shadow_addr (AC.aspZ regs))])) /\
    FP.fp_dj [(fr, fr + FRAME_BYTES); (Sfr fr, Sfr fr + FRAME_SHADOW)] (FP.fp_w cs FS) /\
    SMC.fs_frame FS 1 (SMC.fs_M 1) <= fr.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem md cs K W D HFRA Hcs HK HW HD.
  pose proof (fra_fsfree g fr hb regs mem md HFRA) as HFF.
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (_ & Hfapp).
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ _ _ HAH) as Hhigh.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  refine (fsfree_fp g fr mem cs (AC.aspZ regs) K W D HFF Hcs _ _ _ _ _ _ Hfapp HW _).
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - Z.div_mod_to_equations. lia.
  - intros d Hd. destruct (HD d Hd) as [H1 | [H2 | (Hne & p & n & Hin & Hp & Hn)]];
      [left; exact H1 | right; left; exact H2 |].
    right; right. split; [exact Hne|]. intros x Hx.
    destruct (lw_blocks (APIf rc) _ _ _ p n HAH Hin) as [_ _ _ _ Hall].
    destruct (Hall x ltac:(lia)) as (Happ & _ & _ & _ & Hnfs). split; [exact Happ | exact Hnfs].
Qed.

End S.
