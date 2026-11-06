From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL00 YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require YN03 YL0k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI Img0 MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import KindB VerbsB CommandB joined_c
  rec_calls_free_c CrtSm.
Import ListNotations.
Local Open Scope Z_scope.

Lemma crt_grec_img : image_bytes rsegs 0x22cf8 8 = Some (le8 (Z_to_bv 64 0x34028)).
Proof. vm_compute. repeat first [ reflexivity | apply bv_eq; reflexivity | f_equal ]. Qed.

Lemma crt_ptr_stable : forall A L L' p n, WF A -> In (p, n) (user_blocks A) -> layout_le A L L' ->
  ptr_addr L' p = ptr_addr L p.
Proof.
  intros A L L' p n HW Hin (_ & _ & _ & HR).
  destruct (YN03.block_region A p n HW Hin) as (k & o & rg & -> & Hr & _).
  destruct (region_of_lt A k rg Hr) as [Hk _].
  unfold ptr_addr, loc_addr. rewrite (HR k Hk). reflexivity.
Qed.

Lemma crt_lle_trans : forall A A' L1 L2 L3, layout_le A L1 L2 -> layout_le A' L2 L3 ->
  (length (st_regions A) <= length (st_regions A'))%nat -> layout_le A L1 L3.
Proof.
  intros A A' L1 L2 L3 (H1 & H2 & H3 & H4) (G1 & G2 & G3 & G4) HL.
  split; [congruence|]. split; [congruence|]. split; [congruence|].
  intros r Hr. rewrite (G4 r ltac:(lia)). exact (H4 r Hr).
Qed.

Lemma crt_writable_of_mbyte : forall m a b, 2 ^ 20 <= a < 2 ^ 64 -> mbyte rsegs m a = Some b -> writable_at rsegs m a.
Proof.
  intros m a b Ha H. unfold mbyte in H. unfold writable_at, wview.
  destruct (m (Z_to_bv 64 a)) as [c|] eqn:E; [discriminate|].
  rewrite (YL0k.seg_rom_above rsegs (2 ^ 20) (Z_to_bv 64 a) rsegs_top) in H by (rewrite unsigned_lit by lia; lia).
  discriminate.
Qed.

Lemma crt_nargs_dec : forall c n a, nargs_field c n a \/ ~ nargs_field c n a.
Proof.
  intros c n a.
  destruct (Z_lt_ge_dec ((a - c) mod 56) 4) as [H1|H1].
  { right. intros (i & Hi & Ha). Z.div_mod_to_equations. lia. }
  destruct (Z_lt_ge_dec ((a - c) mod 56) 8) as [H2|H2].
  2: { right. intros (i & Hi & Ha). Z.div_mod_to_equations. lia. }
  destruct (Z_lt_ge_dec ((a - c) / 56) 0) as [H3|H3].
  { right. intros (i & Hi & Ha). Z.div_mod_to_equations. lia. }
  destruct (Z_lt_ge_dec ((a - c) / 56) (Z.of_nat n)) as [H4|H4].
  2: { right. intros (i & Hi & Ha). Z.div_mod_to_equations. lia. }
  left. exists (Z.to_nat ((a - c) / 56)). split; [lia|]. rewrite Z2Nat.id by lia. Z.div_mod_to_equations. lia.
Qed.

Lemma crt_cells_split : forall m A cs1 cs2, rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_bytes_length in B2 by exact W1.
  destruct Hw as (Ha & Hn & Hw). rewrite cells_size_app in Hn, Hw.
  split.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply Hw. lia.
Qed.

Lemma crt_filter_nz : forall l : list (Z * Z), (forall pn, In pn l -> fst pn <> 0) ->
  List.filter (fun pn => negb (fst pn =? 0)) l = l.
Proof.
  induction l as [|x l IH]; intros H; [reflexivity|].
  simpl. assert (Hx : fst x <> 0) by (apply H; left; reflexivity).
  destruct (fst x =? 0) eqn:E; [apply Z.eqb_eq in E; contradiction|].
  cbn [negb]. f_equal. apply IH. intros pn Hp. apply H. right. exact Hp.
Qed.

Lemma crt_ro_munch : forall W m m', ro_agree rsegs m -> munch W m m' ->
  (forall x : word, ~ Frame.outside W (bv_unsigned x) -> ro_addr rsegs x = false) -> ro_agree rsegs m'.
Proof.
  intros W m m' H HM HW x Hx. destruct (KindBGlue.kb_outside_dec W (bv_unsigned x)) as [Ho|Ho].
  - unfold mrd. rewrite (HM x Ho). exact (H x Hx).
  - rewrite (HW x Ho) in Hx. discriminate.
Qed.

Lemma crt_sh_ro : forall x : word, ~ Frame.outside [(213976, 213992)] (bv_unsigned x) -> ro_addr rsegs x = false.
Proof.
  intros x Hx.
  assert (R : 213976 <= bv_unsigned x < 213992).
  { destruct (Z_le_gt_dec 213976 (bv_unsigned x)) as [H1|H1];
      [destruct (Z_lt_ge_dec (bv_unsigned x) 213992) as [H2|H2]|].
    - lia.
    - exfalso. apply Hx. cbn. split; [lia | exact I].
    - exfalso. apply Hx. cbn. split; [lia | exact I]. }
  assert (C : exists k, 0 <= k < 16 /\ bv_unsigned x = 213976 + k) by (exists (bv_unsigned x - 213976); lia).
  destruct C as (k & Hk & E). unfold ro_addr. rewrite E.
  assert (Ck : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/
               k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15) by lia.
  repeat (destruct Ck as [Ck|Ck]; [subst k; vm_compute; reflexivity|]). subst k; vm_compute; reflexivity.
Qed.

Section Keep.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Hypothesis SEGS : ms_segs B = rsegs.

Definition relro_kept (m m' : word -> option byte) : Prop :=
  forall a, in_globals frame_RELRO a -> ~ (SSP_GOT_B <= a < SSP_GOT_B + 8) -> mbyte rsegs m' a = mbyte rsegs m a.

Lemma crt_le_prefix : forall m a x y, le_at B m a (x ++ y) -> le_at B m a x.
Proof.
  intros m a x y H. unfold le_at, blk_data in *. intros i Hi.
  rewrite (H i ltac:(rewrite length_app; lia)). apply nth_error_app1. lia.
Qed.

Lemma crt_words_view_keep : forall m m' W arr wp ws, words_view B m W arr wp ws ->
  (forall a, W + 16 <= a < W + 32 -> mbyte rsegs m' a = mbyte rsegs m a) ->
  (forall i, 0 <= i < 8 * Z.of_nat (length ws) -> mbyte rsegs m' (arr + i) = mbyte rsegs m (arr + i)) ->
  (forall k i, (k < length ws)%nat -> 0 <= i <= Z.of_nat (length (nth k ws [])) ->
     mbyte rsegs m' (nth k wp 0 + i) = mbyte rsegs m (nth k wp 0 + i)) ->
  words_view B m' W arr wp ws.
Proof using SEGS.
  intros m m' W arr wp ws (L1 & L2 & L3 & L4 & L5) KW KA KS.
  split; [exact L1|]. split; [exact L2|].
  split; [apply (sm_le_keep B m); [exact L3|]; rewrite SEGS; intros i Hi; rewrite Mem.length_le4 in Hi;
          apply KW; lia|].
  split; [apply (sm_le_keep B m); [exact L4|]; rewrite SEGS; intros i Hi; rewrite Mem.length_le8 in Hi;
          apply KW; lia|].
  intros k Hk. destruct (L5 k Hk) as (A1 & A2 & A3). split; [|split; [exact A2|]].
  - apply (sm_le_keep B m); [exact A1|]. rewrite SEGS. intros i Hi. rewrite Mem.length_le8 in Hi.
    replace (arr + 8 * Z.of_nat k + i) with (arr + (8 * Z.of_nat k + i)) by ring. apply KA. lia.
  - apply (sm_le_keep B m); [exact A3|]. rewrite SEGS. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    apply KS; [exact Hk | lia].
Qed.

Lemma crt_vr_tables_keep : forall m m' can g, vr_tables B m can -> relro_kept m m' ->
  word_mem rsegs m' SSP_GOT_B SSP_GUARD_B -> word_mem rsegs m' SSP_GUARD_B g -> 0 <= g < 2 ^ 64 ->
  vr_tables B m' (Z_to_bv 64 g).
Proof using SEGS.
  intros m m' can g (V1 & V2 & V3 & V4) K WG WC Hg.
  assert (LIV : length (concat (map (fun p => Mem.le8 (Z_to_bv 64 p)) iv_ptrs_b)) = 144%nat) by (vm_compute; reflexivity).
  assert (LIN : length info_bytes = 160%nat) by (vm_compute; reflexivity).
  split; [|split; [|split]].
  - apply (sm_le_keep B m); [exact V1|]. rewrite SEGS. intros i Hi. rewrite LIV in Hi.
    apply K; [apply sm_relro_of; unfold IV_TABLE_B; lia | unfold IV_TABLE_B, SSP_GOT_B; lia].
  - apply (sm_le_keep B m); [exact V2|]. rewrite SEGS. intros i Hi. rewrite LIN in Hi.
    apply K; [apply sm_relro_of; unfold INFO_TABLE; lia | unfold INFO_TABLE, SSP_GOT_B; lia].
  - apply (sm_le_of_bytes B m' _ _ SEGS).
    apply (KindBGlue.word_mem_le8 rsegs m' SSP_GOT_B SSP_GUARD_B WG); unfold SSP_GUARD_B, SSP_GOT_B; lia.
  - apply (sm_le_of_bytes B m' _ _ SEGS).
    apply (KindBGlue.word_mem_le8 rsegs m' SSP_GUARD_B g WC); unfold SSP_GUARD_B; lia.
Qed.

Lemma crt_cmd_mem_keep : forall m m' g, cmd_mem B m -> ro_agree rsegs m' -> relro_kept m m' ->
  word_mem rsegs m' SSP_GOT_B SSP_GUARD_B -> word_mem rsegs m' SSP_GUARD_B g -> 0 <= g < 2 ^ 64 ->
  cmd_mem B m'.
Proof using SEGS.
  intros m m' g (RO & GIMG & _ & _) RO' K WG WC Hg.
  unfold cmd_mem. rewrite SEGS. split; [exact RO'|].
  split.
  { unfold G_img_c. intros a Ha. rewrite SEGS.
    destruct (Z_lt_ge_dec a SSP_GOT_B) as [H1|H1]; [|destruct (Z_lt_ge_dec a (SSP_GOT_B + 8)) as [H2|H2]].
    - rewrite (K a Ha ltac:(lia)). pose proof (GIMG a Ha) as E. rewrite SEGS in E. exact E.
    - exact (sm_got_rom m' a WG ltac:(lia)).
    - rewrite (K a Ha ltac:(lia)). pose proof (GIMG a Ha) as E. rewrite SEGS in E. exact E. }
  split; [exists (Z_to_bv 64 g); apply (sm_le_of_bytes B m' _ _ SEGS);
          apply (KindBGlue.word_mem_le8 rsegs m' SSP_GUARD_B g WC); unfold SSP_GUARD_B; lia|].
  intros i Hi. exact (sm_guard_wr m' i Hi).
Qed.

Lemma crt_got_bytes : forall m, cmd_mem B m ->
  bytes_at rsegs m 0x22d10 (le8 (Z_to_bv 64 0x343e8)) /\ bytes_at rsegs m 0x22cf8 (le8 (Z_to_bv 64 0x34028)).
Proof using SEGS.
  intros m (_ & GIMG & _ & _).
  assert (G : forall a, 0x226b0 <= a < 0x22d40 -> mbyte rsegs m a = seg_rom rsegs (Z_to_bv 64 a)).
  { intros a Ha. pose proof (GIMG a (sm_relro_of a Ha)) as E. rewrite SEGS in E. exact E. }
  split.
  - apply (sm_bytes_of_image rsegs m 8 _ _ sm_got_img); [| lia | lia]. intros i Hi. cbn in Hi. apply G. lia.
  - apply (sm_bytes_of_image rsegs m 8 _ _ crt_grec_img); [| lia | lia]. intros i Hi. cbn in Hi. apply G. lia.
Qed.

End Keep.
