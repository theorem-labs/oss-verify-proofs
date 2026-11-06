(* Helpers of batch b1 (segments A02, A03, R01-R08 of fuzz_ctrl LLVMFuzzerTestOneInput, plain). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcEmit RcEmitLib RcLay RcSynth RcSynthLib RcFinLib
  RcIdentModel RcReply reac_ctrl_build_as_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot.
Import ListNotations.
Open Scope Z_scope.

(* Bytes a segment does not touch: from the cut's memory through the normalized run to the next cut's memory. *)
Lemma b1_keep : forall W mem m0 m' a bs, ro_agree rsegs mem -> Frame.munch W (normalize rsegs mem) m0 ->
  mem_rel rsegs m' m0 -> Frame.disjoint_from W a (Z.of_nat (length bs)) ->
  bytes_at rsegs mem a bs -> bytes_at rsegs m' a bs.
Proof.
  intros W mem m0 m' a bs Hro MU Hrel HD H.
  apply (proj2 (bytes_at_rel rsegs m' m0 a bs Hrel)).
  exact (bytes_at_transport rsegs W (normalize rsegs mem) m0 a bs (bytes_at_normalize rsegs mem a bs Hro H) MU HD).
Qed.

(* The bytes the run itself leaves at a: from the run's final memory to the next cut's memory. *)
Lemma b1_out : forall m0 m' a bs, mem_rel rsegs m' m0 -> bytes_at rsegs m0 a bs -> bytes_at rsegs m' a bs.
Proof. intros m0 m' a bs Hrel H. exact (proj2 (bytes_at_rel rsegs m' m0 a bs Hrel) H). Qed.

(* beqz / bnez on a non-zero value. *)
Lemma b1_beq0 : forall z, 0 < z < 2 ^ 64 -> bv_eqb (Z_to_bv 64 z) (Z_to_bv 64 0) = false.
Proof. intros z Hz. unfold bv_eqb. rewrite !MState.unsigned_lit by lia. apply Z.eqb_neq. lia. Qed.

(* An 8-byte load from a q64 cell. *)
Lemma b1_ld8 : forall m a v, bytes_at rsegs m a (le8 v) -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 v).
Proof.
  intros m a v H. replace (wa a) with (wa (a + Z.of_nat 0)) by (f_equal; lia).
  rewrite (bytes_at_ov_read rsegs m a (le8 v) 0 8 H) by (rewrite length_le8; lia).
  reflexivity.
Qed.

Lemma b1_remu : forall a b, 0 <= a < 2 ^ 64 -> 0 < b < 2 ^ 64 ->
  mul_div Instr.M_REMU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a mod b).
Proof.
  intros a b Ha Hb. unfold mul_div. rewrite (MState.unsigned_lit b) by lia.
  replace (b =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  apply bv_eq. rewrite bv_modu_unsigned, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616 in *.
  rewrite (Z.mod_small a) by lia. rewrite (Z.mod_small b) by lia.
  rewrite (Z.mod_small (a mod b)); [reflexivity|]. pose proof (Z.mod_pos_bound a b ltac:(lia)). lia.
Qed.

Lemma b1_byte_rng : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. exact R. Qed.

Lemma b1_mode_rng : forall inp, 0 <= mode inp < 256.
Proof.
  intros inp. unfold mode, inb, RcIdentModel.bz. destruct (7 <=? nlen inp); [apply b1_byte_rng | lia].
Qed.

(* ---- Lengths of the round-trip model ---- *)

Lemma b1_fg_st_len : forall len st g, length st = 72%nat -> length g = 50%nat -> length (fg_st len st g) = 72%nat.
Proof.
  intros len st g Hs Hg. unfold fg_st, fcls, fg_class.
  change ((1 =? 0) || (1 =? 0) || (1 =? 0) || (1 =? 0) || (1 =? 0)) with false. cbv iota.
  destruct (fg_fr len g) eqn:Efr; cbn [negb]; [|exact Hs].
  assert (Hn : 1 <= fg_n g <= 22).
  { unfold fg_fr in Efr. rewrite !andb_true_iff in Efr. destruct Efr as [[[_ H1] H2] _].
    apply Z.leb_le in H1. apply Z.leb_le in H2. lia. }
  assert (Hb : forall bs i, 0 <= bat bs i).
  { intros bs i. unfold bat. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) bs (Z_to_bv 8 0))). lia. }
  assert (Hbody : length (fg_body g) = Z.to_nat (fg_n g)).
  { unfold fg_body, bsl. rewrite length_firstn, length_skipn, Hg. lia. }
  destruct (bat g 19 =? 1).
  - cbn [fg_next]. unfold fg_first. rewrite !length_app, Hbody, length_skipn, Hs. cbn [length].
    unfold bsl. rewrite length_firstn, length_skipn, Hg. lia.
  - destruct (fg_keep st g) eqn:Ek; cbn [negb]; [|cbn [fg_next]; unfold fg_clear;
      rewrite !length_app, length_firstn, length_skipn, Hs; cbn [length]; lia].
    assert (HT : fg_T st g <= 64).
    { unfold fg_keep in Ek. rewrite !andb_true_iff in Ek. destruct Ek as [_ H]. apply Z.leb_le in H. exact H. }
    assert (Hj : length (fg_join st g) = 72%nat).
    { unfold fg_join. unfold fg_T, fg_lf in HT. pose proof (Hb st 7).
      rewrite !length_app, Hbody, length_firstn, length_skipn, Hs. unfold fg_T, fg_lf. lia. }
    destruct (fg_close st g); cbn [negb fg_next]; unfold fg_clear;
      rewrite !length_app, length_firstn, length_skipn, Hj; cbn [length]; lia.
Qed.

Lemma b1_RS_len : forall inp b, length (RID inp b) = 38%nat /\ length (RFG inp b) = 72%nat.
Proof.
  intros inp b. unfold RID, RFG. induction b as [|b [IH1 IH2]]; [split; reflexivity|].
  cbn [rt_st].
  destruct (rt_n inp (Z.of_nat b) =? 0); [exact (conj IH1 IH2)|].
  destruct ((Z.of_nat b =? 3) || (Z.of_nat b =? 4)); cbn [fst snd].
  - split; [|exact IH2]. unfold rp_id. destruct (RcReply.ir _ _); [apply RcIdentModel.ING_length; exact IH1 | exact IH1].
  - destruct ((Z.of_nat b =? 5) || (Z.of_nat b =? 6)); cbn [fst snd]; [|exact (conj IH1 IH2)].
    split.
    + unfold fg_id. destruct (fg_rf _ _ _ =? 1); [apply RcIdentModel.ING_length; exact IH1 | exact IH1].
    + apply b1_fg_st_len; [exact IH2 | apply fr50_length].
Qed.

Lemma b1_row_len : forall i, length (rowb i) = 296%nat.
Proof.
  intros i. unfold rowb, img. destruct (Image.image_bytes rsegs (CAT + CAT_ROW * i) 296) eqn:E.
  - exact (Image.image_bytes_length rsegs 296 _ _ E).
  - apply repeat_length.
Qed.

Lemma b1_rtX_len : forall inp b, length (rt_X inp b) = 32%nat.
Proof.
  intros inp b. unfold rt_X, reac_ctrl_build_as_c.ba_X, RcLay.ly_Z.
  assert (HZ : length (if mrow inp =? 0 then RcLay.ly_zero
                       else if RcSynth.rc (rt_mb inp) b =? 1 then RcSynth.synth (rt_mb inp) b (rt_nb inp)
                       else RcLay.ly_zero) = 32%nat).
  { destruct (mrow inp =? 0); [reflexivity|].
    destruct (RcSynth.rc (rt_mb inp) b =? 1); [|reflexivity].
    apply RcSynthLib.rs_synth_len. apply b1_row_len. }
  destruct (b <=? 1); [apply RcFinLib.rcf_stamp32_len; exact HZ | exact HZ].
Qed.

(* n_b != 0: E(b), 124 <= n_b <= 1492, and F_b has n_b bytes. *)
Lemma b1_rtn : forall inp b, rt_n inp b <> 0 ->
  rt_E inp b = true /\ 124 <= rt_n inp b <= 1492 /\ length (rt_F inp b) = Z.to_nat (rt_n inp b).
Proof.
  intros inp b H. unfold rt_n in *. destruct (rt_E inp b) eqn:E; [|congruence].
  pose proof E as E'. unfold rt_E, reac_ctrl_build_as_c.ba_E in E'. apply andb_true_iff in E' as [Ew _].
  destruct (RcEmitLib.em_wok_range _ Ew) as [R _].
  split; [reflexivity|]. split; [lia|].
  unfold rt_F, RcEmit.em_fr, RcEmit.em_hdr, box6. unfold rt_n. rewrite E.
  rewrite !length_app, OUR_length, length_map, b1_rtX_len, repeat_length. cbn [length]. lia.
Qed.

(* The first 50 bytes of a frame of n_b >= 50 bytes are read from F_b itself. *)
Lemma b1_fr50_nth : forall bs i, (i < 50)%nat -> (50 <= length bs)%nat -> nth_error (fr50 bs) i = nth_error bs i.
Proof.
  intros bs i Hi Hl. unfold fr50. rewrite nth_error_firstn. destruct (Nat.ltb_spec i 50) as [_|]; [|lia].
  rewrite nth_error_app1 by lia. reflexivity.
Qed.

(* ---- The round-trip bundle RB across a run that writes nothing in [sp+76, sp+192) ---- *)

Lemma b1_dj_sub : forall W a n a' n', Frame.disjoint_from W a n -> a <= a' -> a' + n' <= a + n ->
  Frame.disjoint_from W a' n'.
Proof.
  induction W as [|[lo hi] W IH]; cbn [disjoint_from]; intros a n a' n' H H1 H2; [exact I|].
  destruct H as [H H']. split; [lia | exact (IH a n a' n' H' H1 H2)].
Qed.

(* YK11.getr: the getr of SlotInv's rg (PropExec has its own getr). *)
Definition b1_kr (regs' regs : bvmap 5 word) : Prop :=
  YK11.getr regs' 8 = YK11.getr regs 8 /\ YK11.getr regs' 9 = YK11.getr regs 9 /\
  YK11.getr regs' 18 = YK11.getr regs 18 /\ YK11.getr regs' 19 = YK11.getr regs 19 /\
  YK11.getr regs' 21 = YK11.getr regs 21 /\ YK11.getr regs' 23 = YK11.getr regs 23 /\
  YK11.getr regs' 24 = YK11.getr regs 24 /\ YK11.getr regs' 25 = YK11.getr regs 25 /\
  YK11.getr regs' 26 = YK11.getr regs 26 /\ YK11.getr regs' 27 = YK11.getr regs 27.

Lemma b1_RB_keep : forall g b idb fgb regs regs' mem m0 m' W,
  ro_agree rsegs mem -> Frame.munch W (normalize rsegs mem) m0 -> mem_rel rsegs m' m0 ->
  length idb = 38%nat -> length fgb = 72%nat -> Frame.disjoint_from W (spk g 76) 116 ->
  b1_kr regs' regs -> RB g b idb fgb regs mem -> RB g b idb fgb regs' m'.
Proof.
  intros g b idb fgb regs regs' mem m0 m' W Hro MU Hrel L1 L2 HD
    (E8 & E9 & E18 & E19 & E21 & E23 & E24 & E25 & E26 & E27)
    (Hb & (Hc & H21 & H27) & HO & (H8 & H18 & H19 & H23 & H24 & H25 & H26) & H9 & HI & HF).
  unfold RB, CUR, RT, rg, OURb, IDB, FGB in *.
  split; [exact Hb|].
  split; [split; [exact Hc|]; split; [rewrite E21; exact H21 | rewrite E27; exact H27]|].
  split.
  { apply (b1_keep W mem m0 m' _ _ Hro MU Hrel); [|exact HO].
    rewrite OUR_length. apply (b1_dj_sub W _ _ _ _ HD); unfold spk; lia. }
  split.
  { rewrite E8, E18, E19, E23, E24, E25, E26. auto 8. }
  split; [rewrite E9; exact H9|].
  split.
  { apply (b1_keep W mem m0 m' _ _ Hro MU Hrel); [|exact HI].
    rewrite L1. apply (b1_dj_sub W _ _ _ _ HD); unfold spk; lia. }
  apply (b1_keep W mem m0 m' _ _ Hro MU Hrel); [|exact HF].
  rewrite L2. apply (b1_dj_sub W _ _ _ _ HD); unfold spk; lia.
Qed.

(* n_b != 0 is 52 + 36 u with 2 <= u <= 40 (em_wok). *)
Lemma b1_rtn_u : forall inp b, rt_n inp b <> 0 -> exists u, rt_n inp b = 52 + 36 * u /\ 2 <= u <= 40.
Proof.
  intros inp b H. unfold rt_n in *. destruct (rt_E inp b) eqn:E; [|congruence].
  unfold rt_E, reac_ctrl_build_as_c.ba_E in E. apply andb_true_iff in E as [Ew _].
  destruct (RcEmitLib.em_wok_range _ Ew) as [R _]. exists (rt_uw inp). split; [reflexivity | exact R].
Qed.

Lemma b1_ba_mbyte : forall m m' a bs, bytes_at rsegs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) ->
  bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs (H1 & H2 & H) Hk. split; [exact H1|]. split; [exact H2|].
  intros i Hi. rewrite <- (H i Hi). pose proof (Hk (Z.of_nat i) ltac:(lia)) as E. unfold mbyte in E.
  unfold Mem.mrd, wa. exact E.
Qed.

Lemma b1_kr_pres : forall regs regs', regs_preserved regs regs' -> b1_kr regs' regs.
Proof.
  intros regs regs' RP.
  refine (conj (RP 8 _) (conj (RP 9 _) (conj (RP 18 _) (conj (RP 19 _) (conj (RP 21 _) (conj (RP 23 _)
         (conj (RP 24 _) (conj (RP 25 _) (conj (RP 26 _) (RP 27 _)))))))))).
  all: unfold callee_saved; lia.
Qed.

(* RB across a step that keeps the bytes [sp+76, sp+192) (an allocator call). *)
Lemma b1_RB_mb : forall g b idb fgb regs regs' m m',
  (forall a, spk g 76 <= a < spk g 192 -> mbyte rsegs m' a = mbyte rsegs m a) ->
  length idb = 38%nat -> length fgb = 72%nat -> b1_kr regs' regs -> RB g b idb fgb regs m -> RB g b idb fgb regs' m'.
Proof.
  intros g b idb fgb regs regs' m m' HM L1 L2 (E8 & E9 & E18 & E19 & E21 & E23 & E24 & E25 & E26 & E27)
    (Hb & (Hc & H21 & H27) & HO & (H8 & H18 & H19 & H23 & H24 & H25 & H26) & H9 & HI & HF).
  unfold RB, CUR, RT, rg, OURb, IDB, FGB in *.
  split; [exact Hb|].
  split; [split; [exact Hc|]; split; [rewrite E21; exact H21 | rewrite E27; exact H27]|].
  split.
  { apply (b1_ba_mbyte m m' _ _ HO). rewrite OUR_length. intros i Hi. apply HM. unfold spk. lia. }
  split; [rewrite E8, E18, E19, E23, E24, E25, E26; auto 8|].
  split; [rewrite E9; exact H9|].
  split; [apply (b1_ba_mbyte m m' _ _ HI); rewrite L1; intros i Hi; apply HM; unfold spk; lia|].
  apply (b1_ba_mbyte m m' _ _ HF). rewrite L2. intros i Hi. apply HM. unfold spk; lia.
Qed.

(* n_b = 0: the turn leaves id and frag as they were. *)
Lemma b1_RS_zero : forall inp b, rt_n inp (Z.of_nat b) = 0 -> RID inp (S b) = RID inp b /\ RFG inp (S b) = RFG inp b.
Proof. intros inp b H. unfold RID, RFG. cbn [rt_st]. rewrite H. split; reflexivity. Qed.

(* A check over n_b = 52 + 36 u, 2 <= u <= 40, done by computation for each u. *)
Lemma b1_u_cases : forall (P : Z -> Prop) (f : Z -> bool), (forall u, f u = true -> P u) ->
  forallb f (map Z.of_nat (seq 2 39)) = true -> forall u, 2 <= u <= 40 -> P u.
Proof.
  intros P f HP Hall u Hu. apply HP. rewrite forallb_forall in Hall. apply Hall.
  apply in_map_iff. exists (Z.to_nat u). split; [lia|]. apply in_seq. lia.
Qed.

(* Goal c = false where c mentions n, with Hu : exists u, n = 52 + 36 u /\ 2 <= u <= 40. *)
Ltac b1_by_u Hu :=
  let u := fresh "u" in let Hr := fresh "Hr" in
  destruct Hu as (u & -> & Hr); revert u Hr;
  lazymatch goal with
  | |- forall u, _ -> @?e u = false =>
      apply (b1_u_cases (fun u => e u = false) (fun u => negb (e u)));
      [intros ? H; apply Bool.negb_true_iff in H; exact H | vm_compute; reflexivity]
  end.

(* ---- RELRO and read-only image bytes ---- *)

Lemma b1_image_nth : forall n A bs, Image.image_bytes rsegs A n = Some bs ->
  forall i, (i < n)%nat -> seg_rom rsegs (wa (A + Z.of_nat i)) = nth_error bs i.
Proof.
  induction n as [|n IH]; intros A bs H i Hi; [lia|].
  cbn [Image.image_bytes] in H.
  destruct (seg_rom rsegs (wa A)) as [b|] eqn:E; [|discriminate].
  destruct (Image.image_bytes rsegs (A + 1) n) as [bs'|] eqn:E'; [|discriminate].
  injection H as <-. destruct i as [|i].
  - cbn [nth_error]. replace (A + Z.of_nat 0) with A by lia. exact E.
  - cbn [nth_error]. replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia. apply IH; [exact E' | lia].
Qed.

(* CTRL_FRAMES rows 3 .. 9 (build_as' table) and the 11 rows of BOX_CATALOGUE, read from the image. *)
Lemma b1_ba_tbl : Image.image_bytes rsegs (reac_ctrl_build_as_c.BA_FR + 72) 168 = Some reac_ctrl_build_as_c.ba_tbl.
Proof. vm_compute. reflexivity. Qed.

Lemma b1_rows : forall i, 0 <= i < CAT_N -> Image.image_bytes rsegs (CAT + CAT_ROW * i) 296 = Some (rowb i).
Proof.
  intros i Hi. unfold CAT_N in Hi.
  assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]; vm_compute; reflexivity.
Qed.

Lemma b1_in_relro : forall a, 0x1ed20 <= a < 0x1fb80 -> in_globals frame_RELRO a.
Proof. intros a Ha. exists 0x1ed20, 3680. split; [left; reflexivity | lia]. Qed.

Lemma b1_find_img : forall B x seg, ms_segs B = rsegs -> find_segment rsegs x 1 = Some seg -> in_img B x.
Proof.
  intros B x seg HS E. destruct (sl_find_segment_in rsegs x 1 seg E) as (Hin & H1 & H2).
  destruct (sl_rsegs_seg seg Hin) as (R1 & R2 & R3).
  split; [rewrite HS; intros Hn; rewrite Hn in Hin; destruct Hin|].
  exists (segment_reservation seg). split.
  - rewrite HS. unfold segments_reserved. apply in_map_iff. exists seg. split; [reflexivity | exact Hin].
  - lia.
Qed.

Lemma b1_pw_perm : forall (T : Type) (R : T -> T -> Prop), (forall a b, R a b -> R b a) ->
  forall l l', Permutation l l' -> pairwise R l -> pairwise R l'.
Proof.
  intros T R Hs l l' HP. induction HP as [|x l l' HP IH|x y l|l l' l'' H1 IH1 H2 IH2]; intros H.
  - exact H.
  - destruct H as [H1 H2]. split; [|exact (IH H2)].
    intros y Hy. apply H1. apply (Permutation_in y (Permutation_sym HP) Hy).
  - destruct H as [Hy [Hx Hl]]. split.
    + intros z [<-|Hz]; [apply Hs, Hy; left; reflexivity | exact (Hx z Hz)].
    + split; [intros z Hz; apply Hy; right; exact Hz | exact Hl].
  - exact (IH2 (IH1 H)).
Qed.

Lemma b1_rd_sym : forall a b, ranges_disjoint a b -> ranges_disjoint b a.
Proof. unfold ranges_disjoint. intros a b H. lia. Qed.

(* A byte outside every image segment that reads Some is present in the memory itself. *)
Lemma b1_present : forall B (m : word -> option byte) x b, ms_segs B = rsegs -> ~ in_img B x -> 0 <= x < 2 ^ 64 ->
  mrd rsegs m (wa x) = Some b -> exists b', m (Z_to_bv 64 x) = Some b'.
Proof.
  intros B m x b HS Hn Hx H. unfold mrd in H. destruct (m (wa x)) as [b'|] eqn:E; [exists b'; exact E|].
  exfalso. destruct (find_segment rsegs (bv_unsigned (wa x)) 1) as [seg|] eqn:Ef.
  - rewrite wa_unsigned in Ef by lia. exact (Hn (b1_find_img B x seg HS Ef)).
  - rewrite (seg_rom_unmapped rsegs (wa x) Ef) in H. discriminate.
Qed.

(* The sink cells of sink_none (0x51191, 0x515b8, 0x515c0) lie in the image. *)
Lemma b1_resv_ok : existsb (fun s : word * word => (bv_unsigned (fst s) <=? 0x51190) &&
    (0x515c8 <=? bv_unsigned (fst s) + bv_unsigned (snd s))) (segments_reserved rsegs) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma b1_img_sink : forall B x, ms_segs B = rsegs -> 0x51190 <= x < 0x515c8 -> in_img B x.
Proof.
  intros B x HS Hx. pose proof b1_resv_ok as H. apply existsb_exists in H as (s & Hs & Hc).
  apply andb_true_iff in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  split; [rewrite HS; intros Hn; rewrite Hn in Hs; cbn in Hs; destruct Hs|].
  exists s. rewrite HS. split; [exact Hs | lia].
Qed.

(* round_trip.box: the 6 read-only bytes at 0x105c9. *)
Lemma b1_box_ro : Image.ro_bytes_b rsegs BOXA box6 = true.
Proof. vm_compute. reflexivity. Qed.

(* name_ok as a check. *)
Definition b1_name_okb (nb : list byte) : bool :=
  (1 <=? length nb)%nat && (length nb <=? 16)%nat &&
  forallb (fun i => negb (bv_unsigned (nth i nb (Z_to_bv 8 0)) =? 0)) (seq 0 (pred (length nb))) &&
  ((length nb =? 16)%nat || (bv_unsigned (nth (pred (length nb)) nb (Z_to_bv 8 0)) =? 0)).

Lemma b1_name_okb_sound : forall nb, b1_name_okb nb = true -> RcBox.name_ok nb.
Proof.
  intros nb H. unfold b1_name_okb in H. rewrite !andb_true_iff in H.
  destruct H as [[[H1 H2] H3] H4]. apply Nat.leb_le in H1. apply Nat.leb_le in H2.
  rewrite forallb_forall in H3. split; [lia|]. split.
  - intros i Hi. pose proof (H3 i ltac:(apply in_seq; lia)) as E. apply Bool.negb_true_iff in E.
    apply Z.eqb_neq in E. exact E.
  - apply orb_true_iff in H4 as [E|E]; [left; apply Nat.eqb_eq in E; exact E | right; apply Z.eqb_eq in E; exact E].
Qed.

(* The model name of each catalogue row that has one: a C string of 1 .. 16 bytes in read-only data. *)
Definition b1_name_chk (i : Z) : bool :=
  let r := rowb i in
  (RcSynth.has r =? 0) || (RcSynth.rname r =? 0) ||
  (b1_name_okb (img_cstr (RcSynth.rname r) 16) &&
   Image.ro_bytes_b rsegs (RcSynth.rname r) (img_cstr (RcSynth.rname r) 16) &&
   (0 <=? RcSynth.rname r) && (RcSynth.rname r + 17 <=? 0x52000)).

Lemma b1_name_chk_all : forallb b1_name_chk (map Z.of_nat (seq 0 11)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma b1_names : forall i, 0 <= i < CAT_N -> RcSynth.has (rowb i) <> 0 -> RcSynth.rname (rowb i) <> 0 ->
  RcBox.name_ok (img_cstr (RcSynth.rname (rowb i)) 16) /\
  Image.ro_bytes_b rsegs (RcSynth.rname (rowb i)) (img_cstr (RcSynth.rname (rowb i)) 16) = true /\
  0 <= RcSynth.rname (rowb i) /\ RcSynth.rname (rowb i) + 17 <= 0x52000.
Proof.
  intros i Hi Hh Hn. unfold CAT_N in Hi. pose proof b1_name_chk_all as H. rewrite forallb_forall in H.
  specialize (H i ltac:(apply in_map_iff; exists (Z.to_nat i); split; [lia | apply in_seq; lia])).
  unfold b1_name_chk in H. cbv zeta in H.
  rewrite (proj2 (Z.eqb_neq _ _) Hh), (proj2 (Z.eqb_neq _ _) Hn) in H. cbn [orb] in H.
  rewrite !andb_true_iff in H. destruct H as [[[H1 H2] H3] H4].
  apply Z.leb_le in H3. apply Z.leb_le in H4.
  split; [exact (b1_name_okb_sound _ H1)|]. split; [exact H2 | lia].
Qed.

Section B1.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Let API := APIf rc.

Lemma b1_relro_bytes : forall mem a n bs, relro B mem -> Image.image_bytes rsegs a n = Some bs ->
  0x1ed20 <= a -> a + Z.of_nat n <= 0x1fb80 -> bytes_at rsegs mem a bs.
Proof.
  intros mem a n bs HR HI H0 H1. pose proof (Image.image_bytes_length rsegs n a bs HI) as L.
  unfold relro, G_img_c in HR. rewrite (sl_segs B APIf ra empty FF) in HR.
  split; [lia|]. split; [rewrite L; lia|]. intros i Hi. rewrite L in Hi.
  rewrite <- (b1_image_nth n a bs HI i Hi).
  exact (HR (a + Z.of_nat i) (b1_in_relro (a + Z.of_nat i) ltac:(lia))).
Qed.

(* The RELRO image helpers: build_as' CTRL_FRAMES rows, the catalogue rows and the whole catalogue. *)
Lemma b1_ba_bytes : forall mem, relro B mem -> bytes_at rsegs mem (reac_ctrl_build_as_c.BA_FR + 72) reac_ctrl_build_as_c.ba_tbl.
Proof.
  intros mem HR. apply (b1_relro_bytes mem _ 168 _ HR b1_ba_tbl); unfold reac_ctrl_build_as_c.BA_FR; lia.
Qed.

Lemma b1_row_bytes : forall mem i, relro B mem -> 0 <= i < CAT_N -> bytes_at rsegs mem (CAT + CAT_ROW * i) (rowb i).
Proof.
  intros mem i HR Hi. apply (b1_relro_bytes mem _ 296 _ HR (b1_rows i Hi)); unfold CAT, CAT_ROW, CAT_N in *; lia.
Qed.

Lemma b1_ax : AllocExtra B (aa_MR API).
Proof.
  pose proof FF as H. repeat apply proj2 in H.
  destruct (H rc fx) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AX & _). exact AX.
Qed.

(* A live block: its bytes are present and not read-only, so the normalized memory holds them. *)
Lemma b1_blk : forall L A mem md a n, aa_MR API L A mem md -> In (a, n) (blocks L A) ->
  stk rsegs (normalize rsegs mem) a (a + n) /\ 4096 <= a /\ a + n <= YM05.alloc_ceiling.
Proof.
  intros L A mem md a n HM Hin.
  apply blocks_In in Hin as (p & <- & Hp).
  destruct (mr_blocks_range B _ (aa_laws API) _ _ _ _ _ _ HM Hp) as [R1 R2].
  pose proof alloc_ceiling_value as Hac.
  split; [|split; lia].
  split; [lia|]. split; [lia|].
  intros x Hx.
  destruct (mr_blocks B _ (aa_laws API) L A mem md p n (x - ptr_addr L p) HM Hp ltac:(lia)) as ([b Hb] & _).
  replace (ptr_addr L p + (x - ptr_addr L p)) with x in Hb by lia.
  assert (Hro : Mem.ro_addr rsegs (wa x) = false).
  { destruct (Mem.ro_addr rsegs (wa x)) eqn:E; [|reflexivity]. exfalso.
    unfold Mem.ro_addr in E. destruct (find_segment rsegs (bv_unsigned (wa x)) 1) as [seg|] eqn:Ef; [|discriminate].
    rewrite wa_unsigned in Ef by lia.
    apply (ax_blocks_img b1_ax L A mem md p n (x - ptr_addr L p) HM Hp ltac:(lia)).
    replace (ptr_addr L p + (x - ptr_addr L p)) with x by lia.
    exact (b1_find_img B x seg (sl_segs B APIf ra empty FF) Ef). }
  assert (E : normalize rsegs mem (wa x) = Some b) by (unfold normalize; rewrite Hro; exact Hb).
  split.
  - exact (YL01.present_writable rsegs _ x (ex_intro _ b E)).
  - exists b. unfold Mem.mrd. rewrite E. reflexivity.
Qed.

Lemma b1_hb : forall g phi n L A regs mem md, FR B APIf ra empty g (hb1 phi n) L A regs mem md ->
  Permutation (blocks L A) (hb1 phi n ++ blocks (g_L g) (g_A g)) ->
  stk rsegs (normalize rsegs mem) phi (phi + n) /\ 4096 <= phi /\ phi + n <= YM05.alloc_ceiling.
Proof.
  intros g phi n L A regs mem md HFR HP. pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & _ & HM & _).
  apply (b1_blk L A mem md phi n HM).
  apply (Permutation_in _ (Permutation_sym HP)). left. reflexivity.
Qed.

Lemma b1_relro_full : forall a, in_globals frame_RELRO a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Proof.
  intros a Ha.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                  _ & _ & _ & _ & _ & _ & _ & H & _).
  exact (H a Ha).
Qed.

Lemma b1_relro_img : forall a, in_globals frame_RELRO a -> in_img B a.
Proof. intros a Ha. exact (proj1 (b1_relro_full a Ha)). Qed.

Lemma b1_syms : ms_ctx B = 0x51208 /\ ms_lock B = 0x51200 /\ ms_libc B = 0x51190 /\ ms_guard B = 0x51170 /\
  ms_got_guard B = 0x1fb80 /\ ms_size_classes B = 0x10788 /\ ms_small_cnt B = 0x107e8 /\ ms_med_cnt B = 0x10728 /\
  ms_debruijn B = 0x10704 /\ ms_vmlock B = None /\ @sk_ofl_head SH = 0x515c0 /\ @sk_ofl_lock SK = 0x515b8 /\
  @sk_threaded SK = 0x51190 + 1.
Proof.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & _ & _ & _ &
                  H20 & H21 & H22 & H23 & _).
  repeat split; assumption.
Qed.

Lemma b1_malloc_addr : ms_malloc B = 0x1649c.
Proof. destruct FF as (_ & _ & H & _). exact H. Qed.

Lemma b1_alloc : frame_allocator B API.
Proof. pose proof FF as H. repeat apply proj2 in H. exact (H rc fx). Qed.

(* The sink cells: in the image and outside the allocator's static, ctx and errno bytes. *)
Lemma b1_sink_addr : forall a, (0x51191 <= a < 0x51192 \/ 0x515b8 <= a < 0x515c8) ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Proof.
  intros a Ha. pose proof b1_syms as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _).
  pose proof (sl_errno_val B APIf ra empty FF) as Ev.
  split; [apply (b1_img_sink B a (sl_segs B APIf ra empty FF)); lia|].
  rewrite Ev. unfold static_owned, vml_lo, vml_len. rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10.
  assert (DBL : ms_debruijn_len B = 132) by (pose proof FF as FF'; unfold frame_facts in FF'; tauto).
  rewrite DBL. cbv iota. unfold CTX_SIZE. lia.
Qed.

Lemma b1_sink_frame : forall mem mem' md md',
  (forall a, (0x51191 <= a < 0x51192 \/ 0x515b8 <= a < 0x515c8) -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a) ->
  m_fds md' = m_fds md -> sink_none B mem md -> sink_none B mem' md'.
Proof.
  intros mem mem' md md' HK Hfd ((V1 & V2) & V3 & V4).
  pose proof b1_syms as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & S3).
  split; [split|split].
  - intros k Hk. rewrite <- (V1 k Hk). apply HK. rewrite S3. lia.
  - intros k Hk. rewrite <- (V2 k Hk). apply HK. rewrite S2. lia.
  - intros k Hk. rewrite <- (V3 k Hk). apply HK. rewrite S1. lia.
  - rewrite Hfd. exact V4.
Qed.

Lemma b1_call_pre : forall g hb L A regs mem md regs_c,
  FR B APIf ra empty g hb L A regs mem md -> YK11.getr regs_c 2 = YK11.getr regs 2 ->
  YK11.getr regs_c 4 = YK11.getr regs 4 -> YK0s.ret_ok (YK11.getr regs_c 1) -> call_pre B (aa_MR API) L A regs_c mem md.
Proof.
  intros g hb L A regs mem md regs_c HF E2 E4 Hra.
  pose proof HF as (HGV & Hsp & _ & Htp & _ & _ & _ & _ & HMR & HWF & HBD & HIN & _ & _ & _ & _ & HER & _ & _ & HSW).
  pose proof HGV as (_ & _ & _ & HS16 & HSK & HS47 & _ & _ & HTP0).
  pose proof alloc_ceiling_value as HAC. unfold SLOT_K, SLOT_STACK in *.
  assert (HSP : spZ regs_c = g_S g - 1936).
  { unfold spZ. rewrite E2, Hsp. unfold fsp, SLOT_FRAME. apply MState.unsigned_lit. lia. }
  unfold call_pre. rewrite HSP. unfold ALLOC_STACK.
  split; [exact HMR|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact Hra|].
  split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|].
  split; [intros a Ha; apply HSW; lia|].
  split; [rewrite E4, Htp; exact HTP0|].
  split; [exact HER|].
  intros H. rewrite HIN in H. discriminate.
Qed.

(* FR after malloc(n) from a cut with no live harness block: the new block (res, n) is the live one, and the
   frame bytes [sp, S) are unchanged. *)
Lemma b1_FR_malloc : forall g L A regs mem md regs_c n L' A' regs' mem' md' res b1 b2,
  FR B APIf ra empty g [] L A regs mem md ->
  Permutation (blocks L A) ([] ++ blocks (g_L g) (g_A g)) ->
  YK11.getr regs_c 2 = YK11.getr regs 2 -> YK11.getr regs_c 3 = YK11.getr regs 3 ->
  YK11.getr regs_c 4 = YK11.getr regs 4 ->
  call_post_k B (aa_MR API) ALLOC_STACK L A regs_c mem md (fun _ => False) L' A' regs' mem' md' ->
  blocks L' A' = b1 ++ (res, n) :: b2 -> blocks L A = b1 ++ b2 ->
  blocks_kept B L A mem mem' (fun _ => False) ->
  ro_agree (ms_segs B) mem' -> st_init_done A' = true ->
  res_ok_slots A' (sb_malloc (sb_hb (g_b g) []) n) ->
  FR B APIf ra empty g (hb1 res n) L' A' regs' mem' md' /\
  Permutation (blocks L' A') (hb1 res n ++ blocks (g_L g) (g_A g)) /\
  (forall a, fsp g <= a < g_S g -> mbyte rsegs mem' a = mbyte rsegs mem a).
Proof.
  intros g L A regs mem md regs_c n L' A' regs' mem' md' res b1 b2 HF HP E2 E3 E4 POST EB' EB KEPT RO' INIT RES'.
  pose proof (sl_segs B APIf ra empty FF) as ES.
  destruct HF as (HGV & Hsp & Hgp & Htp & Hsav & Hstk & HMI & Hrel & HMR & HWF & Hbd & Hin & Hmd & Hhi & Himg &
                  Hblk & Herr & Hsink & HRES & Hwr).
  pose proof HGV as (Hn0 & Hp0 & Hbd0 & HS16 & HSK & HS47 & Hroom & HgS & Htp0).
  destruct POST as (MR' & WF' & BD' & LL' & PA' & RP' & (vm' & Emd) & MEM & UB & SCW).
  pose proof alloc_ceiling_value as HAC. pose proof (sl_errno B APIf ra empty FF) as HEC.
  pose proof (sl_errno_val B APIf ra empty FF) as HEV.
  unfold SLOT_K, SLOT_STACK in *.
  assert (HSP : spZ regs_c = g_S g - 1936).
  { unfold spZ. rewrite E2, Hsp. unfold fsp, SLOT_FRAME. apply MState.unsigned_lit. lia. }
  assert (HOW : forall L0 A0 m0 md0 a, aa_MR API L0 A0 m0 md0 -> owned B L0 A0 a -> a < YM05.alloc_ceiling).
  { intros L0 A0 m0 md0 a H Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ H Ho). lia. }
  assert (HI : forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
      ~ (errno_addr B <= a < errno_addr B + 4) ->
      mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
      (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)).
  { intros a Ha H1 H2 H3. pose proof (sl_in_img_top B a ES Ha) as Hl. unfold SL_TOP in Hl. apply MEM.
    - right. exact Ha.
    - intros [Ho|Ho]; [exact (H2 (ax_img b1_ax L A mem md a HMR Ha Ho)) | exact (H1 Ho)].
    - intros [Ho|Ho]; [exact (H2 (ax_img b1_ax L' A' mem' md' a MR' Ha Ho)) | exact (H1 Ho)].
    - unfold scratch_k. rewrite HSP. unfold ALLOC_STACK. lia.
    - intros []. }
  assert (HH : forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ (g_S g - 1936 - 8192 <= a < g_S g - 1936) ->
      mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
      (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)).
  { intros a Ha Hs. apply MEM.
    - left. exact Ha.
    - intros Ho. pose proof (HOW _ _ _ _ a HMR Ho). lia.
    - intros Ho. pose proof (HOW _ _ _ _ a MR' Ho). lia.
    - unfold scratch_k. rewrite HSP. unfold ALLOC_STACK. lia.
    - intros []. }
  assert (HWR : forall a, g_S g - 65536 <= a < g_S g -> writable_at (ms_segs B) mem' a).
  { intros a Ha. destruct (Z_lt_le_dec a (g_S g - 1936 - 8192)) as [Hl|Hl];
      [|destruct (Z_lt_le_dec a (g_S g - 1936)) as [Hl2|Hl2]].
    - apply (proj2 (HH a ltac:(lia) ltac:(lia))). apply Hwr. lia.
    - apply SCW. unfold scratch_k. rewrite HSP. unfold ALLOC_STACK. lia.
    - apply (proj2 (HH a ltac:(lia) ltac:(lia))). apply Hwr. lia. }
  split; [|split].
  2:{ rewrite EB'. cbn [hb1 app]. eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|].
      apply perm_skip. rewrite <- EB. exact HP. }
  2:{ intros a Ha. unfold fsp, SLOT_FRAME in Ha. rewrite <- ES. exact (proj1 (HH a ltac:(lia) ltac:(lia))). }
  unfold FR, RESB, SLOT_K, SLOT_STACK.
  split; [exact HGV|].
  split; [etransitivity; [exact (RP' 2 ltac:(unfold callee_saved; lia))|]; etransitivity; [exact E2|]; exact Hsp|].
  split; [etransitivity; [exact (RP' 3 ltac:(unfold callee_saved; lia))|]; etransitivity; [exact E3|]; exact Hgp|].
  split; [etransitivity; [exact (RP' 4 ltac:(unfold callee_saved; lia))|]; etransitivity; [exact E4|]; exact Htp|].
  split.
  { apply (b1_ba_mbyte mem); [exact Hsav|]. intros i Hi.
    assert (Hl : length (saved_bytes ra g) = 104%nat)
      by (unfold saved_bytes; rewrite !length_app, !length_le8; reflexivity).
    rewrite Hl in Hi. rewrite <- ES. exact (proj1 (HH (g_S g - 104 + i) ltac:(lia) ltac:(lia))). }
  split; [apply sl_stk_of_writable; [unfold SL_TOP; lia | lia | intros a Ha; rewrite <- ES; apply HWR; exact Ha]|].
  split; [unfold MI; exact RO'|].
  split.
  { unfold relro, G_img_c in *. intros a Ha. rewrite <- (Hrel a Ha).
    destruct (b1_relro_full a Ha) as (H1 & H2 & H3 & H4). exact (proj1 (HI a H1 H2 H3 H4)). }
  split; [exact MR'|]. split; [exact WF'|]. split; [exact BD'|]. split; [exact INIT|].
  split; [destruct Hmd as (vm & ->); exists vm'; rewrite Emd; reflexivity|].
  split.
  { intros a Ha Hs He. destruct (Hhi a Ha Hs He) as [Q1 Q2]. destruct (HH a Ha ltac:(lia)) as [G1 G2].
    rewrite G1. split; [exact Q1|]. tauto. }
  split.
  { intros a Ha H1 H2 H3. destruct (Himg a Ha H1 H2 H3) as [Q1 Q2]. destruct (HI a Ha H1 H2 H3) as [G1 G2].
    rewrite G1. split; [exact Q1|]. tauto. }
  split.
  { intros a k i Hak Hi. rewrite <- (Hblk a k i Hak Hi). apply (KEPT a k i); [| exact (fun H => H) | exact Hi].
    apply (Permutation_in _ (Permutation_sym HP)). exact Hak. }
  split; [intros a Ha; apply SCW; unfold scratch_k; right; exact Ha|].
  split.
  { apply (b1_sink_frame mem mem' md md'); [|rewrite Emd; reflexivity | exact Hsink].
    intros a Ha. destruct (b1_sink_addr a Ha) as (H1 & H2 & H3 & H4). exact (proj1 (HI a H1 H2 H3 H4)). }
  split; [exact (resb_malloc (g_b g) [] (hb1 res n) A' res n (Permutation_refl _) RES')|].
  intros a Ha. apply HWR. exact Ha.
Qed.

(* malloc(n) from a cut with no live harness block, as a Kind B step: the continuation gets FR with hb = (res, n). *)
Lemma b1_malloc_call : forall g L A regs mem md regs_c n (Q : config -> Prop),
  FR B APIf ra empty g [] L A regs mem md ->
  Permutation (blocks L A) ([] ++ blocks (g_L g) (g_A g)) ->
  YK11.getr regs_c 2 = YK11.getr regs 2 -> YK11.getr regs_c 3 = YK11.getr regs 3 ->
  YK11.getr regs_c 4 = YK11.getr regs 4 ->
  YK0s.ret_ok (YK11.getr regs_c 1) -> YK11.getr regs_c 10 = Z_to_bv 64 n -> 0 <= n <= 2 ^ 20 ->
  (forall L' A' regs' mem' md' res, FR B APIf ra empty g (hb1 res n) L' A' regs' mem' md' ->
     Permutation (blocks L' A') (hb1 res n ++ blocks (g_L g) (g_A g)) -> regs_preserved regs_c regs' ->
     YK11.getr regs' 10 = Z_to_bv 64 res -> res <> 0 ->
     (forall a, fsp g <= a < g_S g -> mbyte rsegs mem' a = mbyte rsegs mem a) ->
     SR (ms_segs B) (mkCfg (YK11.mkst regs' (YK11.getr regs_c 1) mem' (YK11.seg_rom (ms_segs B))) md') Q) ->
  SR (ms_segs B) (mkCfg (YK11.mkst regs_c (Z_to_bv 64 0x1649c) mem (YK11.seg_rom (ms_segs B))) md) Q.
Proof.
  intros g L A regs mem md regs_c n Q HF HP E2 E3 E4 Hra H10 Hn K.
  pose proof (b1_call_pre g [] L A regs mem md regs_c HF E2 E4 Hra) as CP.
  pose proof HF as (HGV & _ & _ & _ & _ & _ & HMI & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hb & _).
  pose proof HGV as (_ & _ & _ & _ & _ & _ & Hroom & _).
  destruct b1_alloc as (MAL & _).
  rewrite <- b1_malloc_addr.
  eapply SR_bind.
  { exact (MAL L A regs_c mem md n (sb_hb (g_b g) []) CP HMI H10 Hb
             (resb_room (g_b g) [] n Hroom ltac:(cbn; lia) ltac:(cbn; lia) Hn)). }
  intros c' (L' & A' & regs' & mem' & md' & res & -> & POST & H10' & Hres & _ & _ & (b1 & b2 & EB' & EB) & KEPT &
             RO' & _ & _ & INIT & _ & RES').
  pose proof POST as (_ & _ & _ & _ & _ & RP' & _).
  destruct (b1_FR_malloc g L A regs mem md regs_c n L' A' regs' mem' md' res b1 b2 HF HP E2 E3 E4 POST EB' EB KEPT
              RO' INIT RES') as (HF' & HP' & HK).
  exact (K L' A' regs' mem' md' res HF' HP' RP' H10' Hres HK).
Qed.

Lemma b1_sink_keep : forall (m m' : word -> option byte) md,
  (forall a, in_img B a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) -> sink_none B m md -> sink_none B m' md.
Proof.
  intros m m' md HK (Henv & Hhead & Hn). destruct (sl_sink B APIf ra empty FF) as (E1 & E2 & E3).
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  assert (HM : forall a, 0x51190 <= a < 0x515c8 -> mbyte (ms_segs B) m' a = mbyte (ms_segs B) m a).
  { intros a Ha. unfold mbyte. rewrite (HK a (b1_img_sink B a SEGS Ha)). reflexivity. }
  destruct Henv as [Ht Hl]. split; [split|split; [|exact Hn]].
  - eapply val_mem_frame; [|exact Ht]. intros x Hx. apply HM. rewrite E3 in Hx. cbn in Hx. lia.
  - eapply val_mem_frame; [|exact Hl]. intros x Hx. apply HM. rewrite E2 in Hx. cbn in Hx. lia.
  - apply (val_mem_word_mem (ms_segs B)). apply (val_mem_word_mem (ms_segs B)) in Hhead.
    eapply val_mem_frame; [|exact Hhead]. intros x Hx. apply HM. rewrite E1 in Hx. cbn in Hx. lia.
Qed.

(* FR across a run that writes the stack window [S - K, S - 104) and the live harness block [phi, phi + n). *)
Lemma b1_fr_hb : forall g phi n L A regs mem md regs' mem',
  FR B APIf ra empty g (hb1 phi n) L A regs mem md ->
  Permutation (blocks L A) (hb1 phi n ++ blocks (g_L g) (g_A g)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (g_S g - SLOT_K <= a < g_S g - 104) -> ~ (phi <= a < phi + n) ->
     mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, phi <= a < phi + n -> exists b, mrd rsegs mem' (wa a) = Some b) ->
  Frame.wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  YK11.getr regs' 2 = YK11.getr regs 2 -> YK11.getr regs' 3 = YK11.getr regs 3 ->
  YK11.getr regs' 4 = YK11.getr regs 4 ->
  FR B APIf ra empty g (hb1 phi n) L A regs' mem' md.
Proof.
  intros g phi n L A regs mem md regs' mem' HFR HP HU Hpres WM MI' E2 E3 E4.
  destruct HFR as (HGV & F2 & F3 & F4 & Hsv & Hstk & HMI & Hrel & HM & HWf & HB & HID & Hmd & Hhigh & Himg &
                   Hblk & Herr & Hsn & Hres & Hwin).
  pose proof HGV as (_ & _ & _ & HS16 & HSK & HS47 & _).
  pose proof alloc_ceiling_value as Hac. pose proof (sl_segs B APIf ra empty FF) as SEGS.
  unfold SLOT_K, SLOT_STACK in *.
  assert (Hin : In (phi, n) (blocks L A)) by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
  apply blocks_In in Hin as (p & Ep & Hp).
  destruct (mr_blocks_range B _ (aa_laws API) _ _ _ _ _ _ HM Hp) as [R1 R2]. rewrite Ep in R1, R2.
  assert (Hnimg : forall a, phi <= a < phi + n -> ~ in_img B a).
  { intros a Ha Hi. apply (ax_blocks_img b1_ax L A mem md p n (a - phi) HM Hp ltac:(lia)).
    rewrite Ep. replace (phi + (a - phi)) with a by lia. exact Hi. }
  assert (Hnown : forall a, phi <= a < phi + n -> ~ owned B L A a).
  { intros a Ha. destruct (mr_blocks B _ (aa_laws API) L A mem md p n (a - phi) HM Hp ltac:(lia)) as (_ & _ & _ & H).
    rewrite Ep in H. replace (phi + (a - phi)) with a in H by lia. exact H. }
  assert (HL : forall a, 0 <= a < YM05.alloc_ceiling -> ~ (phi <= a < phi + n) ->
                 mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hn. apply HU; lia. }
  assert (HI : forall a, in_img B a -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha. pose proof (sl_in_img_top B a SEGS Ha) as Ht. unfold SL_TOP in Ht.
    apply HL; [lia | intro Hc; exact (Hnimg a Hc Ha)]. }
  assert (Hwr : forall a, writable_at (ms_segs B) mem a -> writable_at (ms_segs B) mem' a).
  { intros a W. unfold writable_at in *. rewrite SEGS in *. apply WM. exact W. }
  split; [exact HGV|]. split; [rewrite E2; exact F2|]. split; [rewrite E3; exact F3|].
  split; [rewrite E4; exact F4|].
  split.
  { apply (sl_bytes_keep mem mem' _ _ Hsv). intros i Hi. unfold saved_bytes in Hi.
    rewrite !length_app, !length_le8 in Hi. cbn in Hi. apply HU; lia. }
  split.
  { apply sl_stk_of_writable; [unfold SL_TOP, SLOT_K, SLOT_STACK; lia | lia |].
    intros a Ha. rewrite <- SEGS. apply Hwr, Hwin. exact Ha. }
  split; [unfold MI; rewrite SEGS; exact MI'|].
  split.
  { unfold relro, G_img_c in *. intros a Ha. rewrite <- (Hrel a Ha).
    unfold mbyte. rewrite (HI a (b1_relro_img a Ha)). reflexivity. }
  split.
  { destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & Hmat).
    eapply (mr_frame B (aa_MR API) (aa_laws API)); [exact HM | | | | reflexivity | exact Hh | exact Hl | exact Hmat].
    - intros a Ho. pose proof (mr_owned_low B (aa_MR API) (aa_laws API) _ _ _ _ a HM Ho) as Ha.
      unfold mbyte. rewrite (HL a Ha (fun Hc => Hnown a Hc Ho)). reflexivity.
    - intros a Ho [bb Hb]. pose proof (mr_owned_low B (aa_MR API) (aa_laws API) _ _ _ _ a HM Ho) as Ha.
      exists bb. rewrite (HL a Ha (fun Hc => Hnown a Hc Ho)). exact Hb.
    - intros q k i Hq Hi.
      destruct (mr_blocks B (aa_MR API) (aa_laws API) L A mem md q k i HM Hq Hi) as ([bb Hpr] & H1 & H2 & _).
      destruct (Z_le_dec phi (ptr_addr L q + i)) as [Hl1|Hl1];
        [destruct (Z_lt_dec (ptr_addr L q + i) (phi + n)) as [Hl2|Hl2]|].
      + destruct (Hpres _ (conj Hl1 Hl2)) as (b' & Hb').
        exact (b1_present B mem' _ b' SEGS (Hnimg _ (conj Hl1 Hl2)) ltac:(lia) Hb').
      + exists bb. rewrite (HL (ptr_addr L q + i) ltac:(lia) ltac:(lia)). exact Hpr.
      + exists bb. rewrite (HL (ptr_addr L q + i) ltac:(lia) ltac:(lia)). exact Hpr. }
  split; [exact HWf|]. split; [exact HB|]. split; [exact HID|]. split; [exact Hmd|].
  split.
  { intros a Ha Hns Hne. destruct (Hhigh a Ha Hns Hne) as [Q1 Q2]. unfold SLOT_K, SLOT_STACK in Hns.
    rewrite SEGS in *. destruct (sl_eq_at mem mem' a (HU a ltac:(lia) ltac:(lia) ltac:(lia))) as [G1 G2].
    split; [rewrite G1; exact Q1 | rewrite Q2; exact G2]. }
  split.
  { intros a H1 H2 H3 H4. destruct (Himg a H1 H2 H3 H4) as [Q1 Q2].
    destruct (sl_eq_at mem mem' a (HI a H1)) as [G1 G2]. rewrite SEGS in *.
    split; [rewrite G1; exact Q1 | rewrite Q2; exact G2]. }
  split.
  { intros a k i Hin Hi. rewrite <- (Hblk a k i Hin Hi).
    assert (HinL : In (a, k) (blocks L A)) by (apply (Permutation_in _ (Permutation_sym HP)); right; exact Hin).
    apply blocks_In in HinL as (q & Eq & Hq).
    destruct (mr_blocks B (aa_MR API) (aa_laws API) L A mem md q k i HM Hq Hi) as (_ & H1 & H2 & _).
    rewrite Eq in H1, H2.
    pose proof (mr_blocks_disjoint B _ (aa_laws API) _ _ _ _ HM) as PD.
    apply (b1_pw_perm _ ranges_disjoint b1_rd_sym _ _ HP) in PD.
    destruct PD as [PD _]. pose proof (PD (a, k) Hin) as Hd. unfold ranges_disjoint in Hd. cbn [fst snd] in Hd.
    unfold mbyte. rewrite (HL (a + i) ltac:(lia) ltac:(lia)). reflexivity. }
  split; [intros a Ha; apply Hwr; exact (Herr a Ha)|].
  split; [exact (b1_sink_keep mem mem' md HI Hsn)|].
  split; [exact Hres|].
  intros a Ha. apply Hwr, Hwin. exact Ha.
Qed.

End B1.
