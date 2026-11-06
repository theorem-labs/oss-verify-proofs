(* Helpers of batch u1 (segments A02, A03, R01-R09 of fuzz_ctrl LLVMFuzzerTestOneInput, ubsan): the plain batch
   helpers (Tac_b1.v of a working branch, part of Tac_b2m.v of a working branch) at the ubsan frame (1936), the
   ubsan registers and the ubsan image; the ubsan image helpers (build_as' ba_tbl at 0x209c8, the catalogue rows at
   0x1fcc8 + 296 i, KIND_NAME at 0x1fc58, all in frame_RELRO); CATU and PB (slot-plan-ubsan.md section 7 (a working note, not in this delivery)). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInvCF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFrag RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcEmit RcEmitLib RcLay RcSynth RcSynthLib RcFinLib
  RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require reac_ctrl_build_as_c reac_ctrl_kind_name_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Tac_slot.
Import ListNotations.
Open Scope Z_scope.

(* Bytes a segment does not touch: from the cut's memory through the normalized run to the next cut's memory. *)
Lemma u1_keep : forall W mem m0 m' a bs, ro_agree rsegs mem -> Frame.munch W (normalize rsegs mem) m0 ->
  mem_rel rsegs m' m0 -> Frame.disjoint_from W a (Z.of_nat (length bs)) ->
  bytes_at rsegs mem a bs -> bytes_at rsegs m' a bs.
Proof.
  intros W mem m0 m' a bs Hro MU Hrel HD H.
  apply (proj2 (bytes_at_rel rsegs m' m0 a bs Hrel)).
  exact (bytes_at_transport rsegs W (normalize rsegs mem) m0 a bs (bytes_at_normalize rsegs mem a bs Hro H) MU HD).
Qed.

(* The bytes the run itself leaves at a: from the run's final memory to the next cut's memory. *)
Lemma u1_out : forall m0 m' a bs, mem_rel rsegs m' m0 -> bytes_at rsegs m0 a bs -> bytes_at rsegs m' a bs.
Proof. intros m0 m' a bs Hrel H. exact (proj2 (bytes_at_rel rsegs m' m0 a bs Hrel) H). Qed.

(* beqz / bnez on a non-zero value. *)
Lemma u1_beq0 : forall z, 0 < z < 2 ^ 64 -> bv_eqb (Z_to_bv 64 z) (Z_to_bv 64 0) = false.
Proof. intros z Hz. unfold bv_eqb. rewrite !MState.unsigned_lit by lia. apply Z.eqb_neq. lia. Qed.

(* bltu / bgeu on in-range values. *)
Lemma u1_ltu_false : forall a b, 0 <= b <= a -> a < 2 ^ 64 -> bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = false.
Proof. intros a b H1 H2. unfold bv_ltu. rewrite !MState.unsigned_lit by lia. apply Z.ltb_ge. lia. Qed.

Lemma u1_ltu_true : forall a b, 0 <= a < b -> b < 2 ^ 64 -> bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = true.
Proof. intros a b H1 H2. unfold bv_ltu. rewrite !MState.unsigned_lit by lia. apply Z.ltb_lt. lia. Qed.

(* An 8-byte load from a q64 cell. *)
Lemma u1_ld8 : forall m a v, bytes_at rsegs m a (le8 v) -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 v).
Proof.
  intros m a v H. replace (wa a) with (wa (a + Z.of_nat 0)) by (f_equal; lia).
  rewrite (bytes_at_ov_read rsegs m a (le8 v) 0 8 H) by (rewrite length_le8; lia).
  reflexivity.
Qed.

(* A 1-byte load from a byte cell. *)
Lemma u1_ld1 : forall m a b, bytes_at rsegs m a [b] -> ov_read_bytes rsegs m (wa a) 1 = Some [b].
Proof.
  intros m a b H. replace (wa a) with (wa (a + Z.of_nat 0)) by (f_equal; lia).
  rewrite (bytes_at_ov_read rsegs m a [b] 0 1 H) by (cbn; lia).
  reflexivity.
Qed.

Lemma u1_firstn1 : forall (l : list byte) k, (k < length l)%nat ->
  firstn 1 (skipn k l) = [RcIdentModel.nthb l k].
Proof.
  intros l k Hk. unfold RcIdentModel.nthb. revert k Hk.
  induction l as [|x l IH]; intros [|k] Hk; cbn [skipn nth firstn length] in *; try lia; [reflexivity|].
  apply IH. lia.
Qed.

(* andi x,1 (the low bit) as the parity. *)
Lemma u1_land1 : forall x, Z.land x 1 = if Z.odd x then 1 else 0.
Proof.
  intros x. change (Z.land x 1) with (Z.land x (Z.ones 1)). rewrite Z.land_ones by lia. change (2 ^ 1) with 2.
  destruct (Z.odd x) eqn:E.
  - apply Z.odd_spec in E. destruct E as (k & ->).
    rewrite Z.add_comm, Z.mul_comm, Z_mod_plus_full. reflexivity.
  - assert (Ev : Z.even x = true) by (rewrite <- Z.negb_odd, E; reflexivity).
    apply Z.even_spec in Ev. destruct Ev as (k & ->). rewrite Z.mul_comm, Z_mod_mult. reflexivity.
Qed.

Lemma u1_remu : forall a b, 0 <= a < 2 ^ 64 -> 0 < b < 2 ^ 64 ->
  mul_div Instr.M_REMU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a mod b).
Proof.
  intros a b Ha Hb. unfold mul_div. rewrite (MState.unsigned_lit b) by lia.
  replace (b =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  apply bv_eq. rewrite bv_modu_unsigned, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616 in *.
  rewrite (Z.mod_small a) by lia. rewrite (Z.mod_small b) by lia.
  rewrite (Z.mod_small (a mod b)); [reflexivity|]. pose proof (Z.mod_pos_bound a b ltac:(lia)). lia.
Qed.

Lemma u1_byte_rng : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. exact R. Qed.

Lemma u1_mode_rng : forall inp, 0 <= mode inp < 256.
Proof.
  intros inp. unfold mode, inb, RcIdentModel.bz. destruct (7 <=? nlen inp); [apply u1_byte_rng | lia].
Qed.

(* ---- CATU (slot-plan-ubsan.md section 7): T' + 296 i, i <= 10 ---- *)

Lemma u1_catu : forall i, 0 <= i <= 10 ->
  0 < CAT + CAT_ROW * i < 2 ^ 32 /\ (CAT + CAT_ROW * i) mod 8 = 0 /\ 0 <= CAT_ROW * i < 2 ^ 63.
Proof.
  intros i Hi. unfold CAT, CAT_ROW. split; [lia|]. split; [|lia].
  replace (130248 + 296 * i) with ((16281 + 37 * i) * 8) by lia. apply Z.mod_mul. lia.
Qed.

Lemma u1_istar_rng : forall inp, 0 <= istar inp < CAT_N.
Proof. intros inp. unfold istar, CAT_N. apply Z.mod_pos_bound. lia. Qed.

Lemma u1_mrow : forall inp,
  CAT <= mrow inp <= CAT + CAT_ROW * 10 /\ 0 < mrow inp < 2 ^ 32 /\ mrow inp mod 8 = 0.
Proof.
  intros inp. pose proof (u1_istar_rng inp) as H. unfold CAT_N in H.
  destruct (u1_catu (istar inp) ltac:(lia)) as (H1 & H2 & _). unfold mrow.
  split; [unfold CAT, CAT_ROW; lia|]. split; [exact H1 | exact H2].
Qed.

(* ---- Lengths of the round-trip model ---- *)

Lemma u1_fg_st_len : forall len st g, length st = 72%nat -> length g = 50%nat -> length (fg_st len st g) = 72%nat.
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

Lemma u1_RS_len : forall inp b, length (RID inp b) = 38%nat /\ length (RFG inp b) = 72%nat.
Proof.
  intros inp b. unfold RID, RFG. induction b as [|b [IH1 IH2]]; [split; reflexivity|].
  cbn [rt_st].
  destruct (rt_n inp (Z.of_nat b) =? 0); [exact (conj IH1 IH2)|].
  destruct ((Z.of_nat b =? 3) || (Z.of_nat b =? 4)); cbn [fst snd].
  - split; [|exact IH2]. unfold rp_id. destruct (RcReply.ir _ _); [apply RcIdentModel.ING_length; exact IH1 | exact IH1].
  - destruct ((Z.of_nat b =? 5) || (Z.of_nat b =? 6)); cbn [fst snd]; [|exact (conj IH1 IH2)].
    split.
    + unfold fg_id. destruct (fg_rf _ _ _ =? 1); [apply RcIdentModel.ING_length; exact IH1 | exact IH1].
    + apply u1_fg_st_len; [exact IH2 | apply fr50_length].
Qed.

Lemma u1_row_len : forall i, length (rowb i) = 296%nat.
Proof.
  intros i. unfold rowb, img. destruct (Image.image_bytes rsegs (CAT + CAT_ROW * i) 296) eqn:E.
  - exact (Image.image_bytes_length rsegs 296 _ _ E).
  - apply repeat_length.
Qed.

Lemma u1_rtX_len : forall inp b, length (rt_X inp b) = 32%nat.
Proof.
  intros inp b. unfold rt_X, reac_ctrl_build_as_c.ba_X, RcLay.ly_Z.
  assert (HZ : length (if mrow inp =? 0 then RcLay.ly_zero
                       else if RcSynth.rc (rt_mb inp) b =? 1 then RcSynth.synth (rt_mb inp) b (rt_nb inp)
                       else RcLay.ly_zero) = 32%nat).
  { destruct (mrow inp =? 0); [reflexivity|].
    destruct (RcSynth.rc (rt_mb inp) b =? 1); [|reflexivity].
    apply RcSynthLib.rs_synth_len. apply u1_row_len. }
  destruct (b <=? 1); [apply RcFinLib.rcf_stamp32_len; exact HZ | exact HZ].
Qed.

(* n_b != 0: E(b), 124 <= n_b <= 1492, and F_b has n_b bytes. *)
Lemma u1_rtn : forall inp b, rt_n inp b <> 0 ->
  rt_E inp b = true /\ 124 <= rt_n inp b <= 1492 /\ length (rt_F inp b) = Z.to_nat (rt_n inp b).
Proof.
  intros inp b H. unfold rt_n in *. destruct (rt_E inp b) eqn:E; [|congruence].
  pose proof E as E'. unfold rt_E, reac_ctrl_build_as_c.ba_E in E'. apply andb_true_iff in E' as [Ew _].
  destruct (RcEmitLib.em_wok_range _ Ew) as [R _].
  split; [reflexivity|]. split; [lia|].
  unfold rt_F, RcEmit.em_fr, RcEmit.em_hdr, box6. unfold rt_n. rewrite E.
  rewrite !length_app, OUR_length, length_map, u1_rtX_len, repeat_length. cbn [length]. lia.
Qed.

(* The first 50 bytes of a frame of n_b >= 50 bytes are read from F_b itself. *)
Lemma u1_fr50_nth : forall bs i, (i < 50)%nat -> (50 <= length bs)%nat -> nth_error (fr50 bs) i = nth_error bs i.
Proof.
  intros bs i Hi Hl. unfold fr50. rewrite nth_error_firstn. destruct (Nat.ltb_spec i 50) as [_|]; [|lia].
  rewrite nth_error_app1 by lia. reflexivity.
Qed.

(* n_b != 0 is 52 + 36 u with 2 <= u <= 40 (em_wok). *)
Lemma u1_rtn_u : forall inp b, rt_n inp b <> 0 -> exists u, rt_n inp b = 52 + 36 * u /\ 2 <= u <= 40.
Proof.
  intros inp b H. unfold rt_n in *. destruct (rt_E inp b) eqn:E; [|congruence].
  unfold rt_E, reac_ctrl_build_as_c.ba_E in E. apply andb_true_iff in E as [Ew _].
  destruct (RcEmitLib.em_wok_range _ Ew) as [R _]. exists (rt_uw inp). split; [reflexivity | exact R].
Qed.

(* n_b = 0: the turn leaves id and frag as they were. *)
Lemma u1_RS_zero : forall inp b, rt_n inp (Z.of_nat b) = 0 -> RID inp (S b) = RID inp b /\ RFG inp (S b) = RFG inp b.
Proof. intros inp b H. unfold RID, RFG. cbn [rt_st]. rewrite H. split; reflexivity. Qed.

(* A check over n_b = 52 + 36 u, 2 <= u <= 40, done by computation for each u. *)
Lemma u1_u_cases : forall (P : Z -> Prop) (f : Z -> bool), (forall u, f u = true -> P u) ->
  forallb f (map Z.of_nat (seq 2 39)) = true -> forall u, 2 <= u <= 40 -> P u.
Proof.
  intros P f HP Hall u Hu. apply HP. rewrite forallb_forall in Hall. apply Hall.
  apply in_map_iff. exists (Z.to_nat u). split; [lia|]. apply in_seq. lia.
Qed.

(* Goal c = false where c mentions n, with Hu : exists u, n = 52 + 36 u /\ 2 <= u <= 40. *)
Ltac u1_by_u Hu :=
  let u := fresh "u" in let Hr := fresh "Hr" in
  destruct Hu as (u & -> & Hr); revert u Hr;
  lazymatch goal with
  | |- forall u, _ -> @?e u = false =>
      apply (u1_u_cases (fun u => e u = false) (fun u => negb (e u)));
      [intros ? H; apply Bool.negb_true_iff in H; exact H | vm_compute; reflexivity]
  end.

(* ---- Memory: slices, sub-windows, alignment ---- *)

Lemma u1_dj_sub : forall W a n a' n', Frame.disjoint_from W a n -> a <= a' -> a' + n' <= a + n ->
  Frame.disjoint_from W a' n'.
Proof.
  induction W as [|[lo hi] W IH]; cbn [disjoint_from]; intros a n a' n' H H1 H2; [exact I|].
  destruct H as [H H']. split; [lia | exact (IH a n a' n' H' H1 H2)].
Qed.

Lemma u1_ba_mbyte : forall m m' a bs, bytes_at rsegs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) ->
  bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs (H1 & H2 & H) Hk. split; [exact H1|]. split; [exact H2|].
  intros i Hi. rewrite <- (H i Hi). pose proof (Hk (Z.of_nat i) ltac:(lia)) as E. unfold mbyte in E.
  unfold Mem.mrd, wa. exact E.
Qed.

Lemma u1_at_slice : forall m a bs k n, bytes_at rsegs m a bs -> (k + n <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m a bs k n (H1 & H2 & H3) Hk.
  assert (L : length (firstn n (skipn k bs)) = n) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite L; lia|]. intros i Hi. rewrite L in Hi.
  rewrite nth_error_firstn. destruct (Nat.ltb_spec i n) as [_|]; [|lia].
  rewrite nth_error_skipn. replace (a + Z.of_nat k + Z.of_nat i) with (a + Z.of_nat (k + i)) by lia.
  apply H3. lia.
Qed.

Lemma u1_fr50_eq : forall bs, (50 <= length bs)%nat -> fr50 bs = firstn 50 bs.
Proof.
  intros bs H. unfold fr50. rewrite firstn_app. replace (50 - length bs)%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r. reflexivity.
Qed.

Lemma u1_fr50_at : forall m a bs, bytes_at rsegs m a bs -> (50 <= length bs)%nat -> bytes_at rsegs m a (fr50 bs).
Proof.
  intros m a bs H L. rewrite (u1_fr50_eq bs L).
  pose proof (u1_at_slice m a bs 0 50 H ltac:(lia)) as E. rewrite Z.add_0_r in E. exact E.
Qed.

Lemma u1_stk_sub : forall m lo hi lo' hi', stk rsegs m lo hi -> lo <= lo' -> hi' <= hi -> 0 <= lo' ->
  stk rsegs m lo' hi'.
Proof. intros m lo hi lo' hi' (H1 & H2 & H) E1 E2 E3. split; [exact E3|]. split; [lia|]. intros a Ha. apply H. lia. Qed.

Lemma u1_mod : forall s k d, s mod 16 = 0 -> 0 < d -> 16 mod d = 0 -> k mod d = 0 -> (s + k) mod d = 0.
Proof.
  intros s k d Hs Hd H16 Hk.
  apply (proj2 (Z.mod_divide (s + k) d ltac:(lia))). apply Z.divide_add_r.
  - apply (Z.divide_trans d 16 s).
    + apply (proj1 (Z.mod_divide 16 d ltac:(lia))). exact H16.
    + apply (proj1 (Z.mod_divide s 16 ltac:(lia))). exact Hs.
  - apply (proj1 (Z.mod_divide k d ltac:(lia))). exact Hk.
Qed.

(* The reply's result on a frame with IR. *)
Lemma u1_reply_ok : forall fr len pa pp pn g, fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> ir len g = true ->
  reply_ok fr len pa pp pn g = true /\ reply_ret fr len pa pp pn g = 1.
Proof.
  intros fr len pa pp pn g H1 H2 H3 H4 Hir. unfold reply_ok, reply_ret, reply_args.
  rewrite (proj2 (Z.eqb_neq fr 0) H1), (proj2 (Z.eqb_neq pa 0) H2), (proj2 (Z.eqb_neq pp 0) H3),
    (proj2 (Z.eqb_neq pn 0) H4), Hir.
  split; reflexivity.
Qed.

(* ---- The round-trip bundles across a run that writes none of RB's bytes: M8 [sp+24, sp+32), the round trip's
   id [sp+36, sp+74), OURb and FGB [sp+114, sp+192) ---- *)

(* YK11.getr: the getr of SlotInv's rg (PropExec has its own getr). RB reads s0, s1, s2, s3, s6-s11. *)
Definition u1_kr (regs' regs : bvmap 5 word) : Prop :=
  YK11.getr regs' 8 = YK11.getr regs 8 /\ YK11.getr regs' 9 = YK11.getr regs 9 /\
  YK11.getr regs' 18 = YK11.getr regs 18 /\ YK11.getr regs' 19 = YK11.getr regs 19 /\
  YK11.getr regs' 22 = YK11.getr regs 22 /\ YK11.getr regs' 23 = YK11.getr regs 23 /\
  YK11.getr regs' 24 = YK11.getr regs 24 /\ YK11.getr regs' 25 = YK11.getr regs 25 /\
  YK11.getr regs' 26 = YK11.getr regs 26 /\ YK11.getr regs' 27 = YK11.getr regs 27.

Lemma u1_kr_pres : forall regs regs', regs_preserved regs regs' -> u1_kr regs' regs.
Proof.
  intros regs regs' RP.
  refine (conj (RP 8 _) (conj (RP 9 _) (conj (RP 18 _) (conj (RP 19 _) (conj (RP 22 _) (conj (RP 23 _)
         (conj (RP 24 _) (conj (RP 25 _) (conj (RP 26 _) (RP 27 _)))))))))).
  all: unfold callee_saved; lia.
Qed.

(* A register conjunct of RB at regs' from the same conjunct at regs (whichever of the kept registers it names). *)
Ltac u1_kr_rw E8 E9 E18 E19 E22 E23 E24 E25 E26 E27 :=
  rewrite ?E8, ?E9, ?E18, ?E19, ?E22, ?E23, ?E24, ?E25, ?E26, ?E27; assumption.

(* A byte conjunct of RB inside one of its three windows. *)
Ltac u1_rbw_sub HD24 HD36 HD114 :=
  first [ apply (u1_dj_sub _ _ _ _ _ HD24); unfold spk; lia
        | apply (u1_dj_sub _ _ _ _ _ HD36); unfold spk; lia
        | apply (u1_dj_sub _ _ _ _ _ HD114); unfold spk; lia ].

Lemma u1_RB_keep : forall g b idb fgb regs regs' mem m0 m' W,
  ro_agree rsegs mem -> Frame.munch W (normalize rsegs mem) m0 -> mem_rel rsegs m' m0 ->
  length idb = 38%nat -> length fgb = 72%nat ->
  Frame.disjoint_from W (spk g 24) 8 /\ Frame.disjoint_from W (spk g 36) 38 /\
    Frame.disjoint_from W (spk g 114) 78 ->
  u1_kr regs' regs -> RB g b idb fgb regs mem -> RB g b idb fgb regs' m'.
Proof.
  intros g b idb fgb regs regs' mem m0 m' W Hro MU Hrel L1 L2 (HD24 & HD36 & HD114)
    (E8 & E9 & E18 & E19 & E22 & E23 & E24 & E25 & E26 & E27)
    (Hb & (Hc & Hc1 & Hc2) & HO & (H8 & H18 & H19 & H24 & H25 & H26 & H27) & HM8 & H9 & HI & HF).
  unfold RB, CUR, RT, rg, OURb, RIDB, IDB, FGB, M8, q64 in *.
  split; [exact Hb|].
  split; [split; [exact Hc|]; split; u1_kr_rw E8 E9 E18 E19 E22 E23 E24 E25 E26 E27|].
  split.
  { apply (u1_keep W mem m0 m' _ _ Hro MU Hrel); [|exact HO].
    rewrite OUR_length. u1_rbw_sub HD24 HD36 HD114. }
  split.
  { rewrite ?E8, ?E9, ?E18, ?E19, ?E22, ?E23, ?E24, ?E25, ?E26, ?E27. auto 8. }
  split.
  { apply (u1_keep W mem m0 m' _ _ Hro MU Hrel); [|exact HM8].
    rewrite length_le8. u1_rbw_sub HD24 HD36 HD114. }
  split; [u1_kr_rw E8 E9 E18 E19 E22 E23 E24 E25 E26 E27|].
  split.
  { apply (u1_keep W mem m0 m' _ _ Hro MU Hrel); [|exact HI].
    rewrite L1. u1_rbw_sub HD24 HD36 HD114. }
  apply (u1_keep W mem m0 m' _ _ Hro MU Hrel); [|exact HF].
  rewrite L2. u1_rbw_sub HD24 HD36 HD114.
Qed.

(* RB across a step that keeps the bytes [sp+24, sp+192) (an allocator call). *)
Lemma u1_RB_mb : forall g b idb fgb regs regs' m m',
  (forall a, spk g 24 <= a < spk g 192 -> mbyte rsegs m' a = mbyte rsegs m a) ->
  length idb = 38%nat -> length fgb = 72%nat -> u1_kr regs' regs -> RB g b idb fgb regs m -> RB g b idb fgb regs' m'.
Proof.
  intros g b idb fgb regs regs' m m' HM L1 L2 (E8 & E9 & E18 & E19 & E22 & E23 & E24 & E25 & E26 & E27)
    (Hb & (Hc & Hc1 & Hc2) & HO & (H8 & H18 & H19 & H24 & H25 & H26 & H27) & HM8 & H9 & HI & HF).
  unfold RB, CUR, RT, rg, OURb, RIDB, IDB, FGB, M8, q64 in *.
  split; [exact Hb|].
  split; [split; [exact Hc|]; split; u1_kr_rw E8 E9 E18 E19 E22 E23 E24 E25 E26 E27|].
  split.
  { apply (u1_ba_mbyte m m' _ _ HO). rewrite OUR_length. intros i Hi. apply HM. unfold spk. lia. }
  split; [rewrite ?E8, ?E9, ?E18, ?E19, ?E22, ?E23, ?E24, ?E25, ?E26, ?E27; auto 8|].
  split.
  { apply (u1_ba_mbyte m m' _ _ HM8). rewrite length_le8. intros i Hi. apply HM. unfold spk. lia. }
  split; [u1_kr_rw E8 E9 E18 E19 E22 E23 E24 E25 E26 E27|].
  split; [apply (u1_ba_mbyte m m' _ _ HI); rewrite L1; intros i Hi; apply HM; unfold spk; lia|].
  apply (u1_ba_mbyte m m' _ _ HF). rewrite L2. intros i Hi. apply HM. unfold spk; lia.
Qed.

(* RFx also reads s4 (Φ) and s5 (n_b). *)
Definition u1_krf (regs' regs : bvmap 5 word) : Prop :=
  u1_kr regs' regs /\ YK11.getr regs' 20 = YK11.getr regs 20 /\ YK11.getr regs' 21 = YK11.getr regs 21.

(* RFx across a run that writes neither RB's bytes nor the block. *)
Lemma u1_RFx_keep : forall g b idb fgb phi regs regs' mem m0 m' W,
  ro_agree rsegs mem -> Frame.munch W (normalize rsegs mem) m0 -> mem_rel rsegs m' m0 ->
  length idb = 38%nat -> length fgb = 72%nat ->
  Frame.disjoint_from W (spk g 24) 8 /\ Frame.disjoint_from W (spk g 36) 38 /\
    Frame.disjoint_from W (spk g 114) 78 ->
  Frame.disjoint_from W phi (rnb g b) -> u1_krf regs' regs ->
  RFx g b idb fgb phi regs mem -> RFx g b idb fgb phi regs' m'.
Proof.
  intros g b idb fgb phi regs regs' mem m0 m' W Hro MU Hrel L1 L2 HD HDp (KR & E20 & E21)
    ((HRB & Hnz & H20 & HF) & H21).
  destruct (u1_rtn (g_in g) (Z.of_nat b) Hnz) as (_ & HB & HL).
  unfold RFx, RFb, rg in *. rewrite E20, E21.
  split; [split; [|split; [exact Hnz|]; split; [exact H20|]]|exact H21].
  - exact (u1_RB_keep g b idb fgb regs regs' mem m0 m' W Hro MU Hrel L1 L2 HD KR HRB).
  - apply (u1_keep W mem m0 m' _ _ Hro MU Hrel); [|exact HF].
    unfold rFb, rnb in *. rewrite HL, Z2Nat.id by lia. exact HDp.
Qed.

(* ---- RELRO and read-only image bytes ---- *)

Lemma u1_image_nth : forall n A bs, Image.image_bytes rsegs A n = Some bs ->
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

(* The ubsan image helpers: CTRL_FRAMES rows 3 .. 9 (build_as' table) at 0x209c8, the 11 rows of BOX_CATALOGUE at
   0x1fcc8 + 296 i and KIND_NAME at 0x1fc58, read from the image (all three lie in GNU_RELRO, frame_RELRO). *)
Lemma u1_ba_tbl : Image.image_bytes rsegs 0x209c8 168 = Some reac_ctrl_build_as_c.ba_tbl.
Proof. vm_compute. reflexivity. Qed.

Lemma u1_rows : forall i, 0 <= i < CAT_N -> Image.image_bytes rsegs (CAT + CAT_ROW * i) 296 = Some (rowb i).
Proof.
  intros i Hi. unfold CAT_N in Hi.
  assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]; vm_compute; reflexivity.
Qed.

(* Two byte lists with the same values are equal (bv proofs differ between the image and le8). *)
Lemma u1_bytes_eq : forall l1 l2 : list byte, map (@bv_unsigned 8) l1 = map (@bv_unsigned 8) l2 -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

Lemma u1_kind_name_img :
  Image.image_bytes rsegs 0x1fc58 112 = Some reac_ctrl_kind_name_c.kind_name_bytes.
Proof.
  assert (H : option_map (map (@bv_unsigned 8)) (Image.image_bytes rsegs 0x1fc58 112) =
              Some (map (@bv_unsigned 8) reac_ctrl_kind_name_c.kind_name_bytes)) by (vm_compute; reflexivity).
  destruct (Image.image_bytes rsegs 0x1fc58 112) as [l|]; [|discriminate].
  injection H as H. f_equal. apply u1_bytes_eq. exact H.
Qed.

Lemma u1_in_relro : forall a, 0x1fc48 <= a < 0x20b18 -> in_globals frame_RELRO a.
Proof. intros a Ha. exists 0x1fc48, 3792. split; [left; reflexivity | lia]. Qed.

Lemma u1_find_img : forall B x seg, ms_segs B = rsegs -> find_segment rsegs x 1 = Some seg -> in_img B x.
Proof.
  intros B x seg HS E. destruct (sl_find_segment_in rsegs x 1 seg E) as (Hin & H1 & H2).
  destruct (sl_rsegs_seg seg Hin) as (R1 & R2 & R3).
  split; [rewrite HS; intros Hn; rewrite Hn in Hin; destruct Hin|].
  exists (segment_reservation seg). split.
  - rewrite HS. unfold segments_reserved. apply in_map_iff. exists seg. split; [reflexivity | exact Hin].
  - lia.
Qed.

Lemma u1_pw_perm : forall (T : Type) (R : T -> T -> Prop), (forall a b, R a b -> R b a) ->
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

Lemma u1_rd_sym : forall a b, ranges_disjoint a b -> ranges_disjoint b a.
Proof. unfold ranges_disjoint. intros a b H. lia. Qed.

(* A byte outside every image segment that reads Some is present in the memory itself. *)
Lemma u1_present : forall B (m : word -> option byte) x b, ms_segs B = rsegs -> ~ in_img B x -> 0 <= x < 2 ^ 64 ->
  mrd rsegs m (wa x) = Some b -> exists b', m (Z_to_bv 64 x) = Some b'.
Proof.
  intros B m x b HS Hn Hx H. unfold mrd in H. destruct (m (wa x)) as [b'|] eqn:E; [exists b'; exact E|].
  exfalso. destruct (find_segment rsegs (bv_unsigned (wa x)) 1) as [seg|] eqn:Ef.
  - rewrite wa_unsigned in Ef by lia. exact (Hn (u1_find_img B x seg HS Ef)).
  - rewrite (seg_rom_unmapped rsegs (wa x) Ef) in H. discriminate.
Qed.

(* The sink cells of sink_none (0x52121, 0x52548, 0x52550) lie in the image. *)
Lemma u1_resv_ok : existsb (fun s : word * word => (bv_unsigned (fst s) <=? 0x52120) &&
    (0x52558 <=? bv_unsigned (fst s) + bv_unsigned (snd s))) (segments_reserved rsegs) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma u1_img_sink : forall B x, ms_segs B = rsegs -> 0x52120 <= x < 0x52558 -> in_img B x.
Proof.
  intros B x HS Hx. pose proof u1_resv_ok as H. apply existsb_exists in H as (s & Hs & Hc).
  apply andb_true_iff in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  split; [rewrite HS; intros Hn; rewrite Hn in Hs; cbn in Hs; destruct Hs|].
  exists s. rewrite HS. split; [exact Hs | lia].
Qed.

(* round_trip.box: the 6 read-only bytes at 0x105c9. *)
Lemma u1_box_ro : Image.ro_bytes_b rsegs BOXA box6 = true.
Proof. vm_compute. reflexivity. Qed.

(* name_ok as a check. *)
Definition u1_name_okb (nb : list byte) : bool :=
  (1 <=? length nb)%nat && (length nb <=? 16)%nat &&
  forallb (fun i => negb (bv_unsigned (nth i nb (Z_to_bv 8 0)) =? 0)) (seq 0 (pred (length nb))) &&
  ((length nb =? 16)%nat || (bv_unsigned (nth (pred (length nb)) nb (Z_to_bv 8 0)) =? 0)).

Lemma u1_name_okb_sound : forall nb, u1_name_okb nb = true -> RcBox.name_ok nb.
Proof.
  intros nb H. unfold u1_name_okb in H. rewrite !andb_true_iff in H.
  destruct H as [[[H1 H2] H3] H4]. apply Nat.leb_le in H1. apply Nat.leb_le in H2.
  rewrite forallb_forall in H3. split; [lia|]. split.
  - intros i Hi. pose proof (H3 i ltac:(apply in_seq; lia)) as E. apply Bool.negb_true_iff in E.
    apply Z.eqb_neq in E. exact E.
  - apply orb_true_iff in H4 as [E|E]; [left; apply Nat.eqb_eq in E; exact E | right; apply Z.eqb_eq in E; exact E].
Qed.

(* The model name of each catalogue row that has one: a C string of 1 .. 16 bytes in read-only data. *)
Definition u1_name_chk (i : Z) : bool :=
  let r := rowb i in
  (RcSynth.has r =? 0) || (RcSynth.rname r =? 0) ||
  (u1_name_okb (img_cstr (RcSynth.rname r) 16) &&
   Image.ro_bytes_b rsegs (RcSynth.rname r) (img_cstr (RcSynth.rname r) 16) &&
   (0 <=? RcSynth.rname r) && (RcSynth.rname r + 17 <=? 0x53000)).

Lemma u1_name_chk_all : forallb u1_name_chk (map Z.of_nat (seq 0 11)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma u1_names : forall i, 0 <= i < CAT_N -> RcSynth.has (rowb i) <> 0 -> RcSynth.rname (rowb i) <> 0 ->
  RcBox.name_ok (img_cstr (RcSynth.rname (rowb i)) 16) /\
  Image.ro_bytes_b rsegs (RcSynth.rname (rowb i)) (img_cstr (RcSynth.rname (rowb i)) 16) = true /\
  0 <= RcSynth.rname (rowb i) /\ RcSynth.rname (rowb i) + 17 <= 0x53000.
Proof.
  intros i Hi Hh Hn. unfold CAT_N in Hi. pose proof u1_name_chk_all as H. rewrite forallb_forall in H.
  specialize (H i ltac:(apply in_map_iff; exists (Z.to_nat i); split; [lia | apply in_seq; lia])).
  unfold u1_name_chk in H. cbv zeta in H.
  rewrite (proj2 (Z.eqb_neq _ _) Hh), (proj2 (Z.eqb_neq _ _) Hn) in H. cbn [orb] in H.
  rewrite !andb_true_iff in H. destruct H as [[[H1 H2] H3] H4].
  apply Z.leb_le in H3. apply Z.leb_le in H4.
  split; [exact (u1_name_okb_sound _ H1)|]. split; [exact H2 | lia].
Qed.

Section U1.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Let API := APIf rc.

(* PB (slot-plan-ubsan.md section 7, GV's last conjunct): a byte of the input block lies in [4096, alloc_ceiling). *)
Lemma u1_pb : forall g c, GV B empty g -> 0 <= c < g_n g ->
  4096 <= g_p g /\ g_p g + c + 1 <= YM05.alloc_ceiling /\ YM05.alloc_ceiling < 2 ^ 47.
Proof.
  intros g c HGV Hc. pose proof HGV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HPB).
  pose proof YM05.alloc_ceiling_lt as Hlt.
  destruct HPB as [E|(H1 & H2)]; [lia|]. split; [exact H1|]. split; [lia | exact Hlt].
Qed.

Lemma u1_relro_bytes : forall mem a n bs, relro B mem -> Image.image_bytes rsegs a n = Some bs ->
  0x1fc48 <= a -> a + Z.of_nat n <= 0x20b18 -> bytes_at rsegs mem a bs.
Proof.
  intros mem a n bs HR HI H0 H1. pose proof (Image.image_bytes_length rsegs n a bs HI) as L.
  unfold relro, G_img_c in HR. rewrite (sl_segs B APIf ra empty FF) in HR.
  split; [lia|]. split; [rewrite L; lia|]. intros i Hi. rewrite L in Hi.
  rewrite <- (u1_image_nth n a bs HI i Hi).
  exact (HR (a + Z.of_nat i) (u1_in_relro (a + Z.of_nat i) ltac:(lia))).
Qed.

(* FR3' (relro) carries the three tables to every cut. *)
Lemma u1_ba_bytes : forall mem, relro B mem ->
  bytes_at rsegs mem (reac_ctrl_build_as_c.BA_FR + 72) reac_ctrl_build_as_c.ba_tbl.
Proof. intros mem HR. exact (u1_relro_bytes mem 0x209c8 168 _ HR u1_ba_tbl ltac:(lia) ltac:(lia)). Qed.

Lemma u1_row_bytes : forall mem i, relro B mem -> 0 <= i < CAT_N -> bytes_at rsegs mem (CAT + CAT_ROW * i) (rowb i).
Proof.
  intros mem i HR Hi. apply (u1_relro_bytes mem _ 296 _ HR (u1_rows i Hi)); unfold CAT, CAT_ROW, CAT_N in *; lia.
Qed.

Lemma u1_kind_name_bytes : forall mem, relro B mem ->
  bytes_at rsegs mem reac_ctrl_kind_name_c.KIND_NAME reac_ctrl_kind_name_c.kind_name_bytes.
Proof. intros mem HR. exact (u1_relro_bytes mem 0x1fc58 112 _ HR u1_kind_name_img ltac:(lia) ltac:(lia)). Qed.

(* The RELRO bytes read through the normalized memory are the image's; MATCH reads the whole catalogue
   [0x1fcc8, 0x1fcc8 + 3256) this way (its CM_T premise). *)
Lemma u1_relro_mrd : forall mem a, relro B mem -> 0x1fc48 <= a < 0x20b18 ->
  Mem.mrd rsegs (normalize rsegs mem) (wa a) = seg_rom rsegs (wa a).
Proof.
  intros mem a HR Ha. unfold relro, G_img_c in HR.
  pose proof (HR a (u1_in_relro a Ha)) as E. rewrite (sl_segs B APIf ra empty FF) in E.
  unfold Mem.mrd, normalize. destruct (Mem.ro_addr rsegs (wa a)); [reflexivity|].
  unfold mbyte in E. unfold wa. exact E.
Qed.

Lemma u1_cat_mrd : forall mem, relro B mem ->
  forall a, CAT <= a < CAT + 3256 -> Mem.mrd rsegs (normalize rsegs mem) (wa a) = seg_rom rsegs (wa a).
Proof. intros mem HR a Ha. apply (u1_relro_mrd mem a HR). unfold CAT in Ha. lia. Qed.

(* frame_facts taken apart by the TYPE of each conjunct, never by its position (an inserted or moved conjunct of
   frame_facts cannot shift a binding); frame_allocator likewise. *)
Ltac u1_ff := let H := fresh "FFd" in pose proof FF as H; red in H; decompose [and] H.

Lemma u1_alloc : frame_allocator_cf B API.
Proof.
  u1_ff. match goal with H : _ |- _ => exact (H rc fx) end.
Qed.

Lemma u1_ax : AllocExtra B (aa_MR API).
Proof. pose proof u1_alloc as H. red in H. decompose [and] H. assumption. Qed.

(* malloc's contract: the one use of frame_allocator's malloc_contract in this file. *)
Lemma u1_malloc_c : malloc_contract_cfg B API.
Proof. pose proof u1_alloc as H. red in H. decompose [and] H. assumption. Qed.

(* A live block: its bytes are present and not read-only, so the normalized memory holds them. *)
Lemma u1_blk : forall L A mem md a n, aa_MR API L A mem md -> In (a, n) (blocks L A) ->
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
    apply (ax_blocks_img u1_ax L A mem md p n (x - ptr_addr L p) HM Hp ltac:(lia)).
    replace (ptr_addr L p + (x - ptr_addr L p)) with x by lia.
    exact (u1_find_img B x seg (sl_segs B APIf ra empty FF) Ef). }
  assert (E : normalize rsegs mem (wa x) = Some b) by (unfold normalize; rewrite Hro; exact Hb).
  split.
  - exact (YL01.present_writable rsegs _ x (ex_intro _ b E)).
  - exists b. unfold Mem.mrd. rewrite E. reflexivity.
Qed.

Lemma u1_hb : forall g phi n L A regs mem md, FR B APIf ra empty g (hb1 phi n) L A regs mem md ->
  Permutation (blocks L A) (hb1 phi n ++ blocks (g_L g) (g_A g)) ->
  stk rsegs (normalize rsegs mem) phi (phi + n) /\ 4096 <= phi /\ phi + n <= YM05.alloc_ceiling.
Proof.
  intros g phi n L A regs mem md HFR HP. pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & _ & HM & _).
  apply (u1_blk L A mem md phi n HM).
  apply (Permutation_in _ (Permutation_sym HP)). left. reflexivity.
Qed.

(* The input block at a cut: [p, p + n) is a live entry block, so its bytes are those of the entry memory
   (FR's entry-block clause) and the entry memory holds the input there (GV's blk_data). *)
Lemma u1_in_all : forall g hb L A regs mem md,
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> 0 < g_n g ->
  4096 <= g_p g /\ g_p g + g_n g <= YM05.alloc_ceiling /\ bytes_at rsegs mem (g_p g) (g_in g).
Proof.
  intros g hb L A regs mem md HFR HP Hn.
  pose proof HFR as (HGV & _ & _ & _ & _ & _ & _ & _ & HM & _ & _ & _ & _ & _ & _ & Hblk & _).
  pose proof HGV as (_ & Hpn & Hdat & _).
  destruct Hpn as [(Hn0 & _) | (_ & Hin)]; [lia|].
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  destruct (u1_blk L A mem md (g_p g) (g_n g) HM
             (Permutation_in _ (Permutation_sym HP) (in_or_app _ _ _ (or_intror Hin)))) as (_ & H1 & H2).
  pose proof alloc_ceiling_value as Hac.
  split; [exact H1|]. split; [exact H2|].
  split; [lia|]. split; [unfold g_n, nlen in *; lia|].
  intros k Hk.
  assert (Hk' : 0 <= Z.of_nat k < g_n g) by (unfold g_n, nlen; lia).
  pose proof (Hblk (g_p g) (g_n g) (Z.of_nat k) Hin Hk') as E1.
  assert (Hk'' : 0 <= Z.of_nat k < Z.of_nat (length (g_in g))) by lia.
  pose proof (Hdat (Z.of_nat k) Hk'') as E2.
  rewrite E2, Nat2Z.id, SEGS in E1. exact E1.
Qed.

(* The byte at p + i (0 <= i < n) in the memory of a cut is in[i]. *)
Lemma u1_in_byte : forall g hb L A regs mem md i,
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> 0 <= i < g_n g ->
  bytes_at rsegs mem (g_p g + i) [RcIdentModel.nthb (g_in g) (Z.to_nat i)].
Proof.
  intros g hb L A regs mem md i HFR HP Hi.
  destruct (u1_in_all g hb L A regs mem md HFR HP ltac:(lia)) as (H1 & H2 & HB).
  pose proof (u1_at_slice mem (g_p g) (g_in g) (Z.to_nat i) 1 HB ltac:(unfold g_n, nlen in Hi; lia)) as H.
  rewrite Z2Nat.id in H by lia. rewrite (u1_firstn1 (g_in g) (Z.to_nat i)) in H by (unfold g_n, nlen in Hi; lia).
  exact H.
Qed.

(* The same read in the normalized memory of a run. *)
Lemma u1_in_rd : forall g hb L A regs mem md i,
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> 0 <= i < g_n g ->
  ov_read_bytes rsegs (normalize rsegs mem) (wa (g_p g + i)) 1 = Some [RcIdentModel.nthb (g_in g) (Z.to_nat i)].
Proof.
  intros g hb L A regs mem md i HFR HP Hi. apply u1_ld1.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & HMI & _). unfold MI in HMI. rewrite (sl_segs B APIf ra empty FF) in HMI.
  exact (proj1 (bytes_at_rel rsegs _ _ _ _ (mem_rel_normalize rsegs mem HMI)) (u1_in_byte g hb L A regs mem md i HFR HP Hi)).
Qed.

Lemma u1_relro_full : forall a, in_globals frame_RELRO a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Proof.
  intros a Ha. u1_ff.
  match goal with H : _ |- _ => exact (H a Ha) end.
Qed.

Lemma u1_relro_img : forall a, in_globals frame_RELRO a -> in_img B a.
Proof. intros a Ha. exact (proj1 (u1_relro_full a Ha)). Qed.

Lemma u1_syms : ms_ctx B = 0x52198 /\ ms_lock B = 0x52190 /\ ms_libc B = 0x52120 /\ ms_guard B = 0x52100 /\
  ms_got_guard B = 0x20b18 /\ ms_size_classes B = 0x10750 /\ ms_small_cnt B = 0x107b0 /\ ms_med_cnt B = 0x106f0 /\
  ms_debruijn B = 0x106cc /\ ms_vmlock B = None /\ @sk_ofl_head SH = 0x52550 /\ @sk_ofl_lock SK = 0x52548 /\
  @sk_threaded SK = 0x52120 + 1.
Proof. u1_ff. repeat split; assumption. Qed.

Lemma u1_malloc_addr : ms_malloc B = 0x173c0.
Proof. u1_ff. assumption. Qed.

(* The sink cells: in the image and outside the allocator's static, ctx and errno bytes. *)
Lemma u1_sink_addr : forall a, (0x52121 <= a < 0x52122 \/ 0x52548 <= a < 0x52558) ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Proof.
  intros a Ha. pose proof u1_syms as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _).
  pose proof (sl_errno_val B APIf ra empty FF) as Ev.
  split; [apply (u1_img_sink B a (sl_segs B APIf ra empty FF)); lia|].
  rewrite Ev. unfold static_owned, vml_lo, vml_len. rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10.
  rewrite (sl_debruijn_len B APIf ra empty FF).
  cbv iota. unfold CTX_SIZE. lia.
Qed.

Lemma u1_sink_frame : forall mem mem' md md',
  (forall a, (0x52121 <= a < 0x52122 \/ 0x52548 <= a < 0x52558) -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a) ->
  m_fds md' = m_fds md -> sink_none B mem md -> sink_none B mem' md'.
Proof.
  intros mem mem' md md' HK Hfd ((V1 & V2) & V3 & V4).
  pose proof u1_syms as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & S3).
  split; [split|split].
  - intros k Hk. rewrite <- (V1 k Hk). apply HK. rewrite S3. lia.
  - intros k Hk. rewrite <- (V2 k Hk). apply HK. rewrite S2. lia.
  - intros k Hk. rewrite <- (V3 k Hk). apply HK. rewrite S1. lia.
  - rewrite Hfd. exact V4.
Qed.

Lemma u1_call_pre : forall g hb L A regs mem md regs_c,
  FR B APIf ra empty g hb L A regs mem md -> YK11.getr regs_c 2 = YK11.getr regs 2 ->
  YK11.getr regs_c 4 = YK11.getr regs 4 -> YK0s.ret_ok (YK11.getr regs_c 1) -> call_pre B (aa_MR API) L A regs_c mem md.
Proof.
  intros g hb L A regs mem md regs_c HF E2 E4 Hra.
  pose proof HF as (HGV & Hsp & _ & Htp & _ & _ & _ & _ & HMR & HWF & HBD & HIN & _ & _ & _ & _ & HER & _ & _ & HSW).
  pose proof HGV as (_ & _ & _ & HS16 & HSK & HS47 & _ & _ & HTP0 & _).
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
Lemma u1_FR_malloc : forall g L A regs mem md regs_c n L' A' regs' mem' md' res b1 b2,
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
  pose proof HGV as (Hn0 & Hp0 & Hbd0 & HS16 & HSK & HS47 & Hroom & HgS & Htp0 & _).
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
    - intros [Ho|Ho]; [exact (H2 (ax_img u1_ax L A mem md a HMR Ha Ho)) | exact (H1 Ho)].
    - intros [Ho|Ho]; [exact (H2 (ax_img u1_ax L' A' mem' md' a MR' Ha Ho)) | exact (H1 Ho)].
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
  { apply (u1_ba_mbyte mem); [exact Hsav|]. intros i Hi.
    assert (Hl : length (saved_bytes ra g) = 104%nat)
      by (unfold saved_bytes; rewrite !length_app, !length_le8; reflexivity).
    rewrite Hl in Hi. rewrite <- ES. exact (proj1 (HH (g_S g - 104 + i) ltac:(lia) ltac:(lia))). }
  split; [apply sl_stk_of_writable; [unfold SL_TOP; lia | lia | intros a Ha; rewrite <- ES; apply HWR; exact Ha]|].
  split; [unfold MI; exact RO'|].
  split.
  { unfold relro, G_img_c in *. intros a Ha. rewrite <- (Hrel a Ha).
    destruct (u1_relro_full a Ha) as (H1 & H2 & H3 & H4). exact (proj1 (HI a H1 H2 H3 H4)). }
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
  { apply (u1_sink_frame mem mem' md md'); [|rewrite Emd; reflexivity | exact Hsink].
    intros a Ha. destruct (u1_sink_addr a Ha) as (H1 & H2 & H3 & H4). exact (proj1 (HI a H1 H2 H3 H4)). }
  split; [exact (resb_malloc (g_b g) [] (hb1 res n) A' res n (Permutation_refl _) RES')|].
  intros a Ha. apply HWR. exact Ha.
Qed.

(* malloc(n) from a cut with no live harness block, as a Kind B step: the continuation gets FR with hb = (res, n). *)
Lemma u1_malloc_call : forall g L A regs mem md regs_c n (Q : config -> Prop),
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
  SR (ms_segs B) (mkCfg (YK11.mkst regs_c (Z_to_bv 64 0x173c0) mem (YK11.seg_rom (ms_segs B))) md) Q.
Proof.
  intros g L A regs mem md regs_c n Q HF HP E2 E3 E4 Hra H10 Hn K.
  pose proof (u1_call_pre g [] L A regs mem md regs_c HF E2 E4 Hra) as CP.
  pose proof HF as (HGV & _ & _ & _ & _ & _ & HMI & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hb & _).
  pose proof HGV as (_ & _ & _ & _ & _ & _ & Hroom & _).
  pose proof u1_malloc_c as MAL.
  rewrite <- u1_malloc_addr.
  eapply SR_bind.
  { exact (MAL L A regs_c mem md n (sb_hb (g_b g) []) CP HMI H10 Hb
             (resb_room (g_b g) [] n Hroom ltac:(cbn; lia) ltac:(cbn; lia) Hn)). }
  intros c' (L' & A' & regs' & mem' & md' & res & -> & POST & H10' & Hres & _ & _ & (b1 & b2 & EB' & EB) & KEPT &
             RO' & _ & _ & INIT & _ & RES').
  pose proof POST as (_ & _ & _ & _ & _ & RP' & _).
  destruct (u1_FR_malloc g L A regs mem md regs_c n L' A' regs' mem' md' res b1 b2 HF HP E2 E3 E4 POST EB' EB KEPT
              RO' INIT RES') as (HF' & HP' & HK).
  exact (K L' A' regs' mem' md' res HF' HP' RP' H10' Hres HK).
Qed.

Lemma u1_sink_keep : forall (m m' : word -> option byte) md,
  (forall a, in_img B a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) -> sink_none B m md -> sink_none B m' md.
Proof.
  intros m m' md HK (Henv & Hhead & Hn). destruct (sl_sink B APIf ra empty FF) as (E1 & E2 & E3).
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  assert (HM : forall a, 0x52120 <= a < 0x52558 -> mbyte (ms_segs B) m' a = mbyte (ms_segs B) m a).
  { intros a Ha. unfold mbyte. rewrite (HK a (u1_img_sink B a SEGS Ha)). reflexivity. }
  destruct Henv as [Ht Hl]. split; [split|split; [|exact Hn]].
  - eapply val_mem_frame; [|exact Ht]. intros x Hx. apply HM. rewrite E3 in Hx. cbn in Hx. lia.
  - eapply val_mem_frame; [|exact Hl]. intros x Hx. apply HM. rewrite E2 in Hx. cbn in Hx. lia.
  - apply (val_mem_word_mem (ms_segs B)). apply (val_mem_word_mem (ms_segs B)) in Hhead.
    eapply val_mem_frame; [|exact Hhead]. intros x Hx. apply HM. rewrite E1 in Hx. cbn in Hx. lia.
Qed.

(* FR across a run that writes the stack window [S - K, S - 104) and the live harness block [phi, phi + n). *)
Lemma u1_fr_hb : forall g phi n L A regs mem md regs' mem',
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
  { intros a Ha Hi. apply (ax_blocks_img u1_ax L A mem md p n (a - phi) HM Hp ltac:(lia)).
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
    unfold mbyte. rewrite (HI a (u1_relro_img a Ha)). reflexivity. }
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
        exact (u1_present B mem' _ b' SEGS (Hnimg _ (conj Hl1 Hl2)) ltac:(lia) Hb').
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
    apply (u1_pw_perm _ ranges_disjoint u1_rd_sym _ _ HP) in PD.
    destruct PD as [PD _]. pose proof (PD (a, k) Hin) as Hd. unfold ranges_disjoint in Hd. cbn [fst snd] in Hd.
    unfold mbyte. rewrite (HL (a + i) ltac:(lia) ltac:(lia)). reflexivity. }
  split; [intros a Ha; apply Hwr; exact (Herr a Ha)|].
  split; [exact (u1_sink_keep mem mem' md HI Hsn)|].
  split; [exact Hres|].
  intros a Ha. apply Hwr, Hwin. exact Ha.
Qed.

End U1.
