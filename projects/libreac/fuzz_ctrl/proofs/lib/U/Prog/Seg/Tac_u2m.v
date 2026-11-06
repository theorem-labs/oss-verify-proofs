(* Batch u2 helpers of the fuzz_ctrl LLVMFuzzerTestOneInput slot proof (ubsan) for the machine side of segments
   R10-R21: memory slices, register keeps, the round-trip bundles across a run or a call (ubsan slots: M8 at
   sp+24, OUR at sp+114, frag at sp+120, id at sp+36), the fragment call, and HBR (slot-plan-ubsan.md section 7:
   a live harness block lies in [4096, alloc_ceiling)). Ported from the plain Tac_b1, Tac_b2m. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFrag RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcParseLib RcEmit RcEmitLib RcLay RcSynth RcSynthLib
  RcFinLib RcIdentModel RcLeaf RcDecl RcModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import reac_ctrl_identity_fragment_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require reac_ctrl_build_as_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Import Tac_slot Tac_u2.
Import ListNotations.
Open Scope Z_scope.

(* ---- Bytes across a run ---- *)

(* Bytes a segment does not touch: from the cut's memory through the normalized run to the next cut's memory. *)
Lemma u2_keep : forall W mem m0 m' a bs, ro_agree rsegs mem -> Frame.munch W (normalize rsegs mem) m0 ->
  mem_rel rsegs m' m0 -> Frame.disjoint_from W a (Z.of_nat (length bs)) ->
  bytes_at rsegs mem a bs -> bytes_at rsegs m' a bs.
Proof.
  intros W mem m0 m' a bs Hro MU Hrel HD H.
  apply (proj2 (bytes_at_rel rsegs m' m0 a bs Hrel)).
  exact (bytes_at_transport rsegs W (normalize rsegs mem) m0 a bs (bytes_at_normalize rsegs mem a bs Hro H) MU HD).
Qed.

(* The bytes the run itself leaves at a: from the run's final memory to the next cut's memory. *)
Lemma u2_out : forall m0 m' a bs, mem_rel rsegs m' m0 -> bytes_at rsegs m0 a bs -> bytes_at rsegs m' a bs.
Proof. intros m0 m' a bs Hrel H. exact (proj2 (bytes_at_rel rsegs m' m0 a bs Hrel) H). Qed.

Lemma u2_dj_sub : forall W a n a' n', Frame.disjoint_from W a n -> a <= a' -> a' + n' <= a + n ->
  Frame.disjoint_from W a' n'.
Proof.
  induction W as [|[lo hi] W IH]; cbn [disjoint_from]; intros a n a' n' H H1 H2; [exact I|].
  destruct H as [H H']. split; [lia | exact (IH a n a' n' H' H1 H2)].
Qed.

(* ---- Lengths of the round-trip model ---- *)

Lemma u2_fg_st_len : forall len st g, length st = 72%nat -> length g = 50%nat -> length (fg_st len st g) = 72%nat.
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

Lemma u2_RS_len : forall inp b, length (RID inp b) = 38%nat /\ length (RFG inp b) = 72%nat.
Proof.
  intros inp b. unfold RID, RFG. induction b as [|b [IH1 IH2]]; [split; reflexivity|].
  cbn [rt_st].
  destruct (rt_n inp (Z.of_nat b) =? 0); [exact (conj IH1 IH2)|].
  destruct ((Z.of_nat b =? 3) || (Z.of_nat b =? 4)); cbn [fst snd].
  - split; [|exact IH2]. unfold rp_id. destruct (RcReply.ir _ _); [apply RcIdentModel.ING_length; exact IH1 | exact IH1].
  - destruct ((Z.of_nat b =? 5) || (Z.of_nat b =? 6)); cbn [fst snd]; [|exact (conj IH1 IH2)].
    split.
    + unfold fg_id. destruct (fg_rf _ _ _ =? 1); [apply RcIdentModel.ING_length; exact IH1 | exact IH1].
    + apply u2_fg_st_len; [exact IH2 | apply fr50_length].
Qed.

Lemma u2_row_len : forall i, length (rowb i) = 296%nat.
Proof.
  intros i. unfold rowb, img. destruct (Image.image_bytes rsegs (CAT + CAT_ROW * i) 296) eqn:E.
  - exact (Image.image_bytes_length rsegs 296 _ _ E).
  - apply repeat_length.
Qed.

Lemma u2_rtX_len : forall inp b, length (rt_X inp b) = 32%nat.
Proof.
  intros inp b. unfold rt_X, reac_ctrl_build_as_c.ba_X, RcLay.ly_Z.
  assert (HZ : length (if mrow inp =? 0 then RcLay.ly_zero
                       else if RcSynth.rc (rt_mb inp) b =? 1 then RcSynth.synth (rt_mb inp) b (rt_nb inp)
                       else RcLay.ly_zero) = 32%nat).
  { destruct (mrow inp =? 0); [reflexivity|].
    destruct (RcSynth.rc (rt_mb inp) b =? 1); [|reflexivity].
    apply RcSynthLib.rs_synth_len. apply u2_row_len. }
  destruct (b <=? 1); [apply RcFinLib.rcf_stamp32_len; exact HZ | exact HZ].
Qed.

(* n_b != 0: E(b), 124 <= n_b <= 1492, and F_b has n_b bytes. *)
Lemma u2_rtn : forall inp b, rt_n inp b <> 0 ->
  rt_E inp b = true /\ 124 <= rt_n inp b <= 1492 /\ length (rt_F inp b) = Z.to_nat (rt_n inp b).
Proof.
  intros inp b H. unfold rt_n in *. destruct (rt_E inp b) eqn:E; [|congruence].
  pose proof E as E'. unfold rt_E, reac_ctrl_build_as_c.ba_E in E'. apply andb_true_iff in E' as [Ew _].
  destruct (RcEmitLib.em_wok_range _ Ew) as [R _].
  split; [reflexivity|]. split; [lia|].
  unfold rt_F, RcEmit.em_fr, RcEmit.em_hdr, box6. unfold rt_n. rewrite E.
  rewrite !length_app, OUR_length, length_map, u2_rtX_len, repeat_length. cbn [length]. lia.
Qed.

(* ---- Byte slices ---- *)

Lemma u2_at_slice : forall m a bs k n, bytes_at rsegs m a bs -> (k + n <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m a bs k n (H1 & H2 & H3) Hk.
  assert (L : length (firstn n (skipn k bs)) = n) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite L; lia|]. intros i Hi. rewrite L in Hi.
  rewrite nth_error_firstn. destruct (Nat.ltb_spec i n) as [_|]; [|lia].
  rewrite nth_error_skipn. replace (a + Z.of_nat k + Z.of_nat i) with (a + Z.of_nat (k + i)) by lia.
  apply H3. lia.
Qed.

Lemma u2_fr50_eq : forall bs, (50 <= length bs)%nat -> fr50 bs = firstn 50 bs.
Proof.
  intros bs H. unfold fr50. rewrite firstn_app. replace (50 - length bs)%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r. reflexivity.
Qed.

Lemma u2_fr50_at : forall m a bs, bytes_at rsegs m a bs -> (50 <= length bs)%nat -> bytes_at rsegs m a (fr50 bs).
Proof.
  intros m a bs H L. rewrite (u2_fr50_eq bs L).
  pose proof (u2_at_slice m a bs 0 50 H ltac:(lia)) as E. rewrite Z.add_0_r in E. exact E.
Qed.

Lemma u2_bsl_at : forall m a bs k n, bytes_at rsegs m a bs -> 0 <= k -> 0 <= n -> k + n <= Z.of_nat (length bs) ->
  bytes_at rsegs m (a + k) (bsl bs k n).
Proof.
  intros m a bs k n H Hk Hn L. unfold bsl.
  pose proof (u2_at_slice m a bs (Z.to_nat k) (Z.to_nat n) H ltac:(lia)) as E.
  rewrite Z2Nat.id in E by lia. exact E.
Qed.

Lemma u2_bsl_len : forall bs k n, 0 <= k -> 0 <= n -> k + n <= Z.of_nat (length bs) ->
  length (bsl bs k n) = Z.to_nat n.
Proof. intros bs k n Hk Hn L. unfold bsl. rewrite length_firstn, length_skipn. lia. Qed.

(* A stack slot holding known bytes is a writable cell of them. *)
Lemma u2_rw_at : forall m lo hi a bs, stk rsegs m lo hi -> lo <= a -> a + Z.of_nat (length bs) <= hi ->
  bytes_at rsegs m a bs -> rw_cells rsegs m a [CB (length bs) bs].
Proof.
  intros m lo hi a bs ST H1 H2 HB.
  destruct (sl_rw_of_stk m lo hi a (length bs) ST H1 H2) as (junk & _ & HW).
  split; [split|].
  - cbn. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - exact HW.
Qed.

Lemma u2_stk_sub : forall m lo hi lo' hi', stk rsegs m lo hi -> lo <= lo' -> hi' <= hi -> 0 <= lo' ->
  stk rsegs m lo' hi'.
Proof. intros m lo hi lo' hi' (H1 & H2 & H) E1 E2 E3. split; [exact E3|]. split; [lia|]. intros a Ha. apply H. lia. Qed.

Lemma u2_wr_of_stk : forall m lo hi a n, stk rsegs m lo hi -> lo <= a -> a + n <= hi -> 0 <= n -> wr_at rsegs m a n.
Proof.
  intros m lo hi a n (H1 & H2 & H) E1 E2 E3. split; [lia|]. split; [lia|].
  intros i Hi. exact (proj1 (H (a + i) ltac:(lia))).
Qed.

Lemma u2_mod : forall s k d, s mod 16 = 0 -> 0 < d -> 16 mod d = 0 -> k mod d = 0 -> (s + k) mod d = 0.
Proof.
  intros s k d Hs Hd H16 Hk.
  apply (proj2 (Z.mod_divide (s + k) d ltac:(lia))). apply Z.divide_add_r.
  - apply (Z.divide_trans d 16 s).
    + apply (proj1 (Z.mod_divide 16 d ltac:(lia))). exact H16.
    + apply (proj1 (Z.mod_divide s 16 ltac:(lia))). exact Hs.
  - apply (proj1 (Z.mod_divide k d ltac:(lia))). exact Hk.
Qed.

(* ---- Loads and comparisons ---- *)

Lemma u2_ovr : forall m a bs, bytes_at rsegs m a bs -> ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as E.
  rewrite Z.add_0_r, skipn_O, firstn_all in E. exact E.
Qed.

Lemma u2_zx16 : forall v, 0 <= v < 65536 -> zx16 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof. intros v Hv. unfold zx16. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma u2_reply_addr : forall g, reply_addr g = le2 (Z_to_bv 64 (r_addr g)).
Proof. intros g. unfold reply_addr, r_addr. symmetry. apply RcParseLib.rc_le2_pair. Qed.

Lemma u2_r_addr_rng : forall g, 0 <= r_addr g < 65536.
Proof.
  intros g. unfold r_addr. pose proof (cp_v_range' g 36). pose proof (cp_v_range' g 37). lia.
Qed.

Lemma u2_neqb_refl : forall x : word, negb (bv_eqb x x) = false.
Proof. intros x. unfold bv_eqb. rewrite Z.eqb_refl. reflexivity. Qed.

Lemma u2_eqb0 : forall x, 0 < x < 2 ^ 64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = false.
Proof. intros x Hx. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. Qed.

Lemma u2_memcmp_refl : forall l n, (n <= length l)%nat -> StrFun.memcmp_model l l n = Some 0.
Proof.
  intros l n. revert l. induction n as [|n IH]; intros [|a l] H; cbn in *; try lia; try reflexivity.
  rewrite Z.eqb_refl. apply IH. lia.
Qed.

(* CATU for the chosen row: m = T' + 296 i* with i* <= 10 is 8-aligned and inside the catalogue. *)
Lemma u2_mrow_rng : forall inp, CAT <= mrow inp <= CAT + CAT_ROW * 10 /\ mrow inp mod 8 = 0.
Proof.
  intros inp. pose proof (u2_istar_range inp) as H. unfold mrow, CAT, CAT_ROW in *. split; [lia|].
  replace (130248 + 296 * istar inp) with ((16281 + 37 * istar inp) * 8) by lia. apply Z.mod_mul. lia.
Qed.

Lemma u2_row_io : forall i, 0 <= i < 11 ->
  firstn 4 (skipn 16 (rowb i)) = le4 (Z_to_bv 64 (RcDecl.box_ic (rowb i))) /\
  firstn 4 (skipn 20 (rowb i)) = le4 (Z_to_bv 64 (RcDecl.box_oc (rowb i))) /\
  -2 ^ 31 <= RcDecl.box_ic (rowb i) < 2 ^ 31 /\ -2 ^ 31 <= RcDecl.box_oc (rowb i) < 2 ^ 31.
Proof.
  intros i Hi.
  assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]; vm_compute;
    (split; [reflexivity|]); (split; [reflexivity|]); split; split; first [reflexivity | intro H; discriminate H].
Qed.

Lemma u2_ports_ok : forall p q bs, p <> 0 -> q <> 0 -> RcLeaf.decl bs = true -> RcLeaf.ports_ok p q bs = true.
Proof.
  intros p q bs Hp Hq Hd. unfold RcLeaf.ports_ok.
  rewrite (proj2 (Z.eqb_neq p 0) Hp), (proj2 (Z.eqb_neq q 0) Hq), Hd. reflexivity.
Qed.

(* ---- Registers and the round-trip bundles across a run (ubsan registers and slots) ---- *)

(* The registers of RB: s0, s1, s2, s3, s6, s7, s8-s11 (YK11.getr: the getr of SlotInv's rg). *)
Definition u2_kr (regs' regs : bvmap 5 word) : Prop :=
  YK11.getr regs' 8 = YK11.getr regs 8 /\ YK11.getr regs' 9 = YK11.getr regs 9 /\
  YK11.getr regs' 18 = YK11.getr regs 18 /\ YK11.getr regs' 19 = YK11.getr regs 19 /\
  YK11.getr regs' 22 = YK11.getr regs 22 /\ YK11.getr regs' 23 = YK11.getr regs 23 /\
  YK11.getr regs' 24 = YK11.getr regs 24 /\ YK11.getr regs' 25 = YK11.getr regs 25 /\
  YK11.getr regs' 26 = YK11.getr regs 26 /\ YK11.getr regs' 27 = YK11.getr regs 27.

(* RB's registers and the RF registers s4 (Φ) and s5 (n_b). *)
Definition u2_ks (regs' regs : bvmap 5 word) : Prop :=
  u2_kr regs' regs /\ YK11.getr regs' 20 = YK11.getr regs 20 /\ YK11.getr regs' 21 = YK11.getr regs 21.

(* RB across a run that writes nothing in [sp+24, sp+192) (M8, OUR, frag, id). *)
Lemma u2_RB_keep : forall g b idb fgb regs regs' mem m0 m' W,
  ro_agree rsegs mem -> Frame.munch W (normalize rsegs mem) m0 -> mem_rel rsegs m' m0 ->
  length idb = 38%nat -> length fgb = 72%nat -> Frame.disjoint_from W (spk g 24) 168 ->
  u2_kr regs' regs -> RB g b idb fgb regs mem -> RB g b idb fgb regs' m'.
Proof.
  intros g b idb fgb regs regs' mem m0 m' W Hro MU Hrel L1 L2 HD
    (E8 & E9 & E18 & E19 & E22 & E23 & E24 & E25 & E26 & E27)
    (Hb & (Hc & HC1 & HC2) & HO & (H8 & H18 & H19 & H24 & H25 & H26 & H27) & HM8 & H9 & HI & HF).
  unfold RB, CUR, RT, rg, OURb, M8, q64, RIDB, FGB in *.
  split; [exact Hb|].
  split; [split; [exact Hc|]; split; [rewrite ?E22, ?E23; exact HC1 | rewrite ?E22, ?E23; exact HC2]|].
  split.
  { apply (u2_keep W mem m0 m' _ _ Hro MU Hrel); [|exact HO].
    rewrite OUR_length. apply (u2_dj_sub W _ _ _ _ HD); unfold spk; lia. }
  split.
  { rewrite E8, E18, E19, E24, E25, E26, E27. auto 8. }
  split.
  { apply (u2_keep W mem m0 m' _ _ Hro MU Hrel); [|exact HM8].
    rewrite length_le8. apply (u2_dj_sub W _ _ _ _ HD); unfold spk; lia. }
  split; [rewrite E9; exact H9|].
  split.
  { apply (u2_keep W mem m0 m' _ _ Hro MU Hrel); [|exact HI].
    rewrite L1. apply (u2_dj_sub W _ _ _ _ HD); unfold spk; lia. }
  apply (u2_keep W mem m0 m' _ _ Hro MU Hrel); [|exact HF].
  rewrite L2. apply (u2_dj_sub W _ _ _ _ HD); unfold spk; lia.
Qed.

(* RB with the id and frag the run leaves (each shown by the caller), M8 ([sp+24, sp+32)) and OUR ([sp+114, sp+120))
   kept. *)
Lemma u2_RB_new : forall g b idb fgb idb' fgb' regs regs' mem m0 m' W,
  ro_agree rsegs mem -> Frame.munch W (normalize rsegs mem) m0 -> mem_rel rsegs m' m0 ->
  Frame.disjoint_from W (spk g 24) 8 -> Frame.disjoint_from W (spk g 114) 6 -> u2_kr regs' regs ->
  RB g b idb fgb regs mem -> RIDB g m' idb' -> FGB g m' fgb' -> RB g b idb' fgb' regs' m'.
Proof.
  intros g b idb fgb idb' fgb' regs regs' mem m0 m' W Hro MU Hrel HD8 HDO
    (E8 & E9 & E18 & E19 & E22 & E23 & E24 & E25 & E26 & E27)
    (Hb & (Hc & HC1 & HC2) & HO & (H8 & H18 & H19 & H24 & H25 & H26 & H27) & HM8 & H9 & _ & _) HI HF.
  unfold RB, CUR, RT, rg, OURb, M8, q64 in *.
  split; [exact Hb|].
  split; [split; [exact Hc|]; split; [rewrite ?E22, ?E23; exact HC1 | rewrite ?E22, ?E23; exact HC2]|].
  split.
  { apply (u2_keep W mem m0 m' _ _ Hro MU Hrel); [|exact HO].
    rewrite OUR_length. apply (u2_dj_sub W _ _ _ _ HDO); unfold spk; lia. }
  split; [rewrite E8, E18, E19, E24, E25, E26, E27; auto 8|].
  split.
  { apply (u2_keep W mem m0 m' _ _ Hro MU Hrel); [|exact HM8].
    rewrite length_le8. apply (u2_dj_sub W _ _ _ _ HD8); unfold spk; lia. }
  split; [rewrite E9; exact H9|].
  split; [exact HI | exact HF].
Qed.

(* RFb across a run that writes neither [sp+24, sp+192) nor the block. *)
Lemma u2_RFb_keep : forall g b idb fgb phi regs regs' mem m0 m' W,
  ro_agree rsegs mem -> Frame.munch W (normalize rsegs mem) m0 -> mem_rel rsegs m' m0 ->
  length idb = 38%nat -> length fgb = 72%nat -> Frame.disjoint_from W (spk g 24) 168 ->
  Frame.disjoint_from W phi (rnb g b) -> u2_kr regs' regs -> YK11.getr regs' 20 = YK11.getr regs 20 ->
  RFb g b idb fgb phi regs mem -> RFb g b idb fgb phi regs' m'.
Proof.
  intros g b idb fgb phi regs regs' mem m0 m' W Hro MU Hrel L1 L2 HD HDp KR E20 (HRB & Hnz & H20 & HF).
  destruct (u2_rtn (g_in g) (Z.of_nat b) Hnz) as (_ & HB & HL).
  unfold RFb, rg in *. rewrite E20.
  split; [exact (u2_RB_keep g b idb fgb regs regs' mem m0 m' W Hro MU Hrel L1 L2 HD KR HRB)|].
  split; [exact Hnz|]. split; [exact H20|].
  apply (u2_keep W mem m0 m' _ _ Hro MU Hrel); [|exact HF].
  unfold rFb, rnb in *. rewrite HL, Z2Nat.id by lia. exact HDp.
Qed.

(* RFx across a run that writes neither [sp+24, sp+192) nor the block. *)
Lemma u2_RFx_keep : forall g b idb fgb phi regs regs' mem m0 m' W,
  ro_agree rsegs mem -> Frame.munch W (normalize rsegs mem) m0 -> mem_rel rsegs m' m0 ->
  length idb = 38%nat -> length fgb = 72%nat -> Frame.disjoint_from W (spk g 24) 168 ->
  Frame.disjoint_from W phi (rnb g b) -> u2_ks regs' regs ->
  RFx g b idb fgb phi regs mem -> RFx g b idb fgb phi regs' m'.
Proof.
  intros g b idb fgb phi regs regs' mem m0 m' W Hro MU Hrel L1 L2 HD HDp (KR & E20 & E21) (HRF & H21).
  unfold RFx, rg in *. rewrite E21.
  split; [|exact H21].
  exact (u2_RFb_keep g b idb fgb phi regs regs' mem m0 m' W Hro MU Hrel L1 L2 HD HDp KR E20 HRF).
Qed.

(* RFx with the id and frag the run leaves (each shown by the caller), M8, OUR, the block and the registers kept. *)
Lemma u2_RFx_new : forall g b idb fgb idb' fgb' phi regs regs' mem m0 m' W,
  ro_agree rsegs mem -> Frame.munch W (normalize rsegs mem) m0 -> mem_rel rsegs m' m0 ->
  Frame.disjoint_from W (spk g 24) 8 -> Frame.disjoint_from W (spk g 114) 6 ->
  Frame.disjoint_from W phi (rnb g b) -> u2_ks regs' regs ->
  RFx g b idb fgb phi regs mem -> RIDB g m' idb' -> FGB g m' fgb' -> RFx g b idb' fgb' phi regs' m'.
Proof.
  intros g b idb fgb idb' fgb' phi regs regs' mem m0 m' W Hro MU Hrel HD8 HDO HDp (KR & E20 & E21)
    ((HRB & Hnz & H20 & HF) & H21) HI HG.
  destruct (u2_rtn (g_in g) (Z.of_nat b) Hnz) as (_ & HB & HL).
  unfold RFx, RFb, rg in *. rewrite E20, E21.
  split; [split; [|split; [exact Hnz|]; split; [exact H20|]]|exact H21].
  - exact (u2_RB_new g b idb fgb idb' fgb' regs regs' mem m0 m' W Hro MU Hrel HD8 HDO KR HRB HI HG).
  - apply (u2_keep W mem m0 m' _ _ Hro MU Hrel); [|exact HF].
    unfold rFb, rnb in *. rewrite HL, Z2Nat.id by lia. exact HDp.
Qed.

(* ---- The fragment call (sp+120, Φ, n, sp+1824, sp+1752, sp+1688) of R11 and R18 ---- *)

Lemma u2_fg_class : forall f fr pa pp pn len st g, f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
  fg_class f fr pa pp pn len st g = fcls len st g.
Proof.
  intros f fr pa pp pn len st g H1 H2 H3 H4 H5. unfold fcls, fg_class.
  rewrite (proj2 (Z.eqb_neq f 0) H1), (proj2 (Z.eqb_neq fr 0) H2), (proj2 (Z.eqb_neq pa 0) H3),
    (proj2 (Z.eqb_neq pp 0) H4), (proj2 (Z.eqb_neq pn 0) H5). reflexivity.
Qed.

Lemma u2_frag_call : reac_ctrl_identity_fragment_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi n : Z) (st g : list byte) (c : fg_case),
    sp = Z_to_bv 64 spv -> a0 = Z_to_bv 64 (spv + 120) -> a1 = Z_to_bv 64 phi -> a2 = Z_to_bv 64 n ->
    a3 = Z_to_bv 64 (spv + 1824) -> a4 = Z_to_bv 64 (spv + 1752) -> a5 = Z_to_bv 64 (spv + 1688) ->
    65536 <= spv -> spv + 1936 <= 2 ^ 64 -> spv mod 16 = 0 ->
    0 < phi -> phi + 50 <= spv - 96 -> 50 <= n < 2 ^ 64 ->
    stk rsegs m (spv - 96) spv -> mem_inv rsegs m -> length g = 50%nat -> length st = 72%nat ->
    bytes_at rsegs m phi g -> rw_cells rsegs m (spv + 120) [CB 72 st] ->
    wr_at rsegs m (spv + 1824) 2 -> wr_at rsegs m (spv + 1752) 8 -> wr_at rsegs m (spv + 1688) 8 ->
    fcls n st g = c ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fg_ret c))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch (fg_fp 96 (spv + 120) (spv + 1824) (spv + 1752) (spv + 1688) spv c) m m' /\ wmono rsegs m m' /\
         fg_mem (spv + 120) (spv + 1824) (spv + 1752) (spv + 1688) st g c m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_IDENTITY_FRAGMENT) fc None m (seg_rom rsegs)).
Proof.
  intros FRAG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi n st g c -> -> -> -> -> -> -> Hsp0 Hsp H16 Hph0 Hph Hn ST MI Lg Ls HG HF WA WP WN Hc.
  assert (Hspu : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply unsigned_lit; lia).
  pose proof (u2_fg_class (spv + 120) phi (spv + 1824) (spv + 1752) (spv + 1688) n st g ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(lia)) as EC.
  eapply evt_mono.
  { eapply (FRAG ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 s1 _ _ _ _ _ _ a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
              t3 t4 t5 t6 F fc m (spv + 120) phi n (spv + 1824) (spv + 1752) (spv + 1688) st g).
    all: rewrite ?Hspu; unfold REAC_CTRL_IDENTITY_FRAGMENT_FRAME.
    all: first [ reflexivity | exact ST | exact Lg | exact Ls | exact MI
               | intros _ _ _ _ _ _; exact HG
               | intros _ _ _ _ _;
                 split; [exact HF|];
                 split; [apply u2_mod; [exact H16 | lia | reflexivity | reflexivity]|];
                 split; [apply u2_mod; [exact H16 | lia | reflexivity | reflexivity]|];
                 split; [apply u2_mod; [exact H16 | lia | reflexivity | reflexivity]|];
                 split; [exact WA|]; split; [exact WP|]; split; [exact WN|];
                 cbn [all_dj dj_from]; repeat split; lia
               | lia ]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MU & WM & _ & _ & HM).
  rewrite Hspu, EC, Hc in *.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [exact E|]. split; [exact MU|]. split; [exact WM | exact HM].
Qed.

(* ---- HBR: a live harness block lies in [4096, alloc_ceiling) and the normalized memory holds it ---- *)

Lemma u2_find_img : forall B x seg, ms_segs B = rsegs -> find_segment rsegs x 1 = Some seg -> in_img B x.
Proof.
  intros B x seg HS E. destruct (sl_find_segment_in rsegs x 1 seg E) as (Hin & H1 & H2).
  destruct (sl_rsegs_seg seg Hin) as (R1 & R2 & R3).
  split; [rewrite HS; intros Hn; rewrite Hn in Hin; destruct Hin|].
  exists (segment_reservation seg). split.
  - rewrite HS. unfold segments_reserved. apply in_map_iff. exists seg. split; [reflexivity | exact Hin].
  - lia.
Qed.

Section M.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Let API := APIf rc.

Lemma u2_ax : AllocExtra B (aa_MR API).
Proof.
  pose proof FF as H. repeat apply proj2 in H.
  destruct (H rc fx) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AX & _). exact AX.
Qed.

Lemma u2_blk : forall L A mem md a n, aa_MR API L A mem md -> In (a, n) (blocks L A) ->
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
    apply (ax_blocks_img u2_ax L A mem md p n (x - ptr_addr L p) HM Hp ltac:(lia)).
    replace (ptr_addr L p + (x - ptr_addr L p)) with x by lia.
    exact (u2_find_img B x seg (sl_segs B APIf ra empty FF) Ef). }
  assert (E : normalize rsegs mem (wa x) = Some b) by (unfold normalize; rewrite Hro; exact Hb).
  split.
  - exact (YL01.present_writable rsegs _ x (ex_intro _ b E)).
  - exists b. unfold Mem.mrd. rewrite E. reflexivity.
Qed.

(* The RELRO bytes (the catalogue [0x1fcc8, 0x20980) among them) read through the normalized memory are the
   image's (frame_RELRO's first range [0x1fc48, 0x20b18)). *)
Lemma u2_relro_mrd : forall mem a, relro B mem -> 0x1fc48 <= a < 0x20b18 ->
  Mem.mrd rsegs (normalize rsegs mem) (wa a) = seg_rom rsegs (wa a).
Proof.
  intros mem a HR Ha. unfold relro, G_img_c in HR.
  assert (Hg : in_globals frame_RELRO a) by (exists 0x1fc48, 3792; split; [left; reflexivity | lia]).
  pose proof (HR a Hg) as E. rewrite (sl_segs B APIf ra empty FF) in E.
  unfold Mem.mrd, normalize. destruct (Mem.ro_addr rsegs (wa a)); [reflexivity|].
  unfold mbyte in E. unfold wa. exact E.
Qed.

(* HBR at a cut with one live harness block (Φ, n). *)
Lemma u2_hb : forall g phi n L A regs mem md, FR B APIf ra empty g (hb1 phi n) L A regs mem md ->
  Permutation (blocks L A) (hb1 phi n ++ blocks (g_L g) (g_A g)) ->
  stk rsegs (normalize rsegs mem) phi (phi + n) /\ 4096 <= phi /\ phi + n <= YM05.alloc_ceiling.
Proof.
  intros g phi n L A regs mem md HFR HP. pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & _ & HM & _).
  apply (u2_blk L A mem md phi n HM).
  apply (Permutation_in _ (Permutation_sym HP)). left. reflexivity.
Qed.

End M.

(* ---- The block sum loops over bytes 18 .. 49 of the frame (R13, R20): sum, counter, room test AF9 ---- *)

Lemma u2_psum_S : forall bs i,
  RcModel.psum bs (S i) = RcModel.psum bs i + bv_unsigned (nth i bs (Z_to_bv 8 0)).
Proof. reflexivity. Qed.

Lemma u2_psum_rng : forall bs i, 0 <= RcModel.psum bs i <= 255 * Z.of_nat i.
Proof.
  intros bs i. induction i as [|i IH]; cbn [RcModel.psum]; [lia|].
  pose proof (bv_unsigned_in_range 8 (nth i bs (Z_to_bv 8 0))) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. lia.
Qed.

(* blocksum by rewriting, so that no conversion unfolds Z.modulo over psum. *)
Lemma u2_blocksum : forall bs, RcModel.psum bs 32 mod 256 = RcModel.blocksum bs.
Proof. intros bs. unfold RcModel.blocksum. reflexivity. Qed.

Lemma u2_zxb_u : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof.
  intros b. unfold zxb. apply MState.unsigned_lit. pose proof (bv_unsigned_in_range 8 b) as H.
  unfold bv_modulus in H. change (2 ^ Z.of_N 8) with 256 in H. lia.
Qed.

Lemma u2_first1 : forall (l : list byte) k d, (k < length l)%nat -> firstn 1 (skipn k l) = [nth k l d].
Proof.
  induction l as [|x l IH]; intros k d Hk; cbn in Hk; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

(* Byte j of the block X = bytes 18 .. 49 of a frame's first 50 bytes, read from the frame in memory. *)
Lemma u2_rd_blk : forall m phi F j, bytes_at rsegs m phi F -> (50 <= length F)%nat -> (j < 32)%nat ->
  ov_read_bytes rsegs m (wa (phi + 18 + Z.of_nat j)) 1 = Some [nth j (skipn 18 (fr50 F)) (Z_to_bv 8 0)].
Proof.
  intros m phi F j HB HL Hj. rewrite <- Z.add_assoc.
  rewrite (bytes_at_read rsegs m phi F (18 + Z.of_nat j) 1 HB) by lia.
  replace (Z.to_nat (18 + Z.of_nat j)) with (18 + j)%nat by lia.
  rewrite (u2_first1 F (18 + j) (Z_to_bv 8 0)) by lia.
  rewrite nth_skipn. rewrite (u2_fr50_eq F HL). rewrite nth_firstn.
  destruct (Nat.ltb_spec (18 + j) 50); [reflexivity | lia].
Qed.

(* AF9's room value: `li a1,-18; sub a2,a1,s4; sltiu a3,a2,-17; neg a3,a3; and a2,a3,a2` with s4 = Φ gives
   a2 = 2^64 - 18 - Φ when Φ + 18 does not wrap. *)
Lemma u2_room : forall phi, 0 <= phi -> phi + 18 < 2 ^ 64 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (v_sltiu (Z_to_bv 64 (18446744073709551598 -
      bv_unsigned (Z_to_bv 64 phi))) (-17))))) (bv_unsigned (Z_to_bv 64 (18446744073709551598 -
      bv_unsigned (Z_to_bv 64 phi))))) = Z_to_bv 64 (18446744073709551598 - phi).
Proof.
  intros phi H0 H1.
  unfold v_sltiu.
  rewrite (MState.unsigned_lit phi) by lia.
  rewrite (MState.unsigned_lit (18446744073709551598 - phi)) by lia.
  replace (bv_wrap 64 (-17)) with 18446744073709551599 by (vm_compute; reflexivity).
  rewrite (proj2 (Z.ltb_lt (18446744073709551598 - phi) 18446744073709551599)) by lia.
  cbv beta iota.
  rewrite (MState.unsigned_lit 1) by lia.
  replace (bv_unsigned (Z_to_bv 64 (0 - 1))) with (Z.ones 64) by (vm_compute; reflexivity).
  rewrite Z.land_comm, Z.land_ones by lia.
  rewrite Z.mod_small by lia. reflexivity.
Qed.

(* Stack addresses lie above every image segment. *)
Lemma u2_rom_none : forall a, SL_TOP <= a < 2 ^ 64 -> seg_rom rsegs (wa a) = None.
Proof.
  intros a Ha. destruct (find_segment rsegs (bv_unsigned (wa a)) 1) as [seg|] eqn:Ef.
  - apply sl_find_top in Ef. unfold SL_TOP in *. rewrite wa_unsigned in Ef by lia. lia.
  - exact (seg_rom_unmapped rsegs (wa a) Ef).
Qed.

(* A branch decided by unsigned or equality comparisons on Z_to_bv 64 z with z in range: as if_false / if_true,
   with bv_unsigned (Z_to_bv 64 z) rewritten to z (side condition by lia) before lia decides the comparison. *)
Ltac u2_cond := unfold_cond; fold_lit_ux; rewrite ?MState.unsigned_lit by lia; solve_cond_rec.
Ltac u2_if_false :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with false; [cbv iota | symmetry; u2_cond]
  end.
Ltac u2_if_true :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with true; [cbv iota | symmetry; u2_cond]
  end.
