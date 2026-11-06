(* Helpers for the segment lemmas of batch u3 (R22-R24, P01-P09) of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan),
   ported from the plain Tac_b3.v / Tac_b4.v. libreac v1.9.0: frame 1936; OUR at sp+114, frag at sp+120, the P8 id
   at sp+76, the round trip's id at sp+36 (RIDB), `first` at sp+36 (40 bytes, zeroed at 0x136d4: FIRST0):
   - u3_mid: sl_mid with a fixed write set W whose munch over the unnormalized memory reaches the continuation;
   - u3_fp: a write set inside [S - K, S - 104);
   - M8 through the b loop (plan-ubsan section 7; this batch owns it): u3_mrow_and7 (m & 7 = 0, so the store at
     0x133c0 starts M8), u3_M8_keep (across a run whose writes miss [sp+24, sp+32)), u3_M8_rd (the reload
     `ld a0,24(sp)` of T07 and T09 reads 0), and the RB transports u3_RB_bytes / u3_RB_S;
   - the P8 block's bundles, each taken apart in one lemma here (u3_PB_intro, u3_PB_keep, u3_P0_keep, u3_P0_parts,
     u3_PZ_keep), the frame loop's start u3_LI0, and a few word facts. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require PropExec MState Regs6ss RegisterBridge Exec Cells Step Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInvCF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Tac_slot.
Import ListNotations.
Open Scope Z_scope.

Lemma u3_munch_join : forall W W' m1 m2 m3, Frame.munch W m1 m2 -> Frame.munch W' m2 m3 ->
  (forall x, Frame.outside W x -> Frame.outside W' x) -> Frame.munch W m1 m3.
Proof. intros W W' m1 m2 m3 H1 H2 Hs x Hx. rewrite (H2 x (Hs _ Hx)). exact (H1 x Hx). Qed.

(* A write set inside [S - K, S - 104), interval by interval. *)
Lemma u3_fp : forall g W x, Forall (fun iv => g_S g - SLOT_K <= fst iv /\ snd iv <= g_S g - 104) W ->
  0 <= x < 2 ^ 64 -> ~ Frame.outside W x -> g_S g - SLOT_K <= x < g_S g - 104.
Proof.
  intros g W x HF Hx. induction HF as [|[lo hi] W' [H1 H2] HF IH]; cbn [Frame.outside]; intros O.
  - exfalso; exact (O I).
  - cbn [fst snd] in *. destruct (Z_le_dec lo x); destruct (Z_lt_dec x hi).
    + lia.
    + apply IH. intros O'. apply O. split; [lia | exact O'].
    + apply IH. intros O'. apply O. split; [lia | exact O'].
    + apply IH. intros O'. apply O. split; [lia | exact O'].
Qed.

Lemma u3_swrap32 : forall z, -2 ^ 31 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. Z.div_mod_to_equations. lia.
Qed.

Lemma u3_bv_eqb : forall a b, -2 ^ 63 <= a < 2 ^ 63 -> -2 ^ 63 <= b < 2 ^ 63 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616.
  destruct (Z.eqb_spec a b) as [->|Hn]; [apply Z.eqb_refl|]. apply Z.eqb_neq.
  intros E. apply Hn. Z.div_mod_to_equations. lia.
Qed.

(* beqz / bnez on a non-zero value. *)
Lemma u3_eqb0 : forall x, 0 < x < 2 ^ 64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = false.
Proof. intros x Hx. unfold bv_eqb. rewrite !MState.unsigned_lit by lia. apply Z.eqb_neq. lia. Qed.

(* A 1-byte load from a byte cell and an 8-byte load from a q64 cell. *)
Lemma u3_ld1 : forall m a b, bytes_at rsegs m a [b] -> ov_read_bytes rsegs m (wa a) 1 = Some [b].
Proof.
  intros m a b H. replace (wa a) with (wa (a + Z.of_nat 0)) by (f_equal; lia).
  rewrite (bytes_at_ov_read rsegs m a [b] 0 1 H) by (cbn; lia).
  reflexivity.
Qed.

Lemma u3_ld8 : forall m a v, bytes_at rsegs m a (le8 v) -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 v).
Proof.
  intros m a v H. replace (wa a) with (wa (a + Z.of_nat 0)) by (f_equal; lia).
  rewrite (bytes_at_ov_read rsegs m a (le8 v) 0 8 H) by (rewrite length_le8; lia).
  reflexivity.
Qed.

(* ---- M8 through the b loop (plan-ubsan section 7): q64 sp+24 = m & 7 = 0 ---- *)

(* CATU: m = CAT + 296 i is 8-aligned (CAT = 0x1fcc8 = 8 * 16281, 296 = 8 * 37), so `andi a0,s0,7` at 0x133bc
   gives 0. *)
Lemma u3_mrow_and7 : forall inp, Z.land (mrow inp) 7 = 0.
Proof.
  intros inp. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
  unfold mrow, CAT, CAT_ROW.
  replace (0x1fcc8 + 296 * istar inp) with ((16281 + 37 * istar inp) * 8) by lia.
  apply Z.mod_mul. lia.
Qed.

(* M8 across a run whose writes W miss the slot [sp+24, sp+32). *)
Lemma u3_M8_keep : forall g W m m', M8 g m -> Frame.munch W m m' -> disjoint_from W (spk g 24) 8 -> M8 g m'.
Proof.
  intros g W m m' H MU D. unfold M8, q64 in *.
  apply (bytes_at_transport rsegs W m m' _ _ H MU). rewrite length_le8. exact D.
Qed.

(* M8 in the normalized memory of a run (the memory a segment's evt starts from). *)
Lemma u3_M8_norm : forall g m, ro_agree rsegs m -> M8 g m -> M8 g (normalize rsegs m).
Proof.
  intros g m HMI H. unfold M8, q64 in *.
  exact (proj1 (bytes_at_rel rsegs _ _ _ _ (mem_rel_normalize rsegs m HMI)) H).
Qed.

(* The reload `ld a0,24(sp)` (T07 at 0x13584, T09 at 0x1365c) reads 0, so the `bnez a0, 14154` is not taken. *)
Lemma u3_M8_rd : forall g m, M8 g m -> ov_read_bytes rsegs m (wa (spk g 24)) 8 = Some (le8 (Z_to_bv 64 0)).
Proof. intros g m H. exact (u3_ld8 m _ _ H). Qed.

(* M8 from the store `sd a0,24(sp)` of a0 = m & 7 (R04, 0x133c0): the q64 cell holds 0. *)
Lemma u3_M8_of_store : forall g m inp, bytes_at rsegs m (spk g 24) (le8 (Z_to_bv 64 (Z.land (mrow inp) 7))) ->
  M8 g m.
Proof. intros g m inp H. unfold M8, q64. rewrite u3_mrow_and7 in H. exact H. Qed.

(* The three slots of RB and M8, across a munch that misses them. *)
Lemma u3_RB_bytes : forall g b idb fgb regs mem m' W,
  RB g b idb fgb regs mem -> Frame.munch W mem m' ->
  disjoint_from W (spk g 114) 6 -> disjoint_from W (spk g 36) (Z.of_nat (length idb)) ->
  disjoint_from W (spk g 120) (Z.of_nat (length fgb)) -> disjoint_from W (spk g 24) 8 ->
  OURb g m' /\ RIDB g m' idb /\ FGB g m' fgb /\ M8 g m'.
Proof.
  intros g b idb fgb regs mem m' W (_ & _ & HO & _ & HM & _ & HI & HF) MU D1 D2 D3 D4.
  split; [|split; [|split]].
  - unfold OURb in *. apply (bytes_at_transport rsegs W mem m' _ _ HO MU). rewrite OUR_length. exact D1.
  - exact (bytes_at_transport rsegs W mem m' _ _ HI MU D2).
  - exact (bytes_at_transport rsegs W mem m' _ _ HF MU D3).
  - exact (u3_M8_keep g W mem m' HM MU D4).
Qed.

(* RB at turn b from new registers that keep the round-trip ones. *)
Lemma u3_RB : forall g b idb fgb regs mem regs' m',
  RB g b idb fgb regs mem ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 ->
  getr regs' 19 = getr regs 19 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
  getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
  getr regs' 27 = getr regs 27 ->
  OURb g m' -> RIDB g m' idb -> FGB g m' fgb -> M8 g m' ->
  RB g b idb fgb regs' m'.
Proof.
  intros g b idb fgb regs mem regs' m' (Hb & (Hc & H22 & H23) & _ & (H8 & H18 & H19 & H24 & H25 & H26 & H27) & _ & H9 & _)
    E8 E9 E18 E19 E22 E23 E24 E25 E26 E27 B1 B2 B3 B4.
  unfold RB, CUR, RT, rg in *.
  rewrite E8, E9, E18, E19, E22, E23, E24, E25, E26, E27. tauto.
Qed.

(* RB at turn b + 1 (R22's latch: s1 = b + 1). *)
Lemma u3_RB_S : forall g b idb fgb regs mem regs' m',
  RB g b idb fgb regs mem -> (S b <= 6)%nat ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = Z_to_bv 64 (Z.of_nat (S b)) -> getr regs' 18 = getr regs 18 ->
  getr regs' 19 = getr regs 19 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
  getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
  getr regs' 27 = getr regs 27 ->
  OURb g m' -> RIDB g m' idb -> FGB g m' fgb -> M8 g m' ->
  RB g (S b) idb fgb regs' m'.
Proof.
  intros g b idb fgb regs mem regs' m' (Hb & (Hc & H22 & H23) & _ & (H8 & H18 & H19 & H24 & H25 & H26 & H27) & _ & H9 & _)
    HS E8 E9 E18 E19 E22 E23 E24 E25 E26 E27 B1 B2 B3 B4.
  unfold RB, CUR, RT, rg in *.
  rewrite E8, E9, E18, E19, E22, E23, E24, E25, E26, E27. tauto.
Qed.

(* ---- The P8 block (P01-P09) ---- *)

Lemma u3_len_ID0 : length RcIdentModel.ID0 = 38%nat.
Proof. reflexivity. Qed.

(* A disjointness from a range gives the disjointness from each sub-range. *)
Lemma u3_disj_sub : forall W a n a' n', Frame.disjoint_from W a n -> a <= a' -> a' + n' <= a + n ->
  Frame.disjoint_from W a' n'.
Proof.
  induction W as [|[lo hi] W IH]; cbn [disjoint_from]; intros a n a' n' HD H1 H2; [exact I|].
  destruct HD as [H HD]. split; [lia | exact (IH a n a' n' HD H1 H2)].
Qed.

(* PB at U136e4 from its parts: the cursor at c0, our, and `first` = 40 zero bytes at sp+36 (FIRST0, the memset
   at 0x136d4). *)
Lemma u3_PB_intro : forall g regs m, CUR g (c0 (g_in g)) regs -> OURb g m ->
  bytes_at rsegs m (spk g 36) (repeat (Z_to_bv 8 0) 40) -> PB g regs m.
Proof. intros g regs m HC HO HF. exact (conj HC (conj HO HF)). Qed.

(* PB across a run that writes W, disjoint from `first` [sp+36, sp+76) and our [sp+114, sp+120). *)
Lemma u3_PB_keep : forall g regs regs' m m' W,
  PB g regs m -> Frame.munch W m m' ->
  Frame.disjoint_from W (spk g 36) 40 -> Frame.disjoint_from W (spk g 114) 6 ->
  getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 -> PB g regs' m'.
Proof.
  intros g regs regs' m m' W ((Hc & Hp & Hn) & HOUR & HF0) MU D1 D2 E22 E23.
  unfold PB, CUR, OURb, FIRST0, rg in *. rewrite E22, E23.
  refine (conj (conj Hc (conj Hp Hn)) (conj _ _)).
  - apply (bytes_at_transport rsegs W m m' _ _ HOUR MU). rewrite OUR_length. exact D2.
  - apply (bytes_at_transport rsegs W m m' _ _ HF0 MU). rewrite repeat_length. exact D1.
Qed.

(* P0 (the P8 bundle) across a run that writes W, disjoint from [sp+36, sp+192): first [36, 76), id [76, 114),
   our [114, 120), frag [120, 192). *)
Lemma u3_P0_keep : forall g regs regs' m m' W,
  P0 g regs m -> Frame.munch W m m' -> Frame.disjoint_from W (spk g 36) 156 ->
  getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 -> P0 g regs' m'.
Proof.
  intros g regs regs' m m' W (HPB & HID & HFG) MU HD E22 E23.
  refine (conj (u3_PB_keep g regs regs' m m' W HPB MU _ _ E22 E23) (conj _ _)).
  - apply (u3_disj_sub W _ _ _ _ HD); unfold spk; lia.
  - apply (u3_disj_sub W _ _ _ _ HD); unfold spk; lia.
  - unfold IDB in *. apply (bytes_at_transport rsegs W m m' _ _ HID MU). rewrite u3_len_ID0.
    apply (u3_disj_sub W _ _ _ _ HD); unfold spk; lia.
  - unfold FGB in *. apply (bytes_at_transport rsegs W m m' _ _ HFG MU). rewrite z72_length.
    apply (u3_disj_sub W _ _ _ _ HD); unfold spk; lia.
Qed.

(* The parts of P0 (P09). *)
Lemma u3_P0_parts : forall g regs m, P0 g regs m ->
  CUR g (c0 (g_in g)) regs /\ OURb g m /\ IDB g m RcIdentModel.ID0 /\ FGB g m z72 /\
  bytes_at rsegs m (spk g 36) (repeat (Z_to_bv 8 0) 40).
Proof. intros g regs m ((HC & HO & HF) & HI & HG). exact (conj HC (conj HO (conj HI (conj HG HF)))). Qed.

(* PZ across a run that writes W, disjoint from the code byte sp+1824 and the out block [sp+192, sp+224). *)
Lemma u3_PZ_keep : forall g code m m' W, PZ g code m -> Frame.munch W m m' ->
  Frame.disjoint_from W (spk g 1824) 1 -> Frame.disjoint_from W (spk g 192) 32 -> PZ g code m'.
Proof.
  intros g code m m' W (H1 & H2) MU D1 D2. unfold PZ, b8 in *. split.
  - exact (bytes_at_transport rsegs W m m' _ _ H1 MU D1).
  - apply (bytes_at_transport rsegs W m m' _ _ H2 MU). rewrite repeat_length. exact D2.
Qed.

(* The frame loop's start (P09 -> U137d0 at j = 0): ID_0 = 38 zeros is id_ok, FG_0 = 72 zeros is frag_ok, FS_0 =
   (0, 0, 0, 0) satisfies FI and is `first` = 0, and J = 0 when nothing is left after the first c0 bytes. *)
Lemma u3_nth_ID0 : forall j, RcIdentModel.nthb RcIdentModel.ID0 j = RcIdentModel.zb 0.
Proof. intros j. unfold RcIdentModel.nthb, RcIdentModel.ID0. apply nth_repeat. Qed.

Lemma u3_id_ok_ID0 : RcIdentModel.id_ok RcIdentModel.ID0.
Proof.
  assert (Z0 : forall j, RcIdentModel.bz (RcIdentModel.nthb RcIdentModel.ID0 j) = 0).
  { intros j. rewrite u3_nth_ID0. reflexivity. }
  unfold RcIdentModel.id_ok, RcIdentModel.has_fw, RcIdentModel.has_model_name, RcIdentModel.has_reac_version,
    RcIdentModel.fw_milli, RcIdentModel.major, RcIdentModel.minor, RcIdentModel.patch, RcIdentModel.be16.
  repeat split; intros; rewrite ?Z0 in *; lia.
Qed.

Lemma u3_frag_ok_z72 : frag_ok z72.
Proof. unfold frag_ok. split; [left; vm_compute; reflexivity | intros H; vm_compute in H; discriminate H]. Qed.

Lemma u3_FI_z72 : FI z72 fs0.
Proof. unfold FI. split; intros H; vm_compute in H; discriminate H. Qed.

Lemma u3_fJ0 : forall inp, nlen inp - c0 inp = 0 -> fJ inp = 0%nat.
Proof.
  intros inp H. unfold fJ.
  assert (E : forall j f, f_left inp (fc inp j) = 0 -> fJ_from inp j (S f) = j).
  { intros j f Hj. cbn [fJ_from]. rewrite Hj. reflexivity. }
  apply (E 0%nat 255%nat). cbn [fc]. unfold f_left. exact H.
Qed.

(* A run of zero bytes holds zeros on each sub-range. *)
Lemma u3_zero_sub : forall m a n k l, bytes_at rsegs m a (repeat (Z_to_bv 8 0) n) -> (k + l <= n)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (repeat (Z_to_bv 8 0) l).
Proof.
  intros m a n k l H Hk.
  replace n with (k + (l + (n - k - l)))%nat in H by lia.
  rewrite !repeat_app in H.
  apply bytes_at_app in H as [_ H]. rewrite repeat_length in H.
  apply bytes_at_app in H as [H _]. exact H.
Qed.

(* LI at j = 0 (P09 -> U137d0): s1 = j = 0, our, the -7 pair at sp+8 (M7), s0 = sp+128 (OVF), s2 = 1 (S2, A2), the
   cursor at c0 with something left, ID_0 = 38 zeros at sp+76, FG_0 = 72 zeros at sp+120, and FS_0 over `first`
   = 0 (have u32 sp+36 = 0, n u8 sp+40 = 0, the empty body at sp+41). *)
Lemma u3_LI0 : forall g regs m,
  rg regs 9 0 -> OURb g m -> M7 g m -> rg regs 8 (spk g 128) -> rg regs 18 1 ->
  CUR g (c0 (g_in g)) regs -> 1 <= g_n g - c0 (g_in g) ->
  IDB g m RcIdentModel.ID0 -> FGB g m z72 -> bytes_at rsegs m (spk g 36) (repeat (Z_to_bv 8 0) 40) ->
  LI g 0 regs m.
Proof.
  intros g regs m H9 HO H7 H8 H18 HC HL HI HF HZ.
  assert (Ef : t_c (g_in g) 0 = c0 (g_in g)) by reflexivity.
  assert (Ef' : t_left (g_in g) 0 = g_n g - c0 (g_in g)) by reflexivity.
  assert (Z4 : u32 m (spk g 36) 0).
  { pose proof (u3_zero_sub m _ 40 0 4 HZ ltac:(lia)) as X. unfold u32.
    replace (spk g 36 + Z.of_nat 0) with (spk g 36) in X by lia.
    replace (le4 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0) 4) by (vm_compute; reflexivity). exact X. }
  assert (Z1 : b8 m (spk g 40) 0).
  { pose proof (u3_zero_sub m _ 40 4 1 HZ ltac:(lia)) as X. unfold b8.
    replace (spk g 36 + Z.of_nat 4) with (spk g 40) in X by (unfold spk; lia). exact X. }
  assert (Zb : bytes_at rsegs m (spk g 41) []).
  { pose proof (u3_zero_sub m _ 40 5 0 HZ ltac:(lia)) as X.
    replace (spk g 36 + Z.of_nat 5) with (spk g 41) in X by (unfold spk; lia). exact X. }
  unfold LI, LK, IFS, IDj, FGj, FSj, IDb, FGb, FSb, OVF, S2, A2. rewrite Ef, Ef'.
  split; [split; [lia | exact (conj H9 (conj HO (conj H7 (conj H8 H18))))]|].
  split; [exact HC|]. split; [exact HL|]. split; [|exact H18].
  split; [exact (conj HI u3_id_ok_ID0)|]. split; [exact (conj HF u3_frag_ok_z72)|].
  exact (conj Z4 (conj Z1 (conj Zb (conj eq_refl u3_FI_z72)))).
Qed.

(* ---- Image bytes in frame_RELRO's first range [0x1fc48, 0x20b18) ---- *)

Lemma u3_image_nth : forall n A bs, Image.image_bytes rsegs A n = Some bs ->
  forall i, (i < n)%nat -> PropExec.seg_rom rsegs (wa (A + Z.of_nat i)) = nth_error bs i.
Proof.
  induction n as [|n IH]; intros A bs H i Hi; [lia|].
  cbn [Image.image_bytes] in H.
  destruct (PropExec.seg_rom rsegs (wa A)) as [b|] eqn:E; [|discriminate].
  destruct (Image.image_bytes rsegs (A + 1) n) as [bs'|] eqn:E'; [|discriminate].
  injection H as <-. destruct i as [|i].
  - cbn [nth_error]. replace (A + Z.of_nat 0) with A by lia. exact E.
  - cbn [nth_error]. replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia. apply IH; [exact E' | lia].
Qed.

Lemma u3_in_relro : forall a, 0x1fc48 <= a < 0x20b18 -> in_globals frame_RELRO a.
Proof. intros a Ha. exists 0x1fc48, 3792. split; [left; reflexivity | lia]. Qed.

Section S.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma u3_relro_bytes : forall mem a n bs, relro B mem -> Image.image_bytes rsegs a n = Some bs ->
  0x1fc48 <= a -> a + Z.of_nat n <= 0x20b18 -> bytes_at rsegs mem a bs.
Proof.
  intros mem a n bs HR HI H0 H1. pose proof (Image.image_bytes_length rsegs n a bs HI) as L.
  unfold relro, G_img_c in HR. rewrite (sl_segs B APIf ra empty FF) in HR.
  split; [lia|]. split; [rewrite L; lia|]. intros i Hi. rewrite L in Hi.
  rewrite <- (u3_image_nth n a bs HI i Hi).
  exact (HR (a + Z.of_nat i) (u3_in_relro (a + Z.of_nat i) ltac:(lia))).
Qed.

Lemma u3_mid : forall g hb L A regs mem md pc W (Q : machine_state -> Prop) (P : config -> Prop),
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x -> g_S g - SLOT_K <= x < g_S g - 104) ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R pc' m', ms = MState.MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
     Frame.munch W (normalize rsegs mem) m' /\ Frame.wmono rsegs (normalize rsegs mem) m' /\
     getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4) ->
  (forall R pc' m0' regs' m', Q (MState.MS R fp_regs pc' fp_csr None m0' (seg_rom rsegs)) ->
     Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m' m0' -> Frame.munch W mem m' ->
     FR B APIf ra empty g hb L A regs' m' md ->
     SR (ms_segs B) (mkCfg (mkst regs' pc' m' (seg_rom (ms_segs B))) md) P) ->
  SR (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros g hb L A regs mem md pc W Q P HFR HP HW HE Hform HK.
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & HMI & _ & HM & _).
  unfold MI in HMI. rewrite SEGS in HMI.
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  apply (sl_run regs pc mem md Q P Hh Hl HMI HE).
  - intros ms HQ. destruct (Hform ms HQ) as (R & pc' & m' & -> & _). exists R, pc', m'. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel Hsame.
    destruct (Hform _ HQ) as (R1 & pc1 & m1 & E & MU & WM & E2 & E3 & E4).
    injection E; intros; subst.
    pose proof (mem_rel_normalize rsegs mem HMI) as HR0.
    pose proof (munch_rel rsegs W mem (normalize rsegs mem) m' m1 HR0 Hrel Hsame MU) as MU'.
    rewrite <- SEGS. apply (HK R1 pc1 m1 regs' m' HQ Hx Hrel MU').
    apply (sl_fr_run B APIf ra empty FF g hb L A regs mem md regs' m' W HFR HP).
    + exact MU'.
    + exact (wmono_rel rsegs mem (normalize rsegs mem) m' m1 HR0 Hrel Hsame WM).
    + exact (ro_agree_same rsegs mem m' HMI Hsame).
    + exact HW.
    + rewrite (sl_getr_eqv _ _ _ Hx). exact E2.
    + rewrite (sl_getr_eqv _ _ _ Hx). exact E3.
    + rewrite (sl_getr_eqv _ _ _ Hx). exact E4.
Qed.

End S.
