(* Frame helpers for batch b8 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): opening and closing cuts, straight runs
   (b8_run_to, b8_run_ex), runs through a Kind A callee on the normalized memory (b8_mid), the free call with the
   frame transported (b8_free_call), and Post from FR (b8_post_FR). Ported from the fuzz_identity slot's Tac_sj.v
   (a working branch) to this tree's FR (no allocator count) and to blocks of 0 bytes (blocks_nodup).
   libreac v1.9.0 (SlotInv.v's v1.9 cut bundle): frame 1936 bytes; the transports follow the v1.9 bundles (FC with
   s11 and the spill [sp+32], VCm, IFS with nb in s3 and the `first` body at sp+40; b8_VC_* became b8_VCm_*, and
   b8_IFS_regs is new); free at 0x1635c, errno at 0x30f00 - 164, frame_RELRO's first block at 0x1ed20, the sink
   symbols at 0x51191 / 0x515b8 / 0x515c0 (frame_facts' fields). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Exec Step Tac Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b8m.
Import ListNotations.
Open Scope Z_scope.

Lemma b8_in_blocks : forall L A a n, In (a, n) (blocks L A) -> exists p, In (p, n) (user_blocks A) /\ ptr_addr L p = a.
Proof.
  intros L A a n H. unfold blocks in H. apply in_map_iff in H as ([p n'] & E & Hp).
  cbn [fst snd] in E. injection E as E1 E2. subst. exists p. split; [exact Hp | reflexivity].
Qed.

Lemma b8_blocks_in : forall L A p n, In (p, n) (user_blocks A) -> In (ptr_addr L p, n) (blocks L A).
Proof. intros L A p n H. unfold blocks. apply in_map_iff. exists (p, n). split; [reflexivity | exact H]. Qed.

Lemma b8_unsigned : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. exact unsigned_lit. Qed.

Lemma b8_ret_pc : forall z, 0 <= z < 2 ^ 64 -> z mod 2 = 0 -> ret_pc (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. exact ret_pc_even. Qed.

Lemma b8_ret_pc_ra : forall z, z mod 2 = 0 -> ret_pc (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. assert (E : Z_to_bv 64 z = Z_to_bv 64 (z mod 2 ^ 64)).
  { apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    rewrite Z.mod_mod by lia. reflexivity. }
  rewrite E. apply ret_pc_even; [apply Z.mod_pos_bound; lia|].
  rewrite <- Znumtheory.Zmod_div_mod; [exact Hz | lia | lia | exists (2 ^ 63); reflexivity].
Qed.

Lemma b8_pw_app : forall (T : Type) (R : T -> T -> Prop) l1 l2, pairwise R (l1 ++ l2) -> pairwise R l2.
Proof. intros T R l1 l2. induction l1 as [|x l1 IH]; intros H; [exact H | exact (IH (proj2 H))]. Qed.

Lemma b8_stk_sub : forall segs m lo hi lo' hi', stk segs m lo hi -> lo <= lo' -> hi' <= hi -> 0 <= lo' ->
  stk segs m lo' hi'.
Proof.
  intros segs m lo hi lo' hi' (H1 & H2 & H) E1 E2 E3. split; [exact E3|]. split; [lia|]. intros a Ha. apply H. lia.
Qed.

Lemma b8_outside1 : forall lo hi x, outside [(lo, hi)] x <-> ~ (lo <= x < hi).
Proof. intros lo hi x. cbn. tauto. Qed.

Lemma b8_mbyte_eq : forall segs (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> mbyte segs m' a = mbyte segs m a.
Proof. intros segs m m' a H. unfold mbyte. rewrite H. reflexivity. Qed.

Lemma b8_wr_eq : forall segs (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> (writable_at segs m a <-> writable_at segs m' a).
Proof. intros segs m m' a H. unfold writable_at, wview. rewrite H. tauto. Qed.

Lemma b8_ba_munch : forall segs W m m' a bs, bytes_at segs m a bs -> munch W m m' ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> outside W (a + i)) -> bytes_at segs m' a bs.
Proof.
  intros segs W m m' a bs H HM HO. pose proof (bytes_at_bound segs m a bs H) as HB.
  destruct H as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros i Hi.
  unfold mrd, wa. rewrite (HM (Z_to_bv 64 (a + Z.of_nat i))). - exact (H3 i Hi).
  - rewrite unsigned_lit by lia. apply HO. lia.
Qed.

Lemma b8_ba_mbyte : forall m m' a bs, bytes_at rsegs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) ->
  bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs (H1 & H2 & H3) HE. split; [exact H1|]. split; [exact H2|].
  intros i Hi. pose proof (HE (Z.of_nat i) ltac:(lia)) as E. unfold mbyte in E. unfold mrd, wa.
  rewrite <- (H3 i Hi). unfold mrd, wa. exact E.
Qed.

Lemma b8_bytes_le8 : forall segs m a v, bytes_at segs m a (le8 v) -> ov_read_bytes segs m (wa a) 8 = Some (le8 v).
Proof.
  intros segs m a v H. replace (wa a) with (wa (a + Z.of_nat 0)) by (f_equal; lia).
  rewrite (bytes_at_ov_read segs m a (le8 v) 0 8 H) by (rewrite length_le8; lia).
  reflexivity.
Qed.

Lemma b8_bytes_le4 : forall segs m a v, bytes_at segs m a (le4 v) -> ov_read_bytes segs m (wa a) 4 = Some (le4 v).
Proof.
  intros segs m a v H. replace (wa a) with (wa (a + Z.of_nat 0)) by (f_equal; lia).
  rewrite (bytes_at_ov_read segs m a (le4 v) 0 4 H) by (rewrite length_le4; lia).
  reflexivity.
Qed.

Lemma b8_bytes_ovr : forall segs m a bs, bytes_at segs m a bs -> ov_read_bytes segs m (wa a) (length bs) = Some bs.
Proof.
  intros segs m a bs H. replace (wa a) with (wa (a + Z.of_nat 0)) by (f_equal; lia).
  rewrite (bytes_at_ov_read segs m a bs 0 (length bs) H) by lia. rewrite skipn_O, firstn_all. reflexivity.
Qed.

(* Register transport of the cut bundles (SlotInv.v, v1.9.0): FC keeps left - h in s11 (27) and the length in s4
   (20), the body pointer is the spill [sp+32]; VCm keeps s6 (22); the frame state's nb is s3 (19). *)
Lemma b8_FT_regs : forall g j phi regs regs' m, FT g j phi regs m ->
  getr regs' 20 = getr regs 20 -> getr regs' 21 = getr regs 21 -> getr regs' 26 = getr regs 26 ->
  getr regs' 27 = getr regs 27 -> FT g j phi regs' m.
Proof.
  intros g j phi regs regs' m (Hj & H26 & (H27 & H32 & H20) & H21 & HB & HO & HM) E20 E21 E26 E27.
  unfold FT, FC, rg. split; [exact Hj|]. split; [rewrite E26; exact H26|].
  split; [split; [rewrite E27; exact H27|]; split; [exact H32 | rewrite E20; exact H20]|].
  split; [rewrite E21; exact H21|]. split; [exact HB|]. split; [exact HO | exact HM].
Qed.

Lemma b8_VCm_regs : forall g j phi regs regs' m, VCm g j phi regs m ->
  getr regs' 22 = getr regs 22 -> VCm g j phi regs' m.
Proof.
  intros g j phi regs regs' m (H22 & HT & HB) E22. unfold VCm, rg.
  split; [rewrite E22; exact H22|]. split; [exact HT | exact HB].
Qed.

Lemma b8_IFS_regs : forall g k regs regs' m, IFS g k regs m -> getr regs' 19 = getr regs 19 -> IFS g k regs' m.
Proof.
  intros g k regs regs' m (HID & HFG & (H16 & H19 & HBD & HL & HFI)) E19.
  split; [exact HID|]. split; [exact HFG|].
  split; [exact H16|]. split; [unfold rg in *; rewrite E19; exact H19|].
  split; [exact HBD|]. split; [exact HL | exact HFI].
Qed.

Lemma b8_CC7_regs : forall g j phi regs regs' m, CC7 g j phi regs m ->
  getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 ->
  getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 -> getr regs' 26 = getr regs 26 ->
  getr regs' 27 = getr regs 27 -> CC7 g j phi regs' m.
Proof.
  intros g j phi regs regs' m (HFT & H18 & HVC & HI) E18 E19 E20 E21 E22 E26 E27.
  split; [exact (b8_FT_regs g j phi regs regs' m HFT E20 E21 E26 E27)|].
  split; [unfold V2m, rg in *; rewrite E18; exact H18|].
  split; [exact (b8_VCm_regs g j phi regs regs' m HVC E22) | exact (b8_IFS_regs g (S j) regs regs' m HI E19)].
Qed.

Lemma b8_CC_regs : forall g j phi regs regs' m, CC g j phi regs m ->
  getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 ->
  getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
  getr regs' 26 = getr regs 26 -> getr regs' 27 = getr regs 27 -> CC g j phi regs' m.
Proof.
  intros g j phi regs regs' m (HC & H23) E18 E19 E20 E21 E22 E23 E26 E27.
  split; [exact (b8_CC7_regs g j phi regs regs' m HC E18 E19 E20 E21 E22 E26 E27)|].
  unfold V7, rg in *. rewrite E23. exact H23.
Qed.

Lemma b8_eqb_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma b8_ltu_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

(* Memory transport of the cut bundles across a run that writes only inside W. v1.9.0 frame (SlotInv.v): M7 at
   sp+8, have at sp+16, TF at sp+24, the body pointer at sp+32, the `first` body at sp+40 (at most 23 bytes,
   b8_body_len), our at sp+76, frag at sp+82, id at sp+154 (so IFS lies in [sp+16, sp+192)), B at sp+1752. *)
Lemma b8_ba_keepW : forall W m m' a bs, bytes_at rsegs m a bs -> munch W m m' ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> outside W x) -> bytes_at rsegs m' a bs.
Proof. intros W m m' a bs H MU HW. apply (b8_ba_munch rsegs W m m' a bs H MU). intros i Hi. apply HW. lia. Qed.

Lemma b8_IFS_munch : forall g k regs m m' W, IFS g k regs m -> munch W m m' ->
  (forall x, spk g 16 <= x < spk g 192 -> outside W x) -> IFS g k regs m'.
Proof.
  intros g k regs m m' W ((HID & Hok) & (HFG & Hfo) & (H16 & H19 & HBD & HL & HFI)) MU HW.
  split; [split; [|exact Hok]|].
  { unfold IDB in *. apply (b8_ba_keepW W m m' _ _ HID MU). rewrite b8_ID_length. intros x Hx. apply HW.
    unfold spk in *. lia. }
  split; [split; [|exact Hfo]|].
  { unfold FGB in *. apply (b8_ba_keepW W m m' _ _ HFG MU). rewrite b8_FG_length. intros x Hx. apply HW.
    unfold spk in *. lia. }
  unfold q64 in *.
  split; [apply (b8_ba_keepW W m m' _ _ H16 MU); rewrite length_le8; intros x Hx; apply HW; unfold spk in *; lia|].
  split; [exact H19|].
  split; [|split; [exact HL | exact HFI]].
  pose proof (b8_body_len (g_in g) k) as HBL.
  apply (b8_ba_keepW W m m' _ _ HBD MU). intros x Hx. apply HW. unfold spk in *. lia.
Qed.

Lemma b8_OURb_munch : forall g m m' W, OURb g m -> munch W m m' ->
  (forall x, spk g 76 <= x < spk g 82 -> outside W x) -> OURb g m'.
Proof.
  intros g m m' W H MU HW. unfold OURb in *. apply (b8_ba_keepW W m m' _ _ H MU). rewrite OUR_length.
  intros x Hx. apply HW. unfold spk in *. lia.
Qed.

Lemma b8_M7_munch : forall g m m' W, M7 g m -> munch W m m' ->
  (forall x, spk g 8 <= x < spk g 16 -> outside W x) -> M7 g m'.
Proof.
  intros g m m' W H MU HW. unfold M7, q64 in *. apply (b8_ba_keepW W m m' _ _ H MU). rewrite length_le8.
  intros x Hx. apply HW. unfold spk in *. lia.
Qed.

Lemma b8_FT_munch : forall g j phi regs m m' W, FT g j phi regs m -> munch W m m' ->
  (forall x, (spk g 8 <= x < spk g 82 \/ phi <= x < phi + t_len (g_in g) j) -> outside W x) -> FT g j phi regs m'.
Proof.
  intros g j phi regs m m' W (Hj & H26 & (H27 & H32 & H20) & H21 & HB & HO & HM) MU HW.
  pose proof (b8_t_facts (g_in g) j) as (_ & _ & _ & _ & HL & _).
  split; [exact Hj|]. split; [exact H26|].
  split; [split; [exact H27|]; split; [|exact H20]|].
  { unfold q64 in *. apply (b8_ba_keepW W m m' _ _ H32 MU). rewrite length_le8. intros x Hx. apply HW.
    unfold spk in *. lia. }
  split; [exact H21|].
  split; [apply (b8_ba_keepW W m m' _ _ HB MU); rewrite b8_phi_length; intros x Hx; apply HW; unfold spk in *; lia|].
  split; [apply (b8_OURb_munch g m m' W HO MU); intros x Hx; apply HW; unfold spk in *; lia|].
  apply (b8_M7_munch g m m' W HM MU); intros x Hx; apply HW; unfold spk in *; lia.
Qed.

Lemma b8_VCm_munch : forall g j phi regs m m' W, VCm g j phi regs m -> munch W m m' ->
  (forall x, (spk g 24 <= x < spk g 32 \/ spk g 1752 <= x < spk g 1788) -> outside W x) -> VCm g j phi regs m'.
Proof.
  intros g j phi regs m m' W (H22 & HT & HB) MU HW.
  split; [exact H22|]. unfold q64 in *.
  split; [apply (b8_ba_keepW W m m' _ _ HT MU); rewrite length_le8; intros x Hx; apply HW; unfold spk in *; lia|].
  apply (b8_ba_keepW W m m' _ _ HB MU). rewrite b8_B_length. intros x Hx. apply HW. unfold spk in *. lia.
Qed.

Lemma b8_CC7_munch : forall g j phi regs m m' W, CC7 g j phi regs m -> munch W m m' ->
  (forall x, (spk g 8 <= x < spk g 192 \/ spk g 1752 <= x < spk g 1788 \/ phi <= x < phi + t_len (g_in g) j) ->
     outside W x) -> CC7 g j phi regs m'.
Proof.
  intros g j phi regs m m' W (HFT & H18 & HVC & HI) MU HW.
  split; [apply (b8_FT_munch g j phi regs m m' W HFT MU); intros x Hx; apply HW; unfold spk in *; lia|].
  split; [exact H18|].
  split; [apply (b8_VCm_munch g j phi regs m m' W HVC MU); intros x Hx; apply HW; unfold spk in *; lia|].
  apply (b8_IFS_munch g (S j) regs m m' W HI MU); intros x Hx; apply HW; unfold spk in *; lia.
Qed.

Lemma b8_ba_above : forall m m' lo a bs, bytes_at rsegs m a bs -> lo <= a ->
  (forall x, lo <= x < 2 ^ 64 -> mbyte rsegs m' x = mbyte rsegs m x) -> bytes_at rsegs m' a bs.
Proof.
  intros m m' lo a bs H Hlo HK. pose proof (bytes_at_bound rsegs m a bs H) as HB.
  apply (b8_ba_mbyte m m' a bs H). intros i Hi. apply HK. lia.
Qed.

Lemma b8_IFS_above : forall g k regs m m', IFS g k regs m ->
  (forall x, spk g 0 <= x < 2 ^ 64 -> mbyte rsegs m' x = mbyte rsegs m x) -> IFS g k regs m'.
Proof.
  intros g k regs m m' ((HID & Hok) & (HFG & Hfo) & (H16 & H19 & HBD & HL & HFI)) HK.
  split; [split; [apply (b8_ba_above m m' (spk g 0) _ _ HID); [unfold spk; lia | exact HK] | exact Hok]|].
  split; [split; [apply (b8_ba_above m m' (spk g 0) _ _ HFG); [unfold spk; lia | exact HK] | exact Hfo]|].
  split; [apply (b8_ba_above m m' (spk g 0) _ _ H16); [unfold spk; lia | exact HK]|].
  split; [exact H19|].
  split; [apply (b8_ba_above m m' (spk g 0) _ _ HBD); [unfold spk; lia | exact HK]|].
  split; [exact HL | exact HFI].
Qed.

Lemma b8_OURb_above : forall g m m', OURb g m ->
  (forall x, spk g 0 <= x < 2 ^ 64 -> mbyte rsegs m' x = mbyte rsegs m x) -> OURb g m'.
Proof. intros g m m' H HK. apply (b8_ba_above m m' (spk g 0) _ _ H); [unfold spk; lia | exact HK]. Qed.

Lemma b8_M7_above : forall g m m', M7 g m ->
  (forall x, spk g 0 <= x < 2 ^ 64 -> mbyte rsegs m' x = mbyte rsegs m x) -> M7 g m'.
Proof. intros g m m' H HK. apply (b8_ba_above m m' (spk g 0) _ _ H); [unfold spk; lia | exact HK]. Qed.

Ltac b8rg HG := rewrite HG; first [reflexivity | assumption | match goal with H : _ |- _ => exact H end].

Lemma b8_lit0 : forall v, -256 < v < 256 -> (Z_to_bv 64 v = Z_to_bv 64 0 <-> v = 0).
Proof.
  intros v Hv. split; intros E; [|subst; reflexivity].
  apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit_wrap in E. change (0 mod 2 ^ 64) with 0 in E.
  Z.div_mod_to_equations. lia.
Qed.

Lemma b8_ba_sub : forall segs m a bs k n, bytes_at segs m a bs -> (k + n <= length bs)%nat ->
  bytes_at segs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros segs m a bs k n H Hl. rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn in H. replace (Nat.min k (length bs)) with k in H by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

Section TacB8.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Local Notation API := (APIf rc).
Local Notation segs := (ms_segs B).
Local Notation MR := (aa_MR (APIf rc)).

Lemma b8_segs : ms_segs B = rsegs.
Proof. exact (proj1 FF). Qed.

Lemma b8_ra : ra mod 2 = 0.
Proof. exact (proj1 (proj2 FF)). Qed.

Lemma b8_free_addr : ms_free B = 0x1635c.
Proof. destruct FF as (_ & _ & _ & H & _). exact H. Qed.

Lemma b8_errno_ceil : errno_addr B + 4 <= alloc_ceiling.
Proof. destruct FF as (_ & _ & _ & _ & _ & _ & H & _). exact (H rc). Qed.

Lemma b8_errno : errno_addr B = 0x30f00 - 164.
Proof.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H1 & H2 & _).
  unfold errno_addr. rewrite H1, H2. reflexivity.
Qed.

Lemma b8_relro_img : forall a, in_globals frame_RELRO a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Proof.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & H & _). exact H.
Qed.

Lemma b8_alloc : frame_allocator B API.
Proof.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & H). exact (H rc fx).
Qed.

Lemma b8_nodup : blocks_nodup B API.
Proof. destruct b8_alloc as (_ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma b8_ax : AllocExtra B MR.
Proof. destruct b8_alloc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma b8_img_low : img_low B.
Proof.
  apply (img_low_of_check B SL_TOP).
  - unfold img_check. rewrite b8_segs. vm_compute. reflexivity.
  - pose proof sl_ceil. lia.
Qed.

Lemma b8_img_lt : forall a, in_img B a -> 0 <= a < alloc_ceiling.
Proof. intros a H. destruct b8_img_low as [HI _]. exact (HI a H). Qed.

Lemma b8_seg_low : forall x seg, find_segment rsegs x 1 = Some seg -> 0 <= x < alloc_ceiling.
Proof. intros x seg H. destruct b8_img_low as [_ HI]. rewrite b8_segs in HI. exact (HI x seg H). Qed.

Lemma b8_ro_low : forall a : word, ro_addr rsegs a = true -> bv_unsigned a < alloc_ceiling.
Proof.
  intros a H. unfold ro_addr in H. destruct (find_segment rsegs (bv_unsigned a) 1) as [seg|] eqn:E; [|discriminate].
  exact (proj2 (b8_seg_low _ seg E)).
Qed.

Lemma b8_hi_noseg : forall a : word, alloc_ceiling <= bv_unsigned a -> find_segment rsegs (bv_unsigned a) 1 = None.
Proof.
  intros a H. destruct (find_segment rsegs (bv_unsigned a) 1) as [seg|] eqn:E; [|reflexivity].
  pose proof (b8_seg_low _ seg E). lia.
Qed.

Lemma b8_empty : 0 < empty < 2 ^ 62.
Proof.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _).
  exact H.
Qed.

Lemma b8_p_range : forall g hb L A regs mem md, FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  0 <= g_p g /\ g_p g + g_n g < 2 ^ 62 /\ 0 <= g_n g < 2 ^ 26.
Proof.
  intros g hb L A regs mem md HF HP. pose proof HF as (HGV & _ & _ & _ & _ & _ & _ & _ & HMR & _).
  pose proof HGV as (Hn & Hpl & _). pose proof b8_empty as HE. pose proof alloc_ceiling_lt as HAC.
  destruct Hpl as [[E0 Ep]|[Hn0 Hin]].
  - rewrite E0, Ep. lia.
  - assert (Hin' : In (g_p g, g_n g) (blocks L A))
      by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact Hin).
    destruct (b8_in_blocks L A _ _ Hin') as (q & Hq & Eq).
    pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q _ HMR Hq) as [H1 H2]. rewrite Eq in H1, H2. lia.
Qed.

Lemma b8_block_pos : forall g hb L A regs mem md a k, FR B APIf ra empty g hb L A regs mem md ->
  In (a, k) (blocks L A) -> 4096 <= a /\ a + k <= alloc_ceiling.
Proof.
  intros g hb L A regs mem md a k HF Hin. pose proof HF as (_ & _ & _ & _ & _ & _ & _ & _ & HMR & _).
  destruct (b8_in_blocks L A a k Hin) as (p & Hp & <-).
  exact (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p k HMR Hp).
Qed.

(* frame_RELRO's first block (FrameAPI.v, v1.9.0: (0x1ed20, 3680); `left; reflexivity` checks it). *)
Lemma b8_relro_norm : forall mem a, relro B mem -> MI B mem -> 0x1ed20 <= a < 0x1ed20 + 3680 ->
  mrd rsegs (normalize rsegs mem) (wa a) = seg_rom rsegs (wa a).
Proof.
  intros mem a HR HMI Ha. unfold MI in HMI. rewrite b8_segs in HMI.
  change (mrd rsegs (normalize rsegs mem) (wa a)) with (mbyte rsegs (normalize rsegs mem) a).
  rewrite <- (mbyte_rel rsegs mem (normalize rsegs mem) a (mem_rel_normalize rsegs mem HMI)).
  unfold relro, G_img_c in HR. rewrite b8_segs in HR. apply HR.
  exists 0x1ed20, 3680. split; [left; reflexivity | lia].
Qed.

Lemma b8_seg_rom_hi : forall a, alloc_ceiling <= a < 2 ^ 64 -> seg_rom rsegs (wa a) = None.
Proof.
  intros a Ha. pose proof alloc_ceiling_value. apply seg_rom_unmapped. apply b8_hi_noseg. unfold wa.
  rewrite unsigned_lit by lia. lia.
Qed.

Lemma b8_md : forall L A mem md, MR L A mem md -> m_halted md = None /\ m_vm_lazy md = [].
Proof. intros L A mem md H. exact (kb_md B API L A mem md H). Qed.

Lemma b8_cut_open : forall g pc hb P c (Q : config -> Prop),
  CUTST B APIf ra empty g pc hb P c ->
  (forall L A regs mem md, FR B APIf ra empty g hb L A regs mem md ->
     Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> P regs mem ->
     SR segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md) Q) ->
  SR segs c Q.
Proof.
  intros g pc hb P c Q (L & A & regs & mem & md & -> & H1 & H2 & H3) K. exact (K L A regs mem md H1 H2 H3).
Qed.

Lemma b8_cut_close : forall g pc hb (P : bvmap 5 word -> (word -> option byte) -> Prop) L A regs mem md,
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> P regs mem ->
  CUTST B APIf ra empty g pc hb P (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md).
Proof.
  intros g pc hb P L A regs mem md H1 H2 H3. exists L, A, regs, mem, md. split; [reflexivity|].
  split; [exact H1|]. split; [exact H2 | exact H3].
Qed.

Lemma b8_FR_regs : forall g hb L A regs regs' mem md,
  FR B APIf ra empty g hb L A regs mem md ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  FR B APIf ra empty g hb L A regs' mem md.
Proof.
  intros g hb L A regs regs' mem md (H0 & H2 & H3 & H4 & HR) E2 E3 E4.
  split; [exact H0|]. rewrite E2, E3, E4. split; [exact H2|]. split; [exact H3|]. split; [exact H4 | exact HR].
Qed.

Lemma b8_FR_MR : forall g hb L A regs mem md, FR B APIf ra empty g hb L A regs mem md -> MR L A mem md.
Proof. intros g hb L A regs mem md (_ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma b8_FR_sp : forall g hb L A regs mem md, FR B APIf ra empty g hb L A regs mem md ->
  getr regs 2 = Z_to_bv 64 (g_S g - 1936) /\ (g_S g - 1936) mod 16 = 0 /\
  alloc_ceiling + 65536 <= g_S g /\ g_S g <= 2 ^ 47.
Proof.
  intros g hb L A regs mem md (HGV & Hsp & _). pose proof HGV as (_ & _ & _ & HS16 & HSK & HS47 & _).
  unfold fsp, SLOT_FRAME, SLOT_K, SLOT_STACK in *. split; [exact Hsp|]. split; [Z.div_mod_to_equations; lia|].
  split; [exact HSK | exact HS47].
Qed.

Lemma b8_run_to : forall g hb L A regs mem md pc R' pc' mem' (Q : config -> Prop),
  FR B APIf ra empty g hb L A regs mem md ->
  Exec.evt rsegs (fun ms => ms = MS R' fp_regs pc' fp_csr None mem' (seg_rom rsegs))
    (MS (rmk regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall regs', (forall r, getr regs' r = getr R' r) -> SR segs (mkCfg (mkst regs' pc' mem' (seg_rom segs)) md) Q) ->
  SR segs (mkCfg (mkst regs pc mem (seg_rom segs)) md) Q.
Proof.
  intros g hb L A regs mem md pc R' pc' mem' Q HF HE HK.
  destruct (b8_md L A mem md (b8_FR_MR _ _ _ _ _ _ _ HF)) as [Hh Hl].
  apply (kb_run B regs pc mem md (fun R p m => R = R' /\ p = pc' /\ m = mem') Q Hh Hl).
  - rewrite b8_segs. eapply Exec.evt_mono; [exact HE|]. intros ms ->. exists R', pc', mem'.
    split; [reflexivity | repeat split].
  - intros R p m regs' (-> & -> & ->) HG. exact (HK regs' HG).
Qed.

Lemma b8_run_ex : forall g hb L A regs mem md pc (Rf : word -> bvmap 5 word) pc' mem' (Q : config -> Prop),
  FR B APIf ra empty g hb L A regs mem md ->
  Exec.evt rsegs (fun ms => exists y, ms = MS (Rf y) fp_regs pc' fp_csr None mem' (seg_rom rsegs))
    (MS (rmk regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall y regs', (forall r, getr regs' r = getr (Rf y) r) ->
     SR segs (mkCfg (mkst regs' pc' mem' (seg_rom segs)) md) Q) ->
  SR segs (mkCfg (mkst regs pc mem (seg_rom segs)) md) Q.
Proof.
  intros g hb L A regs mem md pc Rf pc' mem' Q HF HE HK.
  destruct (b8_md L A mem md (b8_FR_MR _ _ _ _ _ _ _ HF)) as [Hh Hl].
  apply (kb_run B regs pc mem md (fun R p m => (exists y, R = Rf y) /\ p = pc' /\ m = mem') Q Hh Hl).
  - rewrite b8_segs. eapply Exec.evt_mono; [exact HE|]. intros ms (y & ->). exists (Rf y), pc', mem'.
    split; [reflexivity | split; [exists y; reflexivity | split; reflexivity]].
  - intros R p m regs' ((y & ->) & -> & ->) HG. exact (HK y regs' HG).
Qed.

(* FR survives a run that changes only [S - K, S - 104) (no ro_agree premise: the window is above the image). *)
Lemma b8_FR_frame : forall g hb L A regs mem md mem',
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  munch [(g_S g - SLOT_K, g_S g - 104)] mem mem' ->
  wmono rsegs mem mem' ->
  FR B APIf ra empty g hb L A regs mem' md.
Proof.
  intros g hb L A regs mem md mem' HF HP HM HW.
  pose proof b8_segs as ES.
  destruct HF as (HGV & Hsp & Hgp & Htp & Hsav & Hstk & HMI & Hrel & HMR & HWF & Hbd & Hin & Hmd & Hhi & Himg &
                  Hblk & Herr & Hsink & HRES & Hwr).
  pose proof HGV as (Hn & Hp & Hbd0 & HS16 & HSK & HS47 & Hroom & HgS & Htp0).
  pose proof alloc_ceiling_value as Hc. pose proof b8_errno_ceil as Herrc. pose proof b8_errno as HEV.
  unfold FR. unfold SLOT_K, SLOT_STACK in *.
  assert (Hout : forall a, 0 <= a < 2 ^ 64 -> a < g_S g - 65536 \/ g_S g - 104 <= a ->
                 mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hx. apply HM. rewrite MState.unsigned_lit by exact Ha. apply b8_outside1. lia. }
  assert (Hlow : forall a, 0 <= a < alloc_ceiling -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a))
    by (intros a Ha; apply Hout; lia).
  split; [exact HGV|]. split; [exact Hsp|]. split; [exact Hgp|]. split; [exact Htp|].
  split.
  { apply (sl_bytes_keep mem); [exact Hsav|]. intros i Hi.
    assert (Hl : length (saved_bytes ra g) = 104%nat)
      by (unfold saved_bytes; rewrite !length_app, !length_le8; reflexivity).
    rewrite Hl in Hi. apply Hout; lia. }
  split.
  { destruct Hstk as (S1 & S2 & SH0). split; [exact S1|]. split; [exact S2|]. intros a Ha.
    destruct (SH0 a Ha) as (Hw & _).
    assert (Hu : bv_unsigned (wa a) = a) by (unfold wa; apply MState.unsigned_lit; lia).
    pose proof (HW (wa a) Hw) as Hw'. split; [exact Hw'|].
    assert (Hns : find_segment rsegs (bv_unsigned (wa a)) 1 = None) by (apply b8_hi_noseg; lia).
    unfold wview in Hw'. rewrite Hns in Hw'. unfold mrd.
    destruct (mem' (wa a)) as [b|]; [exists b; reflexivity | exfalso; apply Hw'; reflexivity]. }
  split.
  { unfold MI in *. intros a Ha. rewrite <- (HMI a Ha). unfold mrd.
    pose proof Ha as Ha'. rewrite ES in Ha'.
    pose proof (b8_ro_low a Ha') as X. pose proof (bv_unsigned_in_range 64 a) as R.
    change (bv_modulus 64) with (2 ^ 64) in R.
    rewrite (HM a); [reflexivity|]. apply b8_outside1. lia. }
  split.
  { unfold relro, G_img_c in *. intros a Ha. rewrite <- (Hrel a Ha).
    destruct (b8_relro_img a Ha) as (Hi & _). pose proof (b8_img_lt a Hi). apply b8_mbyte_eq. apply Hlow. lia. }
  assert (Hcond : forall x, 0 <= x < alloc_ceiling ->
      (owned B L A x \/ exists p n, In (p, n) (blocks L A) /\ p <= x < p + n) ->
      outside [(g_S g - 65536, g_S g - 104)] x) by (intros x Hx _; apply b8_outside1; lia).
  split; [exact (kb_MR_A B (APIf rc) L A mem mem' md _ HMR HM Hcond)|].
  split; [exact HWF|]. split; [exact Hbd|]. split; [exact Hin|]. split; [exact Hmd|].
  split.
  { intros a Ha Hs He. destruct (Hhi a Ha Hs He) as [E1 E2].
    assert (Hx : mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) by (apply Hout; lia).
    rewrite (b8_mbyte_eq _ mem mem' a Hx). split; [exact E1|].
    rewrite E2. apply b8_wr_eq. exact Hx. }
  split.
  { intros a Ha H1 H2 H3. destruct (Himg a Ha H1 H2 H3) as [E1 E2]. pose proof (b8_img_lt a Ha).
    assert (Hx : mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) by (apply Hlow; lia).
    rewrite (b8_mbyte_eq _ mem mem' a Hx). split; [exact E1|].
    rewrite E2. apply b8_wr_eq. exact Hx. }
  split.
  { intros a k i Hak Hi. rewrite <- (Hblk a k i Hak Hi).
    apply (kb_blocks_munch B (APIf rc) L A mem mem' md _ HMR HM Hcond a k i); [|exact Hi].
    apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. exact Hak. }
  split.
  { intros a Ha. apply (b8_wr_eq _ mem mem' a); [apply Hlow; lia | exact (Herr a Ha)]. }
  split.
  { apply (sl_sink_keep B APIf ra empty FF mem mem' md); [|exact Hsink].
    intros a Ha. pose proof sl_ceil. apply Hlow. lia. }
  split; [exact HRES|].
  intros a Ha. pose proof (Hwr a Ha) as X. unfold writable_at in *. rewrite ES in X |- *. apply HW. exact X.
Qed.

(* A run through straight code and Kind A callees on the normalized memory, writing only inside W. *)
Lemma b8_mid : forall g hb L A regs mem md pc W (Q : machine_state -> Prop) (P : config -> Prop),
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> g_S g - SLOT_K <= x < g_S g - 104) ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R pc' m', ms = MState.MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
     munch W (normalize rsegs mem) m' /\ wmono rsegs (normalize rsegs mem) m' /\
     getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4) ->
  (forall R pc' m0' regs' m', Q (MState.MS R fp_regs pc' fp_csr None m0' (seg_rom rsegs)) ->
     Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m' m0' -> munch W mem m' ->
     FR B APIf ra empty g hb L A regs' m' md ->
     SR segs (mkCfg (mkst regs' pc' m' (seg_rom segs)) md) P) ->
  SR segs (mkCfg (mkst regs pc mem (seg_rom segs)) md) P.
Proof.
  intros g hb L A regs mem md pc W Q P HFR HP HW HE Hform HK.
  pose proof b8_segs as SEGS.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & HMI & _ & HM & _).
  unfold MI in HMI. rewrite SEGS in HMI.
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  apply (sl_run regs pc mem md Q P Hh Hl HMI HE).
  - intros ms HQ. destruct (Hform ms HQ) as (R & pc' & m' & -> & _). exists R, pc', m'. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel Hsame.
    destruct (Hform _ HQ) as (R1 & pc1 & m1 & E & MU & WM & E2 & E3 & E4).
    injection E; intros; subst.
    pose proof (mem_rel_normalize rsegs mem HMI) as HR0.
    assert (MU' : munch W mem m') by exact (munch_rel rsegs W mem (normalize rsegs mem) m' m1 HR0 Hrel Hsame MU).
    rewrite <- SEGS. apply (HK R1 pc1 m1 regs' m' HQ Hx Hrel MU').
    apply (sl_fr_run B APIf ra empty FF g hb L A regs mem md regs' m' W HFR HP MU').
    + exact (wmono_rel rsegs mem (normalize rsegs mem) m' m1 HR0 Hrel Hsame WM).
    + exact (ro_agree_same rsegs mem m' HMI Hsame).
    + exact HW.
    + rewrite (sl_getr_eqv _ _ _ Hx). exact E2.
    + rewrite (sl_getr_eqv _ _ _ Hx). exact E3.
    + rewrite (sl_getr_eqv _ _ _ Hx). exact E4.
Qed.

Lemma b8_GV_S : forall g, GV B empty g -> spZ (g_regs g) = g_S g /\ alloc_ceiling + SLOT_K <= g_S g <= 2 ^ 47.
Proof.
  intros g (_ & _ & _ & _ & H1 & H2 & _ & H3 & _). unfold spZ. rewrite H3.
  pose proof alloc_ceiling_value. unfold SLOT_K, SLOT_STACK in *. rewrite b8_unsigned by lia. lia.
Qed.

Lemma b8_post_FR : forall g L A regs0 regs mem md,
  FR B APIf ra empty g [] L A regs0 mem md ->
  Permutation (blocks L A) ([] ++ blocks (g_L g) (g_A g)) ->
  getr regs 10 = Z_to_bv 64 0 -> regs_preserved (g_regs g) regs ->
  Post B APIf ra g (mkCfg (mkst regs (Z_to_bv 64 ra) mem (seg_rom segs)) md).
Proof.
  intros g L A regs0 regs mem md HF HP H10 HRP.
  pose proof HF as (HGV & _ & _ & _ & _ & _ & HMI & _ & HMR & HWF & HBD & HIN & HVM & HFA & HFI & HFB & HER & HSN & HRES
    & HSW).
  destruct (b8_GV_S g HGV) as [HSP HS].
  exists L, A, regs, mem, md. split; [reflexivity|].
  split.
  - unfold lib_post. split; [exact HMR|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact HIN|].
    split; [exact H10|]. split; [exact HRP|]. split; [exact HVM|].
    split.
    { intros q k Hq. pose proof (b8_blocks_in (g_L g) (g_A g) q k Hq) as Hb.
      apply (Permutation_in _ (Permutation_sym HP)) in Hb.
      destruct (b8_in_blocks L A _ _ Hb) as (q' & Hq' & E). exists q'. split; [exact Hq' | exact E]. }
    split.
    { intros a Ha Hn. unfold lib_scratch in Hn. rewrite HSP in Hn.
      assert (N1 : ~ (g_S g - SLOT_K <= a < g_S g)) by (unfold SLOT_K; tauto).
      assert (N2 : ~ (errno_addr B <= a < errno_addr B + 4)) by tauto.
      destruct (HFA a Ha N1 N2) as [E1 E2]. split; [exact E1 | tauto]. }
    split.
    { intros a H1 H2 H3 H4. destruct (HFI a H1 H2 H3 H4) as [E1 E2]. split; [exact E1 | tauto]. }
    split.
    { intros q k i Hq _ Hi. apply (HFB (ptr_addr (g_L g) q) k i); [apply b8_blocks_in; exact Hq | exact Hi]. }
    intros a [Ha|Ha]; [apply HSW; rewrite HSP in Ha; unfold SLOT_K; exact Ha | apply HER; exact Ha].
  - split; [exact HSN|]. split; [exact HMI|].
    split.
    + exact (resb_end (g_b g) A HRES).
    + intros i Hi. destruct HGV as (_ & [[Hn _]|[_ Hp]] & _); [lia|].
      apply (HFB (g_p g) (g_n g) i Hp Hi).
Qed.

Lemma b8_call_pre : forall g hb L A regs mem md regs_c,
  FR B APIf ra empty g hb L A regs mem md -> getr regs_c 2 = getr regs 2 -> getr regs_c 4 = getr regs 4 ->
  YK0s.ret_ok (getr regs_c 1) -> call_pre B MR L A regs_c mem md.
Proof.
  intros g hb L A regs mem md regs_c HF E2 E4 Hra.
  pose proof HF as (HGV & Hsp & _ & Htp & _ & _ & _ & _ & HMR & HWF & HBD & HIN & _ & _ & _ & _ & HER & _ & _ & HSW).
  pose proof HGV as (_ & _ & _ & HS16 & HSK & HS47 & _ & _ & HTP0).
  pose proof alloc_ceiling_value as HAC. unfold SLOT_K, SLOT_STACK in *.
  assert (HSP : spZ regs_c = g_S g - 1936).
  { unfold spZ. rewrite E2, Hsp. unfold fsp, SLOT_FRAME. apply b8_unsigned. lia. }
  unfold call_pre. rewrite HSP. unfold ALLOC_STACK.
  split; [exact HMR|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact Hra|].
  split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|].
  split; [intros a Ha; apply HSW; lia|].
  split; [rewrite E4, Htp; exact HTP0|].
  split; [exact HER|].
  intros H. rewrite HIN in H. discriminate.
Qed.

Lemma b8_in_img_b : forall a, existsb (fun s : word * word => (bv_unsigned (fst s) <=? a) &&
    (a <? bv_unsigned (fst s) + bv_unsigned (snd s))) (segments_reserved rsegs) = true -> in_img B a.
Proof.
  intros a H. unfold in_img. rewrite b8_segs. split; [discriminate|].
  apply existsb_exists in H as (s & Hs & E). apply andb_prop in E as [E1 E2].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2. exists s. split; [exact Hs | lia].
Qed.

(* The allocator / sink symbols of frame_facts (SlotInv.v = FrameAPI.v's frame_plain, v1.9.0), by its fields. *)
Lemma b8_syms : ms_ctx B = 0x51208 /\ ms_lock B = 0x51200 /\ ms_libc B = 0x51190 /\ ms_guard B = 0x51170 /\
  ms_got_guard B = 0x1fb80 /\ ms_size_classes B = 0x10788 /\ ms_small_cnt B = 0x107e8 /\ ms_med_cnt B = 0x10728 /\
  ms_debruijn B = 0x10704 /\ ms_vmlock B = None /\
  @sk_ofl_head SH = 0x515c0 /\ @sk_ofl_lock SK = 0x515b8 /\ @sk_threaded SK = 0x51191.
Proof.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & _ & _ & _ &
    H20 & H21 & H22 & H23 & _). repeat split; assumption.
Qed.

Lemma b8_sink_addr : forall a, (0x51191 <= a < 0x51192 \/ 0x515b8 <= a < 0x515bc \/ 0x515c0 <= a < 0x515c8) ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Proof.
  intros a Ha. pose proof b8_syms as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _).
  rewrite b8_errno. unfold static_owned, vml_lo, vml_len. rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10.
  assert (DBL : ms_debruijn_len B = 132) by (pose proof FF as FF'; unfold frame_facts in FF'; tauto).
  rewrite DBL. unfold CTX_SIZE. split; [|lia]. apply b8_in_img_b.
  destruct Ha as [Ha|[Ha|Ha]];
    [ assert (a = 0x51191) by lia; subst a
    | assert (a = 0x515b8 \/ a = 0x515b9 \/ a = 0x515ba \/ a = 0x515bb) as [->|[->|[->| ->]]] by lia
    | assert (a = 0x515c0 \/ a = 0x515c1 \/ a = 0x515c2 \/ a = 0x515c3 \/ a = 0x515c4 \/ a = 0x515c5 \/ a = 0x515c6 \/
        a = 0x515c7) as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]] by lia ];
    vm_compute; reflexivity.
Qed.

Lemma b8_sink_frame : forall mem mem' md md',
  (forall a, (0x51191 <= a < 0x51192 \/ 0x515b8 <= a < 0x515bc \/ 0x515c0 <= a < 0x515c8) ->
     mbyte segs mem' a = mbyte segs mem a) ->
  m_fds md' = m_fds md -> sink_none B mem md -> sink_none B mem' md'.
Proof.
  intros mem mem' md md' HK Hfd ((V1 & V2) & V3 & V4).
  pose proof b8_syms as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & S3).
  split; [split|split].
  - intros k Hk. rewrite <- (V1 k Hk). apply HK. rewrite S3. lia.
  - intros k Hk. rewrite <- (V2 k Hk). apply HK. rewrite S2. lia.
  - intros k Hk. rewrite <- (V3 k Hk). apply HK. rewrite S1. lia.
  - rewrite Hfd. exact V4.
Qed.

(* free of the one live harness block (p, n), n >= 0: FR with hb = [(p, n)] becomes FR with hb = []. *)
Lemma b8_FR_free : forall g L A regs mem md regs_c p n L' A' regs' mem' md' b1 b2,
  FR B APIf ra empty g [(ptr_addr L p, n)] L A regs mem md ->
  Permutation (blocks L A) ([(ptr_addr L p, n)] ++ blocks (g_L g) (g_A g)) ->
  In (p, n) (user_blocks A) ->
  getr regs_c 2 = getr regs 2 -> getr regs_c 3 = getr regs 3 -> getr regs_c 4 = getr regs 4 ->
  call_post B MR L A regs_c mem md (fun a => ptr_addr L p <= a < ptr_addr L p + n) L' A' regs' mem' md' ->
  blocks L A = b1 ++ (ptr_addr L p, n) :: b2 -> blocks L' A' = b1 ++ b2 ->
  blocks_kept B L A mem mem' (fun a => a = ptr_addr L p) ->
  ro_agree segs mem' ->
  (st_init_done A = true -> st_init_done A' = true) ->
  res_ok_slots A' (sb_free (sb_hb (g_b g) [(ptr_addr L p, n)]) n) ->
  FR B APIf ra empty g [] L' A' regs' mem' md' /\
  Permutation (blocks L' A') ([] ++ blocks (g_L g) (g_A g)) /\
  (forall a, g_S g - 1936 <= a < 2 ^ 64 -> mbyte segs mem' a = mbyte segs mem a).
Proof.
  intros g L A regs mem md regs_c p n L' A' regs' mem' md' b1 b2 HF HP Hpn E2 E3 E4
    POST EB EB' KEPT RO' INIT RES'.
  pose proof b8_segs as ES.
  destruct HF as (HGV & Hsp & Hgp & Htp & Hsav & Hstk & HMI & Hrel & HMR & HWF & Hbd & Hin & Hmd & Hhi & Himg &
                  Hblk & Herr & Hsink & HRES & Hwr).
  pose proof HGV as (Hn0 & Hp0 & Hbd0 & HS16 & HSK & HS47 & Hroom & HgS & Htp0).
  destruct POST as (MR' & WF' & BD' & LL' & PA' & RP' & (vm' & Emd) & MEM & UB & SCW).
  pose proof alloc_ceiling_value as HAC. pose proof b8_errno_ceil as HEC. pose proof b8_errno as HEV.
  unfold SLOT_K, SLOT_STACK in *.
  assert (HSP : spZ regs_c = g_S g - 1936).
  { unfold spZ. rewrite E2, Hsp. unfold fsp, SLOT_FRAME. apply b8_unsigned. lia. }
  pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p n HMR Hpn) as [Hp1 Hp2].
  assert (HEimg : forall a, ptr_addr L p <= a < ptr_addr L p + n -> ~ in_img B a).
  { intros a Ha. replace a with (ptr_addr L p + (a - ptr_addr L p)) by lia.
    apply (ax_blocks_img b8_ax L A mem md p n); [exact HMR | exact Hpn | lia]. }
  assert (HOW : forall L0 A0 m0 md0 a, aa_MR API L0 A0 m0 md0 -> owned B L0 A0 a -> a < alloc_ceiling).
  { intros L0 A0 m0 md0 a H Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ H Ho). lia. }
  assert (HI : forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
      ~ (errno_addr B <= a < errno_addr B + 4) ->
      mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)).
  { intros a Ha H1 H2 H3. pose proof (b8_img_lt a Ha) as Hl. apply MEM.
    - right. exact Ha.
    - intros [Ho|Ho]; [exact (H2 (ax_img b8_ax L A mem md a HMR Ha Ho)) | exact (H1 Ho)].
    - intros [Ho|Ho]; [exact (H2 (ax_img b8_ax L' A' mem' md' a MR' Ha Ho)) | exact (H1 Ho)].
    - unfold scratch. rewrite HSP. unfold ALLOC_STACK. lia.
    - intros He. exact (HEimg a He Ha). }
  assert (HH : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (g_S g - 1936 - 8192 <= a < g_S g - 1936) ->
      mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)).
  { intros a Ha Hs. apply MEM.
    - left. exact Ha.
    - intros Ho. pose proof (HOW _ _ _ _ a HMR Ho). lia.
    - intros Ho. pose proof (HOW _ _ _ _ a MR' Ho). lia.
    - unfold scratch. rewrite HSP. unfold ALLOC_STACK. lia.
    - lia. }
  assert (HWR : forall a, g_S g - 65536 <= a < g_S g -> writable_at segs mem' a).
  { intros a Ha. destruct (Z_lt_le_dec a (g_S g - 1936 - 8192)) as [Hl|Hl];
      [|destruct (Z_lt_le_dec a (g_S g - 1936)) as [Hl2|Hl2]].
    - apply (proj2 (HH a ltac:(lia) ltac:(lia))). apply Hwr. lia.
    - apply SCW. unfold scratch. rewrite HSP. unfold ALLOC_STACK. lia.
    - apply (proj2 (HH a ltac:(lia) ltac:(lia))). apply Hwr. lia. }
  assert (HND : List.NoDup (map fst ((ptr_addr L p, n) :: blocks (g_L g) (g_A g)))).
  { apply (Permutation_NoDup (Permutation_map fst HP)). apply NoDup_ListNoDup. exact (b8_nodup L A mem md HMR). }
  cbn [map fst] in HND. apply List.NoDup_cons_iff in HND as [HNI _].
  split; [|split].
  2:{ rewrite EB'. cbn [app]. apply (Permutation_app_inv b1 b2 [] (blocks (g_L g) (g_A g)) (ptr_addr L p, n)).
      rewrite <- EB. exact HP. }
  2:{ intros a Ha. exact (proj1 (HH a ltac:(lia) ltac:(lia))). }
  unfold FR, RESB, SLOT_K, SLOT_STACK.
  split; [exact HGV|].
  split; [etransitivity; [exact (RP' 2 ltac:(unfold callee_saved; lia))|]; etransitivity; [exact E2|]; exact Hsp|].
  split; [etransitivity; [exact (RP' 3 ltac:(unfold callee_saved; lia))|]; etransitivity; [exact E3|]; exact Hgp|].
  split; [etransitivity; [exact (RP' 4 ltac:(unfold callee_saved; lia))|]; etransitivity; [exact E4|]; exact Htp|].
  split.
  { apply (b8_ba_mbyte mem); [exact Hsav|]. intros i Hi.
    assert (Hl : length (saved_bytes ra g) = 104%nat)
      by (unfold saved_bytes; rewrite !length_app, !length_le8; reflexivity).
    rewrite Hl in Hi. rewrite <- ES. exact (proj1 (HH (g_S g - 104 + i) ltac:(lia) ltac:(lia))). }
  split; [apply sl_stk_of_writable; [unfold SL_TOP; pose proof sl_ceil; unfold SL_TOP in *; lia | lia |
            intros a Ha; rewrite <- ES; apply HWR; exact Ha]|].
  split; [exact RO'|].
  split.
  { unfold relro, G_img_c in *. intros a Ha. rewrite <- (Hrel a Ha).
    destruct (b8_relro_img a Ha) as (H1 & H2 & H3 & H4). exact (proj1 (HI a H1 H2 H3 H4)). }
  split; [exact MR'|]. split; [exact WF'|]. split; [exact BD'|]. split; [exact (INIT Hin)|].
  split; [destruct Hmd as (vm & ->); exists vm'; rewrite Emd; reflexivity|].
  split.
  { intros a Ha Hs He. destruct (Hhi a Ha Hs He) as [F1 F2]. destruct (HH a Ha ltac:(lia)) as [G1 G2].
    rewrite G1. split; [exact F1|]. tauto. }
  split.
  { intros a Ha H1 H2 H3. destruct (Himg a Ha H1 H2 H3) as [F1 F2]. destruct (HI a Ha H1 H2 H3) as [G1 G2].
    rewrite G1. split; [exact F1|]. tauto. }
  split.
  { intros a k i Hak Hi. rewrite <- (Hblk a k i Hak Hi). unfold blocks_kept in KEPT. apply (KEPT a k i); [| |exact Hi].
    - apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. exact Hak.
    - intros Ea. subst a. apply HNI. apply in_map_iff. exists (ptr_addr L p, k). split; [reflexivity | exact Hak]. }
  split; [intros a Ha; apply SCW; unfold scratch; right; exact Ha|].
  split.
  { apply (b8_sink_frame mem mem' md md'); [|rewrite Emd; reflexivity | exact Hsink].
    intros a Ha. destruct (b8_sink_addr a Ha) as (H1 & H2 & H3 & H4). exact (proj1 (HI a H1 H2 H3 H4)). }
  split; [exact (resb_free (g_b g) [(ptr_addr L p, n)] [] A' (ptr_addr L p) n (Permutation_refl _) RES')|].
  intros a Ha. apply HWR. exact Ha.
Qed.

Lemma b8_free_call : free_contract B API -> forall g L A regs mem md regs_c p n (Q : config -> Prop),
  FR B APIf ra empty g [(ptr_addr L p, n)] L A regs mem md ->
  Permutation (blocks L A) ([(ptr_addr L p, n)] ++ blocks (g_L g) (g_A g)) ->
  In (p, n) (user_blocks A) ->
  getr regs_c 2 = getr regs 2 -> getr regs_c 3 = getr regs 3 -> getr regs_c 4 = getr regs 4 ->
  YK0s.ret_ok (getr regs_c 1) -> getr regs_c 10 = Z_to_bv 64 (ptr_addr L p) ->
  (forall L' A' regs' mem' md', FR B APIf ra empty g [] L' A' regs' mem' md' ->
     Permutation (blocks L' A') ([] ++ blocks (g_L g) (g_A g)) -> regs_preserved regs_c regs' ->
     (forall a, g_S g - 1936 <= a < 2 ^ 64 -> mbyte segs mem' a = mbyte segs mem a) ->
     SR segs (mkCfg (mkst regs' (getr regs_c 1) mem' (seg_rom segs)) md') Q) ->
  SR segs (mkCfg (mkst regs_c (Z_to_bv 64 0x1635c) mem (seg_rom segs)) md) Q.
Proof.
  intros FREE g L A regs mem md regs_c p n Q HF HP Hpn E2 E3 E4 Hra H10 K.
  pose proof (b8_call_pre g _ L A regs mem md regs_c HF E2 E4 Hra) as CP.
  pose proof HF as (_ & _ & _ & _ & _ & _ & HMI & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hb & _).
  rewrite <- b8_free_addr.
  eapply SR_bind; [exact (FREE L A regs_c mem md p n (sb_hb (g_b g) [(ptr_addr L p, n)]) CP HMI Hpn H10 Hb)|].
  intros c' (L' & A' & regs' & mem' & md' & -> & POST & (b1 & b2 & EB & EB') & KEPT & RO' & _ & _ & INIT & _ & RES').
  pose proof POST as (_ & _ & _ & _ & _ & RP' & _).
  destruct (b8_FR_free g L A regs mem md regs_c p n L' A' regs' mem' md' b1 b2 HF HP Hpn E2 E3 E4
    POST EB EB' KEPT RO' INIT RES') as (HF' & HP' & HKEEP).
  exact (K L' A' regs' mem' md' HF' HP' RP' HKEEP).
Qed.

End TacB8.
