From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac
  Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Cells.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0 Contract FrameAPI OutForm SlotAgree AgreeLift.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog.Slot Require Import PInv USROcf PInvCF.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YM0b.
Import ListNotations.
Open Scope Z_scope.

Lemma ss_canon_mkst : forall {fx : YK11.FPState} (regs : bvmap 5 word) (pc : word) (mem ro : word -> option byte),
  canonical_register_state (YK11.mkst regs pc mem ro) = MS (mkR_of regs) fp_regs pc fp_csr None mem ro.
Proof. reflexivity. Qed.

Lemma ss_eqv_mkst : forall {fx : YK11.FPState} (R : bvmap 5 word) (pc : word) (m ro : word -> option byte) ms',
  ms_eqv (MS R fp_regs pc fp_csr None m ro) ms' -> exists R', ms' = YK11.mkst R' pc m ro /\ xregs_eqv R R'.
Proof.
  intros fx R pc m ro [R' F' pc' svc' rv' fc' m' ro'] (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro).
  cbn in HF, Hpc, Hsvc, Hrv, Hfc, Hm, Hro. subst. exists R'. split; [reflexivity | exact HR].
Qed.

Lemma ss_getr_x : forall (R R' : bvmap 5 word) (r : bv 5),
  xregs_eqv R R' -> is_x0 r = false -> YK11.getr R' r = reg_get R r.
Proof.
  intros R R' r H H0. unfold YK11.getr.
  match goal with |- (if ?b then _ else _) = _ => replace b with false by (symmetry; exact H0) end.
  symmetry. apply H. exact H0.
Qed.

Lemma ss_getr_reg : forall (regs : bvmap 5 word) (r : bv 5), is_x0 r = false -> YK11.getr regs r = reg_get regs r.
Proof.
  intros regs r H0. unfold YK11.getr.
  match goal with |- (if ?b then _ else _) = _ => replace b with false by (symmetry; exact H0) end.
  reflexivity.
Qed.

Lemma ss_ret_pc_lit : forall z, 0 <= z < 2 ^ 64 -> z mod 2 = 0 -> ret_pc (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz He. apply ret_pc_even; assumption. Qed.

Lemma ss_with_vm : forall a b m, with_vmmaps a (with_vmmaps b m) = with_vmmaps a m.
Proof. intros a b m. reflexivity. Qed.

Lemma ss_bytes_same : forall segs (m m' : word -> option byte) a bs,
  (forall i, 0 <= i < Z.of_nat (length bs) -> m' (Z_to_bv 64 (a + i)) = m (Z_to_bv 64 (a + i))) ->
  bytes_at segs m a bs -> bytes_at segs m' a bs.
Proof.
  intros segs m m' a bs H (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
  intros i Hi. unfold mrd, wa. rewrite H by lia. apply H3. exact Hi.
Qed.

Lemma ss_bytes_mbyte : forall segs (m m' : word -> option byte) a bs,
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte segs m' (a + i) = mbyte segs m (a + i)) ->
  bytes_at segs m a bs -> bytes_at segs m' a bs.
Proof.
  intros segs m m' a bs H (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
  intros i Hi. specialize (H (Z.of_nat i) ltac:(lia)).
  change (mbyte segs m' (a + Z.of_nat i) = nth_error bs i). rewrite H.
  change (mrd segs m (wa (a + Z.of_nat i)) = nth_error bs i). apply H3. exact Hi.
Qed.

Lemma ss_fs_in : forall (l : list Segment) x n s, find_segment l x n = Some s ->
  In s l /\ Z.of_N (seg_base s) <= x /\ x + n <= Z.of_N (seg_base s) + Z.of_N (seg_size s).
Proof.
  induction l as [|s0 l IH]; intros x n s E; cbn [find_segment] in E; [discriminate|].
  cbv zeta in E. revert E. match goal with |- (if ?k then _ else _) = _ -> _ => destruct k eqn:C end; intros E.
  - injection E as <-. apply andb_prop in C as [C1 C2]. apply Z.leb_le in C1, C2. split; [left; reflexivity | lia].
  - destruct (IH x n s E) as (H1 & H2 & H3). split; [right; exact H1 | lia].
Qed.

Definition IMG_LO : Z := 0x10000.
Definition IMG_HI : Z := (symaddr ImgPages.Ubsan.top).

Lemma ss_fs_bound : forall x s, find_segment rsegs x 1 = Some s -> IMG_LO <= x < IMG_HI.
Proof.
  intros x s E. destruct (ss_fs_in rsegs x 1 s E) as (Hin & H1 & H2).
  assert (H : forallb (fun s => (IMG_LO <=? Z.of_N (seg_base s)) && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? IMG_HI))
            rsegs = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H s Hin). apply andb_prop in H as [H3 H4].
  apply Z.leb_le in H3, H4. lia.
Qed.

Lemma ss_fs_none : forall x, (x < IMG_LO \/ IMG_HI <= x) -> find_segment rsegs x 1 = None.
Proof.
  intros x Hx. destruct (find_segment rsegs x 1) as [s|] eqn:E; [|reflexivity].
  exfalso. pose proof (ss_fs_bound x s E). lia.
Qed.

Lemma ss_wview_none : forall (m : word -> option byte) (w : word),
  find_segment rsegs (bv_unsigned w) 1 = None -> wview rsegs m w <> None -> exists b, m w = Some b.
Proof.
  intros m w Hf Hw. unfold wview in Hw. destruct (m w) as [b|]; [exists b; reflexivity|].
  rewrite Hf in Hw. exfalso. apply Hw. reflexivity.
Qed.

Lemma ss_ro_lt : forall w : word, Mem.ro_addr rsegs w = true -> IMG_LO <= bv_unsigned w < IMG_HI.
Proof.
  intros w H. unfold Mem.ro_addr in H. destruct (find_segment rsegs (bv_unsigned w) 1) as [s|] eqn:E; [|discriminate].
  exact (ss_fs_bound _ s E).
Qed.

Lemma ss_ret_pc_ra : forall z, z mod 2 = 0 -> ret_pc (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. assert (E : Z_to_bv 64 z = Z_to_bv 64 (z mod 2 ^ 64)).
  { apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    rewrite Zmod_mod. reflexivity. }
  rewrite E. apply ret_pc_even; [apply Z.mod_pos_bound; lia | rewrite KindBGlue.kb_mod2_land; exact Hz].
Qed.

Lemma ss_blocks_in : forall L A p n, In (p, n) (user_blocks A) -> In (ptr_addr L p, n) (blocks L A).
Proof. intros L A p n H. unfold blocks. apply in_map_iff. exists (p, n). split; [reflexivity | exact H]. Qed.

Definition SS_TOP : Z := (symaddr ImgPages.Ubsan.top).

Lemma ss_find_segment_in : forall segs a n seg, find_segment segs a n = Some seg ->
  In seg segs /\ Z.of_N (seg_base seg) <= a /\ a + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  induction segs as [|s segs IH]; intros a n seg E; cbn in E; [discriminate|].
  match type of E with context [if ?c then _ else _] => destruct c eqn:C end.
  - injection E as <-. apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2.
    split; [left; reflexivity | lia].
  - destruct (IH a n seg E) as (H1 & H2 & H3). split; [right; exact H1 | lia].
Qed.

Lemma ss_rsegs_ok : forallb (fun s => let r := segment_reservation s in
    (bv_unsigned (fst r) <=? Z.of_N (seg_base s)) &&
    (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? bv_unsigned (fst r) + bv_unsigned (snd r)) &&
    (bv_unsigned (fst r) + bv_unsigned (snd r) <=? SS_TOP)) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ss_rsegs_seg : forall seg, In seg rsegs ->
  bv_unsigned (fst (segment_reservation seg)) <= Z.of_N (seg_base seg) /\
  Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=
    bv_unsigned (fst (segment_reservation seg)) + bv_unsigned (snd (segment_reservation seg)) /\
  bv_unsigned (fst (segment_reservation seg)) + bv_unsigned (snd (segment_reservation seg)) <= SS_TOP.
Proof.
  intros seg Hin. pose proof (proj1 (forallb_forall _ _) ss_rsegs_ok seg Hin) as H. cbv beta zeta in H.
  apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. auto.
Qed.

Lemma ss_find_top : forall a n seg, find_segment rsegs a n = Some seg -> a + n <= SS_TOP.
Proof.
  intros a n seg E. destruct (ss_find_segment_in rsegs a n seg E) as (Hin & H1 & H2).
  destruct (ss_rsegs_seg seg Hin) as (R1 & R2 & R3). lia.
Qed.

Lemma ss_in_img_top : forall B a, ms_segs B = rsegs -> in_img B a -> 0 <= a < SS_TOP.
Proof.
  intros B a HS [_ (s & Hin & Hr)]. rewrite HS in Hin. unfold segments_reserved in Hin.
  apply in_map_iff in Hin as (seg & <- & Hseg).
  destruct (ss_rsegs_seg seg Hseg) as (R1 & R2 & R3).
  pose proof (bv_unsigned_in_range _ (fst (segment_reservation seg))) as R. lia.
Qed.

Lemma ss_wview_hi : forall m a, SS_TOP <= a < 2 ^ 64 -> wview rsegs m (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros m a Ha. unfold wview. destruct (m (Z_to_bv 64 a)) as [b|]; [reflexivity|].
  rewrite (MState.unsigned_lit a ltac:(unfold SS_TOP in Ha; lia)).
  destruct (find_segment rsegs a 1) as [seg|] eqn:E; [|reflexivity].
  exfalso. pose proof (ss_find_top a 1 seg E). unfold SS_TOP in *. lia.
Qed.

Lemma ss_outside_dec : forall W x, {Frame.outside W x} + {~ Frame.outside W x}.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [Frame.outside]; [left; exact I|].
  destruct (Z_le_dec lo x) as [H1|H1]; [destruct (Z_lt_dec x hi) as [H2|H2]|].
  - right. intros [H _]. lia.
  - destruct (IH x) as [O|O]; [left; split; [lia | exact O] | right; intros [_ H]; exact (O H)].
  - destruct (IH x) as [O|O]; [left; split; [lia | exact O] | right; intros [_ H]; exact (O H)].
Qed.

Lemma ss_unch : forall W m m' lo hi, Frame.munch W m m' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x -> lo <= x < hi) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros W m m' lo hi MU HW a Ha Hn. apply MU. rewrite (MState.unsigned_lit a Ha).
  destruct (ss_outside_dec W a) as [O|O]; [exact O|]. exfalso. apply Hn. exact (HW a Ha O).
Qed.

Lemma ss_eq_at : forall (m m' : word -> option byte) a, m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) ->
  mbyte rsegs m' a = mbyte rsegs m a /\ (writable_at rsegs m a <-> writable_at rsegs m' a).
Proof.
  intros m m' a E. unfold mbyte, writable_at, wview. rewrite E. split; [reflexivity | tauto].
Qed.

Lemma ss_mkFP : forall f : FPState, mkFP (@fp_regs f) (@fp_csr f) = f.
Proof. intros []. reflexivity. Qed.

Lemma ss_eqv_mkfp : forall R F pc fc m ro ms',
  Regs6ss.ms_eqv (MState.MS R F pc fc None m ro) ms' ->
  ms' = @mkst (mkFP F fc) (ms_regs ms') pc m ro /\ Regs6ss.xregs_eqv R (ms_regs ms').
Proof.
  intros R F pc fc m ro ms' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  destruct ms' as [r f p s v c mm rr]; cbn in *. subst. split; [reflexivity | exact H1].
Qed.

Lemma ss_getr_eqv : forall R R' r, Regs6ss.xregs_eqv R R' -> getr R' r = getr R r.
Proof.
  intros R R' r H. unfold getr. destruct (bv_eqb r 0) eqn:E; [reflexivity|].
  symmetry. apply H. exact E.
Qed.

Lemma ss_mkR_of : forall regs, Regs6ss.mkR_of regs = Frame.mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

Lemma ss_bytes_cells_tail : forall m A n j cs,
  Step.rw_cells rsegs m A (Cells.CB n j :: cs) -> bytes_at rsegs m (A + Z.of_nat n) (Cells.cells_bytes cs).
Proof.
  intros m A n j cs [[Hwf Hb] _]. cbn [Cells.cells_bytes Cells.cbytes] in Hb.
  apply (proj1 (bytes_at_app rsegs m A j (Cells.cells_bytes cs))) in Hb as [_ Hb].
  cbn [Cells.cells_wf] in Hwf. destruct Hwf as [Hl _]. rewrite Hl in Hb. exact Hb.
Qed.

Lemma ss_bytes_keep : forall m m' a bs, bytes_at rsegs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> m' (Z_to_bv 64 (a + i)) = m (Z_to_bv 64 (a + i))) ->
  bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs (H1 & H2 & H3) HE. split; [exact H1|]. split; [exact H2|].
  intros i Hi. unfold Mem.mrd, Mem.wa. rewrite (HE (Z.of_nat i) ltac:(lia)). exact (H3 i Hi).
Qed.

Lemma ss_rw_of_stk : forall m lo hi a n, Frame.stk rsegs m lo hi -> lo <= a -> a + Z.of_nat n <= hi ->
  exists bs, Step.rw_cells rsegs m a [Cells.CB n bs].
Proof.
  intros m lo hi a n ST H1 H2.
  destruct (stk_split rsegs m lo (a + Z.of_nat n) hi ST ltac:(lia)) as [ST1 _].
  destruct (stk_carve rsegs m lo (a + Z.of_nat n) n ST1 ltac:(lia)) as [_ (junk & HJ)].
  exists junk. replace a with (a + Z.of_nat n - Z.of_nat n) at 1 by lia. exact HJ.
Qed.

Lemma ss_rw_bytes : forall m A n bs, Step.rw_cells rsegs m A [Cells.CB n bs] -> bytes_at rsegs m A bs.
Proof. intros m A n bs [[_ Hb] _]. cbn [Cells.cells_bytes Cells.cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

Lemma ss_cells_bytes : forall m A cs, Step.rw_cells rsegs m A cs -> bytes_at rsegs m A (Cells.cells_bytes cs).
Proof. intros m A cs [[_ Hb] _]. exact Hb. Qed.

Lemma ss_fp : forall g x, 0 <= x < 2 ^ 64 -> ~ Frame.outside [(g_S g - SLOT_K, fsp g + 72)] x ->
  g_S g - SLOT_K <= x < g_S g - 104.
Proof.
  intros g x Hx O. unfold fsp, SLOT_FRAME in *.
  destruct (Z_le_dec (g_S g - SLOT_K) x); destruct (Z_lt_dec x (g_S g - 176 + 72)); try lia;
    exfalso; apply O; cbn [Frame.outside]; (split; [lia | exact I]).
Qed.

Lemma ss_fp1 : forall g lo hi x, g_S g - SLOT_K <= lo -> hi <= g_S g - 104 ->
  0 <= x < 2 ^ 64 -> ~ Frame.outside [(lo, hi)] x -> g_S g - SLOT_K <= x < g_S g - 104.
Proof.
  intros g lo hi x H1 H2 Hx O.
  destruct (Z_le_dec lo x); destruct (Z_lt_dec x hi); try lia;
    exfalso; apply O; cbn [Frame.outside]; (split; [lia | exact I]).
Qed.

(* The image bytes of img_w lie in writable segments with file bytes: every memory may store to them. *)
Definition wr_chk (a : Z) : bool :=
  match find_segment rsegs a 1 with
  | Some seg => seg_writable seg &&
      match segment_byte_at (seg_bytes seg) (Z.to_N (a - Z.of_N (seg_base seg))) with
      | Some _ => true
      | None => false
      end
  | None => false
  end.

Lemma wr_chk_ok : forall m a, 0 <= a < 2 ^ 64 -> wr_chk a = true ->
  writable_at rsegs m a /\ Mem.ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros m a Ha H. unfold wr_chk in H. unfold writable_at, wview, Mem.ro_addr.
  rewrite (MState.unsigned_lit a Ha).
  destruct (find_segment rsegs a 1) as [seg|]; [|discriminate H].
  apply andb_prop in H as [H1 H2]. rewrite H1. cbn iota. split; [|reflexivity].
  destruct (m (Z_to_bv 64 a)) as [b|]; [discriminate|].
  destruct (segment_byte_at (seg_bytes seg) (Z.to_N (a - Z.of_N (seg_base seg)))) as [b|];
    [discriminate | discriminate H2].
Qed.

Definition rng_chk (lo n : Z) : bool := forallb (fun i => wr_chk (lo + Z.of_nat i)) (seq 0 (Z.to_nat n)).

Lemma rng_chk_ok : forall lo n, rng_chk lo n = true -> forall a, lo <= a < lo + n -> wr_chk a = true.
Proof.
  intros lo n H a Ha. unfold rng_chk in H. rewrite forallb_forall in H.
  replace a with (lo + Z.of_nat (Z.to_nat (a - lo))) by lia.
  apply H. apply in_seq. lia.
Qed.

Lemma img_w_chk : (rng_chk A_STDERR 232 && rng_chk (symaddr Symbols.Ubsan.s_g_file_len) 16 && rng_chk A_OFL_HEAD 8)%bool = true.
Proof. vm_compute. reflexivity. Qed.

Lemma img_w_range : forall a, img_w a ->
  (A_STDERR <= a < A_STDERR + 232) \/ ((symaddr Symbols.Ubsan.s_g_file_len) <= a < (symaddr Symbols.Ubsan.s_environ)) \/ (A_OFL_HEAD <= a < A_OFL_HEAD + 8).
Proof.
  intros a [(lo & len & Hin & Ha) | [Ha | Ha]].
  - unfold frame_G in Hin. cbn [In] in Hin.
    destruct Hin as [E | [E | []]]; injection E as <- <-; unfold A_STDERR; lia.
  - right. right. exact Ha.
  - left. exact Ha.
Qed.

Lemma img_w_iff : forall a, img_w a <->
  (A_STDERR <= a < A_STDERR + 232) \/ ((symaddr Symbols.Ubsan.s_g_file_len) <= a < (symaddr Symbols.Ubsan.s_environ)) \/ (A_OFL_HEAD <= a < A_OFL_HEAD + 8).
Proof.
  intros a. split; [apply img_w_range|].
  intros [R|[R|R]].
  - right. right. exact R.
  - left. exists (symaddr Symbols.Ubsan.s_g_file_len), 16. split; [right; left; reflexivity | lia].
  - right. left. exact R.
Qed.

Lemma img_w_dec : forall a, img_w a \/ ~ img_w a.
Proof.
  intros a. pose proof (img_w_iff a) as [H1 H2].
  assert (D : ((A_STDERR <= a < A_STDERR + 232) \/ ((symaddr Symbols.Ubsan.s_g_file_len) <= a < (symaddr Symbols.Ubsan.s_environ)) \/
               (A_OFL_HEAD <= a < A_OFL_HEAD + 8)) \/
              ~ ((A_STDERR <= a < A_STDERR + 232) \/ ((symaddr Symbols.Ubsan.s_g_file_len) <= a < (symaddr Symbols.Ubsan.s_environ)) \/
                 (A_OFL_HEAD <= a < A_OFL_HEAD + 8)))
    by (unfold A_STDERR, A_OFL_HEAD; lia).
  destruct D as [D|D]; [left; exact (H2 D) | right; intros Hw; exact (D (H1 Hw))].
Qed.

Lemma img_w_wr : forall m a, img_w a ->
  writable_at rsegs m a /\ Mem.ro_addr rsegs (Z_to_bv 64 a) = false /\ IMG_LO <= a < IMG_HI.
Proof.
  intros m a H. pose proof img_w_chk as C. apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2].
  pose proof (img_w_range a H) as R.
  assert (W : wr_chk a = true).
  { destruct R as [R|[R|R]].
    - exact (rng_chk_ok _ _ C1 a R).
    - exact (rng_chk_ok _ _ C2 a ltac:(lia)).
    - exact (rng_chk_ok _ _ C3 a R). }
  unfold A_STDERR, A_OFL_HEAD in R.
  destruct (wr_chk_ok m a ltac:(lia) W) as [W1 W2].
  split; [exact W1|]. split; [exact W2|]. unfold IMG_LO, IMG_HI. lia.
Qed.

Section R.
Context {fx : FPState}.

Lemma ss_run : forall regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] -> ro_agree rsegs mem ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R pc' m', ms = MState.MS R fp_regs pc' fp_csr None m' (seg_rom rsegs)) ->
  (forall R pc' m0', Q (MState.MS R fp_regs pc' fp_csr None m0' (seg_rom rsegs)) ->
     forall regs' m', Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m' m0' -> ro_same rsegs mem m' ->
     SR rsegs (mkCfg (mkst regs' pc' m' (seg_rom rsegs)) md) P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md Q P Hh Hl Hro HE Hform HK.
  apply (evt_SR_canon rsegs _ (fun s => exists s0, Q s0 /\ ms_rel rsegs s s0 /\ ro_same rsegs mem (ms_mem s)) md P);
    [| exact Hh | exact Hl |].
  - change (RegisterBridge.canonical_register_state (mkst regs pc mem (seg_rom rsegs)))
      with (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)).
    apply evt_normalize; [exact wx_apart_rsegs | exact Hro | exact HE].
  - intros ms' (can & (s0 & HQ & Hrel & Hsame) & Heq).
    destruct (Hform s0 HQ) as (R & pc' & m0' & ->).
    destruct can as [cr cf cp cs cv cc cm co].
    destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MState.MS] in *. subst.
    destruct (ss_eqv_mkfp R fp_regs pc' fp_csr cm (seg_rom rsegs) ms' Heq) as [Ems Hx].
    rewrite Ems, ss_mkFP.
    exact (HK R pc' m0' HQ _ cm Hx E8 Hsame).
Qed.

End R.

Section T.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf SH SK ra empty.

Lemma ss_segs : ms_segs B = rsegs.
Proof. exact (proj1 FF). Qed.

Lemma ss_malloc_pc : ms_malloc B = (symaddr Symbols.Ubsan.s_malloc).
Proof. destruct FF as (_ & _ & H & _). exact H. Qed.

Lemma ss_free_pc : ms_free B = (symaddr Symbols.Ubsan.s_free).
Proof. destruct FF as (_ & _ & _ & H & _). exact H. Qed.

Lemma ss_alloc : @frame_allocator rc fx B (APIf rc).
Proof.
  destruct FF as (SEG & RA2 & MAL & FRE & REA & CAL & ERRC & GUA & GOT & CTX & LCK & LIBC & SCL & SMC & MDC & DBR & TP
    & EOFF & REP & OFH & OFL & THR & EMP & EMPR & CTXRO & GLOB & RELRO & ALLOC & VML & DBL).
  exact (ALLOC rc fx).
Qed.

Lemma ss_relro_img : forall a, in_globals frame_RELRO a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Proof.
  destruct FF as (SEG & RA2 & MAL & FRE & REA & CAL & ERRC & GUA & GOT & CTX & LCK & LIBC & SCL & SMC & MDC & DBR & TP
    & EOFF & REP & OFH & OFL & THR & EMP & EMPR & CTXRO & GLOB & RELRO & ALLOC & VML & DBL).
  exact RELRO.
Qed.

Lemma ss_glob_img : forall a, in_globals frame_G a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Proof.
  destruct FF as (SEG & RA2 & MAL & FRE & REA & CAL & ERRC & GUA & GOT & CTX & LCK & LIBC & SCL & SMC & MDC & DBR & TP
    & EOFF & REP & OFH & OFL & THR & EMP & EMPR & CTXRO & GLOB & RELRO & ALLOC & VML & DBL).
  exact GLOB.
Qed.

Lemma ss_errno : errno_addr B = (symaddr (Symbols.Ubsan.s_builtin_tls + 0x24)%Z).
Proof.
  destruct FF as (SEG & RA2 & MAL & FRE & REA & CAL & ERRC & GUA & GOT & CTX & LCK & LIBC & SCL & SMC & MDC & DBR & TP
    & EOFF & REP & OFH & OFL & THR & EMP & EMPR & CTXRO & GLOB & RELRO & ALLOC & VML & DBL).
  unfold errno_addr. rewrite TP, EOFF. reflexivity.
Qed.

Lemma ss_ctx : ms_ctx B = (symaddr Symbols.Ubsan.s___malloc_context).
Proof. destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma ss_ceil : forall a, errno_addr B <= a < errno_addr B + 4 -> a < alloc_ceiling.
Proof.
  destruct FF as (_ & _ & _ & _ & _ & _ & H & _). intros a Ha. specialize (H rc). lia.
Qed.

Let API := APIf rc.
Let MR := aa_MR API.

Lemma ss_laws : MR_laws B MR.
Proof. exact (aa_laws API). Qed.

Lemma ss_ax : AllocExtra B MR.
Proof.
  destruct ss_alloc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H.
Qed.

Lemma ss_img_lt : forall a, in_img B a -> IMG_LO <= a < IMG_HI.
Proof.
  intros a [_ (s & Hin & Ha)]. rewrite ss_segs in Hin.
  assert (H : forallb (fun s => (IMG_LO <=? bv_unsigned (fst s)) && (bv_unsigned (fst s) + bv_unsigned (snd s) <=? IMG_HI))
            (segments_reserved rsegs) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H s Hin). apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1, H2. lia.
Qed.

Lemma ss_fs_img : forall x s, find_segment rsegs x 1 = Some s -> in_img B x.
Proof.
  intros x s E. destruct (ss_fs_in rsegs x 1 s E) as (Hin & H1 & H2).
  assert (H : forallb (fun s => let r := segment_reservation s in
                 (bv_unsigned (fst r) <=? Z.of_N (seg_base s)) &&
                 (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? bv_unsigned (fst r) + bv_unsigned (snd r))) rsegs = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H s Hin). cbv zeta in H. apply andb_prop in H as [H3 H4].
  apply Z.leb_le in H3, H4.
  split; [rewrite ss_segs; discriminate|].
  exists (segment_reservation s). split; [rewrite ss_segs; unfold segments_reserved; apply in_map; exact Hin | lia].
Qed.

Lemma ss_noimg_fs : forall x, ~ in_img B x -> find_segment rsegs x 1 = None.
Proof.
  intros x H. destruct (find_segment rsegs x 1) as [s|] eqn:E; [|reflexivity].
  exfalso. exact (H (ss_fs_img x s E)).
Qed.

Lemma ss_ro_img : forall w : word, Mem.ro_addr rsegs w = true -> in_img B (bv_unsigned w).
Proof.
  intros w H. unfold Mem.ro_addr in H. destruct (find_segment rsegs (bv_unsigned w) 1) as [s|] eqn:E; [|discriminate].
  exact (ss_fs_img _ s E).
Qed.

Lemma ss_ur : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H. exact H. Qed.

Lemma ss_img_rng : forall lo hi,
  existsb (fun s => (bv_unsigned (fst s) <=? lo) && (hi <=? bv_unsigned (fst s) + bv_unsigned (snd s)))
    (segments_reserved rsegs) = true ->
  forall a, lo <= a < hi -> in_img B a.
Proof.
  intros lo hi H a Ha. apply existsb_exists in H as (s & Hs & E).
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
  unfold in_img. rewrite ss_segs. split; [intros N; rewrite N in Hs; exact Hs|].
  exists s. split; [exact Hs | lia].
Qed.

Lemma ss_img_w_facts : forall a, img_w a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4) /\ IMG_LO <= a < IMG_HI /\ Mem.ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Hw. pose proof ss_errno as Er.
  pose proof FF as (SEG & RA2 & MAL & FRE & REA & CAL & ERRC & GUA & GOT & CTX & LCK & LIBC & SCL & SMC & MDC & DBR
    & TP & EOFF & REP & OFH & OFL & THR & EMP & EMPR & CTXRO & GLOB & RELRO & ALLOC & VML & DBL).
  destruct (img_w_wr (fun _ => None) a Hw) as (_ & Hro & Hl).
  assert (Hi : in_img B a).
  { destruct (img_w_range a Hw) as [R|[R|R]].
    - exact (ss_img_rng A_STDERR (A_STDERR + 232) ltac:(vm_compute; reflexivity) a R).
    - exact (ss_img_rng (symaddr Symbols.Ubsan.s_g_file_len) (symaddr Symbols.Ubsan.s_environ) ltac:(vm_compute; reflexivity) a R).
    - exact (ss_img_rng A_OFL_HEAD (A_OFL_HEAD + 8) ltac:(vm_compute; reflexivity) a R). }
  pose proof (img_w_range a Hw) as R. unfold A_STDERR, A_OFL_HEAD in R.
  split; [exact Hi|].
  split; [unfold static_owned, vml_lo, vml_len; rewrite LCK, LIBC, GOT, GUA, DBR, SCL, SMC, MDC, VML, DBL; lia|].
  split; [rewrite CTX; unfold CTX_SIZE; lia|].
  split; [rewrite Er; lia|].
  split; [exact Hl | exact Hro].
Qed.

Lemma ss_pw_perm : forall {X : Type} (R : X -> X -> Prop), (forall a b, R a b -> R b a) ->
  forall l l', Permutation l l' -> pairwise R l -> pairwise R l'.
Proof.
  intros X R Hs l l' HP. induction HP as [|x l l' HP IH|x y l|l l' l'' H1 IH1 H2 IH2]; intros H.
  - exact H.
  - destruct H as [H1 H2]. split; [|apply IH; exact H2].
    intros y Hy. apply H1. apply (Permutation_in _ (Permutation_sym HP)). exact Hy.
  - destruct H as [H1 [H2 H3]]. split.
    + intros z [<-|Hz]; [apply Hs; apply H1; left; reflexivity | apply H2; exact Hz].
    + split; [intros z Hz; apply H1; right; exact Hz | exact H3].
  - apply IH2. apply IH1. exact H.
Qed.

Lemma ss_pw_app : forall {X : Type} (R : X -> X -> Prop) l1 l2, pairwise R (l1 ++ l2) ->
  forall x y, In x l1 -> In y l2 -> R x y.
Proof.
  intros X R l1. induction l1 as [|a l1 IH]; intros l2 H x y Hx Hy; [destruct Hx|].
  destruct H as [H1 H2]. destruct Hx as [<-|Hx].
  - apply H1. apply in_or_app. right. exact Hy.
  - exact (IH l2 H2 x y Hx Hy).
Qed.

Definition in_hb (hb : list (Z * Z)) (x : Z) : Prop := exists a k, In (a, k) hb /\ a <= x < a + k.
(* The bytes a stretch of the slot's own code may change: its frame below the saved registers, the heap blocks
   it holds, and the image bytes it writes outside RELRO. *)
Definition kreg (g : ghost) (hb : list (Z * Z)) (x : Z) : Prop :=
  (g_S g - SLOT_K <= x < g_S g - 104) \/ in_hb hb x \/ (img_w x /\ ~ in_globals frame_RELRO x).
(* The same with all of img_w (a callee that writes the stderr FILE). *)
Definition kreg_r (g : ghost) (hb : list (Z * Z)) (x : Z) : Prop :=
  (g_S g - SLOT_K <= x < g_S g - 104) \/ in_hb hb x \/ img_w x.

Lemma ss_blk_of : forall L A a k, In (a, k) (blocks L A) -> exists p, In (p, k) (user_blocks A) /\ ptr_addr L p = a.
Proof.
  intros L A a k Hin. unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & E & Hp).
  cbn [fst snd] in E. injection E as E1 E2. subst. exists p. split; [exact Hp | reflexivity].
Qed.

Lemma ss_blk_facts : forall L A mem md a k i, MR L A mem md -> In (a, k) (blocks L A) -> 0 <= i < k ->
  present mem (a + i) /\ 4096 <= a /\ a + k <= alloc_ceiling /\ ~ owned B L A (a + i) /\ ~ in_img B (a + i).
Proof.
  intros L A mem md a k i HM Hin Hi. destruct (ss_blk_of L A a k Hin) as (p & Hp & <-).
  destruct (mr_blocks B MR ss_laws L A mem md p k i HM Hp Hi) as (H1 & H2 & H3 & H4).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  exact (ax_blocks_img ss_ax L A mem md p k i HM Hp Hi).
Qed.

Lemma ss_hb_facts : forall L A mem md hb B0 x, MR L A mem md -> Permutation (blocks L A) (hb ++ B0) -> in_hb hb x ->
  present mem x /\ 4096 <= x < alloc_ceiling /\ ~ owned B L A x /\ ~ in_img B x.
Proof.
  intros L A mem md hb B0 x HM HP (a & k & Hin & Hx).
  assert (Hb : In (a, k) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact Hin).
  destruct (ss_blk_facts L A mem md a k (x - a) HM Hb ltac:(lia)) as (H1 & H2 & H3 & H4 & H5).
  replace (a + (x - a)) with x in * by lia. split; [exact H1|]. split; [lia|]. split; assumption.
Qed.

Lemma ss_b0_facts : forall L A mem md hb B0 a k i, MR L A mem md -> Permutation (blocks L A) (hb ++ B0) ->
  In (a, k) B0 -> 0 <= i < k -> 4096 <= a /\ a + i < alloc_ceiling /\ ~ in_hb hb (a + i) /\ ~ in_img B (a + i).
Proof.
  intros L A mem md hb B0 a k i HM HP Hin Hi.
  assert (Hb : In (a, k) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact Hin).
  destruct (ss_blk_facts L A mem md a k i HM Hb Hi) as (_ & H2 & H3 & _ & H5).
  split; [lia|]. split; [lia|]. split; [|exact H5].
  intros (a' & k' & Hin' & Hx).
  pose proof (mr_blocks_disjoint B MR ss_laws L A mem md HM) as Hpw.
  pose proof (ss_pw_perm ranges_disjoint ltac:(intros u v; unfold ranges_disjoint; lia) _ _ HP Hpw) as Hpw'.
  pose proof (ss_pw_app ranges_disjoint hb B0 Hpw' (a', k') (a, k) Hin' Hin) as Hd.
  unfold ranges_disjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

Lemma ss_img_w_owned : forall L A mem md x, MR L A mem md -> img_w x -> ~ owned B L A x.
Proof.
  intros L A mem md x HM Hw Ho. destruct (ss_img_w_facts x Hw) as (Hi & Hs & Hc & _).
  destruct Ho as [Ho|Ho]; [exact (Hc (ax_img ss_ax L A mem md x HM Hi Ho)) | exact (Hs Ho)].
Qed.

Lemma ss_FR_kr : forall g km hb L A regs mem md regs' mem',
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ kreg_r g hb x -> mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) ->
  wmono rsegs mem mem' -> relro B mem' ->
  FR B APIf ra empty g km hb L A regs' mem' md.
Proof.
  intros g km hb L A regs mem md regs' mem' HF HP E2 E3 E4 HU HW HREL.
  pose proof ss_segs as SEG.
  destruct HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & HWF & HBD & HIN & Hmd & Hhi & Himg & HB0
    & Her & HRS & Hwin).
  pose proof HGV as (Hn & Hnp & Hblk & HS16 & HSc & HS47 & _).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC.
  assert (HK : SLOT_K = 65536) by reflexivity.
  assert (NK : forall x, kreg_r g hb x -> x < g_S g - 104 /\ ~ owned B L A x /\ 0 <= x < 2 ^ 64 /\
                 (x < alloc_ceiling \/ g_S g - SLOT_K <= x) /\ (in_img B x -> img_w x)).
  { intros x [Hx|[Hx|Hx]].
    - split; [lia|]. split; [intros Ho; pose proof (mr_owned_low B MR ss_laws L A mem md x HMR Ho); lia|].
      split; [lia|]. split; [lia|]. intros Hi. apply ss_img_lt in Hi. unfold IMG_HI in Hi. lia.
    - destruct (ss_hb_facts L A mem md hb _ x HMR HP Hx) as (_ & H2 & H3 & H4).
      split; [lia|]. split; [exact H3|]. split; [lia|]. split; [lia|]. intros Hi. contradiction.
    - destruct (ss_img_w_facts x Hx) as (Hi & Hs & Hc & He & Hl & _). unfold IMG_LO, IMG_HI in Hl.
      split; [lia|]. split; [exact (ss_img_w_owned L A mem md x HMR Hx)|].
      split; [lia|]. split; [lia|]. intros _. exact Hx. }
  assert (SAME : forall x, 0 <= x < 2 ^ 64 -> ~ kreg_r g hb x ->
     mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x /\
     (writable_at (ms_segs B) mem x <-> writable_at (ms_segs B) mem' x)).
  { intros x Hx Hk. unfold mbyte, writable_at, wview. rewrite (HU x Hx Hk). tauto. }
  assert (PRES : forall x, 0 <= x < 2 ^ 64 -> ~ in_img B x -> wview rsegs mem (Z_to_bv 64 x) <> None ->
     exists b, mem' (Z_to_bv 64 x) = Some b).
  { intros x Hx Hi Hw. apply ss_wview_none; [rewrite (unsigned_lit x Hx); exact (ss_noimg_fs x Hi) | apply HW; exact Hw]. }
  split; [exact HGV|].
  split; [rewrite E2; exact Hsp|]. split; [rewrite E3; exact Hgp|]. split; [rewrite E4; exact Htp|].
  split.
  { apply (ss_bytes_same rsegs mem mem'); [|exact Hsv].
    intros i Hi. unfold saved_bytes in Hi. rewrite ?length_app, ?length_le8 in Hi. cbn in Hi.
    apply HU; [lia|]. intros Hk. destruct (NK _ Hk) as (H2 & _). lia. }
  split.
  { destruct Hstk as (Hs1 & Hs2 & Hs3). split; [exact Hs1|]. split; [exact Hs2|].
    intros a Ha. destruct (Hs3 a Ha) as [Hw _].
    assert (Hw' : wview rsegs mem' (wa a) <> None) by (apply HW; exact Hw).
    split; [exact Hw'|].
    destruct (ss_wview_none mem' (wa a) ltac:(rewrite wa_unsigned by lia; apply ss_fs_none; unfold IMG_HI; lia) Hw')
      as (b & Hb).
    exists b. unfold mrd. rewrite Hb. reflexivity. }
  split.
  { intros w Hro. pose proof Hro as Hro'. rewrite SEG in Hro'. pose proof (ss_ro_img w Hro') as Hi.
    assert (E : mem' w = mem w).
    { rewrite <- (Z_to_bv_bv_unsigned w). apply HU; [exact (ss_ur w)|]. intros Hk.
      destruct (NK _ Hk) as (_ & _ & _ & _ & Himw).
      destruct (ss_img_w_facts _ (Himw Hi)) as (_ & _ & _ & _ & _ & Hrf).
      rewrite Z_to_bv_bv_unsigned in Hrf. rewrite Hrf in Hro'. discriminate. }
    unfold mrd. rewrite E. exact (HMI w Hro). }
  split; [exact HREL|].
  destruct (mr_model B MR ss_laws L A mem md HMR) as (Hh & Hl & Hm).
  split.
  { apply (mr_frame B MR ss_laws L A mem mem' md md HMR).
    - intros a Ho. pose proof (mr_owned_low B MR ss_laws L A mem md a HMR Ho).
      apply (SAME a ltac:(lia)). intros Hk. exact (proj1 (proj2 (NK _ Hk)) Ho).
    - intros a Ho (b & Hb). pose proof (mr_owned_low B MR ss_laws L A mem md a HMR Ho).
      exists b. rewrite (HU a ltac:(lia)); [exact Hb|]. intros Hk. exact (proj1 (proj2 (NK _ Hk)) Ho).
    - intros p n i Hin Hi. destruct (mr_blocks B MR ss_laws L A mem md p n i HMR Hin Hi) as ((b & Hb) & H2 & H3 & _).
      pose proof (ax_blocks_img ss_ax L A mem md p n i HMR Hin Hi) as Hni.
      unfold present. apply (PRES (ptr_addr L p + i) ltac:(lia) Hni). unfold wview. rewrite Hb. discriminate.
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hm. }
  split; [exact HWF|]. split; [exact HBD|]. split; [exact HIN|]. split; [exact Hmd|].
  split.
  { intros a Ha Hw He. destruct (Hhi a Ha Hw He) as [E1 E2'].
    assert (Hnk : ~ kreg_r g hb a).
    { intros Hk. destruct (NK _ Hk) as (H1 & _ & _ & [H|H] & _); [lia|]. apply Hw. lia. }
    destruct (SAME a ltac:(lia) Hnk) as [M3 M4].
    split; [rewrite M3; exact E1 | tauto]. }
  split.
  { intros a Hi Hs Hc He. destruct (Himg a Hi Hs Hc He) as [E1 E2'].
    pose proof (ss_img_lt a Hi) as Hl'. unfold IMG_LO, IMG_HI in Hl'.
    destruct (img_w_dec a) as [Hw|Hw].
    - split; [intros Hnw; contradiction|].
      destruct (img_w_wr (g_mem g) a Hw) as [W1 _]. destruct (img_w_wr mem' a Hw) as [W2 _].
      rewrite SEG. split; intros _; assumption.
    - assert (Hnk : ~ kreg_r g hb a)
        by (intros Hk; exact (Hw (proj2 (proj2 (proj2 (proj2 (NK _ Hk)))) Hi))).
      destruct (SAME a ltac:(lia) Hnk) as [M3 M4].
      split; [intros Hnw; rewrite M3; exact (E1 Hnw) | tauto]. }
  split.
  { intros a k i Hin Hi. rewrite <- (HB0 a k i Hin Hi).
    destruct (ss_b0_facts L A mem md hb _ a k i HMR HP Hin Hi) as (H0 & H1 & H2 & H3).
    refine (proj1 (SAME (a + i) ltac:(lia) _)).
    intros [Hk|[Hk|Hk]]; [lia | exact (H2 Hk) |].
    destruct (ss_img_w_facts _ Hk) as (Hii & _). exact (H3 Hii). }
  split; [intros a Ha; unfold writable_at; rewrite SEG; apply HW; rewrite <- SEG; exact (Her a Ha)|].
  split; [exact HRS|].
  intros a Ha. unfold writable_at. rewrite SEG. apply HW. rewrite <- SEG. exact (Hwin a Ha).
Qed.

Lemma ss_FR_kA : forall g km hb L A regs mem md regs' mem',
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ kreg g hb x -> mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) ->
  wmono rsegs mem mem' ->
  FR B APIf ra empty g km hb L A regs' mem' md.
Proof.
  intros g km hb L A regs mem md regs' mem' HF HP E2 E3 E4 HU HW.
  pose proof HF as (HGV & _ & _ & _ & _ & _ & _ & Hrel & HMR & _).
  pose proof HGV as (_ & _ & _ & _ & HSc & _).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC.
  assert (HK : SLOT_K = 65536) by reflexivity.
  apply (ss_FR_kr g km hb L A regs mem md regs' mem' HF HP E2 E3 E4); [| exact HW |].
  - intros x Hx Hk. apply HU; [exact Hx|]. intros Hk'. apply Hk.
    destruct Hk' as [H|[H|[H _]]]; [left; exact H | right; left; exact H | right; right; exact H].
  - intros a Ha. rewrite <- (Hrel a Ha). destruct (ss_relro_img a Ha) as (Hi & _).
    pose proof (ss_img_lt a Hi) as Hl. unfold IMG_LO, IMG_HI in Hl.
    unfold mbyte. rewrite (HU a ltac:(lia)); [reflexivity|].
    intros [Hk|[Hk|[_ Hk]]]; [lia | | exact (Hk Ha)].
    destruct (ss_hb_facts L A mem md hb _ a HMR HP Hk) as (_ & _ & _ & H4). exact (H4 Hi).
Qed.

Lemma ss_errc : errno_addr B + 4 <= alloc_ceiling.
Proof. destruct FF as (_ & _ & _ & _ & _ & _ & H & _). exact (H rc). Qed.

Lemma ss_noimg_hi : forall a, IMG_HI <= a -> ~ in_img B a.
Proof. intros a Ha Hi. apply ss_img_lt in Hi. lia. Qed.

Lemma ss_spZ : forall g km hb L A regs mem md, FR B APIf ra empty g km hb L A regs mem md ->
  spZ regs = g_S g - 176.
Proof.
  intros g km hb L A regs mem md HF. destruct HF as (HGV & Hsp & _).
  pose proof HGV as (_ & _ & _ & _ & HSc & HS47 & _).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC.
  unfold spZ. rewrite Hsp. unfold fsp, SLOT_FRAME. apply unsigned_lit. unfold SLOT_K, SLOT_STACK in HSc. lia.
Qed.

(* A callee call: the callee's post (call_post_k with scratch stk below the slot's frame) and the facts its own
   post gives about the bytes it may write (E) carry the frame record over. *)
Lemma ss_FR_call : forall g km hb L A regs mem md stk E L' A' regs' mem' md' km' hb',
  FR B APIf ra empty g km hb L A regs mem md ->
  0 <= stk <= SLOT_K - SLOT_FRAME ->
  call_post_k B MR stk L A regs mem md E L' A' regs' mem' md' ->
  (forall a, E a -> (a < alloc_ceiling /\ ~ in_img B a) \/ (g_S g - SLOT_K <= a < g_S g - 104) \/
     (ms_ctx B <= a < ms_ctx B + CTX_SIZE) \/ (img_w a /\ ~ in_globals frame_RELRO a)) ->
  (forall a, g_S g - SLOT_K <= a < g_S g -> E a \/ ~ E a) ->
  (forall a, E a -> g_S g - SLOT_K <= a < g_S g -> writable_at (ms_segs B) mem' a) ->
  (forall a k i, In (a, k) (blocks (g_L g) (g_A g)) -> 0 <= i < k ->
     mbyte (ms_segs B) mem' (a + i) = mbyte (ms_segs B) mem (a + i)) ->
  ro_agree (ms_segs B) mem' -> st_init_done A' = true -> RESB (g_b g) km' hb' A' ->
  FR B APIf ra empty g km' hb' L' A' regs' mem' md'.
Proof.
  intros g km hb L A regs mem md stk E L' A' regs' mem' md' km' hb' HF Hstk0 HC HE HEdec HEW HB0' HRO' HIN' HRS'.
  pose proof ss_segs as SEG. pose proof (ss_spZ _ _ _ _ _ _ _ _ HF) as SPZ.
  destruct HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & HWF & HBD & HIN & Hmd & Hhi & Himg & HB0
    & Her & HRS & Hwin).
  pose proof HGV as (Hn & Hnp & Hblk & HS16 & HSc & HS47 & _).
  destruct HC as (MR' & WF' & BD' & LL' & PA' & RP' & (vm' & Emd) & FR' & UB' & SC').
  pose proof (@YM05.alloc_ceiling_val rc) as HAC.
  assert (HK : SLOT_K = 65536) by reflexivity.
  unfold SLOT_FRAME in Hstk0.
  pose proof ss_errc as ERC.
  assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> (alloc_ceiling <= a \/ in_img B a) ->
     ~ (g_S g - 176 - stk <= a < g_S g - 176) -> ~ (errno_addr B <= a < errno_addr B + 4) ->
     (in_img B a -> ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE)) -> ~ E a ->
     mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
     (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)).
  { intros a Hr Ha Hs He Hc HEa. apply FR'.
    - destruct Ha as [Ha|Ha]; [left; lia | right; exact Ha].
    - intros Ho. pose proof (mr_owned_low B MR ss_laws L A mem md a HMR Ho) as Hlow.
      destruct Ha as [Ha|Ha]; [lia|]. destruct (Hc Ha) as [Hs1 Hc1].
      destruct Ho as [Ho|Ho]; [exact (Hc1 (ax_img ss_ax L A mem md a HMR Ha Ho)) | exact (Hs1 Ho)].
    - intros Ho. pose proof (mr_owned_low B MR ss_laws L' A' mem' md' a MR' Ho) as Hlow.
      destruct Ha as [Ha|Ha]; [lia|]. destruct (Hc Ha) as [Hs1 Hc1].
      destruct Ho as [Ho|Ho]; [exact (Hc1 (ax_img ss_ax L' A' mem' md' a MR' Ha Ho)) | exact (Hs1 Ho)].
    - unfold scratch_k. rewrite SPZ. lia.
    - exact HEa. }
  assert (NE : forall a, (alloc_ceiling <= a \/ in_img B a) ->
     (in_img B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (img_w a /\ ~ in_globals frame_RELRO a)) ->
     (alloc_ceiling <= a -> ~ (g_S g - SLOT_K <= a < g_S g - 104)) -> ~ E a).
  { intros a Ha Hc Hst HEa. destruct (HE a HEa) as [[H1 H2]|[H1|[H1|H1]]].
    - destruct Ha as [Ha|Ha]; [lia | exact (H2 Ha)].
    - destruct Ha as [Ha|Ha]; [exact (Hst Ha H1)|].
      pose proof (ss_img_lt a Ha) as Hl. unfold IMG_HI in Hl. lia.
    - destruct Ha as [Ha|Ha]; [|exact (proj1 (Hc Ha) H1)].
      rewrite ss_ctx in H1. unfold CTX_SIZE in H1. lia.
    - destruct Ha as [Ha|Ha]; [|exact (proj2 (Hc Ha) H1)].
      destruct H1 as [H1 _]. destruct (ss_img_w_facts a H1) as (_ & _ & _ & _ & Hl & _). unfold IMG_HI in Hl. lia. }
  assert (WIN : forall a, g_S g - SLOT_K <= a < g_S g -> writable_at (ms_segs B) mem' a).
  { intros a Ha.
    assert (Hd : (g_S g - 176 - stk <= a < g_S g - 176) \/ ~ (g_S g - 176 - stk <= a < g_S g - 176)) by lia.
    destruct Hd as [Hd|Hd].
    - apply SC'. unfold scratch_k. rewrite SPZ. left. lia.
    - destruct (HEdec a Ha) as [He|He]; [exact (HEW a He Ha)|].
      destruct (KEEP0 a ltac:(lia) ltac:(left; lia) Hd ltac:(lia)
        ltac:(intros Hi; exfalso; exact (ss_noimg_hi a ltac:(unfold IMG_HI; lia) Hi)) He) as [_ M2].
      apply M2. exact (Hwin a Ha). }
  split; [exact HGV|].
  split; [etransitivity; [exact (RP' 2 ltac:(unfold callee_saved; lia))|]; exact Hsp|].
  split; [etransitivity; [exact (RP' 3 ltac:(unfold callee_saved; lia))|]; exact Hgp|].
  split; [etransitivity; [exact (RP' 4 ltac:(unfold callee_saved; lia))|]; exact Htp|].
  split.
  { apply (ss_bytes_mbyte rsegs mem mem'); [|exact Hsv].
    intros i Hi. unfold saved_bytes in Hi. rewrite ?length_app, ?length_le8 in Hi. cbn in Hi.
    assert (Hni : ~ in_img B (g_S g - 104 + i)) by (apply ss_noimg_hi; unfold IMG_HI; lia).
    rewrite <- SEG.
    exact (proj1 (KEEP0 (g_S g - 104 + i) ltac:(lia) ltac:(left; lia) ltac:(lia) ltac:(lia)
      ltac:(intros Hi'; contradiction)
      (NE (g_S g - 104 + i) ltac:(left; lia) ltac:(intros Hi'; contradiction) ltac:(intros _; lia)))). }
  split.
  { destruct Hstk as (Hs1 & Hs2 & Hs3). split; [exact Hs1|]. split; [exact Hs2|].
    intros a Ha. pose proof (WIN a Ha) as W. unfold writable_at in W. rewrite SEG in W. split; [exact W|].
    destruct (ss_wview_none mem' (wa a) ltac:(rewrite wa_unsigned by lia; apply ss_fs_none; unfold IMG_HI; lia) W)
      as (b & Hb).
    exists b. unfold mrd. rewrite Hb. reflexivity. }
  split; [exact HRO'|].
  split.
  { intros a Ha. destruct (ss_relro_img a Ha) as (Hi & Hs & Hc & He).
    pose proof (ss_img_lt a Hi) as Hl. unfold IMG_LO, IMG_HI in Hl.
    destruct (KEEP0 a ltac:(lia) (or_intror Hi) ltac:(lia) He ltac:(intros _; split; assumption)
      (NE a (or_intror Hi) ltac:(intros _; split; [exact Hc | intros [_ Hn']; exact (Hn' Ha)])
        ltac:(intros Hh; lia))) as [M1 _].
    rewrite M1. exact (Hrel a Ha). }
  split; [exact MR'|]. split; [exact WF'|]. split; [exact BD'|]. split; [exact HIN'|].
  split; [destruct Hmd as (vm & Emd0); exists vm'; rewrite Emd, Emd0; reflexivity|].
  split.
  { intros a Ha Hw He. destruct (Hhi a Ha Hw He) as [E1 E2].
    assert (Hni : ~ in_img B a) by (apply ss_noimg_hi; unfold IMG_HI; lia).
    destruct (KEEP0 a ltac:(lia) (or_introl (proj1 Ha)) ltac:(lia) He ltac:(intros Hi'; contradiction)
      (NE a (or_introl (proj1 Ha)) ltac:(intros Hi'; contradiction) ltac:(intros _; lia))) as [M1 M2].
    split; [rewrite M1; exact E1 | tauto]. }
  split.
  { intros a Hi Hs Hc He. destruct (Himg a Hi Hs Hc He) as [E1 E2].
    pose proof (ss_img_lt a Hi) as Hl. unfold IMG_LO, IMG_HI in Hl.
    destruct (img_w_dec a) as [Hw|Hw].
    - split; [intros Hnw; contradiction|].
      destruct (img_w_wr (g_mem g) a Hw) as [W1 _]. destruct (img_w_wr mem' a Hw) as [W2 _].
      rewrite SEG. split; intros _; assumption.
    - destruct (KEEP0 a ltac:(lia) (or_intror Hi) ltac:(lia) He ltac:(intros _; split; assumption)
        (NE a (or_intror Hi) ltac:(intros _; split; [exact Hc | intros [Hw' _]; exact (Hw Hw')])
          ltac:(intros _; lia))) as [M1 M2].
      split; [intros Hnw; rewrite M1; exact (E1 Hnw) | tauto]. }
  split; [intros a k i Hin Hi; rewrite (HB0' a k i Hin Hi); exact (HB0 a k i Hin Hi)|].
  split; [intros a Ha; apply SC'; unfold scratch_k; right; exact Ha|].
  split; [exact HRS'|].
  exact WIN.
Qed.

Lemma ss_call_pre_k : forall g km hb L A regs mem md stk, FR B APIf ra empty g km hb L A regs mem md ->
  0 <= stk <= SLOT_K - SLOT_FRAME -> YK0s.ret_ok (getr regs 1) -> call_pre_k B MR stk L A regs mem md.
Proof.
  intros g km hb L A regs mem md stk HF Hk HRA. pose proof (ss_spZ _ _ _ _ _ _ _ _ HF) as SPZ.
  destruct HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & HWF & HBD & HIN & Hmd & Hhi & Himg & HB0
    & Her & HRS & Hwin).
  pose proof HGV as (Hn & Hnp & Hblk & HS16 & HSc & HS47 & Hroom & HgS & HgT & _).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC.
  unfold SLOT_K, SLOT_STACK, SLOT_FRAME in *.
  unfold call_pre_k. rewrite SPZ.
  split; [exact HMR|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact HRA|].
  split; [Z.div_mod_to_equations; lia|].
  split; [lia|]. split; [lia|].
  split; [intros a Ha; apply Hwin; lia|].
  split; [rewrite Htp; exact HgT|].
  split; [exact Her|].
  intros H0. rewrite HIN in H0. discriminate.
Qed.

Lemma ss_call_pre : forall g km hb L A regs mem md, FR B APIf ra empty g km hb L A regs mem md ->
  YK0s.ret_ok (getr regs 1) -> call_pre B MR L A regs mem md.
Proof.
  intros g km hb L A regs mem md HF HRA. apply call_pre_k_alloc.
  apply (ss_call_pre_k g km hb L A regs mem md ALLOC_STACK HF); [unfold ALLOC_STACK, SLOT_K, SLOT_STACK, SLOT_FRAME; lia | exact HRA].
Qed.

(* guard_ok holds in every allocator state (ax_statics). *)
Lemma ss_guard_of_MR : forall L A mem md, MR L A mem md -> guard_ok mem.
Proof.
  intros L A mem md HM.
  pose proof FF as (SEG & RA2 & MAL & FRE & REA & CAL & ERRC & GUA & GOT & CTX & LCK & LIBC & SCL & SMC & MDC & DBR
    & TP & EOFF & REP & OFH & OFL & THR & EMP & EMPR & CTXRO & GLOB & RELRO & ALLOC & VML & DBL).
  destruct (ax_statics ss_ax L A mem md HM) as (Gw & (g & Hg & Gg) & _).
  rewrite GOT, GUA, SEG in Gw. rewrite GUA, SEG in Gg.
  unfold guard_ok. split.
  - unfold A_GOT_GUARD, A_GUARD, wz. apply (KindBGlue.word_mem_le8 rsegs); [exact Gw | lia | lia | lia].
  - exists (Z_to_bv 64 g). unfold A_GUARD. apply (KindBGlue.word_mem_le8 rsegs); [exact Gg | lia | lia | lia].
Qed.

(* The bytes of stdio_ok other than __libc+3 (static_owned; ax_statics fixes it). *)
Lemma ss_stdio_addr : forall a, (a = A_LIBC + 1 \/ A_OFL_LOCK <= a < A_OFL_LOCK + 4) ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4) /\ IMG_LO <= a < IMG_HI.
Proof.
  intros a Ha. pose proof ss_errno as Er.
  pose proof FF as (SEG & RA2 & MAL & FRE & REA & CAL & ERRC & GUA & GOT & CTX & LCK & LIBC & SCL & SMC & MDC & DBR
    & TP & EOFF & REP & OFH & OFL & THR & EMP & EMPR & CTXRO & GLOB & RELRO & ALLOC & VML & DBL).
  unfold A_LIBC, A_OFL_LOCK in Ha.
  split; [apply (ss_img_rng A_LIBC A_OFL_HEAD); [vm_compute; reflexivity | unfold A_LIBC, A_OFL_HEAD; lia]|].
  split; [unfold static_owned, vml_lo, vml_len; rewrite LCK, LIBC, GOT, GUA, DBR, SCL, SMC, MDC, VML, DBL; lia|].
  split; [rewrite CTX; unfold CTX_SIZE; lia|].
  split; [rewrite Er; lia|].
  unfold IMG_LO, IMG_HI. lia.
Qed.

Lemma ss_stdio_keep : forall L A mem mem' md, MR L A mem' md -> stdio_ok mem ->
  (forall a, (a = A_LIBC + 1 \/ A_OFL_LOCK <= a < A_OFL_LOCK + 4) ->
     mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a) ->
  stdio_ok mem'.
Proof.
  intros L A mem mem' md HM (S1 & S2 & S3) HK.
  pose proof FF as (SEG & RA2 & MAL & FRE & REA & CAL & ERRC & GUA & GOT & CTX & LCK & LIBC & SCL & SMC & MDC & DBR
    & TP & EOFF & REP & OFH & OFL & THR & EMP & EMPR & CTXRO & GLOB & RELRO & ALLOC & VML & DBL).
  rewrite SEG in HK.
  destruct (ax_statics ss_ax L A mem' md HM) as (_ & _ & L3).
  rewrite LIBC, SEG in L3.
  unfold stdio_ok. split; [|split].
  - apply (ss_bytes_mbyte rsegs mem mem'); [|exact S1]. intros i Hi. cbn in Hi. apply HK. left. lia.
  - split; [unfold A_LIBC; lia|]. split; [cbn [length]; unfold A_LIBC; lia|].
    intros i Hi. cbn [length] in Hi. destruct i as [|i]; [|lia].
    change (mbyte rsegs mem' (A_LIBC + 3 + Z.of_nat 0) = nth_error [Z_to_bv 8 0] 0).
    unfold A_LIBC. replace ((symaddr Symbols.Ubsan.s___libc) + 3 + Z.of_nat 0) with ((symaddr Symbols.Ubsan.s___libc) + 3) by lia. exact L3.
  - apply (ss_bytes_mbyte rsegs mem mem'); [|exact S3]. intros i Hi. rewrite length_le4 in Hi. apply HK. right.
    cbn in Hi. lia.
Qed.

Lemma resb_room_w : forall b0 hb n, slot_room b0 -> (length hb <= 16)%nat ->
  0 <= hb_bytes hb <= 2 ^ 27 -> 0 <= n < 2 ^ 26 -> room_slots (sb_hb b0 hb) n.
Proof.
  intros b0 hb n (HL & HB & HC) Hlen HS Hn.
  unfold room_slots, sb_hb. cbn [sb_live sb_bytes sb_cap].
  split; [exact (proj1 Hn)|]. split; [lia|].
  apply (CAPOK_mono CAPMAX (sb_cap b0) (2 ^ 40) _ (2 ^ 28 - 2 ^ 13) n); [lia | lia | lia | exact CAPOK_big].
Qed.

Lemma ss_malloc_step : forall g km hb L A regs mem md n o P,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  (length hb <= 16)%nat -> 0 <= hb_bytes hb <= 2 ^ 27 -> 0 <= n < 2 ^ 26 ->
  YK0s.ret_ok (getr regs 1) -> getr regs 10 = Z_to_bv 64 n -> stdio_ok mem ->
  (forall L' A' regs' mem' md' res,
     FR B APIf ra empty g (km + 1) (hb ++ [(res, n)]) L' A' regs' mem' md' ->
     Permutation (blocks L' A') ((hb ++ [(res, n)]) ++ blocks (g_L g) (g_A g)) ->
     regs_preserved regs regs' -> getr regs' 10 = Z_to_bv 64 res -> res <> 0 ->
     (forall x, fsp g <= x < g_S g -> mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x) ->
     (forall a k i, In (a, k) hb -> 0 <= i < k -> mbyte (ms_segs B) mem' (a + i) = mbyte (ms_segs B) mem (a + i)) ->
     (forall x, img_w x -> mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x) ->
     stdio_ok mem' -> guard_ok mem' ->
     SRO (ms_segs B) (mkCfg (mkst regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md') o P) ->
  SRO (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 (ms_malloc B)) mem (seg_rom (ms_segs B))) md) o P.
Proof.
  intros g km hb L A regs mem md n o P HF HP Hlen Hhb Hn HRA H10 HSTD HK.
  destruct ss_alloc as (MALLOC & _).
  pose proof (ss_spZ _ _ _ _ _ _ _ _ HF) as SPZ.
  pose proof (ss_call_pre _ _ _ _ _ _ _ _ HF HRA) as CP.
  pose proof HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & HWF & HBD & HIN & Hmd & Hhi & Himg & HB0
    & Her & HRS & Hwin).
  pose proof HGV as (Hn0 & Hnp & Hblk & HS16 & HSc & HS47 & Hroom & _).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC. pose proof ss_errc as ERC.
  pose proof (resb_room_w (g_b g) hb n Hroom Hlen Hhb Hn) as ROOM.
  eapply SR_SRO_bind; [exact (MALLOC L A regs mem md n (sb_hb (g_b g) hb) CP HMI H10 HRS ROOM)|].
  intros c' (L' & A' & regs' & mem' & md' & res & -> & HC & R10 & Hr0 & Hr16 & Hfr & (b1 & b2 & Eb' & Eb) & Hkept
    & HRO' & HGK & HUB & HIN' & HLEN & HRES').
  assert (HP' : Permutation (blocks L' A') ((hb ++ [(res, n)]) ++ blocks (g_L g) (g_A g))).
  { rewrite Eb', <- app_assoc. cbn [app].
    apply Permutation_trans with ((res, n) :: (b1 ++ b2)); [apply Permutation_sym, Permutation_middle|].
    rewrite <- Eb. apply Permutation_trans with ((res, n) :: hb ++ blocks (g_L g) (g_A g)); [apply perm_skip; exact HP|].
    apply Permutation_middle. }
  assert (HF' : FR B APIf ra empty g (km + 1) (hb ++ [(res, n)]) L' A' regs' mem' md').
  { apply (ss_FR_call g km hb L A regs mem md ALLOC_STACK (fun _ => False) L' A' regs' mem' md' (km + 1)
      (hb ++ [(res, n)]) HF).
    - unfold ALLOC_STACK, SLOT_K, SLOT_STACK, SLOT_FRAME. lia.
    - exact HC.
    - intros a [].
    - intros a _. right. intros [].
    - intros a [].
    - intros a k i Hin Hi. apply (Hkept a k i); [|intros []|exact Hi].
      apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. exact Hin.
    - exact HRO'.
    - exact HIN'.
    - exact (resb_malloc (g_b g) (km + 1) hb (hb ++ [(res, n)]) A' res n
               (Permutation_sym (Permutation_cons_append hb (res, n))) HRES'). }
  destruct HC as (MR'' & _ & _ & _ & _ & RP' & _ & FR' & _ & _).
  apply (HK L' A' regs' mem' md' res HF' HP' RP' R10 Hr0).
  - intros x Hx. unfold fsp, SLOT_FRAME in Hx. unfold SLOT_K, SLOT_STACK in HSc. apply FR'.
    + left. lia.
    + intros Ho. pose proof (mr_owned_low B MR ss_laws L A mem md x HMR Ho). lia.
    + intros Ho. pose proof (mr_owned_low B MR ss_laws L' A' mem' md' x MR'' Ho). lia.
    + unfold scratch_k. rewrite SPZ. unfold ALLOC_STACK. lia.
    + intros [].
  - intros a k i Hin Hi. apply (Hkept a k i); [|intros []|exact Hi].
    apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hin.
  - intros x Hx. destruct (ss_img_w_facts x Hx) as (Hi & Hs & Hc & He & Hl & _). unfold IMG_LO, IMG_HI in Hl.
    apply FR'.
    + right. exact Hi.
    + exact (ss_img_w_owned L A mem md x HMR Hx).
    + exact (ss_img_w_owned L' A' mem' md' x MR'' Hx).
    + unfold scratch_k. rewrite SPZ. unfold ALLOC_STACK, SLOT_K, SLOT_STACK in *. lia.
    + intros [].
  - refine (ss_stdio_keep L' A' mem mem' md' MR'' HSTD _).
    intros x Hx. destruct (ss_stdio_addr x Hx) as (Hi & Hs & Hc & He & Hl). unfold IMG_LO, IMG_HI in Hl.
    apply FR'.
    + right. exact Hi.
    + intros [Ho|Ho]; [exact (Hc (ax_img ss_ax L A mem md x HMR Hi Ho)) | exact (Hs Ho)].
    + intros [Ho|Ho]; [exact (Hc (ax_img ss_ax L' A' mem' md' x MR'' Hi Ho)) | exact (Hs Ho)].
    + unfold scratch_k. rewrite SPZ. unfold ALLOC_STACK, SLOT_K, SLOT_STACK in *. lia.
    + intros [].
  - exact (ss_guard_of_MR L' A' mem' md' MR'').
Qed.

Lemma ss_free_step : forall g km hb1 a n hb2 L A regs mem md o P,
  FR B APIf ra empty g km (hb1 ++ (a, n) :: hb2) L A regs mem md ->
  Permutation (blocks L A) ((hb1 ++ (a, n) :: hb2) ++ blocks (g_L g) (g_A g)) ->
  YK0s.ret_ok (getr regs 1) -> getr regs 10 = Z_to_bv 64 a -> stdio_ok mem ->
  (forall L' A' regs' mem' md',
     FR B APIf ra empty g km (hb1 ++ hb2) L' A' regs' mem' md' ->
     Permutation (blocks L' A') ((hb1 ++ hb2) ++ blocks (g_L g) (g_A g)) ->
     regs_preserved regs regs' ->
     (forall x, fsp g <= x < g_S g -> mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x) ->
     (forall x, img_w x -> mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x) ->
     stdio_ok mem' -> guard_ok mem' ->
     SRO (ms_segs B) (mkCfg (mkst regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md') o P) ->
  SRO (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 (ms_free B)) mem (seg_rom (ms_segs B))) md) o P.
Proof.
  intros g km hb1 a n hb2 L A regs mem md o P HF HP HRA H10 HSTD HK.
  destruct ss_alloc as (_ & FREE & _).
  pose proof (ss_spZ _ _ _ _ _ _ _ _ HF) as SPZ.
  pose proof (ss_call_pre _ _ _ _ _ _ _ _ HF HRA) as CP.
  pose proof HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & HWF & HBD & HIN & Hmd & Hhi & Himg & HB0
    & Her & HRS & Hwin).
  pose proof HGV as (Hn0 & Hnp & Hblk & HS16 & HSc & HS47 & Hroom & _).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC. pose proof ss_errc as ERC.
  assert (HK0 : SLOT_K = 65536) by reflexivity.
  pose proof (Permutation_sym (Permutation_middle hb1 hb2 (a, n))) as HPm.
  assert (Hab : In (a, n) (blocks L A)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. apply in_or_app. right. left. reflexivity. }
  destruct (ss_blk_of L A a n Hab) as (p & Hp & Epa).
  destruct (mr_blocks_range B MR ss_laws L A mem md p n HMR Hp) as (Ha1 & Ha2). rewrite Epa in Ha1, Ha2.
  assert (HNa : forall k, In (a, k) (blocks (g_L g) (g_A g)) -> False).
  { intros k Hin.
    destruct ss_alloc as (_ & _ & _ & _ & _ & _ & _ & _ & ND & _).
    pose proof (proj1 (stdpp.base.NoDup_ListNoDup _) (ND L A mem md HMR)) as Hnd.
    pose proof (Permutation_map fst HP) as HPf. apply (Permutation_NoDup HPf) in Hnd.
    rewrite !map_app in Hnd. cbn [map fst] in Hnd. rewrite <- app_assoc in Hnd. cbn [app] in Hnd.
    apply NoDup_remove_2 in Hnd. apply Hnd.
    apply in_or_app. right. apply in_or_app. right. apply in_map_iff. exists (a, k). split; [reflexivity | exact Hin]. }
  eapply SR_SRO_bind;
    [exact (FREE L A regs mem md p n (sb_hb (g_b g) (hb1 ++ (a, n) :: hb2)) CP HMI Hp ltac:(rewrite Epa; exact H10) HRS)|].
  intros c' (L' & A' & regs' & mem' & md' & -> & HC & (b1 & b2 & Eb & Eb') & Hkept & HRO' & HGK & HUB & HINi & HLEN
    & HRES').
  rewrite Epa in Eb, Hkept, HC.
  apply call_post_k_alloc in HC.
  assert (HP' : Permutation (blocks L' A') ((hb1 ++ hb2) ++ blocks (g_L g) (g_A g))).
  { rewrite Eb', <- app_assoc. apply (Permutation_app_inv _ _ _ _ (a, n)).
    rewrite <- Eb. rewrite <- app_assoc in HP. cbn [app] in HP. exact HP. }
  assert (HF' : FR B APIf ra empty g km (hb1 ++ hb2) L' A' regs' mem' md').
  { apply (ss_FR_call g km (hb1 ++ (a, n) :: hb2) L A regs mem md ALLOC_STACK (fun x => a <= x < a + n)
      L' A' regs' mem' md' km (hb1 ++ hb2) HF).
    - unfold ALLOC_STACK, SLOT_K, SLOT_STACK, SLOT_FRAME. lia.
    - exact HC.
    - intros x Hx. left. destruct (ss_blk_facts L A mem md a n (x - a) HMR Hab ltac:(lia)) as (_ & H2 & H3 & _ & H5).
      replace (a + (x - a)) with x in H5 by lia. split; [lia | exact H5].
    - intros x Hx. right. intros Hx'. unfold SLOT_K, SLOT_STACK in *. lia.
    - intros x Hx Hx'. exfalso. unfold SLOT_K, SLOT_STACK in *. lia.
    - intros a' k i Hin Hi. apply (Hkept a' k i); [| | exact Hi].
      + apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. exact Hin.
      + intros Ea. subst a'. exact (HNa k Hin).
    - exact HRO'.
    - exact (HINi HIN).
    - apply (resb_free (g_b g) km (hb1 ++ (a, n) :: hb2) (hb1 ++ hb2) A' a n HPm).
      exact HRES'. }
  destruct HC as (MR'' & _ & _ & _ & _ & RP' & _ & FR' & _ & _).
  apply (HK L' A' regs' mem' md' HF' HP' RP').
  - intros x Hx. unfold fsp, SLOT_FRAME in Hx. unfold SLOT_K, SLOT_STACK in HSc. apply FR'.
    + left. lia.
    + intros Ho. pose proof (mr_owned_low B MR ss_laws L A mem md x HMR Ho). lia.
    + intros Ho. pose proof (mr_owned_low B MR ss_laws L' A' mem' md' x MR'' Ho). lia.
    + unfold scratch, scratch_k. rewrite SPZ. unfold ALLOC_STACK. lia.
    + cbn. lia.
  - intros x Hx. destruct (ss_img_w_facts x Hx) as (Hi & Hs & Hc & He & Hl & _). unfold IMG_LO, IMG_HI in Hl.
    apply FR'.
    + right. exact Hi.
    + exact (ss_img_w_owned L A mem md x HMR Hx).
    + exact (ss_img_w_owned L' A' mem' md' x MR'' Hx).
    + unfold scratch, scratch_k. rewrite SPZ. unfold ALLOC_STACK. lia.
    + cbn. intros Hx'.
      destruct (ss_blk_facts L A mem md a n (x - a) HMR Hab ltac:(lia)) as (_ & _ & _ & _ & H5).
      replace (a + (x - a)) with x in H5 by lia. exact (H5 Hi).
  - refine (ss_stdio_keep L' A' mem mem' md' MR'' HSTD _).
    intros x Hx. destruct (ss_stdio_addr x Hx) as (Hi & Hs & Hc & He & Hl). unfold IMG_LO, IMG_HI in Hl.
    apply FR'.
    + right. exact Hi.
    + intros [Ho|Ho]; [exact (Hc (ax_img ss_ax L A mem md x HMR Hi Ho)) | exact (Hs Ho)].
    + intros [Ho|Ho]; [exact (Hc (ax_img ss_ax L' A' mem' md' x MR'' Hi Ho)) | exact (Hs Ho)].
    + unfold scratch, scratch_k. rewrite SPZ. unfold ALLOC_STACK. lia.
    + cbn. intros Hx'.
      destruct (ss_blk_facts L A mem md a n (x - a) HMR Hab ltac:(lia)) as (_ & _ & _ & _ & H5).
      replace (a + (x - a)) with x in H5 by lia. exact (H5 Hi).
  - exact (ss_guard_of_MR L' A' mem' md' MR'').
Qed.


Lemma ss_kA_run : forall (regs : bvmap 5 word) pc mem md (Q : bvmap 5 word -> word -> (word -> option byte) -> Prop) P,
  m_halted md = None -> m_vm_lazy md = [] -> ro_agree (ms_segs B) mem ->
  Exec.evt rsegs (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\ Q R pc' m')
    (MS (mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall R pc' m' regs' mem', Q R pc' m' -> xregs_eqv R regs' -> mem_rel rsegs mem' m' -> ro_same rsegs mem mem' ->
     SR (ms_segs B) (mkCfg (mkst regs' pc' mem' (seg_rom (ms_segs B))) md) P) ->
  SR (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros regs pc mem md Q P Hh Hl HRO HE HK.
  pose proof ss_segs as SEG.
  eapply (evt_SR_canon (ms_segs B) (mkst regs pc mem (seg_rom (ms_segs B))) _ md P); [| exact Hh | exact Hl |].
  - rewrite ss_canon_mkst. rewrite SEG. apply (evt_normalize rsegs); [exact wx_apart_rsegs | rewrite <- SEG; exact HRO |].
    exact HE.
  - intros ms' (can & (s0 & (R & pc' & m' & -> & HQ) & Hrel & Hsame) & Heq).
    destruct can as [cR cF cpc csvc cres cfc cmem crom].
    destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & Hmr). cbn in E1, E2, E3, E4, E5, E6, E7, Hmr, Hsame.
    subst cR cF cpc csvc cres cfc crom.
    destruct (ss_eqv_mkst R pc' cmem (seg_rom rsegs) ms' Heq) as (R' & -> & XR).
    rewrite <- SEG. apply (HK R pc' m' R' cmem HQ XR Hmr Hsame).
Qed.

Lemma ss_stk_nrm : forall m lo hi, stk rsegs m lo hi -> IMG_HI <= lo -> stk rsegs (normalize rsegs m) lo hi.
Proof.
  intros m lo hi (H1 & H2 & H3) Hlo. split; [exact H1|]. split; [exact H2|].
  intros a Ha. assert (Hro : Mem.ro_addr rsegs (wa a) = false).
  { unfold Mem.ro_addr. rewrite wa_unsigned by lia. rewrite ss_fs_none by lia. reflexivity. }
  assert (E : normalize rsegs m (wa a) = m (wa a)) by (unfold normalize; rewrite Hro; reflexivity).
  destruct (H3 a Ha) as [Hw (b & Hb)]. unfold wview, mrd in *. rewrite E. split; [exact Hw | exists b; exact Hb].
Qed.

Lemma ss_outside : forall (P : Z -> Prop) W x, (forall lo hi y, In (lo, hi) W -> lo <= y < hi -> P y) -> ~ P x ->
  outside W x.
Proof.
  intros P W x H Hx. induction W as [|[lo hi] W IH]; cbn; [exact I|].
  split; [intros Hr; exact (Hx (H lo hi x (or_introl eq_refl) Hr))|].
  apply IH. intros lo' hi' y Hin Hy. exact (H lo' hi' y (or_intror Hin) Hy).
Qed.

Lemma ss_munch_unch : forall (P : Z -> Prop) W (mem mem' : word -> option byte),
  munch W mem mem' -> (forall lo hi y, In (lo, hi) W -> lo <= y < hi -> P y) ->
  forall x, 0 <= x < 2 ^ 64 -> ~ P x -> mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x).
Proof.
  intros P W mem mem' Hm HW x Hx HP. apply Hm. rewrite unsigned_lit by exact Hx. exact (ss_outside P W x HW HP).
Qed.

Lemma ss_kA_run0 : forall (regs : bvmap 5 word) pc mem md (Q : bvmap 5 word -> word -> (word -> option byte) -> Prop) P,
  m_halted md = None -> m_vm_lazy md = [] ->
  Exec.evt rsegs (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\ Q R pc' m')
    (MS (mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall R pc' m' regs', Q R pc' m' -> xregs_eqv R regs' ->
     SR (ms_segs B) (mkCfg (mkst regs' pc' m' (seg_rom (ms_segs B))) md) P) ->
  SR (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros regs pc mem md Q P Hh Hl HE HK.
  pose proof ss_segs as SEG.
  eapply (evt_SR_canon (ms_segs B) (mkst regs pc mem (seg_rom (ms_segs B))) _ md P); [| exact Hh | exact Hl |].
  - rewrite ss_canon_mkst. rewrite SEG. exact HE.
  - intros ms' (can & (R & pc' & m' & -> & HQ) & Heq).
    destruct (ss_eqv_mkst R pc' m' (seg_rom rsegs) ms' Heq) as (R' & -> & XR).
    rewrite <- SEG. exact (HK R pc' m' R' HQ XR).
Qed.

Lemma ss_kA_run_o : forall (regs : bvmap 5 word) pc mem md (Q : bvmap 5 word -> word -> (word -> option byte) -> Prop)
    o P,
  m_halted md = None -> m_vm_lazy md = [] -> ro_agree (ms_segs B) mem ->
  Exec.evt rsegs (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\ Q R pc' m')
    (MS (mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall R pc' m' regs' mem', Q R pc' m' -> xregs_eqv R regs' -> mem_rel rsegs mem' m' -> ro_same rsegs mem mem' ->
     SRO (ms_segs B) (mkCfg (mkst regs' pc' mem' (seg_rom (ms_segs B))) md) o P) ->
  SRO (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) o P.
Proof.
  intros regs pc mem md Q o P Hh Hl HRO HE HK.
  apply (SR_SRO_bind (ms_segs B) _ o (fun c' => SRO (ms_segs B) c' o P) P); [|intros c' Hc; exact Hc].
  apply (ss_kA_run regs pc mem md Q _ Hh Hl HRO HE).
  intros R pc' m' regs' mem' HQ XR Hr Hs. apply SR_ret. exact (HK R pc' m' regs' mem' HQ XR Hr Hs).
Qed.

Lemma ss_kA_run0_o : forall (regs : bvmap 5 word) pc mem md
    (Q : bvmap 5 word -> word -> (word -> option byte) -> Prop) o P,
  m_halted md = None -> m_vm_lazy md = [] ->
  Exec.evt rsegs (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\ Q R pc' m')
    (MS (mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall R pc' m' regs', Q R pc' m' -> xregs_eqv R regs' ->
     SRO (ms_segs B) (mkCfg (mkst regs' pc' m' (seg_rom (ms_segs B))) md) o P) ->
  SRO (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) o P.
Proof.
  intros regs pc mem md Q o P Hh Hl HE HK.
  apply (SR_SRO_bind (ms_segs B) _ o (fun c' => SRO (ms_segs B) c' o P) P); [|intros c' Hc; exact Hc].
  apply (ss_kA_run0 regs pc mem md Q _ Hh Hl HE).
  intros R pc' m' regs' HQ XR. apply SR_ret. exact (HK R pc' m' regs' HQ XR).
Qed.

Lemma ss_FR_munch : forall g km hb L A regs mem md regs' mem' W,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  munch W mem mem' -> wmono rsegs mem mem' ->
  (forall lo hi y, In (lo, hi) W -> lo <= y < hi -> kreg g hb y) ->
  FR B APIf ra empty g km hb L A regs' mem' md.
Proof.
  intros g km hb L A regs mem md regs' mem' W HF HP E2 E3 E4 Hm Hw HW.
  apply (ss_FR_kA g km hb L A regs mem md regs' mem' HF HP E2 E3 E4); [|exact Hw].
  exact (ss_munch_unch (kreg g hb) W mem mem' Hm HW).
Qed.

Lemma ss_FR_munch_r : forall g km hb L A regs mem md regs' mem' W,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  munch W mem mem' -> wmono rsegs mem mem' ->
  (forall lo hi y, In (lo, hi) W -> lo <= y < hi -> kreg_r g hb y) -> relro B mem' ->
  FR B APIf ra empty g km hb L A regs' mem' md.
Proof.
  intros g km hb L A regs mem md regs' mem' W HF HP E2 E3 E4 Hm Hw HW HR.
  apply (ss_FR_kr g km hb L A regs mem md regs' mem' HF HP E2 E3 E4); [|exact Hw | exact HR].
  exact (ss_munch_unch (kreg_r g hb) W mem mem' Hm HW).
Qed.

Lemma ss_hb_low : forall g km hb L A regs mem md x,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> in_hb hb x ->
  4096 <= x < alloc_ceiling /\ x + SLOT_K < g_S g.
Proof.
  intros g km hb L A regs mem md x HF HP Hx.
  destruct HF as (HGV & _ & _ & _ & _ & _ & _ & _ & HMR & _).
  pose proof HGV as (_ & _ & _ & _ & HSc & _).
  destruct (ss_hb_facts L A mem md hb _ x HMR HP Hx) as (_ & H2 & _). split; [exact H2 | lia].
Qed.

Lemma ss_hb_blk : forall g km hb L A regs mem md a k,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> In (a, k) hb ->
  (forall i, 0 <= i < k -> writable_at (ms_segs B) mem (a + i) /\ present mem (a + i) /\ ~ in_img B (a + i)) /\
  4096 <= a /\ a + k <= alloc_ceiling /\ a mod 16 = 0.
Proof.
  intros g km hb L A regs mem md a k HF HP Hin.
  destruct HF as (HGV & _ & _ & _ & _ & _ & _ & _ & HMR & _).
  assert (Hb : In (a, k) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact Hin).
  destruct (ss_blk_of L A a k Hb) as (p & Hp & Ea).
  destruct (mr_blocks_range B MR ss_laws L A mem md p k HMR Hp) as (R1 & R2).
  pose proof (mr_blocks_aligned B MR ss_laws L A mem md p k HMR Hp) as Hal.
  rewrite Ea in R1, R2, Hal.
  destruct ss_alloc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BW & _).
  split; [|split; [exact R1 | split; [exact R2 | exact Hal]]].
  intros i Hi. destruct (ss_blk_facts L A mem md a k i HMR Hb Hi) as (H1 & _ & _ & _ & H5).
  split; [exact (BW L A mem md a k i HMR Hb Hi)|]. split; assumption.
Qed.

Lemma ss_hb_in1 : forall a k y, a <= y < a + k -> in_hb [(a, k)] y.
Proof. intros a k y H. exists a, k. split; [left; reflexivity | exact H]. Qed.

Lemma ss_ra : ra mod 2 = 0.
Proof. exact (proj1 (proj2 FF)). Qed.

Lemma ss_sink : @sk_ofl_head SH = (symaddr Symbols.Ubsan.s_ofl_head) /\ @sk_ofl_lock SK = (symaddr Symbols.Ubsan.s_ofl_lock) /\ @sk_threaded SK = (symaddr Symbols.Ubsan.s___libc) + 1.
Proof.
  destruct FF as (SEG & RA2 & MAL & FRE & REA & CAL & ERRC & GUA & GOT & CTX & LCK & LIBC & SCL & SMC & MDC & DBR & TP
    & EOFF & REP & OFH & OFL & THR & EMP & EMPR & CTXRO & GLOB & RELRO & ALLOC & VML & DBL).
  auto.
Qed.

Lemma ss_errno_val : errno_addr B = (symaddr (Symbols.Ubsan.s_builtin_tls + 0xc8)%Z) - 164.
Proof. rewrite ss_errno. reflexivity. Qed.

Lemma ss_top_ceil : SS_TOP < alloc_ceiling.
Proof. pose proof alloc_ceiling_value. unfold SS_TOP. lia. Qed.

Lemma ss_present_of_writable : forall m a, SS_TOP <= a < 2 ^ 64 ->
  writable_at rsegs m a -> exists b, m (Z_to_bv 64 a) = Some b.
Proof.
  intros m a Ha W. unfold writable_at in W. rewrite (ss_wview_hi m a Ha) in W.
  destruct (m (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | contradiction].
Qed.

Lemma ss_stk_of_writable : forall m lo hi, SS_TOP <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> writable_at rsegs m a) -> Frame.stk rsegs m lo hi.
Proof.
  intros m lo hi Hlo Hhi H. split; [unfold SS_TOP in Hlo; lia|]. split; [lia|]. intros a Ha.
  pose proof (H a Ha) as W. unfold writable_at in W. rewrite (ss_wview_hi m a ltac:(lia)) in W.
  unfold Mem.wa. split.
  - rewrite (ss_wview_hi m a ltac:(lia)). exact W.
  - unfold Mem.mrd. destruct (m (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | contradiction].
Qed.

Lemma ss_ro_false : forall a, SS_TOP <= a < 2 ^ 64 -> Mem.ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha. unfold Mem.ro_addr. rewrite (MState.unsigned_lit a ltac:(unfold SS_TOP in Ha; lia)).
  destruct (find_segment rsegs a 1) as [seg|] eqn:E; [|reflexivity].
  exfalso. pose proof (ss_find_top a 1 seg E). unfold SS_TOP in *. lia.
Qed.

Lemma ss_stk_norm : forall m lo hi, ro_agree rsegs m -> SS_TOP <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> writable_at rsegs m a) -> Frame.stk rsegs (normalize rsegs m) lo hi.
Proof.
  intros m lo hi Hro Hlo Hhi H. apply ss_stk_of_writable; [exact Hlo | exact Hhi |].
  intros a Ha. unfold writable_at.
  rewrite (wview_rel_rw rsegs m (normalize rsegs m) _ (mem_rel_normalize rsegs m Hro) (ss_ro_false a ltac:(lia))).
  exact (H a Ha).
Qed.

(* The first frame record: from the facts of a state mem0 on the ghost's image and blocks, and a state mem' that
   differs from mem0 only in the slot's stack window and the image bytes the slot writes outside RELRO. *)
Lemma ss_fr_of : forall g km hb L A mem0 md regs' mem',
  GV B empty g ->
  aa_MR API L A mem0 md -> WF A -> bounded A -> st_init_done A = true ->
  (exists vm, md = with_vmmaps vm (g_md g)) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (g_S g - SLOT_K <= a < g_S g) ->
     ~ (errno_addr B <= a < errno_addr B + 4) ->
     mbyte (ms_segs B) mem0 a = mbyte (ms_segs B) (g_mem g) a /\
     (writable_at (ms_segs B) (g_mem g) a <-> writable_at (ms_segs B) mem0 a)) ->
  (forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
     ~ (errno_addr B <= a < errno_addr B + 4) ->
     (~ img_w a -> mbyte (ms_segs B) mem0 a = mbyte (ms_segs B) (g_mem g) a) /\
     (writable_at (ms_segs B) (g_mem g) a <-> writable_at (ms_segs B) mem0 a)) ->
  (forall a k i, In (a, k) (blocks (g_L g) (g_A g)) -> 0 <= i < k ->
     mbyte (ms_segs B) mem0 (a + i) = mbyte (ms_segs B) (g_mem g) (a + i)) ->
  (forall a k, In (a, k) (blocks (g_L g) (g_A g)) -> In (a, k) (blocks L A)) ->
  (forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at (ms_segs B) mem0 a) ->
  RESB (g_b g) km hb A ->
  (forall a, g_S g - SLOT_K <= a < g_S g -> writable_at (ms_segs B) mem0 a) ->
  relro B mem0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (g_S g - SLOT_K <= a < g_S g) -> ~ (img_w a /\ ~ in_globals frame_RELRO a) ->
     mem' (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)) ->
  Frame.wmono rsegs mem0 mem' -> ro_agree rsegs mem' ->
  getr regs' 2 = Z_to_bv 64 (fsp g) -> getr regs' 3 = getr (g_regs g) 3 -> getr regs' 4 = getr (g_regs g) 4 ->
  bytes_at rsegs mem' (g_S g - 104) (saved_bytes ra g) ->
  FR B APIf ra empty g km hb L A regs' mem' md.
Proof.
  intros g km hb L A mem0 md regs' mem' HGV HM HW HB HID Hmd Hhigh Himg Hblk HBL Herr Hres Hwin Hrel
    HU WM MI' E2 E3 E4 Hsv.
  pose proof ss_segs as SEGS. pose proof ss_top_ceil as Hc. pose proof ss_errc as Her.
  pose proof alloc_ceiling_value as Hac.
  pose proof HGV as (_ & _ & _ & HS16 & HSK & HS47 & _).
  unfold SLOT_K, SLOT_STACK in *. assert (HK0 : SLOT_K = 65536) by reflexivity.
  assert (NW : forall a, ~ in_img B a -> ~ (img_w a /\ ~ in_globals frame_RELRO a)).
  { intros a Hi [Hw _]. exact (Hi (proj1 (ss_img_w_facts a Hw))). }
  assert (HL' : forall a, 0 <= a < alloc_ceiling -> ~ (img_w a /\ ~ in_globals frame_RELRO a) ->
     mem' (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)).
  { intros a Ha Hn. apply HU; [lia | lia | exact Hn]. }
  assert (Hwr : forall a, writable_at (ms_segs B) mem0 a -> writable_at (ms_segs B) mem' a).
  { intros a W. unfold writable_at in *. rewrite SEGS in *. apply WM. exact W. }
  split; [exact HGV|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact Hsv|].
  split.
  { apply ss_stk_of_writable; [unfold SS_TOP; lia | lia |].
    intros a Ha. rewrite <- SEGS. apply Hwr, Hwin. exact Ha. }
  split; [unfold MI; rewrite SEGS; exact MI'|].
  split.
  { unfold relro, G_img_c in *. intros a Ha. rewrite <- (Hrel a Ha).
    destruct (ss_relro_img a Ha) as (Hi & _). pose proof (ss_img_lt a Hi) as Hl. unfold IMG_LO, IMG_HI in Hl.
    unfold mbyte. rewrite (HL' a ltac:(lia) ltac:(intros [_ Hn]; exact (Hn Ha))). reflexivity. }
  split.
  { destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & Hmat).
    eapply (mr_frame B (aa_MR API) (aa_laws API)); [exact HM | | | | reflexivity | exact Hh | exact Hl | exact Hmat].
    - intros a Ho. pose proof (mr_owned_low B (aa_MR API) (aa_laws API) _ _ _ _ a HM Ho) as Ha.
      unfold mbyte. rewrite (HL' a Ha ltac:(intros [Hw _]; exact (ss_img_w_owned L A mem0 md a HM Hw Ho))).
      reflexivity.
    - intros a Ho [bb Hb]. pose proof (mr_owned_low B (aa_MR API) (aa_laws API) _ _ _ _ a HM Ho) as Ha.
      exists bb. rewrite (HL' a Ha ltac:(intros [Hw _]; exact (ss_img_w_owned L A mem0 md a HM Hw Ho))). exact Hb.
    - intros p n i Hin Hi.
      destruct (mr_blocks B (aa_MR API) (aa_laws API) L A mem0 md p n i HM Hin Hi) as ([bb Hpr] & H1 & H2 & _).
      pose proof (ax_blocks_img ss_ax L A mem0 md p n i HM Hin Hi) as Hni.
      exists bb. rewrite (HL' (ptr_addr L p + i) ltac:(lia) (NW _ Hni)). exact Hpr. }
  split; [exact HW|]. split; [exact HB|]. split; [exact HID|]. split; [exact Hmd|].
  split.
  { intros a Ha Hns Hne. destruct (Hhigh a Ha Hns Hne) as [F1 F2].
    assert (Hni : ~ in_img B a) by (apply ss_noimg_hi; unfold IMG_HI, SS_TOP in *; lia).
    rewrite SEGS in *. destruct (ss_eq_at mem0 mem' a (HU a ltac:(lia) Hns (NW a Hni))) as [G1 G2].
    split; [rewrite G1; exact F1 | rewrite F2; exact G2]. }
  split.
  { intros a H1 H2 H3 H4. pose proof (ss_in_img_top B a SEGS H1) as Ht. destruct (Himg a H1 H2 H3 H4) as [F1 F2].
    destruct (img_w_dec a) as [Hw|Hw].
    - split; [intros Hn; contradiction|].
      destruct (img_w_wr (g_mem g) a Hw) as [W1 _]. destruct (img_w_wr mem' a Hw) as [W2 _].
      rewrite SEGS. split; intros _; assumption.
    - rewrite SEGS in *.
      destruct (ss_eq_at mem0 mem' a (HU a ltac:(unfold SS_TOP in Ht; lia) ltac:(unfold SS_TOP in Ht; lia)
        ltac:(intros [Hw' _]; exact (Hw Hw')))) as [G1 G2].
      split; [intros Hn; rewrite G1; exact (F1 Hn) | rewrite F2; exact G2]. }
  split.
  { intros a k i Hin Hi. rewrite <- (Hblk a k i Hin Hi).
    pose proof (HBL a k Hin) as Hin2. apply blocks_In in Hin2 as (p & Hp & Hpin).
    destruct (mr_blocks B (aa_MR API) (aa_laws API) L A mem0 md p k i HM Hpin Hi) as (_ & H1 & H2 & _).
    pose proof (ax_blocks_img ss_ax L A mem0 md p k i HM Hpin Hi) as Hni. subst a.
    unfold mbyte. rewrite (HL' (ptr_addr L p + i) ltac:(lia) (NW _ Hni)). reflexivity. }
  split.
  { intros a Ha. pose proof ss_errno_val as Ev.
    assert (Hnw : ~ (img_w a /\ ~ in_globals frame_RELRO a)).
    { intros [Hw _]. destruct (ss_img_w_facts a Hw) as (_ & _ & _ & Hne & _). exact (Hne Ha). }
    destruct (ss_eq_at mem0 mem' a (HL' a ltac:(lia) Hnw)) as [_ G2].
    rewrite SEGS. apply G2. rewrite <- SEGS. exact (Herr a Ha). }
  split; [exact Hres|].
  intros a Ha. apply Hwr, Hwin. exact Ha.
Qed.

Lemma ss_fr_run : forall g km hb L A regs mem md regs' mem' W,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  Frame.munch W mem mem' -> Frame.wmono rsegs mem mem' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
     (g_S g - SLOT_K <= x < g_S g - 104) \/ (img_w x /\ ~ in_globals frame_RELRO x)) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  FR B APIf ra empty g km hb L A regs' mem' md.
Proof.
  intros g km hb L A regs mem md regs' mem' W HFR HP MU WM HW E2 E3 E4.
  apply (ss_FR_kA g km hb L A regs mem md regs' mem' HFR HP E2 E3 E4); [|exact WM].
  intros x Hx Hk. apply MU. rewrite (unsigned_lit x Hx).
  destruct (ss_outside_dec W x) as [O|O]; [exact O|]. exfalso. apply Hk.
  destruct (HW x Hx O) as [H|H]; [left; exact H | right; right; exact H].
Qed.

Lemma ss_fr_stk : forall g km hb L A regs mem md,
  FR B APIf ra empty g km hb L A regs mem md ->
  Frame.stk rsegs (normalize rsegs mem) (g_S g - SLOT_K) (g_S g).
Proof.
  intros g km hb L A regs mem md HFR.
  destruct HFR as (HGV & _ & _ & _ & _ & _ & HMI & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin).
  pose proof HGV as (_ & _ & _ & HS16 & HSK & HS47 & _).
  pose proof alloc_ceiling_value as Hac. pose proof ss_segs as SEGS.
  unfold MI in HMI. rewrite SEGS in HMI.
  apply ss_stk_norm; [exact HMI | unfold SS_TOP, SLOT_K, SLOT_STACK in *; lia | lia |].
  intros a Ha. rewrite <- SEGS. exact (Hwin a Ha).
Qed.

Lemma ss_fr_bnd : forall g km hb L A regs mem md,
  FR B APIf ra empty g km hb L A regs mem md ->
  getr regs 2 = Z_to_bv 64 (fsp g) /\ fsp g mod 16 = 0 /\ SS_TOP + SLOT_K <= g_S g /\ g_S g <= 2 ^ 47 /\
  ro_agree rsegs mem.
Proof.
  intros g km hb L A regs mem md HFR.
  destruct HFR as (HGV & F2 & _ & _ & _ & _ & HMI & _).
  pose proof HGV as (_ & _ & _ & HS16 & HSK & HS47 & _).
  pose proof alloc_ceiling_value as Hac. pose proof ss_segs as SEGS.
  unfold MI in HMI. rewrite SEGS in HMI.
  unfold fsp, SLOT_FRAME, SS_TOP in *. repeat split; try assumption; try lia.
Qed.

(* A stretch of the slot's own code: an evt from a frame record to states whose writes lie in kreg's frame
   and image parts keeps the frame record. *)
Lemma ss_mid : forall g km hb L A regs mem md pc (Q : machine_state -> Prop) (P : config -> Prop),
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R pc' m', ms = MState.MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
     (exists W, Frame.munch W (normalize rsegs mem) m' /\ Frame.wmono rsegs (normalize rsegs mem) m' /\
        (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
           (g_S g - SLOT_K <= x < g_S g - 104) \/ (img_w x /\ ~ in_globals frame_RELRO x))) /\
     getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4) ->
  (forall R pc' m0' regs' m', Q (MState.MS R fp_regs pc' fp_csr None m0' (seg_rom rsegs)) ->
     Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m' m0' ->
     FR B APIf ra empty g km hb L A regs' m' md ->
     SR (ms_segs B) (mkCfg (mkst regs' pc' m' (seg_rom (ms_segs B))) md) P) ->
  SR (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros g km hb L A regs mem md pc Q P HFR HP HE Hform HK.
  pose proof ss_segs as SEGS.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & HMI & _ & HM & _).
  unfold MI in HMI. rewrite SEGS in HMI.
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  apply (ss_run regs pc mem md Q P Hh Hl HMI HE).
  - intros ms HQ. destruct (Hform ms HQ) as (R & pc' & m' & -> & _). exists R, pc', m'. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel Hsame.
    destruct (Hform _ HQ) as (R1 & pc1 & m1 & E & (W & MU & WM & HW) & E2 & E3 & E4).
    injection E; intros; subst.
    pose proof (mem_rel_normalize rsegs mem HMI) as HR0.
    rewrite <- SEGS. apply (HK R1 pc1 m1 regs' m' HQ Hx Hrel).
    apply (ss_fr_run g km hb L A regs mem md regs' m' W HFR HP).
    + exact (munch_rel rsegs W mem (normalize rsegs mem) m' m1 HR0 Hrel Hsame MU).
    + exact (wmono_rel rsegs mem (normalize rsegs mem) m' m1 HR0 Hrel Hsame WM).
    + exact HW.
    + rewrite (ss_getr_eqv _ _ _ Hx). exact E2.
    + rewrite (ss_getr_eqv _ _ _ Hx). exact E3.
    + rewrite (ss_getr_eqv _ _ _ Hx). exact E4.
Qed.

Lemma ss_mid_o : forall g km hb L A regs mem md pc (Q : machine_state -> Prop) o (P : config -> Prop),
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R pc' m', ms = MState.MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
     (exists W, Frame.munch W (normalize rsegs mem) m' /\ Frame.wmono rsegs (normalize rsegs mem) m' /\
        (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
           (g_S g - SLOT_K <= x < g_S g - 104) \/ (img_w x /\ ~ in_globals frame_RELRO x))) /\
     getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4) ->
  (forall R pc' m0' regs' m', Q (MState.MS R fp_regs pc' fp_csr None m0' (seg_rom rsegs)) ->
     Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m' m0' ->
     FR B APIf ra empty g km hb L A regs' m' md ->
     SRO (ms_segs B) (mkCfg (mkst regs' pc' m' (seg_rom (ms_segs B))) md) o P) ->
  SRO (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) o P.
Proof.
  intros g km hb L A regs mem md pc Q o P HFR HP HE Hform HK.
  apply (SR_SRO_bind (ms_segs B) _ o (fun c' => SRO (ms_segs B) c' o P) P); [|intros c' Hc; exact Hc].
  apply (ss_mid g km hb L A regs mem md pc Q _ HFR HP HE Hform).
  intros R pc' m0' regs' m' HQ Hx Hrel HF'. apply SR_ret. exact (HK R pc' m0' regs' m' HQ Hx Hrel HF').
Qed.


(* The cut-free twins (agreement frame, SlotAgree.lib_contract_cg) of the run and allocator steps above: the same
   statements with SR -> SRcf and SRO -> SROcf, through the cut-free allocator contracts. room_cf at a malloc needs
   the slot's cap bound (sb_cap <= CAP_AG, the agreement shape) and the budget law LIMLAW. *)
Hypothesis HMALCF : forall fx' : YK11.FPState, @malloc_contract_cf fx' rc B (APIf rc).
Hypothesis HFREECF : forall fx' : YK11.FPState, @free_contract_cf fx' rc B (APIf rc).
Hypothesis LIMLAW : forall L A mem md, aa_MR (APIf rc) L A mem md -> SRC_LIM_MIN <= vm_limit (m_vmmaps md).

Lemma ss_run_cf : forall regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] -> ro_agree rsegs mem ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R pc' m', ms = MState.MS R fp_regs pc' fp_csr None m' (seg_rom rsegs)) ->
  (forall R pc' m0', Q (MState.MS R fp_regs pc' fp_csr None m0' (seg_rom rsegs)) ->
     forall regs' m', Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m' m0' -> ro_same rsegs mem m' ->
     SRcf B (mkCfg (mkst regs' pc' m' (seg_rom rsegs)) md) P) ->
  SRcf B (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md Q P Hh Hl Hro HE Hform HK.
  apply (evt_SRcf_canon B _ (fun s => exists s0, Q s0 /\ ms_rel rsegs s s0 /\ ro_same rsegs mem (ms_mem s)) md P);
    [| exact Hh | exact Hl |].
  - rewrite ss_segs.
    change (RegisterBridge.canonical_register_state (mkst regs pc mem (seg_rom rsegs)))
      with (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)).
    apply evt_normalize; [exact wx_apart_rsegs | exact Hro | exact HE].
  - intros ms' (can & (s0 & HQ & Hrel & Hsame) & Heq).
    destruct (Hform s0 HQ) as (R & pc' & m0' & ->).
    destruct can as [cr cf cp cs cv cc cm co].
    destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MState.MS] in *. subst.
    destruct (ss_eqv_mkfp R fp_regs pc' fp_csr cm (seg_rom rsegs) ms' Heq) as [Ems Hx].
    rewrite Ems, ss_mkFP.
    exact (HK R pc' m0' HQ _ cm Hx E8 Hsame).
Qed.

Lemma ss_kA_run_cf : forall (regs : bvmap 5 word) pc mem md (Q : bvmap 5 word -> word -> (word -> option byte) -> Prop) P,
  m_halted md = None -> m_vm_lazy md = [] -> ro_agree (ms_segs B) mem ->
  Exec.evt rsegs (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\ Q R pc' m')
    (MS (mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall R pc' m' regs' mem', Q R pc' m' -> xregs_eqv R regs' -> mem_rel rsegs mem' m' -> ro_same rsegs mem mem' ->
     SRcf B (mkCfg (mkst regs' pc' mem' (seg_rom (ms_segs B))) md) P) ->
  SRcf B (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros regs pc mem md Q P Hh Hl HRO HE HK.
  pose proof ss_segs as SEG.
  eapply (evt_SRcf_canon B (mkst regs pc mem (seg_rom (ms_segs B))) _ md P); [| exact Hh | exact Hl |].
  - rewrite ss_canon_mkst. rewrite SEG. apply (evt_normalize rsegs); [exact wx_apart_rsegs | rewrite <- SEG; exact HRO |].
    exact HE.
  - intros ms' (can & (s0 & (R & pc' & m' & -> & HQ) & Hrel & Hsame) & Heq).
    destruct can as [cR cF cpc csvc cres cfc cmem crom].
    destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & Hmr). cbn in E1, E2, E3, E4, E5, E6, E7, Hmr, Hsame.
    subst cR cF cpc csvc cres cfc crom.
    destruct (ss_eqv_mkst R pc' cmem (seg_rom rsegs) ms' Heq) as (R' & -> & XR).
    rewrite <- SEG. apply (HK R pc' m' R' cmem HQ XR Hmr Hsame).
Qed.

Lemma ss_kA_run0_cf : forall (regs : bvmap 5 word) pc mem md (Q : bvmap 5 word -> word -> (word -> option byte) -> Prop) P,
  m_halted md = None -> m_vm_lazy md = [] ->
  Exec.evt rsegs (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\ Q R pc' m')
    (MS (mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall R pc' m' regs', Q R pc' m' -> xregs_eqv R regs' ->
     SRcf B (mkCfg (mkst regs' pc' m' (seg_rom (ms_segs B))) md) P) ->
  SRcf B (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros regs pc mem md Q P Hh Hl HE HK.
  pose proof ss_segs as SEG.
  eapply (evt_SRcf_canon B (mkst regs pc mem (seg_rom (ms_segs B))) _ md P); [| exact Hh | exact Hl |].
  - rewrite ss_canon_mkst. rewrite SEG. exact HE.
  - intros ms' (can & (R & pc' & m' & -> & HQ) & Heq).
    destruct (ss_eqv_mkst R pc' m' (seg_rom rsegs) ms' Heq) as (R' & -> & XR).
    rewrite <- SEG. exact (HK R pc' m' R' HQ XR).
Qed.

Lemma ss_kA_run_o_cf : forall (regs : bvmap 5 word) pc mem md (Q : bvmap 5 word -> word -> (word -> option byte) -> Prop)
    o P,
  m_halted md = None -> m_vm_lazy md = [] -> ro_agree (ms_segs B) mem ->
  Exec.evt rsegs (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\ Q R pc' m')
    (MS (mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall R pc' m' regs' mem', Q R pc' m' -> xregs_eqv R regs' -> mem_rel rsegs mem' m' -> ro_same rsegs mem mem' ->
     SROcf (ms_segs B) (mkCfg (mkst regs' pc' mem' (seg_rom (ms_segs B))) md) o P) ->
  SROcf (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) o P.
Proof.
  intros regs pc mem md Q o P Hh Hl HRO HE HK.
  apply (SRcf_SROcf_bind B _ o (fun c' => SROcf (ms_segs B) c' o P) P); [|intros c' Hc; exact Hc].
  apply (ss_kA_run_cf regs pc mem md Q _ Hh Hl HRO HE).
  intros R pc' m' regs' mem' HQ XR Hr Hs. apply SRcf_ret. exact (HK R pc' m' regs' mem' HQ XR Hr Hs).
Qed.

Lemma ss_kA_run0_o_cf : forall (regs : bvmap 5 word) pc mem md
    (Q : bvmap 5 word -> word -> (word -> option byte) -> Prop) o P,
  m_halted md = None -> m_vm_lazy md = [] ->
  Exec.evt rsegs (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\ Q R pc' m')
    (MS (mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall R pc' m' regs', Q R pc' m' -> xregs_eqv R regs' ->
     SROcf (ms_segs B) (mkCfg (mkst regs' pc' m' (seg_rom (ms_segs B))) md) o P) ->
  SROcf (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) o P.
Proof.
  intros regs pc mem md Q o P Hh Hl HE HK.
  apply (SRcf_SROcf_bind B _ o (fun c' => SROcf (ms_segs B) c' o P) P); [|intros c' Hc; exact Hc].
  apply (ss_kA_run0_cf regs pc mem md Q _ Hh Hl HE).
  intros R pc' m' regs' HQ XR. apply SRcf_ret. exact (HK R pc' m' regs' HQ XR).
Qed.

Lemma ss_mid_cf : forall g km hb L A regs mem md pc (Q : machine_state -> Prop) (P : config -> Prop),
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R pc' m', ms = MState.MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
     (exists W, Frame.munch W (normalize rsegs mem) m' /\ Frame.wmono rsegs (normalize rsegs mem) m' /\
        (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
           (g_S g - SLOT_K <= x < g_S g - 104) \/ (img_w x /\ ~ in_globals frame_RELRO x))) /\
     getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4) ->
  (forall R pc' m0' regs' m', Q (MState.MS R fp_regs pc' fp_csr None m0' (seg_rom rsegs)) ->
     Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m' m0' ->
     FR B APIf ra empty g km hb L A regs' m' md ->
     SRcf B (mkCfg (mkst regs' pc' m' (seg_rom (ms_segs B))) md) P) ->
  SRcf B (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros g km hb L A regs mem md pc Q P HFR HP HE Hform HK.
  pose proof ss_segs as SEGS.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & HMI & _ & HM & _).
  unfold MI in HMI. rewrite SEGS in HMI.
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  apply (ss_run_cf regs pc mem md Q P Hh Hl HMI HE).
  - intros ms HQ. destruct (Hform ms HQ) as (R & pc' & m' & -> & _). exists R, pc', m'. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel Hsame.
    destruct (Hform _ HQ) as (R1 & pc1 & m1 & E & (W & MU & WM & HW) & E2 & E3 & E4).
    injection E; intros; subst.
    pose proof (mem_rel_normalize rsegs mem HMI) as HR0.
    rewrite <- SEGS. apply (HK R1 pc1 m1 regs' m' HQ Hx Hrel).
    apply (ss_fr_run g km hb L A regs mem md regs' m' W HFR HP).
    + exact (munch_rel rsegs W mem (normalize rsegs mem) m' m1 HR0 Hrel Hsame MU).
    + exact (wmono_rel rsegs mem (normalize rsegs mem) m' m1 HR0 Hrel Hsame WM).
    + exact HW.
    + rewrite (ss_getr_eqv _ _ _ Hx). exact E2.
    + rewrite (ss_getr_eqv _ _ _ Hx). exact E3.
    + rewrite (ss_getr_eqv _ _ _ Hx). exact E4.
Qed.

Lemma ss_mid_o_cf : forall g km hb L A regs mem md pc (Q : machine_state -> Prop) o (P : config -> Prop),
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R pc' m', ms = MState.MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
     (exists W, Frame.munch W (normalize rsegs mem) m' /\ Frame.wmono rsegs (normalize rsegs mem) m' /\
        (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
           (g_S g - SLOT_K <= x < g_S g - 104) \/ (img_w x /\ ~ in_globals frame_RELRO x))) /\
     getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4) ->
  (forall R pc' m0' regs' m', Q (MState.MS R fp_regs pc' fp_csr None m0' (seg_rom rsegs)) ->
     Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m' m0' ->
     FR B APIf ra empty g km hb L A regs' m' md ->
     SROcf (ms_segs B) (mkCfg (mkst regs' pc' m' (seg_rom (ms_segs B))) md) o P) ->
  SROcf (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) o P.
Proof.
  intros g km hb L A regs mem md pc Q o P HFR HP HE Hform HK.
  apply (SRcf_SROcf_bind B _ o (fun c' => SROcf (ms_segs B) c' o P) P); [|intros c' Hc; exact Hc].
  apply (ss_mid_cf g km hb L A regs mem md pc Q _ HFR HP HE Hform).
  intros R pc' m0' regs' m' HQ Hx Hrel HF'. apply SRcf_ret. exact (HK R pc' m0' regs' m' HQ Hx Hrel HF').
Qed.

Lemma ss_malloc_step_cf : forall g km hb L A regs mem md n o P,
  sb_cap (g_b g) <= CAP_AG ->
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  (length hb <= 16)%nat -> 0 <= hb_bytes hb <= 2 ^ 27 -> 0 <= n < 2 ^ 26 ->
  YK0s.ret_ok (getr regs 1) -> getr regs 10 = Z_to_bv 64 n -> stdio_ok mem ->
  (forall L' A' regs' mem' md' res,
     FR B APIf ra empty g (km + 1) (hb ++ [(res, n)]) L' A' regs' mem' md' ->
     Permutation (blocks L' A') ((hb ++ [(res, n)]) ++ blocks (g_L g) (g_A g)) ->
     regs_preserved regs regs' -> getr regs' 10 = Z_to_bv 64 res -> res <> 0 ->
     (forall x, fsp g <= x < g_S g -> mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x) ->
     (forall a k i, In (a, k) hb -> 0 <= i < k -> mbyte (ms_segs B) mem' (a + i) = mbyte (ms_segs B) mem (a + i)) ->
     (forall x, img_w x -> mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x) ->
     stdio_ok mem' -> guard_ok mem' ->
     SROcf (ms_segs B) (mkCfg (mkst regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md') o P) ->
  SROcf (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 (ms_malloc B)) mem (seg_rom (ms_segs B))) md) o P.
Proof.
  intros g km hb L A regs mem md n o P HCAP HF HP Hlen Hhb Hn HRA H10 HSTD HK.
  pose proof (ss_spZ _ _ _ _ _ _ _ _ HF) as SPZ.
  pose proof (ss_call_pre _ _ _ _ _ _ _ _ HF HRA) as CP.
  pose proof HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & HWF & HBD & HIN & Hmd & Hhi & Himg & HB0
    & Her & HRS & Hwin).
  pose proof HGV as (Hn0 & Hnp & Hblk & HS16 & HSc & HS47 & Hroom & _).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC. pose proof ss_errc as ERC.
  pose proof (resb_room_w (g_b g) hb n Hroom Hlen Hhb Hn) as ROOM.
  assert (ROOMCF : room_cf md (sb_hb (g_b g) hb) n).
  { pose proof Hroom as (_ & (HB1 & HB2) & (HC1 & HC2)).
    apply room_cf_slot; [exact ROOM | unfold sb_hb; cbn [sb_cap]; lia | unfold sb_hb; cbn [sb_bytes]; lia |
      exact (LIMLAW L A mem md HMR)]. }
  eapply (SRcf_SROcf_bind B); [exact (HMALCF fx L A regs mem md n (sb_hb (g_b g) hb) CP HMI H10 HRS ROOMCF)|].
  intros c' (L' & A' & regs' & mem' & md' & res & -> & HC & R10 & Hr0 & Hr16 & Hfr & (b1 & b2 & Eb' & Eb) & Hkept
    & HRO' & HGK & HUB & HIN' & HLEN & HRES').
  assert (HP' : Permutation (blocks L' A') ((hb ++ [(res, n)]) ++ blocks (g_L g) (g_A g))).
  { rewrite Eb', <- app_assoc. cbn [app].
    apply Permutation_trans with ((res, n) :: (b1 ++ b2)); [apply Permutation_sym, Permutation_middle|].
    rewrite <- Eb. apply Permutation_trans with ((res, n) :: hb ++ blocks (g_L g) (g_A g)); [apply perm_skip; exact HP|].
    apply Permutation_middle. }
  assert (HF' : FR B APIf ra empty g (km + 1) (hb ++ [(res, n)]) L' A' regs' mem' md').
  { apply (ss_FR_call g km hb L A regs mem md ALLOC_STACK (fun _ => False) L' A' regs' mem' md' (km + 1)
      (hb ++ [(res, n)]) HF).
    - unfold ALLOC_STACK, SLOT_K, SLOT_STACK, SLOT_FRAME. lia.
    - exact HC.
    - intros a [].
    - intros a _. right. intros [].
    - intros a [].
    - intros a k i Hin Hi. apply (Hkept a k i); [|intros []|exact Hi].
      apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. exact Hin.
    - exact HRO'.
    - exact HIN'.
    - exact (resb_malloc (g_b g) (km + 1) hb (hb ++ [(res, n)]) A' res n
               (Permutation_sym (Permutation_cons_append hb (res, n))) HRES'). }
  destruct HC as (MR'' & _ & _ & _ & _ & RP' & _ & FR' & _ & _).
  apply (HK L' A' regs' mem' md' res HF' HP' RP' R10 Hr0).
  - intros x Hx. unfold fsp, SLOT_FRAME in Hx. unfold SLOT_K, SLOT_STACK in HSc. apply FR'.
    + left. lia.
    + intros Ho. pose proof (mr_owned_low B MR ss_laws L A mem md x HMR Ho). lia.
    + intros Ho. pose proof (mr_owned_low B MR ss_laws L' A' mem' md' x MR'' Ho). lia.
    + unfold scratch_k. rewrite SPZ. unfold ALLOC_STACK. lia.
    + intros [].
  - intros a k i Hin Hi. apply (Hkept a k i); [|intros []|exact Hi].
    apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hin.
  - intros x Hx. destruct (ss_img_w_facts x Hx) as (Hi & Hs & Hc & He & Hl & _). unfold IMG_LO, IMG_HI in Hl.
    apply FR'.
    + right. exact Hi.
    + exact (ss_img_w_owned L A mem md x HMR Hx).
    + exact (ss_img_w_owned L' A' mem' md' x MR'' Hx).
    + unfold scratch_k. rewrite SPZ. unfold ALLOC_STACK, SLOT_K, SLOT_STACK in *. lia.
    + intros [].
  - refine (ss_stdio_keep L' A' mem mem' md' MR'' HSTD _).
    intros x Hx. destruct (ss_stdio_addr x Hx) as (Hi & Hs & Hc & He & Hl). unfold IMG_LO, IMG_HI in Hl.
    apply FR'.
    + right. exact Hi.
    + intros [Ho|Ho]; [exact (Hc (ax_img ss_ax L A mem md x HMR Hi Ho)) | exact (Hs Ho)].
    + intros [Ho|Ho]; [exact (Hc (ax_img ss_ax L' A' mem' md' x MR'' Hi Ho)) | exact (Hs Ho)].
    + unfold scratch_k. rewrite SPZ. unfold ALLOC_STACK, SLOT_K, SLOT_STACK in *. lia.
    + intros [].
  - exact (ss_guard_of_MR L' A' mem' md' MR'').
Qed.

Lemma ss_free_step_cf : forall g km hb1 a n hb2 L A regs mem md o P,
  FR B APIf ra empty g km (hb1 ++ (a, n) :: hb2) L A regs mem md ->
  Permutation (blocks L A) ((hb1 ++ (a, n) :: hb2) ++ blocks (g_L g) (g_A g)) ->
  YK0s.ret_ok (getr regs 1) -> getr regs 10 = Z_to_bv 64 a -> stdio_ok mem ->
  (forall L' A' regs' mem' md',
     FR B APIf ra empty g km (hb1 ++ hb2) L' A' regs' mem' md' ->
     Permutation (blocks L' A') ((hb1 ++ hb2) ++ blocks (g_L g) (g_A g)) ->
     regs_preserved regs regs' ->
     (forall x, fsp g <= x < g_S g -> mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x) ->
     (forall x, img_w x -> mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x) ->
     stdio_ok mem' -> guard_ok mem' ->
     SROcf (ms_segs B) (mkCfg (mkst regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md') o P) ->
  SROcf (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 (ms_free B)) mem (seg_rom (ms_segs B))) md) o P.
Proof.
  intros g km hb1 a n hb2 L A regs mem md o P HF HP HRA H10 HSTD HK.
  pose proof (ss_spZ _ _ _ _ _ _ _ _ HF) as SPZ.
  pose proof (ss_call_pre _ _ _ _ _ _ _ _ HF HRA) as CP.
  pose proof HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & HWF & HBD & HIN & Hmd & Hhi & Himg & HB0
    & Her & HRS & Hwin).
  pose proof HGV as (Hn0 & Hnp & Hblk & HS16 & HSc & HS47 & Hroom & _).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC. pose proof ss_errc as ERC.
  assert (HK0 : SLOT_K = 65536) by reflexivity.
  pose proof (Permutation_sym (Permutation_middle hb1 hb2 (a, n))) as HPm.
  assert (Hab : In (a, n) (blocks L A)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. apply in_or_app. right. left. reflexivity. }
  destruct (ss_blk_of L A a n Hab) as (p & Hp & Epa).
  destruct (mr_blocks_range B MR ss_laws L A mem md p n HMR Hp) as (Ha1 & Ha2). rewrite Epa in Ha1, Ha2.
  assert (HNa : forall k, In (a, k) (blocks (g_L g) (g_A g)) -> False).
  { intros k Hin.
    destruct ss_alloc as (_ & _ & _ & _ & _ & _ & _ & _ & ND & _).
    pose proof (proj1 (stdpp.base.NoDup_ListNoDup _) (ND L A mem md HMR)) as Hnd.
    pose proof (Permutation_map fst HP) as HPf. apply (Permutation_NoDup HPf) in Hnd.
    rewrite !map_app in Hnd. cbn [map fst] in Hnd. rewrite <- app_assoc in Hnd. cbn [app] in Hnd.
    apply NoDup_remove_2 in Hnd. apply Hnd.
    apply in_or_app. right. apply in_or_app. right. apply in_map_iff. exists (a, k). split; [reflexivity | exact Hin]. }
  eapply (SRcf_SROcf_bind B);
    [exact (HFREECF fx L A regs mem md p n (sb_hb (g_b g) (hb1 ++ (a, n) :: hb2)) CP HMI Hp ltac:(rewrite Epa; exact H10) HRS)|].
  intros c' (L' & A' & regs' & mem' & md' & -> & HC & (b1 & b2 & Eb & Eb') & Hkept & HRO' & HGK & HUB & HINi & HLEN
    & HRES').
  rewrite Epa in Eb, Hkept, HC.
  apply call_post_k_alloc in HC.
  assert (HP' : Permutation (blocks L' A') ((hb1 ++ hb2) ++ blocks (g_L g) (g_A g))).
  { rewrite Eb', <- app_assoc. apply (Permutation_app_inv _ _ _ _ (a, n)).
    rewrite <- Eb. rewrite <- app_assoc in HP. cbn [app] in HP. exact HP. }
  assert (HF' : FR B APIf ra empty g km (hb1 ++ hb2) L' A' regs' mem' md').
  { apply (ss_FR_call g km (hb1 ++ (a, n) :: hb2) L A regs mem md ALLOC_STACK (fun x => a <= x < a + n)
      L' A' regs' mem' md' km (hb1 ++ hb2) HF).
    - unfold ALLOC_STACK, SLOT_K, SLOT_STACK, SLOT_FRAME. lia.
    - exact HC.
    - intros x Hx. left. destruct (ss_blk_facts L A mem md a n (x - a) HMR Hab ltac:(lia)) as (_ & H2 & H3 & _ & H5).
      replace (a + (x - a)) with x in H5 by lia. split; [lia | exact H5].
    - intros x Hx. right. intros Hx'. unfold SLOT_K, SLOT_STACK in *. lia.
    - intros x Hx Hx'. exfalso. unfold SLOT_K, SLOT_STACK in *. lia.
    - intros a' k i Hin Hi. apply (Hkept a' k i); [| | exact Hi].
      + apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. exact Hin.
      + intros Ea. subst a'. exact (HNa k Hin).
    - exact HRO'.
    - exact (HINi HIN).
    - apply (resb_free (g_b g) km (hb1 ++ (a, n) :: hb2) (hb1 ++ hb2) A' a n HPm).
      exact HRES'. }
  destruct HC as (MR'' & _ & _ & _ & _ & RP' & _ & FR' & _ & _).
  apply (HK L' A' regs' mem' md' HF' HP' RP').
  - intros x Hx. unfold fsp, SLOT_FRAME in Hx. unfold SLOT_K, SLOT_STACK in HSc. apply FR'.
    + left. lia.
    + intros Ho. pose proof (mr_owned_low B MR ss_laws L A mem md x HMR Ho). lia.
    + intros Ho. pose proof (mr_owned_low B MR ss_laws L' A' mem' md' x MR'' Ho). lia.
    + unfold scratch, scratch_k. rewrite SPZ. unfold ALLOC_STACK. lia.
    + cbn. lia.
  - intros x Hx. destruct (ss_img_w_facts x Hx) as (Hi & Hs & Hc & He & Hl & _). unfold IMG_LO, IMG_HI in Hl.
    apply FR'.
    + right. exact Hi.
    + exact (ss_img_w_owned L A mem md x HMR Hx).
    + exact (ss_img_w_owned L' A' mem' md' x MR'' Hx).
    + unfold scratch, scratch_k. rewrite SPZ. unfold ALLOC_STACK. lia.
    + cbn. intros Hx'.
      destruct (ss_blk_facts L A mem md a n (x - a) HMR Hab ltac:(lia)) as (_ & _ & _ & _ & H5).
      replace (a + (x - a)) with x in H5 by lia. exact (H5 Hi).
  - refine (ss_stdio_keep L' A' mem mem' md' MR'' HSTD _).
    intros x Hx. destruct (ss_stdio_addr x Hx) as (Hi & Hs & Hc & He & Hl). unfold IMG_LO, IMG_HI in Hl.
    apply FR'.
    + right. exact Hi.
    + intros [Ho|Ho]; [exact (Hc (ax_img ss_ax L A mem md x HMR Hi Ho)) | exact (Hs Ho)].
    + intros [Ho|Ho]; [exact (Hc (ax_img ss_ax L' A' mem' md' x MR'' Hi Ho)) | exact (Hs Ho)].
    + unfold scratch, scratch_k. rewrite SPZ. unfold ALLOC_STACK. lia.
    + cbn. intros Hx'.
      destruct (ss_blk_facts L A mem md a n (x - a) HMR Hab ltac:(lia)) as (_ & _ & _ & _ & H5).
      replace (a + (x - a)) with x in H5 by lia. exact (H5 Hi).
  - exact (ss_guard_of_MR L' A' mem' md' MR'').
Qed.

End T.

Lemma ss_FReq_munch : forall g W (mem mem' : word -> option byte), munch W mem mem' ->
  (forall lo hi y, In (lo, hi) W -> lo <= y < hi -> y < fsp g \/ g_S g <= y) -> 0 <= fsp g -> g_S g <= 2 ^ 64 ->
  forall x, fsp g <= x < g_S g -> mbyte rsegs mem' x = mbyte rsegs mem x.
Proof.
  intros g W mem mem' Hm HW H0 H1 x Hx. unfold mbyte.
  rewrite (ss_munch_unch (fun y => y < fsp g \/ g_S g <= y) W mem mem' Hm HW x ltac:(lia) ltac:(cbv beta; lia)).
  reflexivity.
Qed.

Lemma ss_nowrite : forall (mem mem' : word -> option byte),
  mem_rel rsegs mem' (normalize rsegs mem) -> ro_same rsegs mem mem' -> forall w, mem' w = mem w.
Proof.
  intros mem mem' Hr Hs w. destruct (Mem.ro_addr rsegs w) eqn:E.
  - exact (Hs w E).
  - rewrite <- (mem_rel_rw rsegs mem' (normalize rsegs mem) w Hr E). unfold normalize. rewrite E. reflexivity.
Qed.

Lemma ss_wmono_eq : forall (mem mem' : word -> option byte), (forall w, mem' w = mem w) -> wmono rsegs mem mem'.
Proof. intros mem mem' H x Hx. unfold wview in *. rewrite H. exact Hx. Qed.

Definition CSeq (regs regs' : bvmap 5 word) : Prop :=
  forall r, callee_saved r -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Definition FReq (g : ghost) (mem mem' : word -> option byte) : Prop :=
  forall x, fsp g <= x < g_S g -> mbyte rsegs mem' x = mbyte rsegs mem x.

Lemma ss_CSeq_trans : forall r1 r2 r3, CSeq r1 r2 -> CSeq r2 r3 -> CSeq r1 r3.
Proof. intros r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.

Lemma ss_CSeq_pres : forall r1 r2, regs_preserved r1 r2 -> CSeq r1 r2.
Proof. intros r1 r2 H. exact H. Qed.

Lemma ss_FReq_trans : forall g m1 m2 m3, FReq g m1 m2 -> FReq g m2 m3 -> FReq g m1 m3.
Proof. intros g m1 m2 m3 H1 H2 x Hx. rewrite (H2 x Hx). exact (H1 x Hx). Qed.

Lemma ss_FReq_eq : forall g (m1 m2 : word -> option byte), (forall w, m2 w = m1 w) -> FReq g m1 m2.
Proof. intros g m1 m2 H x Hx. unfold mbyte. rewrite H. reflexivity. Qed.

Lemma ss_fbytes : forall g (mem mem' : word -> option byte) k l, FReq g mem mem' ->
  0 <= k -> k + Z.of_nat (length l) <= SLOT_FRAME -> bytes_at rsegs mem (spk g k) l -> bytes_at rsegs mem' (spk g k) l.
Proof.
  intros g mem mem' k l H Hk Hl Hb. apply (ss_bytes_mbyte rsegs mem mem'); [|exact Hb].
  intros i Hi. apply H. unfold spk, fsp, SLOT_FRAME in *. lia.
Qed.

Lemma ss_q64_tr : forall g mem mem' k v, FReq g mem mem' -> 0 <= k <= SLOT_FRAME - 8 ->
  q64 mem (spk g k) v -> q64 mem' (spk g k) v.
Proof. intros g mem mem' k v H Hk Hb. apply (ss_fbytes g mem mem' k); [exact H | lia | rewrite length_le8; lia | exact Hb]. Qed.

Ltac ss_cs CS k := etransitivity; [exact (CS k ltac:(unfold callee_saved; lia))|].

Ltac ss_cs_split r Hr :=
  unfold callee_saved in Hr;
  let Hr' := fresh "Hr" in
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| -> ]]]]]]]]]]]]]].

Lemma ss_eqb : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite (unsigned_lit x Hx), (unsigned_lit y Hy). reflexivity. Qed.

Lemma ss_ltu : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite (unsigned_lit x Hx), (unsigned_lit y Hy). reflexivity. Qed.

Lemma ss_lts : forall x y, -2 ^ 63 <= x < 2 ^ 63 -> -2 ^ 63 <= y < 2 ^ 63 ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
  intros x y Hx Hy. unfold bv_lts. rewrite !Z_to_bv_signed.
  rewrite !bv_swrap_small by (unfold bv_half_modulus, bv_modulus; cbn; lia). reflexivity.
Qed.

Lemma ss_byte_eq : forall (b : byte) z, z mod 256 = bv_unsigned b -> Z_to_bv 8 z = b.
Proof.
  intros b z H. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  exact H.
Qed.

Lemma ss_bz_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. exact H. Qed.

Lemma ss_le2 : forall b0 b1 : byte,
  le2 (Z_to_bv 64 (bv_unsigned b0 + 256 * bv_unsigned b1)) = [b0; b1].
Proof.
  intros b0 b1. pose proof (ss_bz_range b0). pose proof (ss_bz_range b1).
  unfold le2. rewrite (unsigned_lit _) by lia. cbn [Z_to_le_bytes].
  f_equal; [apply ss_byte_eq; Z.div_mod_to_equations; lia|]. f_equal.
  apply ss_byte_eq. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. Z.div_mod_to_equations; lia.
Qed.

Lemma ss_zx16 : forall v, 0 <= v < 2 ^ 16 -> zx16 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof. intros v Hv. unfold zx16. rewrite (unsigned_lit v) by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma ss_lor8 : forall lo hi, 0 <= lo < 256 -> 0 <= hi < 256 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 hi)) 8))) (bv_unsigned (Z_to_bv 64 lo))) =
  Z_to_bv 64 (lo + 256 * hi).
Proof.
  intros lo hi Hl Hh. rewrite (unsigned_lit hi) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  rewrite (unsigned_lit (hi * 256)) by lia. rewrite (unsigned_lit lo) by lia.
  rewrite (KindBGlue.kb_lor_low (hi * 256) lo 8) by (try lia; change (2 ^ 8) with 256; Z.div_mod_to_equations; lia).
  f_equal. lia.
Qed.

Definition KP (l : list Z) (regs regs' : bvmap 5 word) : Prop :=
  forall k, In k l -> getr regs' (Z_to_bv 5 k) = getr regs (Z_to_bv 5 k).

Ltac ss_kp XR regs :=
  let k := fresh "k" in let Hk := fresh "Hk" in
  intros k Hk; cbn [In] in Hk;
  repeat (destruct Hk as [<-|Hk];
          [rewrite (ss_getr_x _ _ _ XR) by reflexivity; rewrite (ss_getr_reg regs) by reflexivity; reflexivity|]);
  destruct Hk.

Ltac ss_in := cbn [In]; repeat (first [left; reflexivity | right]).

Ltac ss_k KP k := etransitivity; [exact (KP k ltac:(ss_in))|].

Lemma ss_KP_CSeq : forall regs regs1, KP [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs regs1 ->
  CSeq regs regs1.
Proof. intros regs regs1 H r Hr. ss_cs_split r Hr; apply H; ss_in. Qed.

Lemma ss_bytes_munch1 : forall lo hi (m m' : word -> option byte) a bs, munch [(lo, hi)] m m' ->
  (a + Z.of_nat (length bs) <= lo \/ hi <= a) -> bytes_at rsegs m a bs -> bytes_at rsegs m' a bs.
Proof.
  intros lo hi m m' a bs H Hd HB. pose proof HB as (B1 & B2 & _).
  apply (ss_bytes_same rsegs m m' a bs); [|exact HB]. intros i Hi. apply H.
  rewrite unsigned_lit by lia. cbn [outside]. split; [lia | exact I].
Qed.

Lemma ss_bytes_munchP : forall (P : Z -> Prop) W (m m' : word -> option byte) a bs, munch W m m' ->
  (forall lo hi y, In (lo, hi) W -> lo <= y < hi -> P y) ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> ~ P (a + i)) -> bytes_at rsegs m a bs -> bytes_at rsegs m' a bs.
Proof.
  intros P W m m' a bs MU HW HN HB. pose proof HB as (B1 & B2 & _).
  apply (ss_bytes_same rsegs m m' a bs); [|exact HB]. intros i Hi.
  apply (ss_munch_unch P W m m' MU HW); [lia | exact (HN i Hi)].
Qed.

Fixpoint ss_rd_list (mem : word -> option byte) (a : Z) (k : nat) : list byte :=
  match k with
  | O => []
  | S k' => (match mem (Z_to_bv 64 a) with Some b => b | None => z8 end) :: ss_rd_list mem (a + 1) k'
  end.

Lemma ss_rd_list_len : forall mem k a, length (ss_rd_list mem a k) = k.
Proof. intros mem k. induction k as [|k IH]; intros a; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma ss_rd_list_nth : forall mem k a j, (j < k)%nat ->
  nth_error (ss_rd_list mem a k) j =
  Some (match mem (Z_to_bv 64 (a + Z.of_nat j)) with Some b => b | None => z8 end).
Proof.
  intros mem k. induction k as [|k IH]; intros a j Hj; [lia|].
  destruct j as [|j]; cbn [ss_rd_list nth_error].
  - rewrite Z.add_0_r. reflexivity.
  - rewrite IH by lia. replace (a + 1 + Z.of_nat j) with (a + Z.of_nat (S j)) by lia. reflexivity.
Qed.

Lemma ss_wr_norm : forall m a n, IMG_HI <= a -> a + n <= 2 ^ 64 -> wr_at rsegs m a n ->
  wr_at rsegs (normalize rsegs m) a n.
Proof.
  intros m a n Ha Hn (H1 & H2 & H). split; [lia|]. split; [lia|]. intros i Hi.
  assert (Hro : Mem.ro_addr rsegs (wa (a + i)) = false).
  { unfold Mem.ro_addr. rewrite wa_unsigned by lia. rewrite ss_fs_none by lia. reflexivity. }
  unfold wview, normalize. rewrite Hro. apply H. exact Hi.
Qed.

Lemma ss_wr_sub : forall m a n a' n', wr_at rsegs m a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' ->
  wr_at rsegs m a' n'.
Proof.
  intros m a n a' n' (H1 & H2 & H) Ha Hb Hn. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply H. lia.
Qed.

Lemma ss_ro_write : forall m a bs, ro_agree rsegs m -> IMG_HI <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  ro_agree rsegs (write_to_mem m (wa a) bs).
Proof.
  intros m a bs H Ha Hl w Hw. pose proof (ss_ro_lt w Hw) as Hlt. unfold IMG_LO, IMG_HI in *.
  unfold mrd. rewrite write_to_mem_spec by lia.
  destruct (_ && _)%bool eqn:E; [apply andb_prop in E as [E1 _]; apply Z.leb_le in E1; lia|].
  exact (H w Hw).
Qed.

Lemma ss_rd_q64 : forall m a v, bytes_at rsegs m a (le8 v) -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 v).
Proof.
  intros m a v H. rewrite <- (Z.add_0_r a) at 1.
  rewrite (bytes_at_read rsegs m a (le8 v) 0 8 H) by (rewrite ?length_le8; lia).
  cbn [Z.to_nat skipn]. rewrite <- (length_le8 v) at 1. rewrite firstn_all. reflexivity.
Qed.

Ltac ss_subfp := let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [outside] in *; repeat split; lia.

Section T2.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf SH SK ra empty.

Lemma ss_FReq_hb : forall g km hb L A regs mem md (mem' : word -> option byte),
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ in_hb hb x -> mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) ->
  FReq g mem mem'.
Proof.
  intros g km hb L A regs mem md mem' HF HP HU x Hx.
  pose proof HF as (HGV & _). pose proof HGV as (_ & _ & _ & _ & HSc & HS47 & _).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC.
  unfold fsp, SLOT_FRAME, SLOT_K, SLOT_STACK in *.
  unfold mbyte. rewrite HU; [reflexivity | lia |].
  intros Hh. pose proof (ss_hb_low B APIf ra empty FF g km hb L A regs mem md x HF HP Hh) as (_ & H2).
  unfold SLOT_K, SLOT_STACK in H2. lia.
Qed.

Lemma ss_FR_hb : forall g km hb L A regs mem md regs' (mem' : word -> option byte),
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  KP [2; 3; 4] regs regs' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ in_hb hb x -> mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) ->
  wmono rsegs mem mem' ->
  FR B APIf ra empty g km hb L A regs' mem' md.
Proof.
  intros g km hb L A regs mem md regs' mem' HF HP C HU HW.
  apply (ss_FR_kA B APIf ra empty FF g km hb L A regs mem md regs' mem' HF HP).
  - exact (C 2 ltac:(ss_in)).
  - exact (C 3 ltac:(ss_in)).
  - exact (C 4 ltac:(ss_in)).
  - intros x Hx Hk. apply HU; [exact Hx|]. intros Hh. apply Hk. right. left. exact Hh.
  - exact HW.
Qed.

Lemma ss_slack : forall L A mem md p n s, aa_MR (APIf rc) L A mem md -> In (p, n) (blocks L A) ->
  cstr mem p s -> Z.of_nat (length s) + 1 <= n ->
  exists slack, bytes_at rsegs mem p (s ++ z8 :: slack) /\
    (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack) /\
    p + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= alloc_ceiling.
Proof.
  intros L A mem md p n s HM Hin HC Hn.
  assert (HSL : block_slack_present B (APIf rc)).
  { destruct (ss_alloc B APIf ra empty FF) as (_ & _ & _ & _ & _ & H & _). exact H. }
  destruct (ss_blk_facts B APIf ra empty FF L A mem md p n 0 HM Hin ltac:(lia)) as (_ & B1 & B2 & _).
  pose proof (@YM05.alloc_ceiling_val rc) as [AC1 AC2].
  set (x := p + Z.of_nat (length s) + 1).
  set (e := 8 * ((p + n + 7) / 8)).
  assert (He1 : p + n <= e) by (unfold e; Z.div_mod_to_equations; lia).
  assert (He2 : e <= alloc_ceiling) by (unfold e; Z.div_mod_to_equations; lia).
  assert (PR : forall a, x <= a < e -> present mem a).
  { intros a Ha. destruct (Z_lt_le_dec a (p + n)) as [Hlt|Hge].
    - replace a with (p + (a - p)) by lia.
      exact (proj1 (ss_blk_facts B APIf ra empty FF L A mem md p n (a - p) HM Hin ltac:(unfold x in Ha; lia))).
    - exact (HSL L A mem md p n a HM Hin ltac:(unfold e in Ha; lia)). }
  exists (ss_rd_list mem x (Z.to_nat (e - x))). rewrite ss_rd_list_len.
  destruct HC as (C1 & C2 & C3). rewrite length_app in C2. cbn [length] in C2.
  split; [| split; [fold x; Z.div_mod_to_equations; lia | fold x; lia]].
  split; [lia|]. split; [rewrite length_app; cbn [length]; rewrite ss_rd_list_len; lia|].
  intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. rewrite ss_rd_list_len in Hi.
  replace (s ++ z8 :: ss_rd_list mem x (Z.to_nat (e - x))) with ((s ++ [z8]) ++ ss_rd_list mem x (Z.to_nat (e - x)))
    by (rewrite <- app_assoc; reflexivity).
  destruct (Nat.lt_ge_cases i (length s + 1)) as [Hl|Hl].
  - rewrite nth_error_app1 by (rewrite length_app; cbn [length]; lia). apply C3. rewrite length_app. cbn. lia.
  - rewrite nth_error_app2 by (rewrite length_app; cbn [length]; lia). rewrite length_app. cbn [length].
    rewrite ss_rd_list_nth by lia.
    destruct (PR (p + Z.of_nat i) ltac:(unfold x; lia)) as [b Hb].
    replace (x + Z.of_nat (i - (length s + 1))) with (p + Z.of_nat i) by (unfold x; lia).
    unfold mrd, wa. rewrite Hb. reflexivity.
Qed.

Lemma ss_stk_fsp : forall g km hb L A regs mem md, FR B APIf ra empty g km hb L A regs mem md ->
  stk rsegs mem (g_S g - SLOT_K) (fsp g) /\ IMG_HI <= g_S g - SLOT_K /\ g_S g - SLOT_K + 8192 <= fsp g /\
  fsp g + 176 = g_S g /\ alloc_ceiling + SLOT_K <= g_S g /\ g_S g <= 2 ^ 47 /\ SLOT_K = 65536 /\
  getr regs 2 = Z_to_bv 64 (fsp g).
Proof.
  intros g km hb L A regs mem md HF.
  pose proof HF as (HGV & Hsp & _ & _ & _ & Hstk & _). pose proof HGV as (_ & _ & _ & _ & HSc & HS47 & _).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC. assert (HK : SLOT_K = 65536) by reflexivity.
  unfold fsp, SLOT_FRAME, IMG_HI in *.
  split; [exact (proj1 (stk_split rsegs mem _ (g_S g - 176) _ Hstk ltac:(lia)))|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [exact HSc|]. split; [exact HS47|]. split; [exact HK|].
  exact Hsp.
Qed.

End T2.

Fixpoint ss_ro_chk (a : Z) (bs : list byte) : bool :=
  match bs with
  | [] => true
  | b :: r => Mem.ro_addr rsegs (Z_to_bv 64 a) &&
              match seg_rom rsegs (Z_to_bv 64 a) with Some b' => bv_eqb b' b | None => false end &&
              ss_ro_chk (a + 1) r
  end.

Lemma ss_ro_chk_ok : forall bs a, ss_ro_chk a bs = true -> forall i, (i < length bs)%nat ->
  Mem.ro_addr rsegs (Z_to_bv 64 (a + Z.of_nat i)) = true /\
  seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i)) = nth_error bs i.
Proof.
  induction bs as [|b r IH]; intros a H i Hi; cbn [Datatypes.length] in Hi; [lia|].
  cbn [ss_ro_chk] in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  destruct i as [|i].
  - rewrite Z.add_0_r. split; [exact H1|]. cbn [nth_error]. revert H2.
    destruct (seg_rom rsegs (Z_to_bv 64 a)) as [b'|]; intros H2; [|discriminate H2].
    f_equal. apply bv_eq. unfold bv_eqb in H2. apply Z.eqb_eq. exact H2.
  - destruct (IH (a + 1) H3 i ltac:(lia)) as [E1 E2].
    replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. split; [exact E1 | exact E2].
Qed.

Lemma ss_ro_chk_bytes : forall m a bs, ro_agree rsegs m -> ss_ro_chk a bs = true -> 0 <= a ->
  a + Z.of_nat (length bs) <= 2 ^ 64 -> bytes_at rsegs m a bs.
Proof.
  intros m a bs HR H Ha Hl. split; [exact Ha|]. split; [exact Hl|]. intros i Hi.
  destruct (ss_ro_chk_ok bs a H i Hi) as [E1 E2]. unfold wa. rewrite (HR _ E1). exact E2.
Qed.

Definition ss_rom_list (a : Z) (k : nat) : list byte :=
  map (fun i => match seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i)) with Some b => b | None => z8 end) (seq 0 k).

Lemma ss_rom_list_len : forall a k, length (ss_rom_list a k) = k.
Proof. intros a k. unfold ss_rom_list. rewrite length_map, length_seq. reflexivity. Qed.

Lemma ss_ro_agree_norm : forall m, ro_agree rsegs (normalize rsegs m).
Proof. intros m a H. unfold mrd, normalize. rewrite H. reflexivity. Qed.

Fixpoint ss_rel_chk (a : Z) (bs : list byte) : bool :=
  match bs with
  | [] => true
  | b :: r => match seg_rom rsegs (Z_to_bv 64 a) with Some b' => bv_eqb b' b | None => false end &&
              ss_rel_chk (a + 1) r
  end.

Lemma ss_rel_chk_ok : forall bs a, ss_rel_chk a bs = true -> forall i, (i < length bs)%nat ->
  seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i)) = nth_error bs i.
Proof.
  induction bs as [|b r IH]; intros a H i Hi; cbn [Datatypes.length] in Hi; [lia|].
  cbn [ss_rel_chk] in H. apply andb_prop in H as [H2 H3].
  destruct i as [|i].
  - rewrite Z.add_0_r. cbn [nth_error]. revert H2.
    destruct (seg_rom rsegs (Z_to_bv 64 a)) as [b'|]; intros H2; [|discriminate H2].
    f_equal. apply bv_eq. unfold bv_eqb in H2. apply Z.eqb_eq. exact H2.
  - replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. exact (IH (a + 1) H3 i ltac:(lia)).
Qed.
