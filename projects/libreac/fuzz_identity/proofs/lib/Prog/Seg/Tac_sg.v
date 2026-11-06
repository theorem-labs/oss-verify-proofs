From Stdlib Require Import ZArith List Bool Lia Permutation String.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Tac.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require reac_box_family_of_c reac_box_family_stem_c.
Import ListNotations.
Open Scope Z_scope.

Definition rmk (regs : bvmap 5 word) : bvmap 5 word :=
  Frame.mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
    (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
    (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
    (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
    (getr regs 29) (getr regs 30) (getr regs 31).

Lemma sg_getr_eqv : forall R R', Regs6ss.xregs_eqv R R' -> forall r, getr R' r = getr R r.
Proof.
  intros R R' H r. unfold getr. destruct (bv_eqb r 0) eqn:E; [reflexivity|].
  symmetry. apply H. rewrite <- bv_eqb0_is_x0. exact E.
Qed.

Lemma sg_rmk_getr : forall regs r, getr (rmk regs) r = getr regs r.
Proof. intros regs r. apply sg_getr_eqv. exact (Regs6ss.mkR_of_eqv regs). Qed.

Lemma sg_find_segment : forall (l : list Segment) x n seg, find_segment l x n = Some seg ->
  In seg l /\ Z.of_N (seg_base seg) <= x /\ x + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  induction l as [|s l IH]; intros x n seg H; cbn in H; [discriminate|].
  match type of H with context [if ?c then _ else _] => destruct c eqn:E end.
  - injection H as <-. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1, E2.
    split; [left; reflexivity | lia].
  - destruct (IH x n seg H) as (H1 & H2). split; [right; exact H1 | exact H2].
Qed.

Lemma sg_outside_dec : forall W x, {outside W x} + {~ outside W x}.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn; [left; exact I|].
  destruct (Z_le_gt_dec lo x) as [H1|H1]; [destruct (Z_lt_ge_dec x hi) as [H2|H2]|].
  - right. intros [H _]. lia.
  - destruct (IH x) as [H|H]; [left; split; [lia | exact H] | right; intros [_ H']; exact (H H')].
  - destruct (IH x) as [H|H]; [left; split; [lia | exact H] | right; intros [_ H']; exact (H H')].
Qed.

Lemma sg_outside_app : forall W1 W2 x, outside (W1 ++ W2) x -> outside W1 x /\ outside W2 x.
Proof.
  induction W1 as [|[lo hi] W1 IH]; intros W2 x H; cbn in *; [split; [exact I | exact H]|].
  destruct H as [H1 H2]. destruct (IH W2 x H2) as [H3 H4]. split; [split; assumption | exact H4].
Qed.

Lemma sg_munch_cat : forall W1 W2 m m1 m2, munch W1 m m1 -> munch W2 m1 m2 -> munch (W1 ++ W2) m m2.
Proof.
  intros W1 W2 m m1 m2 H1 H2 x Hx. destruct (sg_outside_app W1 W2 _ Hx) as [Ha Hb].
  rewrite (H2 x Hb). apply H1. exact Ha.
Qed.

Lemma sg_with_vmmaps_twice : forall vm vm' md, with_vmmaps vm' (with_vmmaps vm md) = with_vmmaps vm' md.
Proof. intros vm vm' [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma sg_fds_with_vmmaps : forall vm md, m_fds (with_vmmaps vm md) = m_fds md.
Proof. intros vm [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma sg_segs_low : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 2 ^ 20) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sg_res_low : forallb (fun s => bv_unsigned (fst s) + bv_unsigned (snd s) <=? 2 ^ 20) (segments_reserved rsegs) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sg_res_cover : forallb (fun s =>
    (bv_unsigned (fst (segment_reservation s)) <=? Z.of_N (seg_base s)) &&
    (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=?
       bv_unsigned (fst (segment_reservation s)) + bv_unsigned (snd (segment_reservation s)))) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sg_rsegs_nil : rsegs <> [].
Proof. intros H. pose proof (f_equal (@length Segment) H) as L. vm_compute in L. discriminate L. Qed.

Lemma sg_seg_low : forall x seg, find_segment rsegs x 1 = Some seg -> 0 <= x < 2 ^ 20.
Proof.
  intros x seg H. destruct (sg_find_segment rsegs x 1 seg H) as (Hin & H1 & H2).
  pose proof sg_segs_low as L. rewrite forallb_forall in L. specialize (L seg Hin). apply Z.leb_le in L. lia.
Qed.

Lemma sg_noseg_high : forall x, 2 ^ 20 <= x -> find_segment rsegs x 1 = None.
Proof.
  intros x Hx. destruct (find_segment rsegs x 1) as [seg|] eqn:E; [|reflexivity].
  apply sg_seg_low in E. lia.
Qed.

Lemma sg_range_seg : forall lo hi,
  existsb (fun s => (Z.of_N (seg_base s) <=? lo) && (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs = true ->
  forall x, lo <= x < hi -> exists seg, find_segment rsegs x 1 = Some seg.
Proof.
  intros lo hi H x Hx. apply existsb_exists in H as (s & Hs & Hc).
  apply andb_prop in Hc as [C1 C2]. apply Z.leb_le in C1, C2.
  destruct (find_segment rsegs x 1) as [seg|] eqn:E; [exists seg; reflexivity|].
  exfalso. apply (find_segment_some rsegs s x 1 Hs); [lia | lia | exact E].
Qed.

Definition relro_b (a : Z) : bool :=
  ((0x1de98 <=? a) && (a <? 0x1de98 + 3440)) || ((0x1ec10 <=? a) && (a <? 0x1ec10 + 16)).

Definition opt_byte_eqb (o : option byte) (b : byte) : bool :=
  match o with Some b' => bv_eqb b' b | None => false end.

Fixpoint img_chk (a : Z) (bs : list byte) : bool :=
  match bs with
  | [] => true
  | b :: r => (ro_addr rsegs (Z_to_bv 64 a) || relro_b a) && opt_byte_eqb (seg_rom rsegs (Z_to_bv 64 a)) b &&
              img_chk (a + 1) r
  end.

Lemma relro_b_ok : forall a, relro_b a = true -> in_globals frame_RELRO a.
Proof.
  intros a H. unfold relro_b in H. apply orb_true_iff in H as [H|H]; apply andb_prop in H as [H1 H2];
    apply Z.leb_le in H1; apply Z.ltb_lt in H2.
  - exists 0x1de98, 3440. split; [left; reflexivity | lia].
  - exists 0x1ec10, 16. split; [right; left; reflexivity | lia].
Qed.

Lemma img_chk_ok : forall bs a, img_chk a bs = true -> forall i, (i < length bs)%nat ->
  (ro_addr rsegs (Z_to_bv 64 (a + Z.of_nat i)) = true \/ in_globals frame_RELRO (a + Z.of_nat i)) /\
  seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i)) = nth_error bs i.
Proof.
  induction bs as [|b r IH]; intros a H i Hi; cbn [length] in Hi; [lia|].
  cbn [img_chk] in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  destruct i as [|i].
  - rewrite Z.add_0_r. split.
    + apply orb_true_iff in H1 as [E|E]; [left; exact E | right; apply relro_b_ok; exact E].
    + unfold opt_byte_eqb in H2. destruct (seg_rom rsegs (Z_to_bv 64 a)) as [b'|]; [|discriminate].
      unfold bv_eqb in H2. apply Z.eqb_eq in H2. cbn. f_equal. apply bv_eq. exact H2.
  - destruct (IH (a + 1) H3 i ltac:(lia)) as [E1 E2].
    replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (S i)) in E1, E2 by lia. split; [exact E1 | exact E2].
Qed.

Fixpoint relro_chk (a : Z) (bs : list byte) : bool :=
  match bs with
  | [] => true
  | b :: r => relro_b a && opt_byte_eqb (seg_rom rsegs (Z_to_bv 64 a)) b && relro_chk (a + 1) r
  end.

Lemma relro_chk_ok : forall bs a, relro_chk a bs = true -> forall i, (i < length bs)%nat ->
  in_globals frame_RELRO (a + Z.of_nat i) /\ seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i)) = nth_error bs i.
Proof.
  induction bs as [|b r IH]; intros a H i Hi; cbn [length] in Hi; [lia|].
  cbn [relro_chk] in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  destruct i as [|i].
  - rewrite Z.add_0_r. split; [apply relro_b_ok; exact H1|].
    unfold opt_byte_eqb in H2. destruct (seg_rom rsegs (Z_to_bv 64 a)) as [b'|]; [|discriminate].
    unfold bv_eqb in H2. apply Z.eqb_eq in H2. cbn. f_equal. apply bv_eq. exact H2.
  - destruct (IH (a + 1) H3 i ltac:(lia)) as [E1 E2].
    replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (S i)) in E1, E2 by lia. split; [exact E1 | exact E2].
Qed.

Lemma sg_ro_rsegs_high : forall x, 2 ^ 20 <= x < 2 ^ 64 -> Mem.ro_addr rsegs (Z_to_bv 64 x) = false.
Proof.
  intros x Hx. unfold Mem.ro_addr. rewrite MState.unsigned_lit by lia. rewrite sg_noseg_high by lia. reflexivity.
Qed.

Lemma sg_stk_norm : forall m lo hi, stk rsegs m lo hi -> 2 ^ 20 <= lo -> stk rsegs (normalize rsegs m) lo hi.
Proof.
  intros m lo hi (H1 & H2 & H) Hlo. split; [lia|]. split; [lia|]. intros a Ha. destruct (H a Ha) as [Hw (b & Hb)].
  assert (E : normalize rsegs m (wa a) = m (wa a)) by (unfold normalize, wa; rewrite sg_ro_rsegs_high by lia; reflexivity).
  split; [unfold wview; rewrite E; exact Hw | exists b; unfold mrd; rewrite E; exact Hb].
Qed.

Lemma sg_ba_win : forall m m' a bs lo hi, bytes_at rsegs m a bs -> munch [(lo, hi)] m m' ->
  a + Z.of_nat (length bs) <= lo \/ hi <= a -> bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs lo hi H Hm Hd. apply (bytes_at_transport rsegs [(lo, hi)] m m' a bs H Hm). cbn. split; [exact Hd | exact I].
Qed.

Lemma sg_famof : forall id idb, id <> 0 -> reac_box_family_of_c.FAMOF_FAM id idb = FAM idb.
Proof. intros id idb H. unfold FAM, reac_box_family_of_c.FAMOF_FAM. destruct (Z.eqb_spec id 0); [lia|]. reflexivity. Qed.

Lemma sg_FAM_range : forall idb, 0 <= FAM idb <= 3.
Proof.
  intros idb. unfold FAM, reac_box_family_of_c.FAMOF_FAM.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia.
Qed.

Lemma sg_nfam_range : forall inp, 0 <= n_fam inp <= 127.
Proof.
  intros inp. unfold n_fam. destruct (128 <=? t_fam_raw inp).
  - pose proof (inb_range inp (cT inp + 0)) as R.
    replace (Z.land (t_fam_raw inp) 127) with (t_fam_raw inp mod 128)
      by (change 127 with (Z.ones 7); rewrite Z.land_ones by lia; reflexivity).
    pose proof (Z.mod_pos_bound (t_fam_raw inp) 128 ltac:(lia)). lia.
  - pose proof (sg_FAM_range (idT inp)). lia.
Qed.

Lemma sg_out1 : forall lo hi x, ~ outside [(lo, hi)] x -> lo <= x < hi.
Proof.
  intros lo hi x H. cbn in H. assert (D : lo <= x < hi \/ ~ (lo <= x < hi)) by lia.
  destruct D as [D|D]; [exact D|]. exfalso. apply H. split; [exact D | exact I].
Qed.

Set Default Proof Using "All".
Section Seg.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Let API := APIf rc.
Let MR := aa_MR API.

Lemma sg_segs : ms_segs B = rsegs.
Proof. exact (proj1 FF). Qed.

Lemma sg_FA : frame_allocator B API.
Proof.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & H). exact (H rc fx).
Qed.

Lemma sg_laws : MR_laws B MR.
Proof. exact (aa_laws API). Qed.

Lemma sg_AX : AllocExtra B MR.
Proof.
  destruct sg_FA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H.
Qed.

Lemma sg_bw : blocks_writable B API.
Proof. destruct sg_FA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma sg_relro_unowned : forall L A mem md a, MR L A mem md -> in_globals frame_RELRO a -> ~ owned B L A a.
Proof. destruct sg_FA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.

Lemma sg_relro_img : forall a, in_globals frame_RELRO a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Proof.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & H & _). exact H.
Qed.

Lemma sg_ceil : 2 ^ 20 < alloc_ceiling.
Proof. pose proof alloc_ceiling_val. lia. Qed.

Lemma sg_in_img_low : forall a, in_img B a -> 0 <= a < 2 ^ 20.
Proof.
  intros a (_ & s & Hs & Ha). rewrite sg_segs in Hs.
  pose proof sg_res_low as L. rewrite forallb_forall in L. specialize (L s Hs). apply Z.leb_le in L.
  pose proof (bv_unsigned_in_range 64 (fst s)). lia.
Qed.

Lemma sg_seg_in_img : forall x seg, find_segment rsegs x 1 = Some seg -> in_img B x.
Proof.
  intros x seg H. destruct (sg_find_segment rsegs x 1 seg H) as (Hin & H1 & H2).
  pose proof sg_res_cover as C. rewrite forallb_forall in C. specialize (C seg Hin).
  apply andb_prop in C as [C1 C2]. apply Z.leb_le in C1, C2.
  split; [rewrite sg_segs; exact sg_rsegs_nil|].
  exists (segment_reservation seg). split; [|lia].
  rewrite sg_segs. unfold segments_reserved. apply in_map. exact Hin.
Qed.

Lemma sg_range_img : forall lo hi,
  existsb (fun s => (Z.of_N (seg_base s) <=? lo) && (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs = true ->
  forall x, lo <= x < hi -> in_img B x.
Proof.
  intros lo hi H x Hx. destruct (sg_range_seg lo hi H x Hx) as [seg E]. exact (sg_seg_in_img x seg E).
Qed.

Lemma sg_present_high : forall m x, 2 ^ 20 <= x < 2 ^ 64 -> writable_at (ms_segs B) m x ->
  exists b, m (Z_to_bv 64 x) = Some b.
Proof.
  intros m x Hx Hw. unfold writable_at, wview in Hw.
  destruct (m (Z_to_bv 64 x)) as [b|]; [exists b; reflexivity|].
  rewrite MState.unsigned_lit in Hw by lia.  rewrite sg_segs, sg_noseg_high in Hw by lia.
  contradiction.
Qed.

Lemma sg_present_noimg : forall m x, 0 <= x < 2 ^ 64 -> ~ in_img B x -> writable_at (ms_segs B) m x ->
  exists b, m (Z_to_bv 64 x) = Some b.
Proof.
  intros m x Hx Hn Hw. unfold writable_at, wview in Hw.
  destruct (m (Z_to_bv 64 x)) as [b|]; [exists b; reflexivity|].
  rewrite MState.unsigned_lit in Hw by lia.  rewrite sg_segs in Hw.
  destruct (find_segment rsegs x 1) as [seg|] eqn:E; [|contradiction].
  exfalso. exact (Hn (sg_seg_in_img x seg E)).
Qed.

Lemma sg_ro_high : forall x, 2 ^ 20 <= x < 2 ^ 64 -> ro_addr (ms_segs B) (Z_to_bv 64 x) = false.
Proof.
  intros x Hx. unfold ro_addr. rewrite MState.unsigned_lit by lia.  rewrite sg_segs, sg_noseg_high by lia.
  reflexivity.
Qed.

Lemma sg_stk_of_writable : forall m lo hi, 2 ^ 20 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> writable_at (ms_segs B) m a) -> stk rsegs m lo hi.
Proof.
  intros m lo hi Hlo Hhi H. split; [lia|]. split; [lia|]. intros a Ha.
  pose proof (H a Ha) as Hw. split.
  - unfold writable_at in Hw. rewrite <- sg_segs. exact Hw.
  - destruct (sg_present_high m a ltac:(lia) Hw) as [b Hb]. exists b. unfold mrd, wa. rewrite Hb. reflexivity.
Qed.

Lemma sg_bytes_at_mbyte : forall m m' a bs, bytes_at rsegs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte (ms_segs B) m' (a + i) = mbyte (ms_segs B) m (a + i)) ->
  bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs (H1 & H2 & H3) H. split; [exact H1|]. split; [exact H2|]. intros i Hi.
  rewrite <- (H3 i Hi). pose proof (H (Z.of_nat i) ltac:(lia)) as E. unfold mbyte in E. 
  rewrite sg_segs in E. unfold mrd, wa. exact E.
Qed.

Definition in_hb (hb : list (Z * Z)) (x : Z) : Prop := exists p n, In (p, n) hb /\ p <= x < p + n.

Lemma sg_blk : forall L A mem md p n i, MR L A mem md -> In (p, n) (blocks L A) -> 0 <= i < n ->
  4096 <= p /\ p + n <= alloc_ceiling /\ ~ owned B L A (p + i) /\ ~ in_img B (p + i) /\
  writable_at (ms_segs B) mem (p + i).
Proof.
  intros L A mem md p n i HM Hin Hi.
  pose proof Hin as Hin'. unfold blocks in Hin'. apply in_map_iff in Hin' as ([q n'] & Eq & Hq).
  cbn [fst snd] in Eq. injection Eq as Ea En. subst p n'.
  destruct (mr_blocks _ _ sg_laws _ _ _ _ q n i HM Hq Hi) as (_ & H1 & H2 & H3).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split.
  - exact (ax_blocks_img sg_AX L A mem md q n i HM Hq Hi).
  - exact (sg_bw L A mem md (ptr_addr L q) n i HM Hin Hi).
Qed.

Lemma sg_pairwise_perm : forall (l l' : list (Z * Z)), Permutation l l' ->
  pairwise ranges_disjoint l -> pairwise ranges_disjoint l'.
Proof.
  intros l l' HP. induction HP as [|x l l' HP IH|x y l|l l' l'' H1 IH1 H2 IH2]; intros H.
  - exact H.
  - destruct H as [Hx Hl]. split; [intros y Hy; apply Hx; apply (Permutation_in y (Permutation_sym HP) Hy)|].
    exact (IH Hl).
  - destruct H as [Hy [Hx Hl]]. split.
    + intros z [<-|Hz]; [unfold ranges_disjoint in *; specialize (Hy x (or_introl eq_refl)); lia|].
      apply Hx. exact Hz.
    + split; [intros z Hz; apply Hy; right; exact Hz | exact Hl].
  - exact (IH2 (IH1 H)).
Qed.

Lemma sg_pairwise_app : forall (l1 l2 : list (Z * Z)), pairwise ranges_disjoint (l1 ++ l2) ->
  forall a b, In a l1 -> In b l2 -> ranges_disjoint a b.
Proof.
  induction l1 as [|x l1 IH]; intros l2 H a b Ha Hb; [destruct Ha|].
  destruct H as [Hx Hl]. destruct Ha as [<-|Ha].
  - apply Hx. apply in_or_app. right. exact Hb.
  - exact (IH l2 Hl a b Ha Hb).
Qed.

Lemma sg_hb_in : forall L A hb B0 p n, Permutation (blocks L A) (hb ++ B0) -> In (p, n) hb -> In (p, n) (blocks L A).
Proof.
  intros L A hb B0 p n HP H. apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact H.
Qed.

Lemma sg_b0_in : forall L A hb B0 p n, Permutation (blocks L A) (hb ++ B0) -> In (p, n) B0 -> In (p, n) (blocks L A).
Proof.
  intros L A hb B0 p n HP H. apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. exact H.
Qed.

Lemma sg_sink : forall mem mem' md md', sink_none B mem md ->
  (forall a, (a = sk_threaded \/ sk_ofl_lock <= a < sk_ofl_lock + 4 \/ sk_ofl_head <= a < sk_ofl_head + 8) ->
     mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a) ->
  m_fds md' = m_fds md -> sink_none B mem' md'.
Proof.
  intros mem mem' md md' ((H1 & H2) & H3 & H4) HE HF.
  split; [split|]; [| | split].
  - intros k Hk. rewrite HE by (left; cbn in Hk; assert (k = 0)%nat by lia; subst k; cbn; lia). exact (H1 k Hk).
  - intros k Hk. rewrite HE by (right; left; lia). exact (H2 k Hk).
  - intros k Hk. rewrite HE by (right; right; lia). exact (H3 k Hk).
  - rewrite HF. exact H4.
Qed.

Lemma sg_sinkaddrs : sk_ofl_head = 0x50640 /\ sk_ofl_lock = 0x50638 /\ sk_threaded = 0x50211.
Proof.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H1 & H2 & H3 & _).
  split; [exact H1|]. split; [exact H2|]. rewrite H3. reflexivity.
Qed.

Lemma sg_syms : ms_ctx B = 0x50288 /\ ms_lock B = 0x50280 /\ ms_libc B = 0x50210 /\ ms_size_classes B = 0x10678 /\
  ms_small_cnt B = 0x106d8 /\ ms_med_cnt B = 0x106f3 /\ ms_debruijn B = 0x10658 /\ ms_tp B = 0x2ff80 /\
  ms_errno_off B = -164 /\ ms_guard B = 0x501f0 /\ ms_got_guard B = 0x1ec08 /\ ms_malloc B = 0x15580.
Proof.
  destruct FF as (_ & _ & H3 & _ & _ & _ & _ & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & _).
  repeat split; assumption.
Qed.

Lemma sg_sink_img_chk :
  existsb (fun s => (Z.of_N (seg_base s) <=? 0x50211) && (0x50648 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs
  = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sg_sink_unowned : forall L A mem md a, MR L A mem md ->
  (a = sk_threaded \/ sk_ofl_lock <= a < sk_ofl_lock + 4 \/ sk_ofl_head <= a < sk_ofl_head + 8) ->
  in_img B a /\ ~ owned B L A a /\ ~ (errno_addr B <= a < errno_addr B + 4) /\ 0 <= a < 2 ^ 20.
Proof.
  intros L A mem md a HM Ha. destruct sg_sinkaddrs as (S1 & S2 & S3). rewrite S1, S2, S3 in Ha.
  destruct sg_syms as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & _).
  assert (Hi : in_img B a) by (apply (sg_range_img 0x50211 0x50648 sg_sink_img_chk); lia).
  split; [exact Hi|]. split; [|split; [unfold errno_addr; rewrite Y8, Y9; lia | pose proof (sg_in_img_low a Hi); lia]].
  intros [Ho|Ho].
  - pose proof (ax_img sg_AX L A mem md a HM Hi Ho) as Hc. rewrite Y1 in Hc. unfold CTX_SIZE in Hc. lia.
  - unfold static_owned, vml_lo, vml_len in Ho. rewrite (ff_vmlock _ _ _ _ _ _ _ FF) in Ho.
    rewrite (ff_dbl _ _ _ _ _ _ _ FF), Z.max_id in Ho.
    rewrite Y2, Y3, Y4, Y5, Y6, Y7, Y10, Y11 in Ho. lia.
Qed.

Lemma sg_run : forall regs pc mem md (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] -> ro_agree (ms_segs B) mem ->
  Exec.evt (ms_segs B) (fun ms => exists R pc' m0, ms = MS R fp_regs pc' fp_csr None m0 (seg_rom (ms_segs B)) /\ K R pc' m0)
    (MS (rmk regs) fp_regs pc fp_csr None (normalize (ms_segs B) mem) (seg_rom (ms_segs B))) ->
  (forall R pc' m0 m' regs', K R pc' m0 -> mem_rel (ms_segs B) m' m0 -> ro_same (ms_segs B) mem m' ->
     (forall r, getr regs' r = getr R r) ->
     Rz (ms_segs B) (mkCfg (mkst regs' pc' m' (seg_rom (ms_segs B))) md) P) ->
  Rz (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros regs pc mem md K P Hh Hl Hro HE HK.
  assert (Hwx : wx_apart (ms_segs B) = true) by ( rewrite sg_segs; exact wx_apart_rsegs).
  pose proof (evt_normalize (ms_segs B) _ (rmk regs) fp_regs pc fp_csr None mem (seg_rom (ms_segs B)) Hwx Hro HE) as HE'.
  eapply (rz_evt_canon (ms_segs B) (mkst regs pc mem (seg_rom (ms_segs B))) _ md P); [exact HE' | exact Hh | exact Hl |].
  intros ms' (can & (s0 & (R & pc' & m0 & Es0 & HKR) & Hrel & Hsame) & Heq).
  subst s0.
  destruct can as [cr cf cpc csvc cres cfc cm cro]; destruct ms' as [r' f' pc'' svc' res' fc' m'' ro'].
  destruct Hrel as (HR1 & HF1 & Hpc1 & Hsvc1 & Hres1 & Hfc1 & Hrom1 & Hmr).
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS] in *.
  subst cr cf cpc csvc cres cfc cro. subst f' pc'' svc' res' fc' m'' ro'.
  exact (HK R pc' m0 cm r' HKR Hmr Hsame (sg_getr_eqv R r' HR)).
Qed.

Lemma sg_FR_munch : forall g km hb L A regs mem md regs' mem' W,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  munch W mem mem' -> wmono (ms_segs B) mem mem' -> ro_same (ms_segs B) mem mem' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> (g_S g - SLOT_K <= x < g_S g - 104) \/ in_hb hb x) ->
  FR B APIf ra empty g km hb L A regs' mem' md.
Proof.
  intros g km hb L A regs mem md regs' mem' W HFR HP E2 E3 E4 HM HW HS HWin.
  destruct HFR as (HGV & R2 & R3 & R4 & Hsav & Hstk & HMI & Hrelro & HMR & HWF & Hbd & Hinit & Hvm & Hhigh & Himg &
    Hb0 & Herr & Hsink & Hres & Hwin).
  pose proof HGV as (Gn & Gp & Gd & GS16 & GSc & GS47 & Groom & Gsp & Gtp).
  pose proof sg_ceil as Hc. pose proof alloc_ceiling_lt as Hc47. unfold SLOT_K, SLOT_STACK in *.
  assert (Hhb : forall x, in_hb hb x -> 4096 <= x < alloc_ceiling /\ ~ owned B L A x /\ ~ in_img B x).
  { intros x (p & n & Hin & Hx). pose proof (sg_hb_in L A hb _ p n HP Hin) as Hb.
    destruct (sg_blk L A mem md p n (x - p) HMR Hb ltac:(lia)) as (H1 & H2 & H3 & H4 & _).
    replace (p + (x - p)) with x in * by lia. split; [lia|]. split; assumption. }
  assert (Heq : forall x, 0 <= x < 2 ^ 64 -> ~ (g_S g - 65536 <= x < g_S g - 104) -> ~ in_hb hb x ->
     mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
  { intros x Hx H1 H2. apply HM. rewrite MState.unsigned_lit by lia.
    destruct (sg_outside_dec W x) as [Ho|Ho]; [exact Ho|]. exfalso. destruct (HWin x Hx Ho); tauto. }
  assert (Hmb : forall x, 0 <= x < 2 ^ 64 -> ~ (g_S g - 65536 <= x < g_S g - 104) -> ~ in_hb hb x ->
     mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x /\ (writable_at (ms_segs B) mem x <-> writable_at (ms_segs B) mem' x)).
  { intros x Hx H1 H2. unfold mbyte, writable_at, wview. rewrite (Heq x Hx H1 H2). tauto. }
  assert (Hlow : forall x, 0 <= x < alloc_ceiling -> ~ in_hb hb x ->
     mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x /\ (writable_at (ms_segs B) mem x <-> writable_at (ms_segs B) mem' x)).
  { intros x Hx H. apply Hmb; [lia | lia | exact H]. }
  assert (Hwr : forall x, writable_at (ms_segs B) mem x -> writable_at (ms_segs B) mem' x).
  { intros x H. unfold writable_at in *. apply HW. exact H. }
  unfold FR; unfold SLOT_K, SLOT_STACK. split; [exact HGV|].
  split; [rewrite E2; exact R2|]. split; [rewrite E3; exact R3|]. split; [rewrite E4; exact R4|].
  split.
  { assert (Ls : Z.of_nat (length (saved_bytes ra g)) = 104)
      by (unfold saved_bytes; rewrite !length_app, !length_le8; reflexivity).
    apply (sg_bytes_at_mbyte mem mem' _ _ Hsav). intros i Hi. rewrite Ls in Hi.
    apply (Hmb (g_S g - 104 + i) ltac:(lia) ltac:(lia)). intros H. destruct (Hhb _ H). lia. }
  split.
  { apply sg_stk_of_writable; [lia | lia |]. intros a Ha. apply Hwr. exact (Hwin a Ha). }
  split.
  { unfold MI in *. exact (ro_agree_same (ms_segs B) mem mem' HMI HS). }
  split.
  { unfold relro, G_img_c in *. intros a Ha. destruct (sg_relro_img a Ha) as (Hi & _).
    pose proof (sg_in_img_low a Hi) as Hlo.
    rewrite (proj1 (Hlow a ltac:(lia) ltac:(intro H; exact (proj2 (proj2 (Hhb a H)) Hi)))). exact (Hrelro a Ha). }
  split.
  { destruct (mr_model _ _ sg_laws _ _ _ _ HMR) as (Hh & Hl & Hmat).
    apply (mr_frame _ _ sg_laws L A mem mem' md md HMR).
    - intros a Ho. pose proof (mr_owned_low _ _ sg_laws _ _ _ _ _ HMR Ho) as Hol.
      apply (Hlow a ltac:(lia)). intro Hq. exact (proj1 (proj2 (Hhb a Hq)) Ho).
    - intros a Ho (b & Hb). pose proof (mr_owned_low _ _ sg_laws _ _ _ _ _ HMR Ho) as Hol.
      exists b. rewrite (Heq a ltac:(lia) ltac:(lia) ltac:(intro Hq; exact (proj1 (proj2 (Hhb a Hq)) Ho))). exact Hb.
    - intros p n i Hin Hi.
      assert (Hb : In (ptr_addr L p, n) (blocks L A)) by (unfold blocks; apply in_map_iff; exists (p, n); split; [reflexivity | exact Hin]).
      destruct (sg_blk L A mem md _ n i HMR Hb Hi) as (H1 & H2 & _ & H4 & H5).
      exact (sg_present_noimg mem' (ptr_addr L p + i) ltac:(lia) H4 (Hwr _ H5)).
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  split; [exact HWF|]. split; [exact Hbd|]. split; [exact Hinit|]. split; [exact Hvm|].
  split.
  { intros a Ha H1 H2. destruct (Hhigh a Ha H1 H2) as [Ea Wa].
    destruct (Hmb a ltac:(lia) ltac:(lia) ltac:(intro H; destruct (Hhb a H); lia)) as [Ea' Wa'].
    rewrite Ea'. split; [exact Ea | tauto]. }
  split.
  { intros a Hi H1 H2 H3. pose proof (sg_in_img_low a Hi) as Hlo. destruct (Himg a Hi H1 H2 H3) as [Ea Wa].
    destruct (Hlow a ltac:(lia) ltac:(intro H; exact (proj2 (proj2 (Hhb a H)) Hi))) as [Ea' Wa'].
    rewrite Ea'. split; [exact Ea | tauto]. }
  split.
  { intros a k i Hin Hi. rewrite <- (Hb0 a k i Hin Hi).
    pose proof (sg_b0_in L A hb _ a k HP Hin) as Hb.
    destruct (sg_blk L A mem md a k i HMR Hb Hi) as (H1 & H2 & _).
    apply (Hlow (a + i) ltac:(lia)). intros (p & n & Hpn & Hx).
    pose proof (sg_pairwise_perm _ _ HP (mr_blocks_disjoint _ _ sg_laws _ _ _ _ HMR)) as PW.
    pose proof (sg_pairwise_app hb _ PW (p, n) (a, k) Hpn Hin) as D. unfold ranges_disjoint in D. cbn in D. lia. }
  split.
  { intros a Ha. apply Hwr. exact (Herr a Ha). }
  split.
  { apply (sg_sink mem mem' md md Hsink); [|reflexivity]. intros a Ha.
    destruct (sg_sink_unowned L A mem md a HMR Ha) as (Hi & _ & _ & Hr).
    apply (Hlow a ltac:(lia)). intro H. exact (proj2 (proj2 (Hhb a H)) Hi). }
  split; [exact Hres|].
  intros a Ha. apply Hwr. exact (Hwin a Ha).
Qed.

Lemma sg_FR_regs : forall g km hb L A regs mem md regs',
  FR B APIf ra empty g km hb L A regs mem md ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  FR B APIf ra empty g km hb L A regs' mem md.
Proof.
  intros g km hb L A regs mem md regs' HFR E2 E3 E4.
  destruct HFR as (HGV & R2 & R3 & R4 & HR). split; [exact HGV|].
  split; [rewrite E2; exact R2|]. split; [rewrite E3; exact R3|]. split; [rewrite E4; exact R4|]. exact HR.
Qed.

Lemma sg_malloc :
  forall g km hb L A regs mem md n (P : config -> Prop),
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  YK0s.ret_ok (getr regs 1) ->
  getr regs 10 = Z_to_bv 64 n -> 0 <= n <= 2 ^ 20 -> (length hb <= 16)%nat -> 0 <= hb_bytes hb <= 2 ^ 24 ->
  (forall L' A' regs' mem' md' res,
     FR B APIf ra empty g (km + 1) (hb ++ [(res, n)]) L' A' regs' mem' md' ->
     Permutation (blocks L' A') ((hb ++ [(res, n)]) ++ blocks (g_L g) (g_A g)) ->
     regs_preserved regs regs' -> getr regs' 10 = Z_to_bv 64 res -> res <> 0 ->
     (forall a, fsp g <= a < g_S g -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a) ->
     Rz (ms_segs B) (mkCfg (mkst regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md') P) ->
  Rz (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 (ms_malloc B)) mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros g km hb L A regs mem md n P HFR HP Hra Hn Hn' Hlen Hhb HK.
  pose proof HFR as (HGV & R2 & R3 & R4 & Hsav & Hstk & HMI & Hrelro & HMR & HWF & Hbd & Hinit & Hvm & Hhigh & Himg &
    Hb0 & Herr & Hsink & Hres & Hwin).
  pose proof HGV as (Gn & Gp & Gd & GS16 & GSc & GS47 & Groom & Gsp & Gtp).
  pose proof sg_ceil as Hc. pose proof alloc_ceiling_lt as Hc47.
  unfold SLOT_K, SLOT_STACK in *.
  assert (Hsp : spZ regs = g_S g - 368)
    by (unfold spZ; rewrite R2; unfold fsp, SLOT_FRAME; apply MState.unsigned_lit; lia).
  pose proof (rz_room_of L A mem md (g_b g) (Z.of_nat (length hb)) (hb_bytes hb) n HMR Groom ltac:(lia) Hhb Hn')
    as Hroom.
  assert (Hpre : call_pre B MR L A regs mem md).
  { split; [exact HMR|]. split; [exact HWF|]. split; [exact Hbd|]. split; [exact Hra|].
    rewrite Hsp. split; [rewrite Zminus_mod, GS16; reflexivity|].
    split; [unfold ALLOC_STACK; lia|]. split; [lia|].
    split; [intros a Ha; apply Hwin; unfold ALLOC_STACK in Ha; lia|].
    split; [rewrite R4; exact Gtp|]. split; [exact Herr|].
    rewrite Hinit. discriminate. }
  eapply rz_bind; [exact (rz_malloc L A regs mem md n (sb_hb (g_b g) hb) Hpre HMI Hn Hres Hroom)|].
  intros c' (L' & A' & regs' & mem' & md' & res & -> & Hpost & Ha0 & Hr0 & Hr16 & Hfresh & Hsplit & Hkept & Hro' &
    Hguard & Hub & Hinit' & Hreg & Hres').
  destruct Hpost as (HMR' & HWF' & Hbd' & Hlay & Hptr & Hpres & Hvm' & Hmem & Hblk & Hscr).
  destruct Hvm as (vm & Hvm). destruct Hvm' as (vm' & Hvm'). subst md'.
  assert (Hno : forall a, alloc_ceiling <= a -> ~ owned B L A a /\ ~ owned B L' A' a).
  { intros a Ha. split; intro Ho;
      [pose proof (mr_owned_low _ _ sg_laws _ _ _ _ _ HMR Ho) | pose proof (mr_owned_low _ _ sg_laws _ _ _ _ _ HMR' Ho)];
      lia. }
  assert (Hnoimg : forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
            ~ owned B L A a /\ ~ owned B L' A' a).
  { intros a Hi Hs Hctx. split; intros [Ho|Ho]; try exact (Hs Ho); apply Hctx;
      [exact (ax_img sg_AX L A mem md a HMR Hi Ho) | exact (ax_img sg_AX L' A' mem' _ a HMR' Hi Ho)]. }
  assert (Hkeep : forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L A a -> ~ owned B L' A' a ->
            ~ (g_S g - 368 - 8192 <= a < g_S g - 368) -> ~ (errno_addr B <= a < errno_addr B + 4) ->
            mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\ (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)).
  { intros a H1 H2 H3 H4 H5. apply (Hmem a H1 H2 H3); [|intros []].
    unfold scratch_k. rewrite Hsp. unfold ALLOC_STACK. tauto. }
  assert (Herrlo : errno_addr B + 4 <= alloc_ceiling).
  { destruct FF as (_ & _ & _ & _ & _ & _ & H7 & _). exact (H7 rc). }
  assert (Hframe : forall a, g_S g - 368 <= a < 2 ^ 64 ->
            mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\ (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)).
  { intros a Ha. destruct (Hno a ltac:(lia)) as [N1 N2]. apply Hkeep; [left; lia | exact N1 | exact N2 | lia | lia]. }
  assert (Hwin' : forall a, g_S g - 65536 <= a < g_S g -> writable_at (ms_segs B) mem' a).
  { intros a Ha. destruct (Z_lt_ge_dec a (g_S g - 368)) as [Lt|Ge].
    - destruct (Z_lt_ge_dec a (g_S g - 368 - 8192)) as [Lt2|Ge2].
      + destruct (Hno a ltac:(lia)) as [N1 N2].
        apply (proj2 (Hkeep a ltac:(left; lia) N1 N2 ltac:(lia) ltac:(lia))). exact (Hwin a Ha).
      + apply Hscr. unfold scratch_k. rewrite Hsp. unfold ALLOC_STACK. left. lia.
    - apply (proj2 (Hframe a ltac:(lia))). exact (Hwin a Ha). }
  destruct Hsplit as (b1 & b2 & Hs1 & Hs2).
  assert (HP' : Permutation (blocks L' A') ((hb ++ [(res, n)]) ++ blocks (g_L g) (g_A g))).
  { pose proof HP as HP2. rewrite Hs2 in HP2. rewrite Hs1, <- app_assoc. cbn [app].
    eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|].
    eapply Permutation_trans; [apply perm_skip, HP2|]. apply Permutation_middle. }
  apply (HK L' A' regs' mem' (with_vmmaps vm' md) res); [| exact HP' | exact Hpres | exact Ha0 | exact Hr0 |
    intros a Ha; exact (proj1 (Hframe a ltac:(unfold fsp, SLOT_FRAME in Ha; lia)))].
  unfold FR; unfold SLOT_K, SLOT_STACK. split; [exact HGV|].
  split; [transitivity (getr regs 2); [exact (Hpres 2 ltac:(unfold callee_saved; lia)) | exact R2]|].
  split; [transitivity (getr regs 3); [exact (Hpres 3 ltac:(unfold callee_saved; lia)) | exact R3]|].
  split; [transitivity (getr regs 4); [exact (Hpres 4 ltac:(unfold callee_saved; lia)) | exact R4]|].
  split.
  { assert (Ls : Z.of_nat (length (saved_bytes ra g)) = 104)
      by (unfold saved_bytes; rewrite !length_app, !length_le8; reflexivity).
    apply (sg_bytes_at_mbyte mem mem' _ _ Hsav). intros i Hi. rewrite Ls in Hi.
    exact (proj1 (Hframe (g_S g - 104 + i) ltac:(lia))). }
  split; [apply sg_stk_of_writable; [lia | lia | exact Hwin']|].
  split; [exact Hro'|].
  split.
  { unfold relro, G_img_c in *. intros a Ha. destruct (sg_relro_img a Ha) as (Hi & Hs & Hctx & He).
    pose proof (sg_in_img_low a Hi) as Hlo.
    rewrite (proj1 (Hkeep a (or_intror Hi) (sg_relro_unowned L A mem _ a HMR Ha) (sg_relro_unowned L' A' mem' _ a HMR' Ha)
      ltac:(lia) He)). exact (Hrelro a Ha). }
  split; [exact HMR'|]. split; [exact HWF'|]. split; [exact Hbd'|]. split; [exact Hinit'|].
  split; [exists vm'; rewrite Hvm; apply sg_with_vmmaps_twice|].
  split.
  { intros a Ha H1 H2. destruct (Hhigh a Ha H1 H2) as [Ea Wa]. destruct (Hno a ltac:(lia)) as [N1 N2].
    destruct (Hkeep a (or_introl Ha) N1 N2 ltac:(lia) H2) as [Ea' Wa']. rewrite Ea'. split; [exact Ea | tauto]. }
  split.
  { intros a Hi H1 H2 H3. pose proof (sg_in_img_low a Hi) as Hlo. destruct (Himg a Hi H1 H2 H3) as [Ea Wa].
    destruct (Hnoimg a Hi H1 H2) as [N1 N2].
    destruct (Hkeep a (or_intror Hi) N1 N2 ltac:(lia) H3) as [Ea' Wa']. rewrite Ea'. split; [exact Ea | tauto]. }
  split.
  { intros a k i Hin Hi. rewrite <- (Hb0 a k i Hin Hi). apply (Hkept a k i); [exact (sg_b0_in L A hb _ a k HP Hin) | intros [] | exact Hi]. }
  split.
  { intros a Ha. apply Hscr. unfold scratch_k. right. exact Ha. }
  split.
  { apply (sg_sink mem mem' md (with_vmmaps vm' md) Hsink); [| apply sg_fds_with_vmmaps]. intros a Ha.
    destruct (sg_sink_unowned L A mem md a HMR Ha) as (Hi & N1 & He & Hr).
    assert (N2 : ~ owned B L' A' a).
    { intros [Ho|Ho]; [| exact (N1 (or_intror Ho))].
      pose proof (ax_img sg_AX L' A' mem' _ a HMR' Hi Ho) as Hctx.
      destruct (sg_sink_unowned L A mem md a HMR Ha) as (_ & N1' & _).
      apply N1'. left. destruct sg_syms as (Y1 & _). rewrite Y1 in Hctx. unfold CTX_SIZE in Hctx.
      destruct sg_sinkaddrs as (S1 & S2 & S3). rewrite S1, S2, S3 in Ha. exfalso. lia. }
    exact (proj1 (Hkeep a (or_intror Hi) N1 N2 ltac:(lia) He)). }
  split.
  { exact (resb_malloc (g_b g) (km + 1) hb (hb ++ [(res, n)]) A' res n
             (Permutation_sym (Permutation_cons_append hb (res, n))) Hres'). }
  exact Hwin'.
Qed.

Lemma sg_same_mem : forall mem m', ro_agree (ms_segs B) mem ->
  mem_rel (ms_segs B) m' (normalize (ms_segs B) mem) -> ro_same (ms_segs B) mem m' -> forall x, m' x = mem x.
Proof.
  intros mem m' Hro Hr Hs x.
  exact (mem_unchanged_rel (ms_segs B) mem (normalize (ms_segs B) mem) m' (normalize (ms_segs B) mem)
    (mem_rel_normalize (ms_segs B) mem Hro) Hr Hs (fun _ => eq_refl) x).
Qed.

Lemma sg_FR_same : forall g km hb L A regs mem md regs' mem',
  FR B APIf ra empty g km hb L A regs mem md -> Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  (forall x, mem' x = mem x) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  FR B APIf ra empty g km hb L A regs' mem' md.
Proof.
  intros g km hb L A regs mem md regs' mem' HF HP HE E2 E3 E4.
  apply (sg_FR_munch g km hb L A regs mem md regs' mem' [] HF HP E2 E3 E4).
  - intros x _. exact (HE x).
  - intros x Hx. unfold wview. rewrite HE. exact Hx.
  - intros x _. exact (HE x).
  - intros x _ Ho. exfalso. apply Ho. exact I.
Qed.

Lemma sg_bytes_same : forall m m' a bs, bytes_at rsegs m a bs -> (forall x, m' x = m x) -> bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs (H1 & H2 & H3) HE. split; [exact H1|]. split; [exact H2|]. intros i Hi.
  unfold mrd. rewrite HE. exact (H3 i Hi).
Qed.

Lemma sg_bytes_frame : forall m m' a bs lo hi, bytes_at rsegs m a bs -> lo <= a -> a + Z.of_nat (length bs) <= hi ->
  (forall x, lo <= x < hi -> mbyte (ms_segs B) m' x = mbyte (ms_segs B) m x) -> bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs lo hi H Hlo Hhi HE. apply (sg_bytes_at_mbyte m m' a bs H). intros i Hi. apply HE. lia.
Qed.

Lemma sg_cut : forall g pc km hb (P : bvmap 5 word -> (word -> option byte) -> Prop) L A regs mem md,
  FR B APIf ra empty g km hb L A regs mem md -> Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  P regs mem -> CUTST B APIf ra empty g pc km hb P (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom (ms_segs B))) md).
Proof.
  intros g pc km hb P L A regs mem md HF HP HPr. exists L, A, regs, mem, md.
  split; [reflexivity|]. split; [exact HF|]. split; [exact HP | exact HPr].
Qed.

Lemma sg_md : forall L A mem md, MR L A mem md -> m_halted md = None /\ m_vm_lazy md = [].
Proof.
  intros L A mem md H. destruct (mr_model _ _ sg_laws _ _ _ _ H) as (H1 & H2 & _). split; assumption.
Qed.

Lemma sg_ro_agree_norm : forall mem, MI B mem -> ro_agree (ms_segs B) mem.
Proof. intros mem H. exact H. Qed.

Lemma sg_hb_range : forall L A mem md hb B0 p n, MR L A mem md -> Permutation (blocks L A) (hb ++ B0) ->
  In (p, n) hb -> 0 < n -> 4096 <= p /\ p + n <= alloc_ceiling.
Proof.
  intros L A mem md hb B0 p n HM HP Hin Hn.
  destruct (sg_blk L A mem md p n 0 HM (sg_hb_in L A hb B0 p n HP Hin) ltac:(lia)) as (H1 & H2 & _). lia.
Qed.

Lemma sg_hb_nz : forall L A mem md hb B0 p n, MR L A mem md -> Permutation (blocks L A) (hb ++ B0) ->
  In (p, n) hb -> 0 < n -> bv_eqb (Z_to_bv 64 p) (Z_to_bv 64 0) = false.
Proof.
  intros L A mem md hb B0 p n HM HP Hin Hn.
  destruct (sg_hb_range L A mem md hb B0 p n HM HP Hin Hn) as [H1 H2]. pose proof alloc_ceiling_lt.
  unfold bv_eqb. rewrite !MState.unsigned_lit by lia. apply Z.eqb_neq. lia.
Qed.

Lemma sg_relro_bytes : forall mem a bs, relro B mem -> relro_chk a bs = true -> 0 <= a ->
  a + Z.of_nat (length bs) <= 2 ^ 64 -> bytes_at rsegs mem a bs.
Proof.
  intros mem a bs Hr Hc Ha Hl. split; [lia|]. split; [lia|]. intros i Hi.
  destruct (relro_chk_ok bs a Hc i Hi) as [Hg Hs].
  pose proof (Hr _ Hg) as E. unfold mbyte in E. rewrite sg_segs in E.
  rewrite <- Hs. exact E.
Qed.

End Seg.

Lemma sg_firstn1 : forall (l : list byte) k, (k < length l)%nat -> firstn 1 (skipn k l) = [RcIdentModel.nthb l k].
Proof.
  induction l as [|x l IH]; intros k Hk; cbn [length] in Hk; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn]. rewrite IH by lia. reflexivity.
Qed.

Lemma sg_land255 : forall c, 0 <= c < 256 -> Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 c)) 255) = Z_to_bv 64 c.
Proof.
  intros c Hc. rewrite MState.unsigned_lit by lia. f_equal. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  apply Z.mod_small. lia.
Qed.

Lemma sg_sltiu1 : forall c, 0 <= c < 2 ^ 64 -> bv_unsigned (PropExec.v_sltiu (Z_to_bv 64 c) 1) = if c =? 0 then 1 else 0.
Proof.
  intros c Hc. unfold PropExec.v_sltiu. rewrite MState.unsigned_lit by lia. change (bv_wrap 64 1) with 1.
  destruct (Z.ltb_spec c 1); destruct (Z.eqb_spec c 0); try lia; rewrite MState.unsigned_lit by lia; reflexivity.
Qed.

Lemma sg_bufsz : forall c, 0 <= c < 256 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 c)) 255 +
    bv_unsigned (PropExec.v_sltiu (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 c)) 255)) 1)) = Z_to_bv 64 (bsz c).
Proof.
  intros c Hc. rewrite MState.unsigned_lit by lia.
  replace (Z.land c 255) with c by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
  rewrite sg_sltiu1 by lia. unfold bsz. f_equal. destruct (Z.eqb_spec c 0); lia.
Qed.

Lemma sg_caps : forall inp, 0 <= t_cap_name inp < 40 /\ 0 <= t_cap_tok inp < 40 /\ 0 <= t_cap_disp inp < 64.
Proof.
  intros inp. unfold t_cap_name, t_cap_tok, t_cap_disp.
  pose proof (Z.mod_pos_bound (tb inp 5) 40 ltac:(lia)). pose proof (Z.mod_pos_bound (tb inp 6) 40 ltac:(lia)).
  pose proof (Z.mod_pos_bound (tb inp 7) 64 ltac:(lia)). lia.
Qed.

Lemma sg_ret_ok : forall z, 0 <= z < 2 ^ 63 -> z mod 2 = 0 -> YK0s.ret_ok (Z_to_bv 64 z).
Proof.
  intros z Hz He. unfold YK0s.ret_ok, YK14.v_jalr, jalr_tgtZ. apply bv_eq.
  rewrite !Z_to_bv_unsigned. rewrite (bv_wrap_small 64 z) by (unfold bv_modulus; lia). rewrite Z.add_0_r.
  rewrite YK0s.land_m2_even by exact He. apply bv_wrap_small. unfold bv_modulus. lia.
Qed.

Ltac sg_pres Hp r :=
  lazymatch type of Hp with
  | regs_preserved ?r1 ?r2 =>
      lazymatch goal with
      | |- getr r2 ?x = _ => transitivity (getr r1 x); [exact (Hp r ltac:(unfold callee_saved; lia)) |]
      end
  end.

Lemma sg_bufsz2 : forall c, 0 <= c < 256 ->
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 c) + bv_unsigned (PropExec.v_sltiu (Z_to_bv 64 c) 1)) = Z_to_bv 64 (bsz c).
Proof.
  intros c Hc. rewrite sg_sltiu1 by lia. rewrite MState.unsigned_lit by lia. unfold bsz. f_equal.
  destruct (Z.eqb_spec c 0); lia.
Qed.

Lemma sg_bufsz3 : forall c, 0 <= c < 256 ->
  Z_to_bv 64 (c + bv_unsigned (PropExec.v_sltiu (Z_to_bv 64 c) 1)) = Z_to_bv 64 (bsz c).
Proof.
  intros c Hc. rewrite sg_sltiu1 by lia. unfold bsz. f_equal. destruct (Z.eqb_spec c 0); lia.
Qed.
