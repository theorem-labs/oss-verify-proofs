From Stdlib Require Import String ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK14 YP09 YO0i YO0f YO0d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0o.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU RecKindB.
Import ListNotations.
Local Open Scope Z_scope.

Definition GLOB_LO : Z := 0x33ff0.
Definition GLOB_N : nat := 1020.

Lemma forallb_seq_at : forall (f : nat -> bool) k i, forallb f (seq 0 k) = true -> (i < k)%nat -> f i = true.
Proof.
  intros f k i H Hi. apply (proj1 (forallb_forall f (seq 0 k)) H). apply in_seq. lia.
Qed.

Lemma glob_rom_some_b :
  forallb (fun i => match PropExec.seg_rom rsegs (Z_to_bv 64 (GLOB_LO + Z.of_nat i)) with
                    | Some _ => true | None => false end)
    (seq 0 GLOB_N) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma glob_ro_false_b :
  forallb (fun i => negb (ro_addr rsegs (Z_to_bv 64 (GLOB_LO + Z.of_nat i)))) (seq 0 GLOB_N) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma glob_found_b :
  forallb (fun i => match find_segment rsegs (GLOB_LO + Z.of_nat i) 1 with Some _ => true | None => false end)
    (seq 0 GLOB_N) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma glob_idx : forall a, GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N ->
  a = GLOB_LO + Z.of_nat (Z.to_nat (a - GLOB_LO)) /\ (Z.to_nat (a - GLOB_LO) < GLOB_N)%nat.
Proof. intros a Ha. unfold GLOB_LO, GLOB_N in *. split; lia. Qed.

Lemma glob_readable : forall m a, GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N ->
  exists b, mrd rsegs m (wa a) = Some b.
Proof.
  intros m a Ha. destruct (glob_idx a Ha) as [E Hi].
  pose proof (forallb_seq_at _ _ _ glob_rom_some_b Hi) as H. cbv beta in H. rewrite <- E in H.
  unfold mrd. destruct (m (wa a)) as [b|]; [exists b; reflexivity|].
  unfold wa. destruct (PropExec.seg_rom rsegs (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | discriminate].
Qed.

Lemma glob_ro_false : forall a, GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. destruct (glob_idx a Ha) as [E Hi].
  pose proof (forallb_seq_at _ _ _ glob_ro_false_b Hi) as H. cbv beta in H. rewrite <- E in H.
  unfold wa. destruct (ro_addr rsegs (Z_to_bv 64 a)); [discriminate | reflexivity].
Qed.

Lemma glob_found : forall a, GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N -> find_segment rsegs a 1 <> None.
Proof.
  intros a Ha. destruct (glob_idx a Ha) as [E Hi].
  pose proof (forallb_seq_at _ _ _ glob_found_b Hi) as H. cbv beta in H. rewrite <- E in H.
  destruct (find_segment rsegs a 1); [discriminate | discriminate H].
Qed.

Lemma glob_wview_b :
  forallb (fun i => match wview rsegs (fun _ => None) (Z_to_bv 64 (GLOB_LO + Z.of_nat i)) with
                    | Some _ => true | None => false end)
    (seq 0 GLOB_N) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma wview_any : forall m x, wview rsegs (fun _ => None) x <> None -> wview rsegs m x <> None.
Proof. intros m x H. unfold wview in *. destruct (m x); [discriminate | exact H]. Qed.

Lemma glob_writable : forall m a, GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N -> writable_at rsegs m a.
Proof.
  intros m a Ha. destruct (glob_idx a Ha) as [E Hi].
  pose proof (forallb_seq_at _ _ _ glob_wview_b Hi) as H. cbv beta in H. rewrite <- E in H.
  unfold writable_at. apply wview_any.
  destruct (wview rsegs (fun _ => None) (Z_to_bv 64 a)); [discriminate | discriminate H].
Qed.

Lemma glob_wr_at : forall m a n, GLOB_LO <= a -> a + n <= GLOB_LO + Z.of_nat GLOB_N -> 0 <= n ->
  wr_at rsegs m a n.
Proof.
  intros m a n H1 H2 H3. split; [unfold GLOB_LO in H1; lia|]. split; [unfold GLOB_LO, GLOB_N in *; lia|].
  intros i Hi. exact (glob_writable m (a + i) ltac:(lia)).
Qed.

Lemma bytes_rw_cells : forall m a bs, GLOB_LO <= a -> a + Z.of_nat (length bs) <= GLOB_LO + Z.of_nat GLOB_N ->
  bytes_at rsegs m a bs -> rw_cells rsegs m a [CB (length bs) bs].
Proof.
  intros m a bs H1 H2 Hb. split; [split|].
  - cbn. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. apply glob_wr_at; lia.
Qed.

Lemma readable_rw_cells : forall segs m a (k : nat), wr_at segs m a (Z.of_nat k) ->
  (forall i, 0 <= i < Z.of_nat k -> exists b, mrd segs m (wa (a + i)) = Some b) ->
  exists junk, rw_cells segs m a [CB k junk].
Proof.
  intros segs m a k Hw H.
  set (junk := map (fun i => match mrd segs m (wa (a + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end)
                   (seq 0 k)).
  assert (L : length junk = k) by (unfold junk; rewrite length_map, length_seq; reflexivity).
  exists junk. destruct Hw as (Ha & Hn & Hw').
  split; [split|].
  - cbn. split; [exact L | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [exact Ha|]. split; [rewrite L; exact Hn|].
    intros i Hi. rewrite L in Hi.
    destruct (H (Z.of_nat i) ltac:(lia)) as [b E].
    unfold junk. rewrite (map_nth_error _ _ _ (nth_error_seq_lt 0 k i Hi)). cbn [Nat.add]. rewrite E. reflexivity.
  - split; [exact Ha|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. apply Hw'. lia.
Qed.

Lemma glob_rw_cells : forall m a (k : nat), GLOB_LO <= a -> a + Z.of_nat k <= GLOB_LO + Z.of_nat GLOB_N ->
  exists junk, rw_cells rsegs m a [CB k junk].
Proof.
  intros m a k H1 H2. apply readable_rw_cells; [apply glob_wr_at; lia|].
  intros i Hi. apply glob_readable. lia.
Qed.

Lemma sb_malloc_le : forall b b' n, sb_le b b' -> sb_le (sb_malloc b n) (sb_malloc b' n).
Proof. intros b b' n H. exact (sb_malloc_mono b b' n H). Qed.

Lemma rfree_b_le : forall (F : list (Z * Z)) b, Forall (fun pn => 0 <= snd pn) F ->
  sb_le (fold_left (fun b' (pn : Z * Z) => sb_free b' (snd pn)) F b) b.
Proof.
  induction F as [|pn F IH]; intros b HF; cbn [fold_left]; [apply sb_le_refl|].
  inversion HF as [|? ? H0 HF']; subst.
  eapply sb_le_trans; [apply IH; exact HF' | apply sb_free_le; exact H0].
Qed.

Definition NULL_LIT : Z := 0x10a19.

Lemma null_lit_ro : forall i, 0 <= i < 7 -> ro_addr rsegs (Z_to_bv 64 (NULL_LIT + i)) = true.
Proof.
  intros i Hi. assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6) by lia.
  repeat (destruct C as [C|C]; [subst i; vm_compute; reflexivity|]). subst i. vm_compute. reflexivity.
Qed.

Lemma null_lit_bytes : forall m, ro_agree rsegs m ->
  bytes_at rsegs m NULL_LIT (bstr "(null)"%string ++ [Z_to_bv 8 0]).
Proof.
  intros m RA. split; [unfold NULL_LIT; lia|]. split; [cbn; unfold NULL_LIT; lia|].
  intros i Hi. cbn in Hi.
  unfold wa. rewrite (RA _ (null_lit_ro (Z.of_nat i) ltac:(lia))).
  assert (C : i = 0%nat \/ i = 1%nat \/ i = 2%nat \/ i = 3%nat \/ i = 4%nat \/ i = 5%nat \/ i = 6%nat) by lia.
  repeat (destruct C as [C|C]; [subst i; vm_compute; reflexivity|]). subst i. vm_compute. reflexivity.
Qed.

Definition sel_null (u : word) : word := if Z.eqb (bv_unsigned u) 0 then Z_to_bv 64 NULL_LIT else u.

Lemma null_no0 : no0 (bstr "(null)"%string).
Proof. apply no0_nz. vm_compute. reflexivity. Qed.

Lemma glob_in : forall a, GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N -> in_globals frame_G a.
Proof. intros a Ha. exists 0x33ff0, 1020. split; [left; reflexivity | unfold GLOB_LO, GLOB_N in Ha; lia]. Qed.

Lemma r_state_record : forall R fn As, r_state (rec_record R fn As) = r_state R.
Proof. intros R fn As. unfold rec_record. destruct (Nat.ltb (length (r_calls R)) 16); reflexivity. Qed.

Section Img.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Hypothesis SEGS : ms_segs B = rsegs.

Lemma glob_in_img : forall a, GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N -> in_img B a.
Proof using SEGS.
  intros a Ha. apply (in_img_found B SEGS); [unfold GLOB_LO in Ha; lia|]. exact (glob_found a Ha).
Qed.

Lemma null_lit_in_img : forall i, 0 <= i < 7 -> in_img B (NULL_LIT + i).
Proof using SEGS.
  intros i Hi. apply (ro_in_img B SEGS); [unfold NULL_LIT; lia | exact (null_lit_ro i Hi)].
Qed.

Lemma sarg_src : forall L A O S K mem p v, ro_agree rsegs mem -> 0 <= K -> NULL_LIT + 7 <= S - K ->
  str_arg B L A O S K mem p v ->
  exists s slack, 0 <= p < 2 ^ 64 /\ (if p =? 0 then NULL_LIT else p) = s /\ 0 <= s /\
    bytes_at rsegs mem s (sarg v ++ Z_to_bv 8 0 :: slack) /\ no0 (sarg v) /\ Z.of_nat (length (sarg v)) <= LMAX /\
    (- (s + Z.of_nat (length (sarg v)) + 1)) mod 8 <= Z.of_nat (length slack) /\
    (s + Z.of_nat (length (sarg v ++ Z_to_bv 8 0 :: slack)) <= S - K \/ S <= s) /\
    str_home B L A S s (Z.of_nat (length (sarg v)) + 1) /\
    (forall a, s <= a < s + Z.of_nat (length (sarg v ++ Z_to_bv 8 0 :: slack)) -> ~ rec_area a).
Proof using SEGS.
  intros L A O S K mem p v RA HK HS H. destruct v as [x|].
  - destruct H as (Hp0 & N0 & LX & slack & BS & AL & DJ & HOME & NRA).
    rewrite SEGS in BS. pose proof (bytes_at_bound _ _ _ _ BS) as BB. rewrite length_app in BB. cbn [length] in BB.
    exists p, slack. cbn [sarg].
    split; [lia|]. split; [rewrite (proj2 (Z.eqb_neq _ _) Hp0); reflexivity|]. split; [lia|].
    split; [exact BS|]. split; [exact N0|]. split; [exact LX|]. split; [exact AL|]. split; [exact DJ|].
    split; [|exact NRA].
    unfold str_home. destruct HOME as [H1 | [(q & k & Hq & _ & H2) | H3]]; [left; exact H1 | right; left | right; right; exact H3].
    exists q, k. split; [exact Hq | exact H2].
  - cbn in H. subst p. exists NULL_LIT, []. cbn [sarg].
    split; [lia|]. split; [reflexivity|]. split; [unfold NULL_LIT; lia|].
    split; [exact (null_lit_bytes mem RA)|]. split; [exact null_no0|]. split; [cbn; unfold LMAX; lia|].
    split; [vm_compute; discriminate|]. split; [left; cbn; lia|].
    split.
    + right. right. split; [unfold NULL_LIT; lia|]. split; [cbn; unfold NULL_LIT; lia|].
      intros i Hi. rewrite SEGS. apply null_lit_ro. cbn in Hi. lia.
    + intros a Ha. cbn in Ha. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE, NULL_LIT in *. lia.
Qed.

End Img.

Lemma slack_bytes : forall segs m p n bs, bytes_at segs m p bs -> Z.of_nat (length bs) = n -> 0 <= p ->
  p + n + 8 <= 2 ^ 64 -> (forall a, p + n <= a < 8 * ((p + n + 7) / 8) -> present m a) ->
  exists slack, bytes_at segs m p (bs ++ slack) /\ Z.of_nat (length slack) = 8 * ((p + n + 7) / 8) - (p + n).
Proof.
  intros segs m p n bs Hb Hl Hp Hn HS.
  assert (R : 0 <= 8 * ((p + n + 7) / 8) - (p + n) <= 7) by (Z.div_mod_to_equations; lia).
  set (k := Z.to_nat (8 * ((p + n + 7) / 8) - (p + n))).
  set (sl := map (fun i => match m (wa (p + n + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 k)).
  assert (L : length sl = k) by (unfold sl; rewrite length_map, length_seq; reflexivity).
  exists sl. split; [|rewrite L; unfold k; lia].
  apply bytes_at_app. split; [exact Hb|]. rewrite Hl.
  split; [lia|]. split; [rewrite L; unfold k; lia|].
  intros i Hi. rewrite L in Hi.
  destruct (HS (p + n + Z.of_nat i) ltac:(unfold k in Hi; lia)) as [b E].
  unfold sl. rewrite (map_nth_error _ _ _ (nth_error_seq_lt 0 k i Hi)). cbn [Nat.add].
  unfold mrd, wa. unfold wa in E. rewrite E. reflexivity.
Qed.

Section MR.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis LAWS : MR_laws B MR.

Lemma mr_keep : forall L A m m' md W, MR L A m md -> munch W m m' ->
  (forall a, owned B L A a -> outside W a) ->
  (forall p n i, In (p, n) (user_blocks A) -> 0 <= i < n -> outside W (ptr_addr L p + i)) ->
  MR L A m' md.
Proof using LAWS.
  intros L A m m' md W HM MU HO HB.
  destruct (mr_model B MR LAWS L A m md HM) as (Hh & Hl & Hmat). pose proof alloc_ceiling_lt as ACL.
  eapply (mr_frame B MR LAWS L A m m' md md HM).
  - intros a Ho. destruct (owned_low B MR LAWS L A m md a HM Ho).
    eapply munch_mbyte; [exact MU | lia | exact (HO a Ho)].
  - intros a Ho Hp. destruct (owned_low B MR LAWS L A m md a HM Ho).
    eapply munch_present; [exact MU | lia | exact (HO a Ho) | exact Hp].
  - intros p n i Hin Hi. destruct (mr_blocks B MR LAWS L A m md p n i HM Hin Hi) as (Hp & H4 & Hc & _).
    eapply munch_present; [exact MU | lia | exact (HB p n i Hin Hi) | exact Hp].
  - reflexivity.
  - exact Hh.
  - exact Hl.
  - exact Hmat.
Qed.

End MR.
