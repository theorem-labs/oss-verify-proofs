From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require YL01 YO0x YO0u.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract Img0 KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import Ledger ReaderRes parse_items_shape.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import pj_set_runs pj_set_shape.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import pj_get_c memcpy_c memset_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import pj_free_c grow_c fuzz_strdup_c pj_set_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF ReaderResCF.
Module YK11 := YK11.
Module YK0s := YK0s.
Module YM05 := YM05.
Module YL01 := U.Reusable.YL01.
Module YO0x := YO0x.
Module YO0u := YO0u.
Module MemNorm := U.MemNorm.
Module strtod_c := U.Prog.strtod_c.
Import YM05.
Import ListNotations.
Local Open Scope Z_scope.

Ltac cs_cases tac :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; unfold callee_saved in Hr;
  destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; [tac .. |];
  let Hr' := fresh "Hr" in
  assert (Hr' : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
    by lia;
  destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; tac.

Lemma g_out : forall W x, (~ Frame.outside W x -> False) -> Frame.outside W x.
Proof. intros W x H. destruct (kb_outside_dec W x) as [Ho|Ho]; [exact Ho | exfalso; exact (H Ho)]. Qed.

Lemma g_pw : forall (l : list (Z * Z)) x y, pairwise ranges_disjoint l -> In x l -> In y l -> x <> y ->
  ranges_disjoint x y.
Proof.
  induction l as [|z l IH]; intros x y H Hx Hy Hne; [destruct Hx|].
  cbn [pairwise] in H. destruct H as [Hz Hl]. destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
  - exfalso. apply Hne. reflexivity.
  - exact (Hz y Hy).
  - pose proof (Hz x Hx) as D. unfold ranges_disjoint in *. lia.
  - exact (IH x y Hl Hx Hy Hne).
Qed.

Lemma g_pw_dup : forall (c1 c2 : list (Z * Z)) x, pairwise ranges_disjoint (c1 ++ x :: c2) -> In x (c1 ++ c2) ->
  snd x <= 0.
Proof.
  induction c1 as [|z c1 IH]; intros c2 x H Hin; cbn [app pairwise] in H, Hin.
  - destruct H as [H _]. pose proof (H x Hin) as D. unfold ranges_disjoint in D. lia.
  - destruct H as [Hz H]. destruct Hin as [<-|Hin].
    + pose proof (Hz z (in_or_app c1 (z :: c2) z (or_intror (in_eq z c2)))) as D. unfold ranges_disjoint in D. lia.
    + exact (IH c2 x H Hin).
Qed.

Lemma g_old : forall segs m p k, 0 <= k -> (forall i, 0 <= i < k -> mbyte segs m (p + i) <> None) ->
  exists old : list byte, Z.of_nat (length old) = k /\
    forall i, 0 <= i < k -> mbyte segs m (p + i) = nth_error old (Z.to_nat i).
Proof.
  intros segs m p k Hk H.
  assert (G : forall nn : nat, Z.of_nat nn <= k -> exists old : list byte, length old = nn /\
    forall i, 0 <= i < Z.of_nat nn -> mbyte segs m (p + i) = nth_error old (Z.to_nat i)).
  { induction nn as [|nn IH]; intros Hn.
    - exists []. split; [reflexivity|]. intros i Hi. lia.
    - destruct (IH ltac:(lia)) as (old & Hl & Ho).
      destruct (mbyte segs m (p + Z.of_nat nn)) as [bb|] eqn:Eb; [|exfalso; exact (H (Z.of_nat nn) ltac:(lia) Eb)].
      exists (old ++ [bb]). split; [rewrite length_app; cbn [length]; lia|].
      intros i Hi. destruct (Z.eq_dec i (Z.of_nat nn)) as [->|Hne].
      + rewrite Nat2Z.id, nth_error_app2 by lia. rewrite Hl, Nat.sub_diag. cbn [nth_error]. exact Eb.
      + rewrite nth_error_app1 by lia. apply Ho. lia. }
  destruct (G (Z.to_nat k) ltac:(lia)) as (old & Hl & Ho). exists old. split; [lia|]. intros i Hi. apply Ho. lia.
Qed.



Lemma g_nout1 : forall lo hi x, ~ Frame.outside [(lo, hi)] x -> lo <= x < hi.
Proof.
  intros lo hi x H. destruct (Z_le_gt_dec lo x); destruct (Z_lt_ge_dec x hi); try lia;
    exfalso; apply H; cbn; refine (conj _ I); lia.
Qed.

Lemma g_nout2 : forall a b c d x, ~ Frame.outside [(a, b); (c, d)] x -> a <= x < b \/ c <= x < d.
Proof.
  intros a b c d x H. destruct (Z_le_gt_dec a x); destruct (Z_lt_ge_dec x b); try (left; lia);
    destruct (Z_le_gt_dec c x); destruct (Z_lt_ge_dec x d); try (right; lia);
    exfalso; apply H; cbn; refine (conj _ (conj _ I)); lia.
Qed.

Lemma g_lsum_app : forall l1 l2, lsum (l1 ++ l2) = lsum l1 + lsum l2.
Proof. induction l1 as [|[a k] l1 IH]; intros l2; cbn [app lsum]; [lia | rewrite IH; lia]. Qed.

Lemma g_lsum_perm : forall l l', Permutation l l' -> lsum l = lsum l'.
Proof.
  intros l l' H. induction H as [|[a k] l l' H IH|[a k] [a' k'] l|l l' l'' H1 IH1 H2 IH2]; cbn [lsum]; lia.
Qed.

Lemma g_same_trans : forall sg m1 m2 m3 x, pis_same sg m1 m2 x -> pis_same sg m2 m3 x -> pis_same sg m1 m3 x.
Proof. intros sg m1 m2 m3 x (E1 & W1) (E2 & W2). split; [congruence | intros H; exact (W2 (W1 H))]. Qed.

Lemma g_same_munch : forall sg W m m' x, munch W m m' -> wmono sg m m' -> 0 <= x < 2 ^ 64 -> outside W x ->
  pis_same sg m m' x.
Proof. intros sg W m m' x HM HW Hx Ho. split; [exact (mbyte_munch sg W m m' x HM Hx Ho) | intros H; exact (HW _ H)]. Qed.

Lemma g_z8_id : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma g_zb_map : forall cs, map (Z_to_bv 8) (zb cs) = cs.
Proof. intros cs. unfold zb. rewrite map_map. rewrite (map_ext _ (fun b => b)) by exact g_z8_id. apply map_id. Qed.

Lemma g_zb_pos : forall cs, ~ In (Z_to_bv 8 0) cs -> Forall (fun c => 0 < c < 256) (zb cs).
Proof.
  intros cs H. unfold zb. rewrite Forall_forall. intros c Hc. apply in_map_iff in Hc as (bt & <- & Hbt).
  pose proof (bv_unsigned_in_range 8 bt) as R. unfold bv_modulus in R. cbn in R.
  split; [|lia]. destruct (Z.eq_dec (bv_unsigned bt) 0) as [E|E]; [|lia].
  exfalso. apply H. assert (Eb : bt = Z_to_bv 8 0) by (rewrite <- (g_z8_id bt), E; reflexivity).
  rewrite Eb in Hbt. exact Hbt.
Qed.

Section Tr.
Variable sg : list Segment.

Lemma t_mbyte_mrd : forall m a, mbyte sg m a = mrd sg m (wa a).
Proof. reflexivity. Qed.

Lemma t_stk_rel : forall m m0 lo hi, MemNorm.mem_rel sg m m0 -> stk sg m0 lo hi -> stk sg m lo hi.
Proof.
  intros m m0 lo hi HR (H0 & H1 & H). split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (H a Ha) as [W [b R]]. split.
  - rewrite <- (MemNorm.wview_rel_rw sg m m0 _ HR (MemNorm.ro_false_of_wview sg m m0 _ HR W)). exact W.
  - exists b. rewrite (MemNorm.mrd_rel sg m m0 _ HR). exact R.
Qed.

Lemma t_rw_rel : forall m m0 A cs, MemNorm.mem_rel sg m m0 -> rw_cells sg m0 A cs -> rw_cells sg m A cs.
Proof.
  intros m m0 A cs HR [[Hwf HB] HW].
  split; [split; [exact Hwf | exact (proj2 (MemNorm.bytes_at_rel sg m m0 A _ HR) HB)] |
          exact (MemNorm.wr_at_rel sg m m0 A _ HR HW)].
Qed.

Lemma t_stk_norm : forall m lo hi, MemNorm.ro_agree sg m -> (forall a, lo <= a < hi -> ro_addr sg (wa a) = false) ->
  stk sg m lo hi -> stk sg (MemNorm.normalize sg m) lo hi.
Proof.
  intros m lo hi Hro Hf (H0 & H1 & H). split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (H a Ha) as [W [b R]]. pose proof (MemNorm.mem_rel_normalize sg m Hro) as HR. split.
  - rewrite (MemNorm.wview_rel_rw sg m (MemNorm.normalize sg m) _ HR (Hf a Ha)). exact W.
  - exists b. rewrite <- (MemNorm.mrd_rel sg m (MemNorm.normalize sg m) _ HR). exact R.
Qed.

Lemma t_rw_norm : forall m A cs, MemNorm.ro_agree sg m ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> ro_addr sg (wa (A + i)) = false) ->
  rw_cells sg m A cs -> rw_cells sg (MemNorm.normalize sg m) A cs.
Proof.
  intros m A cs Hro Hf [[Hwf HB] HW].
  split; [split; [exact Hwf | exact (MemNorm.bytes_at_normalize sg m A _ Hro HB)] |].
  exact (MemNorm.wr_at_norm sg m (MemNorm.normalize sg m) A _ (MemNorm.mem_rel_normalize sg m Hro) HW Hf).
Qed.

Lemma t_norm_eq : forall m (x : word), ro_addr sg x = false -> MemNorm.normalize sg m x = m x.
Proof. intros m x H. unfold MemNorm.normalize. rewrite H. reflexivity. Qed.

Lemma t_node_norm : forall m lblk p t D, pj_node sg m lblk p t D -> MemNorm.ro_agree sg m ->
  (forall x : word, pj_foot p D (bv_unsigned x) -> ro_addr sg x = false) ->
  pj_node sg (MemNorm.normalize sg m) lblk p t D.
Proof.
  intros m lblk p t D H Hro Hf. apply (pj_node_frame sg t m lblk (MemNorm.normalize sg m) lblk p D H).
  - intros a k Hb. exact (pis_node_lblk sg t m lblk p D H (a, k) Hb).
  - intros x Hx. apply t_norm_eq. exact (Hf x Hx).
Qed.

Lemma t_hdr_norm : forall m p ty num str kids keys n cap, pj_hdr sg m p ty num str kids keys n cap ->
  (forall x : word, p <= bv_unsigned x < p + 56 -> ro_addr sg x = false) ->
  pj_hdr sg (MemNorm.normalize sg m) p ty num str kids keys n cap.
Proof.
  intros m p ty num str kids keys n cap H Hf. apply (pj_hdr_eq sg m _ p _ _ _ _ _ _ _ H).
  intros x Hx. apply t_norm_eq. exact (Hf x Hx).
Qed.

Lemma t_cbytes_norm : forall m a s, MemNorm.ro_agree sg m -> pj_cbytes sg m a s -> pj_cbytes sg (MemNorm.normalize sg m) a s.
Proof.
  intros m a s Hro (HF & HB). split; [exact HF | exact (MemNorm.bytes_at_normalize sg m a _ Hro HB)].
Qed.

End Tr.

Section G.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.


Lemma g_img : ms_segs B = rsegs -> img_low B.
Proof.
  intros HS. apply (img_low_of_check B 140735332483072).
  - unfold img_check. rewrite HS. vm_compute. reflexivity.
  - pose proof alloc_ceiling_value. lia.
Qed.

Lemma g_blocks_user : forall L A p k, In (p, k) (blocks L A) -> exists q, In (q, k) (user_blocks A) /\ ptr_addr L q = p.
Proof.
  intros L A p k Hin. unfold blocks in Hin. apply in_map_iff in Hin.
  destruct Hin as ([q k'] & E & Hq). cbn [fst snd] in E. injection E as E1 E2. subst k'.
  exists q. split; [exact Hq | exact E1].
Qed.

Lemma g_user_blocks : forall L A q k, In (q, k) (user_blocks A) -> In (ptr_addr L q, k) (blocks L A).
Proof. intros L A q k H. unfold blocks. apply in_map_iff. exists (q, k). split; [reflexivity | exact H]. Qed.

Lemma g_blk_range : forall L A mem md p k, aa_MR API L A mem md -> In (p, k) (blocks L A) ->
  4096 <= p /\ p + k <= alloc_ceiling.
Proof.
  intros L A mem md p k HM Hin. destruct (g_blocks_user L A p k Hin) as (q & Hq & <-).
  exact (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q k HM Hq).
Qed.

Lemma g_disj : forall L A mem md a k a' k', aa_MR API L A mem md -> In (a, k) (blocks L A) ->
  In (a', k') (blocks L A) -> (a, k) <> (a', k') -> a + k <= a' \/ a' + k' <= a.
Proof.
  intros L A mem md a k a' k' HM H1 H2 Hne.
  exact (g_pw _ _ _ (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HM) H1 H2 Hne).
Qed.

Lemma g_ptr : forall L L' A p n, WF A -> In (p, n) (user_blocks A) -> layout_le A L L' -> ptr_addr L' p = ptr_addr L p.
Proof.
  intros L L' A p n HW Hin (_ & _ & _ & HR).
  destruct (YO0x.user_blocks_frame A p n HW Hin) as (g & am & idx & fr & Hu & _ & _ & _ & _ & ->).
  pose proof (YO0u.used_group_prid_lt [] None U0 A g am HW Hu) as Hlt.
  unfold frame_ptr, slot_start, ptr_addr. destruct (am_mem am) as [r o]. cbn in Hlt |- *.
  rewrite (HR r Hlt). reflexivity.
Qed.

Lemma g_vm : forall vm1 vm2 md, with_vmmaps vm2 (with_vmmaps vm1 md) = with_vmmaps vm2 md.
Proof. intros vm1 vm2 md. reflexivity. Qed.

Lemma g_bytes : forall m m' a bs, bytes_at (ms_segs B) m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> mbyte (ms_segs B) m' x = mbyte (ms_segs B) m x) ->
  bytes_at (ms_segs B) m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H) Hm. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  rewrite <- (H i Hi). exact (Hm (a + Z.of_nat i) ltac:(lia)).
Qed.

Lemma g_wr : forall m a n, 0 <= a -> a + n <= 2 ^ 64 ->
  (forall i, 0 <= i < n -> writable_at (ms_segs B) m (a + i)) -> wr_at (ms_segs B) m a n.
Proof. intros m a n H0 H1 H. split; [exact H0|]. split; [exact H1|]. intros i Hi. exact (H i Hi). Qed.

Lemma g_rw_cells : forall m m' a cs, Step.rw_cells (ms_segs B) m a cs ->
  (forall x, a <= x < a + Z.of_nat (cells_size cs) -> mbyte (ms_segs B) m' x = mbyte (ms_segs B) m x /\
     (writable_at (ms_segs B) m x -> writable_at (ms_segs B) m' x)) ->
  Step.rw_cells (ms_segs B) m' a cs.
Proof.
  intros m m' a cs ((Hwf & Hb) & (W0 & W1 & W)) H.
  split; [split; [exact Hwf|]|].
  - apply (g_bytes m m' a _ Hb). intros x Hx. rewrite (cells_bytes_length cs Hwf) in Hx. exact (proj1 (H x Hx)).
  - split; [exact W0|]. split; [exact W1|]. intros i Hi. apply (proj2 (H (a + i) ltac:(lia))). exact (W i Hi).
Qed.

Lemma g_bytes_some : forall m a bs x, bytes_at (ms_segs B) m a bs -> a <= x < a + Z.of_nat (length bs) ->
  mbyte (ms_segs B) m x <> None.
Proof.
  intros m a bs x (_ & _ & H) Hx Hn. pose proof (H (Z.to_nat (x - a)) ltac:(lia)) as E.
  replace (a + Z.of_nat (Z.to_nat (x - a))) with x in E by lia.
  assert (E2 : mbyte (ms_segs B) m x = nth_error bs (Z.to_nat (x - a))) by exact E.
  rewrite Hn in E2. symmetry in E2. apply nth_error_None in E2. lia.
Qed.

Lemma g_seg_img : ms_segs B = rsegs -> forall x seg, find_segment (ms_segs B) x 1 = Some seg -> in_img B x.
Proof.
  intros HSEG x seg E. destruct (kb_find_segment _ x 1 seg E) as (Hin & H1 & H2).
  assert (C : forallb (fun s => existsb (fun rr => (bv_unsigned (fst rr) <=? Z.of_N (seg_base s)) &&
      (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? bv_unsigned (fst rr) + bv_unsigned (snd rr)))
      (segments_reserved (ms_segs B))) (ms_segs B) = true) by (rewrite HSEG; vm_compute; reflexivity).
  rewrite forallb_forall in C. specialize (C seg Hin). apply existsb_exists in C. destruct C as (rr & Hr & Hc).
  apply andb_prop in Hc as (Hc1 & Hc2). apply Z.leb_le in Hc1, Hc2.
  split; [intros E'; rewrite E' in Hin; destruct Hin | exists rr; split; [exact Hr | lia]].
Qed.

Lemma g_ro_notimg : ms_segs B = rsegs -> forall a, 0 <= a < 2 ^ 64 -> ~ in_img B a ->
  ro_addr (ms_segs B) (Z_to_bv 64 a) = false.
Proof.
  intros HSEG a Ha Hn. unfold ro_addr. rewrite unsigned_lit by lia.
  destruct (find_segment (ms_segs B) a 1) as [seg|] eqn:E; [exfalso; exact (Hn (g_seg_img HSEG a seg E)) | reflexivity].
Qed.

Lemma g_ro_low : img_low B -> forall a, alloc_ceiling <= a < 2 ^ 64 -> ro_addr (ms_segs B) (Z_to_bv 64 a) = false.
Proof.
  intros HIL a Ha. pose proof alloc_ceiling_value. unfold ro_addr. rewrite unsigned_lit by lia.
  destruct (find_segment (ms_segs B) a 1) as [seg|] eqn:E; [exfalso; pose proof (proj2 HIL a seg E); lia | reflexivity].
Qed.

Lemma g_ro_munch : forall W m m', MemNorm.ro_agree (ms_segs B) m -> Frame.munch W m m' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Frame.outside W a -> ro_addr (ms_segs B) (Z_to_bv 64 a) = false) ->
  MemNorm.ro_agree (ms_segs B) m'.
Proof.
  intros W m m' H HM HW a Ha. destruct (kb_outside_dec W (bv_unsigned a)) as [Ho|Ho].
  - pose proof (H a Ha) as E. unfold mrd in *. rewrite (HM a Ho). exact E.
  - exfalso. pose proof (bv_unsigned_in_range 64 a) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    pose proof (HW (bv_unsigned a) Hr Ho) as E. rewrite Step.Z_to_bv_lit_self in E. congruence.
Qed.

Lemma g_ledger_munch : forall L A mem md mem' Lam peak cnt fail W,
  aa_MR API L A mem md -> ledger B L A mem Lam peak cnt fail -> Frame.munch W mem mem' ->
  (forall x, ~ Frame.outside W x -> ~ alloc_statics x /\ forall a k, In (a, k) Lam -> ~ (a - 16 <= x < a - 8)) ->
  ledger B L A mem' Lam peak cnt fail.
Proof.
  intros L A mem md mem' Lam peak cnt fail W HM HL Hm HW.
  destruct HL as ((H1 & H2 & H3 & H4) & H5 & H6 & H7 & H8 & H9).
  assert (Hst : forall a v, word_mem (ms_segs B) mem a v -> (forall k, 0 <= k < 8 -> alloc_statics (a + k)) ->
    word_mem (ms_segs B) mem' a v).
  { intros a v Hw Hs. apply (kb_word_munch (ms_segs B) mem mem' W a v Hw Hm). intros k Hk.
    pose proof (Hs k Hk) as Hsk. split; [unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Hsk; lia|].
    apply g_out. intros Hn. exact (proj1 (HW _ Hn) Hsk). }
  split; [|split; [exact H5|]; split; [exact H6|]; split; [exact H7|]; split; [exact H8|]].
  - split; [apply Hst; [exact H1 | intros k Hk; unfold alloc_statics; lia]|].
    split; [apply Hst; [exact H2 | intros k Hk; unfold alloc_statics; lia]|].
    split; [apply Hst; [exact H3 | intros k Hk; unfold alloc_statics; lia]|].
    apply Hst; [exact H4 | intros k Hk; unfold alloc_statics; lia].
  - rewrite Forall_forall in H9 |- *. intros [a k] Hin. destruct (H9 _ Hin) as (Hk & Hb & Hw & Hi). cbn [fst snd] in *.
    split; [exact Hk|]. split; [exact Hb|]. split; [|exact Hi].
    destruct (g_blk_range L A mem md _ _ HM Hb) as [R1 R2].
    apply (kb_word_munch (ms_segs B) mem mem' W (a - 16) k Hw Hm). intros j Hj.
    pose proof alloc_ceiling_lt. split; [lia|].
    apply g_out. intros Hn. exact (proj2 (HW _ Hn) a k Hin ltac:(lia)).
Qed.

Lemma g_kept_blk : forall K1 L1 A1 regs1 mem1 md1 E1 L2 A2 regs2 mem2 md2 g a k,
  call_post_k B (aa_MR API) K1 L1 A1 regs1 mem1 md1 E1 L2 A2 regs2 mem2 md2 ->
  ublocks_kept L1 A1 A2 g -> In (a, k) (blocks L1 A1) -> (a, k) <> g -> In (a, k) (blocks L2 A2).
Proof.
  intros K1 L1 A1 regs1 mem1 md1 E1 L2 A2 regs2 mem2 md2 g a k HP Hub Hin Hne.
  destruct (g_blocks_user L1 A1 a k Hin) as (q & Hq & Eq).
  pose proof HP as (_ & _ & _ & _ & C5 & _).
  assert (Hq2 : In (q, k) (user_blocks A2)) by (apply Hub; [exact Hq | rewrite Eq; exact Hne]).
  rewrite <- Eq, <- (C5 q k Hq Hq2). apply g_user_blocks. exact Hq2.
Qed.

Lemma g_fresh : forall L1 A1 L2 A2 mem2 md2 p k res nn,
  aa_MR API L2 A2 mem2 md2 -> 0 < nn + 16 ->
  (p = 0 /\ (exists b1 b2, blocks L2 A2 = b1 ++ (res - 16, nn + 16) :: b2 /\ blocks L1 A1 = b1 ++ b2)
   \/ p <> 0 /\ (exists b1 b2 c1 c2, blocks L1 A1 = b1 ++ (p - 16, k + 16) :: b2 /\
         blocks L2 A2 = c1 ++ (res - 16, nn + 16) :: c2 /\ c1 ++ c2 = b1 ++ b2)) ->
  (res - 16, nn + 16) <> (p - 16, k + 16) ->
  ~ In (res - 16, nn + 16) (blocks L1 A1) /\ In (res - 16, nn + 16) (blocks L2 A2).
Proof.
  intros L1 A1 L2 A2 mem2 md2 p k res nn HM Hn Hsh Hne.
  pose proof (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HM) as PW. fold (blocks L2 A2) in PW.
  destruct Hsh as [(_ & b1 & b2 & E2 & E1) | (_ & b1 & b2 & c1 & c2 & E1 & E2 & E12)];
    (split; [| rewrite E2; apply in_or_app; right; left; reflexivity]); intros Hin; rewrite E2 in PW.
  - rewrite E1 in Hin. pose proof (g_pw_dup b1 b2 _ PW Hin). cbn [snd] in *. lia.
  - rewrite E1 in Hin. apply in_app_or in Hin. destruct Hin as [Hin|[Heq|Hin]].
    + pose proof (g_pw_dup c1 c2 _ PW ltac:(rewrite E12; apply in_or_app; left; exact Hin)). cbn [snd] in *. lia.
    + exact (Hne (eq_sym Heq)).
    + pose proof (g_pw_dup c1 c2 _ PW ltac:(rewrite E12; apply in_or_app; right; exact Hin)). cbn [snd] in *. lia.
Qed.

Lemma g_auxv_keep : forall sec lo mem mem', auxv_pre B sec lo mem ->
  (forall i, 0 <= i < 8 -> mbyte (ms_segs B) mem' (ms_libc B + 8 + i) = mbyte (ms_segs B) mem (ms_libc B + 8 + i)) ->
  (forall a, lo <= a < 2 ^ 63 -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a) ->
  auxv_pre B sec lo mem'.
Proof.
  intros sec lo mem mem' (av & ar & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10) Hl Hh.
  exists av, ar.
  split; [apply (word_mem_frame (ms_segs B) mem mem' _ _ H1); intros k Hk; apply Hl; lia|].
  split; [intros k Hk; apply (word_mem_frame (ms_segs B) mem mem' _ _ (H2 k Hk)); intros j Hj; apply Hh; lia|].
  split; [apply (word_mem_frame (ms_segs B) mem mem' _ _ H3); intros j Hj; apply Hh; lia|].
  split; [apply (word_mem_frame (ms_segs B) mem mem' _ _ H4); intros j Hj; apply Hh; lia|].
  repeat (split; [assumption|]); assumption.
Qed.

Definition vloc (L : layout) (A : astate) (Lam : list (Z * Z)) (S v r rk : Z) : Prop :=
  (S <= v /\ v + 56 <= 2 ^ 64 /\ r = 0 /\ rk = -1) \/
  (In (r, rk) (blocks L A) /\ r <= v /\ v + 56 <= r + rk /\
   (forall a k, In (a, k) Lam -> a - 8 <= v \/ v + 56 <= a - 16)).

Lemma vloc_own : forall L A Lam mem md S v r rk x, vloc L A Lam S v r rk -> aa_MR API L A mem md ->
  alloc_ceiling <= S -> v <= x < v + 56 -> ~ static_owned B x -> ~ owned B L A x.
Proof.
  intros L A Lam mem md S v r rk x [(Hs & _ & _ & _)|(Hin & H1 & H2 & _)] HM Hc Hx Hst Ho.
  - pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ x HM Ho). lia.
  - destruct Ho as [Ho|Ho]; [|exact (Hst Ho)]. destruct Ho as [_ Hn]. apply Hn.
    destruct (g_blocks_user L A r rk Hin) as (q & Hq & Eq).
    exists (q, rk). split; [exact Hq|]. cbn [fst snd]. unfold ptr_addr in Eq. rewrite Eq. lia.
Qed.

Lemma vloc_heads : forall L A Lam mem md peak cnt fail S v r rk a k, vloc L A Lam S v r rk ->
  aa_MR API L A mem md -> ledger B L A mem Lam peak cnt fail -> alloc_ceiling <= S -> In (a, k) Lam ->
  a - 8 <= v \/ v + 56 <= a - 16.
Proof.
  intros L A Lam mem md peak cnt fail S v r rk a k [(Hs & _ & _ & _)|(_ & _ & _ & Hh)] HM HL Hc Hin;
    [|exact (Hh a k Hin)].
  pose proof (ledger_block_range B API L A mem md Lam peak cnt fail a k HM HL Hin) as (R1 & R2 & _).
  pose proof HL as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF. destruct (HF _ Hin) as (Hk & _).
  cbn [snd] in Hk. lia.
Qed.

Lemma vloc_call : forall L1 A1 Lam1 S v r rk K1 regs1 mem1 md1 E1 L2 A2 regs2 mem2 md2 g Lam2 peak2 cnt2 fail2,
  vloc L1 A1 Lam1 S v r rk ->
  call_post_k B (aa_MR API) K1 L1 A1 regs1 mem1 md1 E1 L2 A2 regs2 mem2 md2 ->
  ublocks_kept L1 A1 A2 g -> (r, rk) <> g ->
  ledger B L2 A2 mem2 Lam2 peak2 cnt2 fail2 ->
  (forall a k, In (a, k) Lam2 -> In (a, k) Lam1 \/ ~ In (a - 16, k + 16) (blocks L1 A1)) ->
  vloc L2 A2 Lam2 S v r rk.
Proof.
  intros L1 A1 Lam1 S v r rk K1 regs1 mem1 md1 E1 L2 A2 regs2 mem2 md2 g Lam2 peak2 cnt2 fail2
    [Hs|(Hin & H1 & H2 & Hh)] HP Hub Hne HL Hsub; [left; exact Hs|].
  right. pose proof (g_kept_blk K1 L1 A1 regs1 mem1 md1 E1 L2 A2 regs2 mem2 md2 g r rk HP Hub Hin Hne) as Hin2.
  split; [exact Hin2|]. split; [exact H1|]. split; [exact H2|].
  intros a k Hak. destruct (Hsub a k Hak) as [Ho|Hn]; [exact (Hh a k Ho)|].
  pose proof HL as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF. destruct (HF _ Hak) as (Hk & Hb & _).
  cbn [fst snd] in *.
  assert (Hd : (a - 16, k + 16) <> (r, rk)) by (intros E; rewrite E in Hn; exact (Hn Hin)).
  pose proof HP as (HM2 & _).
  destruct (g_disj L2 A2 mem2 md2 _ _ _ _ HM2 Hb Hin2 Hd); lia.
Qed.

Lemma vloc_bytes : forall L1 A1 Lam1 S v r rk K1 regs1 mem1 md1 E1 L2 A2 regs2 mem2 md2 g x,
  vloc L1 A1 Lam1 S v r rk -> aa_MR API L1 A1 mem1 md1 ->
  call_post_k B (aa_MR API) K1 L1 A1 regs1 mem1 md1 E1 L2 A2 regs2 mem2 md2 ->
  ublocks_kept L1 A1 A2 g -> (r, rk) <> g ->
  alloc_ceiling <= S -> spZ regs1 <= S -> (forall a, E1 a -> a < alloc_ceiling) ->
  ~ (errno_addr B <= x < errno_addr B + 4) -> v <= x < v + 56 ->
  mbyte (ms_segs B) mem2 x = mbyte (ms_segs B) mem1 x /\
  (writable_at (ms_segs B) mem1 x -> writable_at (ms_segs B) mem2 x).
Proof.
  intros L1 A1 Lam1 S v r rk K1 regs1 mem1 md1 E1 L2 A2 regs2 mem2 md2 g x
    HV HM1 HP Hub Hne Hc Hsp HE1 Herr Hx.
  pose proof HP as (C1 & _ & _ & _ & C5 & _ & _ & C8 & C9 & _).
  destruct HV as [(Hs & Hv & _ & _)|(Hin & H1 & H2 & _)].
  - assert (No1 : ~ owned B L1 A1 x) by (intros Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM1 Ho); lia).
    assert (No2 : ~ owned B L2 A2 x) by (intros Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ C1 Ho); lia).
    destruct (C8 x ltac:(left; lia) No1 No2 ltac:(unfold scratch_k; lia)
      ltac:(intros HE; pose proof (HE1 x HE); lia)) as [E1' E2'].
    split; [exact E1' | apply E2'].
  - destruct (g_blocks_user L1 A1 r rk Hin) as (q & Hq & Eq).
    assert (Hq2 : In (q, rk) (user_blocks A2)) by (apply Hub; [exact Hq | rewrite Eq; exact Hne]).
    split.
    + pose proof (C9 q rk (x - r) Hq Hq2 ltac:(lia)) as E. rewrite Eq in E.
      replace (r + (x - r)) with x in E by lia. exact E.
    + intros _. destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ q rk (x - r) C1 Hq2 ltac:(lia)) as (P & _).
      rewrite (C5 q rk Hq Hq2), Eq in P. replace (r + (x - r)) with x in P by lia.
      exact (present_writable B mem2 x P).
Qed.

Lemma vloc_ne : forall L A Lam S v r rk a k, vloc L A Lam S v r rk -> ~ In (a, k) (blocks L A) -> 0 < k ->
  (r, rk) <> (a, k).
Proof.
  intros L A Lam S v r rk a k [(_ & _ & _ & Hr)|(Hin & _)] Hn Hk E; injection E as E1 E2.
  - lia.
  - subst a k. exact (Hn Hin).
Qed.

Lemma vloc_disj : forall L A Lam mem md S v r rk a k x, vloc L A Lam S v r rk -> aa_MR API L A mem md ->
  alloc_ceiling <= S -> In (a, k) (blocks L A) -> (a, k) <> (r, rk) -> a <= x < a + k -> x < v \/ v + 56 <= x.
Proof.
  intros L A Lam mem md S v r rk a k x [(Hs & _)|(Hin & H1 & H2 & _)] HM Hc Hak Hne Hx.
  - pose proof (g_blk_range L A mem md a k HM Hak). lia.
  - destruct (g_disj L A mem md a k r rk HM Hak Hin Hne); lia.
Qed.

Lemma g_vloc0 : forall L A mem md Lam peak cnt fail S v ty kids keys cap,
  aa_MR API L A mem md -> ledger B L A mem Lam peak cnt fail -> alloc_ceiling <= S ->
  pj_place (lin Lam) (fun a k => In (a, k) (blocks L A)) S (2 ^ 64) v ->
  pj_apart (kids_blk kids cap ++ keys_blk ty keys cap) v ->
  0 <= cap -> (0 < cap -> lin Lam kids (56 * cap) /\ (ty = 6 -> lin Lam keys (8 * cap))) ->
  exists r rk, vloc L A Lam S v r rk /\ (r, rk) <> (kids - 16, 56 * cap + 16) /\
    (ty = 6 -> (r, rk) <> (keys - 16, 8 * cap + 16)).
Proof.
  intros L A mem md Lam peak cnt fail S v ty kids keys cap HM HL Hc Hpl Hap Hcap Hcp.
  pose proof HL as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF.
  destruct Hpl as [(H1 & H2)|[(a & k & Hb & Hnl & H1 & H2)|(a & k & Hl & H1 & H2)]].
  - exists 0, (-1). split; [left; lia|].
    split; [intros E; injection E; lia | intros _ E; injection E; lia].
  - exists a, k. split.
    + right. split; [exact Hb|]. split; [lia|]. split; [lia|].
      intros a' k' Hin. destruct (HF _ Hin) as (Hk' & Hb' & _). cbn [fst snd] in *.
      assert (Hne : (a' - 16, k' + 16) <> (a, k)).
      { intros E. injection E as E1 E2. apply Hnl. unfold lin.
        replace (a + 16) with a' by lia. replace (k - 16) with k' by lia. exact Hin. }
      destruct (g_disj L A mem md _ _ _ _ HM Hb' Hb Hne); lia.
    + split.
      * intros E. injection E as E1 E2. destruct (Z.eq_dec cap 0) as [->|Hc0]; [lia|].
        apply Hnl. unfold lin. replace (a + 16) with kids by lia. replace (k - 16) with (56 * cap) by lia.
        exact (proj1 (Hcp ltac:(lia))).
      * intros Hty E. injection E as E1 E2. destruct (Z.eq_dec cap 0) as [->|Hc0]; [lia|].
        apply Hnl. unfold lin. replace (a + 16) with keys by lia. replace (k - 16) with (8 * cap) by lia.
        exact (proj2 (Hcp ltac:(lia)) Hty).
  - destruct (HF _ Hl) as (Hk & Hb & _). cbn [fst snd] in *.
    exists (a - 16), (k + 16). split.
    + right. split; [exact Hb|]. split; [lia|]. split; [lia|].
      intros a' k' Hin. destruct (HF _ Hin) as (Hk' & Hb' & _). cbn [fst snd] in *.
      destruct (Z.eq_dec a' a) as [->|Ha'].
      * left; lia.
      * assert (Hne : (a' - 16, k' + 16) <> (a - 16, k + 16)) by (intros E; injection E; lia).
        destruct (g_disj L A mem md _ _ _ _ HM Hb' Hb Hne); lia.
    + split.
      * intros E. injection E as E1 E2. destruct (Z.eq_dec cap 0) as [->|Hc0]; [lia|].
        apply (Hap (kids, 56 * cap) v); [| unfold pj_holds; cbn [fst snd]; lia | lia].
        apply in_or_app. left. unfold kids_blk. rewrite (proj2 (Z.eqb_neq cap 0) Hc0). left. reflexivity.
      * intros Hty E. injection E as E1 E2. destruct (Z.eq_dec cap 0) as [->|Hc0]; [lia|].
        apply (Hap (keys, 8 * cap) v); [| unfold pj_holds; cbn [fst snd]; lia | lia].
        apply in_or_app. right. unfold keys_blk. rewrite (proj2 (Z.eqb_neq cap 0) Hc0), Hty. cbn. left. reflexivity.
Qed.

Lemma g_stk : forall m lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall x, lo <= x < hi -> writable_at (ms_segs B) m x /\ mbyte (ms_segs B) m x <> None) ->
  stk (ms_segs B) m lo hi.
Proof.
  intros m lo hi H0 H1 H. split; [exact H0|]. split; [exact H1|]. intros a Ha. destruct (H a Ha) as [Hw Hm].
  split; [exact Hw|]. destruct (mbyte (ms_segs B) m a) as [bb|] eqn:E; [exists bb; exact E | contradiction].
Qed.

Lemma rp_refl : forall K L A regs mem md E gone,
  call_pre_k B (aa_MR API) K L A regs mem md ->
  rpost B API K L A regs mem md E gone L A regs mem md.
Proof.
  intros K L A regs mem md E gone (HM & HW & HB & _ & _ & _ & _ & HS & _ & HE & _).
  split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [apply layout_le_refl|].
  split; [tauto|]. split; [intros _ i _; reflexivity|]. split; [lia|].
  split; [intros p n Hp _; exact Hp|]. split; [intros; reflexivity|].
  split; [intros r _; reflexivity|]. split; [exists (m_vmmaps md); symmetry; apply kb_vm_id|].
  split; [intros; split; [reflexivity | tauto]|]. split; [intros; split; [reflexivity | tauto]|].
  split; [intros; reflexivity|].
  intros a [Ha|Ha]; [apply HS; exact Ha | apply HE; exact Ha].
Qed.

Lemma rp_regs : forall K L A regs mem md E gone L' A' mem' md' regs',
  rpost B API K L A regs mem md E gone L' A' regs mem' md' -> regs_preserved regs regs' ->
  rpost B API K L A regs mem md E gone L' A' regs' mem' md'.
Proof.
  intros K L A regs mem md E gone L' A' mem' md' regs'
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & _ & H11 & H12 & H13 & H14 & H15) Hr.
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj Hr
    (conj H11 (conj H12 (conj H13 (conj H14 H15)))))))))))))).
Qed.

Lemma rp_A : img_low B -> forall K L A regs mem md E gone L1 A1 mem1 md1 mem2 W,
  aa_MR API L A mem md -> alloc_ceiling + K <= spZ regs ->
  rpost B API K L A regs mem md E gone L1 A1 regs mem1 md1 ->
  Frame.munch W mem1 mem2 -> Frame.wmono (ms_segs B) mem1 mem2 ->
  (forall x, 0 <= x < alloc_ceiling -> ~ Frame.outside W x -> mem1 (Z_to_bv 64 x) <> None ->
     mem2 (Z_to_bv 64 x) <> None) ->
  (forall x, ~ Frame.outside W x -> ((spZ regs - K <= x < spZ regs) \/ E x) /\ ~ owned B L1 A1 x) ->
  rpost B API K L A regs mem md E gone L1 A1 regs mem2 md1.
Proof.
  intros HIL K L A regs mem md E gone L1 A1 mem1 md1 mem2 W HM0 Hsp
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15) Hm Hw Hp HW.
  pose proof alloc_ceiling_lt as Hc.
  assert (Ho : forall a, owned B L1 A1 a -> Frame.outside W a).
  { intros a Ha. apply g_out. intros Hn. exact (proj2 (HW a Hn) Ha). }
  assert (Hol : forall a, owned B L1 A1 a -> 0 <= a < alloc_ceiling)
    by (intros a Ha; exact (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ H1 Ha)).
  assert (Hq : forall a, ~ scratch_k B K regs a -> ~ E a -> Frame.outside W a).
  { intros a Hs He. apply g_out. intros Hn. destruct (HW a Hn) as [[Hx|Hx] _];
      [apply Hs; left; exact Hx | exact (He Hx)]. }
  split.
  { destruct (mr_model _ _ (aa_laws API) _ _ _ _ H1) as (Hh & Hl & Hmat).
    apply (mr_frame _ _ (aa_laws API) L1 A1 mem1 mem2 md1 md1 H1).
    - intros a Ha. pose proof (Hol a Ha). apply (mbyte_munch (ms_segs B) W); [exact Hm | lia | exact (Ho a Ha)].
    - intros a Ha Hpr. pose proof (Hol a Ha).
      apply (present_munch W mem1); [exact Hm | lia | exact (Ho a Ha) | exact Hpr].
    - intros q n i Hin Hi. destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ q n i H1 Hin Hi) as ((b0 & Hb) & R1 & R2 & _).
      destruct (kb_outside_dec W (ptr_addr L1 q + i)) as [Hout|Hout].
      + exists b0. rewrite (Hm (Z_to_bv 64 (ptr_addr L1 q + i))); [exact Hb|]. rewrite unsigned_lit by lia. exact Hout.
      + destruct (mem2 (Z_to_bv 64 (ptr_addr L1 q + i))) as [b'|] eqn:E2; [exists b'; exact E2|].
        exfalso. refine (Hp (ptr_addr L1 q + i) ltac:(lia) Hout _ E2). rewrite Hb. discriminate.
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split.
  { intros Hd i Hi. rewrite <- (H6 Hd i Hi).
    assert (Hs : owned B L1 A1 (ms_libc B + 8 + i)) by (right; unfold static_owned; right; right; left; lia).
    pose proof (Hol _ Hs). apply (mbyte_munch (ms_segs B) W); [exact Hm | lia | exact (Ho _ Hs)]. }
  split; [exact H7|]. split; [exact H8|]. split; [exact H9|]. split; [exact H10|]. split; [exact H11|].
  split.
  { intros a Ha Hs He. destruct (H12 a Ha Hs He) as [E1 E2]. pose proof (Hq a Hs He) as Hout.
    pose proof alloc_ceiling_value.
    split; [rewrite (mbyte_munch (ms_segs B) W mem1 mem2 a Hm ltac:(lia) Hout); exact E1|].
    rewrite E2. exact (writable_munch (ms_segs B) W mem1 mem2 a Hm ltac:(lia) Hout). }
  split.
  { intros a Ha Hn Hs He. destruct (H13 a Ha Hn Hs He) as [E1 E2].
    pose proof (proj1 HIL a Ha) as Har. pose proof (Hq a Hs He) as Hout.
    split; [rewrite (mbyte_munch (ms_segs B) W mem1 mem2 a Hm ltac:(lia) Hout); exact E1|].
    rewrite E2. exact (writable_munch (ms_segs B) W mem1 mem2 a Hm ltac:(lia) Hout). }
  split.
  { intros p n i Hin Hin1 Hi He. rewrite <- (H14 p n i Hin Hin1 Hi He).
    destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ p n i HM0 Hin Hi) as (_ & R1 & R2 & _).
    apply (mbyte_munch (ms_segs B) W); [exact Hm | lia |]. apply g_out. intros Hn.
    destruct (HW _ Hn) as [[Hx|Hx] _]; [lia | exact (He Hx)]. }
  intros a Ha. unfold writable_at. apply Hw. exact (H15 a Ha).
Qed.

Lemma rp_call : img_low B -> forall K L A regs mem md E gone L1 A1 mem1 md1 K1 regs1 E1 g1 L2 A2 regs2 mem2 md2,
  aa_MR API L A mem md -> WF A -> alloc_ceiling + K <= spZ regs -> spZ regs <= 2 ^ 64 ->
  spZ regs - K <= spZ regs1 - K1 -> spZ regs1 <= spZ regs ->
  rpost B API K L A regs mem md E gone L1 A1 regs mem1 md1 ->
  call_post_k B (aa_MR API) K1 L1 A1 regs1 mem1 md1 E1 L2 A2 regs2 mem2 md2 ->
  (st_init_done A1 = true -> st_init_done A2 = true) ->
  (st_init_done A2 = false -> forall i, 0 <= i < 8 ->
     mbyte (ms_segs B) mem2 (ms_libc B + 8 + i) = mbyte (ms_segs B) mem1 (ms_libc B + 8 + i)) ->
  (length (st_regions A1) <= length (st_regions A2))%nat ->
  ublocks_kept L1 A1 A2 g1 ->
  (forall a, E1 a -> a < alloc_ceiling /\ (in_img B a -> E a)) ->
  (forall p n, In (p, n) (user_blocks A) -> (ptr_addr L p, n) = g1 -> gone (ptr_addr L p) n) ->
  (forall p n i, In (p, n) (user_blocks A) -> 0 <= i < n -> gone (ptr_addr L p) n -> E (ptr_addr L p + i)) ->
  rpost B API K L A regs mem md E gone L2 A2 regs mem2 md2.
Proof.
  intros HIL K L A regs mem md E gone L1 A1 mem1 md1 K1 regs1 E1 g1 L2 A2 regs2 mem2 md2
    HM0 HWF0 Hsp Hsp2 Hk1 Hk2
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15)
    (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10) Hi Hav Hlen Hub HE1 Hg Hge.
  pose proof alloc_ceiling_lt as Hc.
  assert (Hscr : forall a, ~ scratch_k B K regs a -> ~ scratch_k B K1 regs1 a).
  { intros a Hs [Hx|Hx]; apply Hs; [left; lia | right; exact Hx]. }
  assert (Hlay : layout_le A L L2).
  { destruct H4 as (a1 & a2 & a3 & a4). destruct C4 as (b1 & b2 & b3 & b4).
    split; [congruence|]. split; [congruence|]. split; [congruence|].
    intros r Hr. rewrite (b4 r ltac:(lia)). exact (a4 r Hr). }
  split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact Hlay|].
  split; [intros Hd; exact (Hi (H5 Hd))|].
  split.
  { intros Hd i Hr. rewrite (Hav Hd i Hr). apply H6; [|exact Hr].
    destruct (st_init_done A1) eqn:Ed; [rewrite (Hi eq_refl) in Hd; discriminate | reflexivity]. }
  split; [lia|].
  split.
  { intros p n Hin Hng. pose proof (H8 p n Hin Hng) as Hin1. apply Hub; [exact Hin1|].
    rewrite (H9 p n Hin Hin1). intros Heq. exact (Hng (Hg p n Hin Heq)). }
  split; [intros p n Hin _; exact (g_ptr L L2 A p n HWF0 Hin Hlay)|].
  split; [exact H10|].
  split; [destruct C7 as (vm2 & ->); destruct H11 as (vm1 & ->); exists vm2; apply g_vm|].
  split.
  { intros a Ha Hs He. destruct (H12 a Ha Hs He) as [E1a E1w].
    assert (No1 : ~ owned B L1 A1 a) by (intros Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ H1 Ho); lia).
    assert (No2 : ~ owned B L2 A2 a) by (intros Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ C1 Ho); lia).
    destruct (C8 a (or_introl Ha) No1 No2 (Hscr a Hs) ltac:(intros HE; pose proof (proj1 (HE1 a HE)); lia))
      as [E2a E2w].
    split; [congruence | tauto]. }
  split.
  { intros a Ha Hn Hs He. destruct (H13 a Ha Hn Hs He) as [E1a E1w].
    destruct (C8 a (or_intror Ha) (Hn _ _ _ _ H1) (Hn _ _ _ _ C1) (Hscr a Hs)
      ltac:(intros HE; exact (He (proj2 (HE1 a HE) Ha)))) as [E2a E2w].
    split; [congruence | tauto]. }
  split.
  { intros p n i Hin Hin2 Hi' He.
    assert (Hng : ~ gone (ptr_addr L p) n) by (intros Hgo; exact (He (Hge p n i Hin Hi' Hgo))).
    pose proof (H8 p n Hin Hng) as Hin1.
    rewrite <- (H14 p n i Hin Hin1 Hi' He). rewrite <- (H9 p n Hin Hin1). exact (C9 p n i Hin1 Hin2 Hi'). }
  intros a Ha.
  assert (D : scratch_k B K1 regs1 a \/ ~ scratch_k B K1 regs1 a) by (unfold scratch_k; lia).
  destruct D as [D|D]; [exact (C10 a D)|].
  destruct Ha as [Ha|Ha]; [|exfalso; apply D; right; exact Ha].
  assert (No1 : ~ owned B L1 A1 a) by (intros Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ H1 Ho); lia).
  assert (No2 : ~ owned B L2 A2 a) by (intros Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ C1 Ho); lia).
  destruct (C8 a ltac:(left; lia) No1 No2 D ltac:(intros HE; pose proof (proj1 (HE1 a HE)); lia)) as [_ Ew].
  apply Ew. apply H15. left. exact Ha.
Qed.


Lemma rp_A2 : img_low B -> forall K L A regs mem md E gone L1 A1 mem1 md1 mem2 W,
  aa_MR API L A mem md -> alloc_ceiling + K <= spZ regs ->
  rpost B API K L A regs mem md E gone L1 A1 regs mem1 md1 ->
  Frame.munch W mem1 mem2 -> Frame.wmono (ms_segs B) mem1 mem2 ->
  (forall x, 0 <= x < alloc_ceiling -> ~ Frame.outside W x -> mem1 (Z_to_bv 64 x) <> None ->
     mem2 (Z_to_bv 64 x) <> None) ->
  (forall x, ~ Frame.outside W x -> ~ owned B L1 A1 x /\
     ((spZ regs - K <= x < spZ regs) \/ E x \/
      (x < alloc_ceiling /\ ~ in_img B x /\
       forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A1) -> ~ (ptr_addr L p <= x < ptr_addr L p + n)))) ->
  rpost B API K L A regs mem md E gone L1 A1 regs mem2 md1.
Proof.
  intros HIL K L A regs mem md E gone L1 A1 mem1 md1 mem2 W HM0 Hsp
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15) Hm Hw Hp HW.
  pose proof alloc_ceiling_lt as Hc. pose proof alloc_ceiling_value as Hcv.
  assert (Ho : forall a, owned B L1 A1 a -> Frame.outside W a).
  { intros a Ha. apply g_out. intros Hn. exact (proj1 (HW a Hn) Ha). }
  assert (Hol : forall a, owned B L1 A1 a -> 0 <= a < alloc_ceiling)
    by (intros a Ha; exact (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ H1 Ha)).
  assert (Hqh : forall a, alloc_ceiling <= a -> ~ scratch_k B K regs a -> ~ E a -> Frame.outside W a).
  { intros a Hh Hs He. apply g_out. intros Hn. destruct (HW a Hn) as [_ [Hx|[Hx|(Hx & _)]]];
      [apply Hs; left; exact Hx | exact (He Hx) | lia]. }
  assert (Hqi : forall a, in_img B a -> ~ scratch_k B K regs a -> ~ E a -> Frame.outside W a).
  { intros a Hi Hs He. apply g_out. intros Hn. destruct (HW a Hn) as [_ [Hx|[Hx|(_ & Hx & _)]]];
      [apply Hs; left; exact Hx | exact (He Hx) | exact (Hx Hi)]. }
  split.
  { destruct (mr_model _ _ (aa_laws API) _ _ _ _ H1) as (Hh & Hl & Hmat).
    apply (mr_frame _ _ (aa_laws API) L1 A1 mem1 mem2 md1 md1 H1).
    - intros a Ha. pose proof (Hol a Ha). apply (mbyte_munch (ms_segs B) W); [exact Hm | lia | exact (Ho a Ha)].
    - intros a Ha Hpr. pose proof (Hol a Ha).
      apply (present_munch W mem1); [exact Hm | lia | exact (Ho a Ha) | exact Hpr].
    - intros q n i Hin Hi. destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ q n i H1 Hin Hi) as ((b0 & Hb) & R1 & R2 & _).
      destruct (kb_outside_dec W (ptr_addr L1 q + i)) as [Hout|Hout].
      + exists b0. rewrite (Hm (Z_to_bv 64 (ptr_addr L1 q + i))); [exact Hb|]. rewrite unsigned_lit by lia. exact Hout.
      + destruct (mem2 (Z_to_bv 64 (ptr_addr L1 q + i))) as [b'|] eqn:E2; [exists b'; exact E2|].
        exfalso. refine (Hp (ptr_addr L1 q + i) ltac:(lia) Hout _ E2). rewrite Hb. discriminate.
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split.
  { intros Hd i Hi. rewrite <- (H6 Hd i Hi).
    assert (Hs : owned B L1 A1 (ms_libc B + 8 + i)) by (right; unfold static_owned; right; right; left; lia).
    pose proof (Hol _ Hs). apply (mbyte_munch (ms_segs B) W); [exact Hm | lia | exact (Ho _ Hs)]. }
  split; [exact H7|]. split; [exact H8|]. split; [exact H9|]. split; [exact H10|]. split; [exact H11|].
  split.
  { intros a Ha Hs He. destruct (H12 a Ha Hs He) as [E1 E2]. pose proof (Hqh a ltac:(lia) Hs He) as Hout.
    split; [rewrite (mbyte_munch (ms_segs B) W mem1 mem2 a Hm ltac:(lia) Hout); exact E1|].
    rewrite E2. exact (writable_munch (ms_segs B) W mem1 mem2 a Hm ltac:(lia) Hout). }
  split.
  { intros a Ha Hn Hs He. destruct (H13 a Ha Hn Hs He) as [E1 E2].
    pose proof (proj1 HIL a Ha) as Har. pose proof (Hqi a Ha Hs He) as Hout.
    split; [rewrite (mbyte_munch (ms_segs B) W mem1 mem2 a Hm ltac:(lia) Hout); exact E1|].
    rewrite E2. exact (writable_munch (ms_segs B) W mem1 mem2 a Hm ltac:(lia) Hout). }
  split.
  { intros p n i Hin Hin1 Hi He. rewrite <- (H14 p n i Hin Hin1 Hi He).
    destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ p n i HM0 Hin Hi) as (_ & R1 & R2 & _).
    apply (mbyte_munch (ms_segs B) W); [exact Hm | lia |]. apply g_out. intros Hn.
    destruct (HW _ Hn) as [_ [Hx|[Hx|(_ & _ & Hx)]]]; [lia | exact (He Hx) | exact (Hx p n Hin Hin1 ltac:(lia))]. }
  intros a Ha. unfold writable_at. apply Hw. exact (H15 a Ha).
Qed.

Lemma rp_rec : forall K L A regs mem md E gone L1 A1 mem1 md1 K1 regs1 E1 g1 L2 A2 regs2 mem2 md2,
  WF A -> alloc_ceiling + K <= spZ regs -> spZ regs <= 2 ^ 64 ->
  spZ regs - K <= spZ regs1 - K1 -> spZ regs1 <= spZ regs ->
  rpost B API K L A regs mem md E gone L1 A1 regs mem1 md1 ->
  rpost B API K1 L1 A1 regs1 mem1 md1 E1 g1 L2 A2 regs2 mem2 md2 ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ scratch_k B K regs a -> E1 a -> E a) ->
  (forall a, in_img B a -> ~ scratch_k B K regs a -> E1 a -> E a) ->
  (forall p n i, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A1) -> 0 <= i < n ->
     E1 (ptr_addr L p + i) -> E (ptr_addr L p + i)) ->
  (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A1) -> g1 (ptr_addr L p) n -> gone (ptr_addr L p) n) ->
  (forall p n i, In (p, n) (user_blocks A) -> 0 <= i < n -> gone (ptr_addr L p) n -> E (ptr_addr L p + i)) ->
  (forall a, spZ regs - K <= a < spZ regs -> ~ scratch_k B K1 regs1 a -> ~ E1 a) ->
  rpost B API K L A regs mem md E gone L2 A2 regs mem2 md2.
Proof.
  intros K L A regs mem md E gone L1 A1 mem1 md1 K1 regs1 E1 g1 L2 A2 regs2 mem2 md2
    HWF0 Hsp Hsp2 Hk1 Hk2
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15)
    (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15)
    HEh HEi HEb Hg Hge HEs.
  pose proof alloc_ceiling_lt as Hc.
  assert (Hscr : forall a, ~ scratch_k B K regs a -> ~ scratch_k B K1 regs1 a).
  { intros a Hs [Hx|Hx]; apply Hs; [left; lia | right; exact Hx]. }
  assert (Hlay : layout_le A L L2).
  { destruct H4 as (a1 & a2 & a3 & a4). destruct C4 as (b1 & b2 & b3 & b4).
    split; [congruence|]. split; [congruence|]. split; [congruence|].
    intros r Hr. rewrite (b4 r ltac:(lia)). exact (a4 r Hr). }
  split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact Hlay|].
  split; [intros Hd; exact (C5 (H5 Hd))|].
  split.
  { intros Hd i Hr. rewrite (C6 Hd i Hr). apply H6; [|exact Hr].
    destruct (st_init_done A1) eqn:Ed; [rewrite (C5 eq_refl) in Hd; discriminate | reflexivity]. }
  split; [lia|].
  split.
  { intros p n Hin Hng. pose proof (H8 p n Hin Hng) as Hin1. apply C8; [exact Hin1|].
    rewrite (H9 p n Hin Hin1). intros Hg1. exact (Hng (Hg p n Hin Hin1 Hg1)). }
  split; [intros p n Hin _; exact (g_ptr L L2 A p n HWF0 Hin Hlay)|].
  split; [exact H10|].
  split; [destruct C11 as (vm2 & ->); destruct H11 as (vm1 & ->); exists vm2; apply g_vm|].
  split.
  { intros a Ha Hs He. destruct (H12 a Ha Hs He) as [E1a E1w].
    destruct (C12 a Ha (Hscr a Hs) ltac:(intros HE; exact (He (HEh a Ha Hs HE)))) as [E2a E2w].
    split; [congruence | tauto]. }
  split.
  { intros a Ha Hn Hs He. destruct (H13 a Ha Hn Hs He) as [E1a E1w].
    destruct (C13 a Ha Hn (Hscr a Hs) ltac:(intros HE; exact (He (HEi a Ha Hs HE)))) as [E2a E2w].
    split; [congruence | tauto]. }
  split.
  { intros p n i Hin Hin2 Hi' He.
    assert (Hng : ~ gone (ptr_addr L p) n) by (intros Hgo; exact (He (Hge p n i Hin Hi' Hgo))).
    pose proof (H8 p n Hin Hng) as Hin1.
    rewrite <- (H14 p n i Hin Hin1 Hi' He). rewrite <- (H9 p n Hin Hin1).
    apply (C14 p n i Hin1 Hin2 Hi'). rewrite (H9 p n Hin Hin1). intros HE. exact (He (HEb p n i Hin Hin1 Hi' HE)). }
  intros a Ha.
  assert (D : scratch_k B K1 regs1 a \/ ~ scratch_k B K1 regs1 a) by (unfold scratch_k; lia).
  destruct D as [D|D]; [exact (C15 a D)|].
  destruct Ha as [Ha|Ha]; [|exfalso; apply D; right; exact Ha].
  destruct (C12 a ltac:(lia) D (HEs a Ha D)) as [_ Ew].
  apply Ew. apply H15. left. exact Ha.
Qed.

Lemma rp_same_hi : forall K L A regs mem md E gone L' A' regs' mem' md' x,
  rpost B API K L A regs mem md E gone L' A' regs' mem' md' ->
  alloc_ceiling <= x < 2 ^ 64 -> ~ scratch_k B K regs x -> ~ E x ->
  pis_same (ms_segs B) mem mem' x.
Proof.
  intros K L A regs mem md E gone L' A' regs' mem' md' x
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H12 & _) Hx Hs He.
  destruct (H12 x Hx Hs He) as [E1 E2]. split; [exact E1 | apply E2].
Qed.

Lemma rp_same_blk : forall K L A regs mem md E gone L' A' regs' mem' md' a k x,
  rpost B API K L A regs mem md E gone L' A' regs' mem' md' ->
  In (a, k) (blocks L A) -> ~ gone a k -> a <= x < a + k -> ~ E x ->
  pis_same (ms_segs B) mem mem' x.
Proof.
  intros K L A regs mem md E gone L' A' regs' mem' md' a k x
    (H1 & _ & _ & _ & _ & _ & _ & H8 & H9 & _ & _ & _ & _ & H14 & _) Hin Hg Hx He.
  destruct (g_blocks_user L A a k Hin) as (q & Hq & Eq).
  assert (Hq' : In (q, k) (user_blocks A')) by (apply H8; [exact Hq | rewrite Eq; exact Hg]).
  split.
  - assert (He' : ~ E (ptr_addr L q + (x - a))) by (rewrite Eq; replace (a + (x - a)) with x by lia; exact He).
    pose proof (H14 q k (x - a) Hq Hq' ltac:(lia) He') as Eb. rewrite Eq in Eb.
    replace (a + (x - a)) with x in Eb by lia. exact Eb.
  - intros _. destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ q k (x - a) H1 Hq' ltac:(lia)) as (P & _).
    rewrite (H9 q k Hq Hq'), Eq in P. replace (a + (x - a)) with x in P by lia.
    exact (present_writable B mem' x P).
Qed.

Lemma rp_blk_kept : forall K L A regs mem md E gone L' A' regs' mem' md' a k,
  rpost B API K L A regs mem md E gone L' A' regs' mem' md' ->
  In (a, k) (blocks L A) -> ~ gone a k -> In (a, k) (blocks L' A').
Proof.
  intros K L A regs mem md E gone L' A' regs' mem' md' a k (_ & _ & _ & _ & _ & _ & _ & H8 & H9 & _) Hin Hg.
  destruct (g_blocks_user L A a k Hin) as (q & Hq & Eq).
  assert (Hq' : In (q, k) (user_blocks A')) by (apply H8; [exact Hq | rewrite Eq; exact Hg]).
  rewrite <- Eq, <- (H9 q k Hq Hq'). exact (g_user_blocks L' A' q k Hq').
Qed.

Lemma vloc_rp : forall L1 A1 Lam1 S v r rk K1 regs1 mem1 md1 E1 g1 L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2,
  vloc L1 A1 Lam1 S v r rk ->
  rpost B API K1 L1 A1 regs1 mem1 md1 E1 g1 L2 A2 regs2 mem2 md2 -> ~ g1 r rk ->
  ledger B L2 A2 mem2 Lam2 peak2 cnt2 fail2 ->
  (forall a k, In (a, k) Lam2 -> In (a, k) Lam1 \/ ~ In (a - 16, k + 16) (blocks L1 A1)) ->
  vloc L2 A2 Lam2 S v r rk.
Proof.
  intros L1 A1 Lam1 S v r rk K1 regs1 mem1 md1 E1 g1 L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2
    [Hs|(Hin & H1 & H2 & Hh)] HP Hg HL Hsub; [left; exact Hs|].
  right. pose proof (rp_blk_kept _ _ _ _ _ _ _ _ _ _ _ _ _ r rk HP Hin Hg) as Hin2.
  split; [exact Hin2|]. split; [exact H1|]. split; [exact H2|].
  intros a k Hak. destruct (Hsub a k Hak) as [Ho|Hn]; [exact (Hh a k Ho)|].
  pose proof HL as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF. destruct (HF _ Hak) as (Hk & Hb & _).
  cbn [fst snd] in *.
  assert (Hd : (a - 16, k + 16) <> (r, rk)) by (intros E; rewrite E in Hn; exact (Hn Hin)).
  pose proof HP as (HM2 & _).
  destruct (g_disj L2 A2 mem2 md2 _ _ _ _ HM2 Hb Hin2 Hd); lia.
Qed.

Lemma vloc_same : forall L1 A1 Lam1 S v r rk K1 regs1 mem1 md1 E1 g1 L2 A2 regs2 mem2 md2 x,
  vloc L1 A1 Lam1 S v r rk ->
  rpost B API K1 L1 A1 regs1 mem1 md1 E1 g1 L2 A2 regs2 mem2 md2 -> ~ g1 r rk ->
  alloc_ceiling <= S -> spZ regs1 <= S -> ~ (errno_addr B <= x < errno_addr B + 4) -> v <= x < v + 56 -> ~ E1 x ->
  pis_same (ms_segs B) mem1 mem2 x.
Proof.
  intros L1 A1 Lam1 S v r rk K1 regs1 mem1 md1 E1 g1 L2 A2 regs2 mem2 md2 x
    [(Hs & Hv & _ & _)|(Hin & H1 & H2 & _)] HP Hg Hc Hsp Herr Hx HE.
  - apply (rp_same_hi _ _ _ _ _ _ _ _ _ _ _ _ _ x HP ltac:(lia)); [unfold scratch_k; lia | exact HE].
  - exact (rp_same_blk _ _ _ _ _ _ _ _ _ _ _ _ _ r rk x HP Hin Hg ltac:(lia) HE).
Qed.

Lemma g_perm_sub : forall (l1 l2 : list (Z * Z)), List.NoDup l1 -> incl l1 l2 -> List.NoDup l2 ->
  exists r, Permutation l2 (l1 ++ r).
Proof.
  induction l1 as [|x l1 IH]; intros l2 H1 H2 H3.
  - exists l2. reflexivity.
  - assert (Hx : In x l2) by (apply H2; left; reflexivity).
    destruct (in_split x l2 Hx) as (u & v & ->).
    apply List.NoDup_cons_iff in H1 as [Hn1 Hd1].
    destruct (IH (u ++ v) Hd1) as (r & Hr).
    + intros y Hy. assert (Hy' : In y (u ++ x :: v)) by (apply H2; right; exact Hy).
      apply in_app_or in Hy'. apply in_or_app.
      destruct Hy' as [Hy'|[Hy'|Hy']]; [left; exact Hy' | subst y; contradiction | right; exact Hy'].
    + exact (List.NoDup_remove_1 u v x H3).
    + exists r. eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|]. cbn [app].
      apply perm_skip. exact Hr.
Qed.

Lemma g_pre_k : forall K L A regs mem md E gone L1 A1 mem1 md1 regs1 K1 lo,
  call_pre_k B (aa_MR API) K L A regs mem md ->
  rpost B API K L A regs mem md E gone L1 A1 regs mem1 md1 ->
  YK0s.ret_ok (YK11.getr regs1 1) -> spZ regs1 mod 16 = 0 ->
  spZ regs - K <= spZ regs1 - K1 -> spZ regs1 <= spZ regs -> 0 <= K1 ->
  YK11.getr regs1 4 = YK11.getr regs 4 -> errno_addr B + 4 <= spZ regs ->
  spZ regs <= lo -> (st_init_done A = false -> auxv_pre B (ly_sec L) lo mem) -> (forall x, E x -> x < lo) ->
  call_pre_k B (aa_MR API) K1 L1 A1 regs1 mem1 md1.
Proof.
  intros K L A regs mem md E gone L1 A1 mem1 md1 regs1 K1 lo
    (HM & HW & HB & Hra & H16 & Hc & H63 & Hst & Htp & Her & Hax)
    (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15)
    Hra1 H161 Hk1 Hk2 HK1 Htp1 Herr Hlo Hax0 HElo.
  pose proof alloc_ceiling_lt as Hcl.
  split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact Hra1|].
  split; [exact H161|]. split; [lia|]. split; [lia|].
  split; [intros a Ha; apply C15; left; lia|].
  split; [transitivity (YK11.getr regs 4); [exact Htp1 | exact Htp]|].
  split; [intros a Ha; apply C15; right; exact Ha|].
  intros Hd.
  assert (HdA : st_init_done A = false)
    by (destruct (st_init_done A) eqn:Ed; [rewrite (C5 eq_refl) in Hd; discriminate | reflexivity]).
  destruct C4 as (_ & Hsec & _ & _). rewrite Hsec.
  apply (auxv_pre_mono B (ly_sec L) lo (spZ regs1) mem1); [lia|].
  apply (g_auxv_keep (ly_sec L) lo mem mem1 (Hax0 HdA)).
  - intros i Hi. exact (C6 Hd i Hi).
  - intros a Ha.
    assert (Hns : ~ scratch_k B K regs a) by (unfold scratch_k; lia).
    assert (HnE : ~ E a) by (intros He; pose proof (HElo a He); lia).
    exact (proj1 (C12 a ltac:(lia) Hns HnE)).
Qed.

Lemma g_bytes_old : forall m a k, 0 <= a -> 0 <= k -> a + k <= 2 ^ 64 ->
  (forall i, 0 <= i < k -> mbyte (ms_segs B) m (a + i) <> None) ->
  exists bs, Z.of_nat (length bs) = k /\ bytes_at (ms_segs B) m a bs.
Proof.
  intros m a k H0 Hk H1 H. destruct (g_old (ms_segs B) m a k Hk H) as (bs & Hl & Hb).
  exists bs. split; [exact Hl|]. split; [exact H0|]. split; [lia|].
  intros i Hi. rewrite <- t_mbyte_mrd. rewrite (Hb (Z.of_nat i) ltac:(lia)). rewrite Nat2Z.id. reflexivity.
Qed.

Lemma g_bytes_eq : forall m m' a a' bs, bytes_at (ms_segs B) m a bs -> bytes_at (ms_segs B) m' a' bs ->
  forall i, 0 <= i < Z.of_nat (length bs) -> mbyte (ms_segs B) m (a + i) = mbyte (ms_segs B) m' (a' + i).
Proof.
  intros m m' a a' bs (_ & _ & H) (_ & _ & H') i Hi.
  rewrite !t_mbyte_mrd. replace i with (Z.of_nat (Z.to_nat i)) by lia.
  rewrite (H (Z.to_nat i) ltac:(lia)), (H' (Z.to_nat i) ltac:(lia)). reflexivity.
Qed.

Lemma g_rw56 : forall m a bs, length bs = 56%nat -> bytes_at (ms_segs B) m a bs ->
  (forall i, 0 <= i < 56 -> writable_at (ms_segs B) m (a + i)) -> rw_cells (ms_segs B) m a [CB 56 bs].
Proof.
  intros m a bs Hl Hb Hw. split.
  - split; [cbn; split; [exact Hl | exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact Hb].
  - cbn [cells_size csize Nat.add]. pose proof Hb as (H0 & H1 & _). rewrite Hl in H1.
    split; [exact H0|]. split; [lia|]. intros i Hi. exact (Hw i Hi).
Qed.

Lemma g_present_wr : ms_segs B = rsegs -> forall m x, 0 <= x < 2 ^ 64 -> ~ in_img B x ->
  writable_at (ms_segs B) m x -> m (Z_to_bv 64 x) <> None.
Proof.
  intros HSEG m x Hx Hn W.
  destruct (find_segment (ms_segs B) x 1) as [seg|] eqn:F; [exfalso; exact (Hn (g_seg_img HSEG x seg F))|].
  revert W. unfold writable_at, wview.
  destruct (m (Z_to_bv 64 x)) as [b|]; intros W; [discriminate|].
  rewrite unsigned_lit in W by lia. rewrite F in W. contradiction.
Qed.

Lemma g_stk_rw : forall m a cs, rw_cells (ms_segs B) m a cs ->
  stk (ms_segs B) m a (a + Z.of_nat (cells_size cs)).
Proof.
  intros m a cs [[Hwf (H0 & H1 & HB)] (W0 & W1 & HW)].
  rewrite cells_bytes_length in HB by exact Hwf.
  split; [lia|]. split; [lia|]. intros x Hx. split.
  - replace x with (a + (x - a)) by lia. apply HW. lia.
  - pose proof (HB (Z.to_nat (x - a)) ltac:(lia)) as E.
    replace (a + Z.of_nat (Z.to_nat (x - a))) with x in E by lia.
    destruct (nth_error (cells_bytes cs) (Z.to_nat (x - a))) as [b|] eqn:N; [exists b; exact E|].
    apply nth_error_None in N. rewrite cells_bytes_length in N by exact Hwf. lia.
Qed.

Lemma g_range_img : ms_segs B = rsegs -> forall base n x,
  forallb (fun j => match find_segment rsegs (base + Z.of_nat j) 1 with Some _ => true | None => false end)
    (seq 0 n) = true ->
  base <= x < base + Z.of_nat n -> in_img B x.
Proof.
  intros HSEG base n x Hc Hx. rewrite forallb_forall in Hc.
  specialize (Hc (Z.to_nat (x - base)) ltac:(apply in_seq; lia)).
  replace (base + Z.of_nat (Z.to_nat (x - base))) with x in Hc by lia.
  destruct (find_segment rsegs x 1) as [seg|] eqn:F; [|discriminate].
  rewrite <- HSEG in F. exact (g_seg_img HSEG x seg F).
Qed.

Lemma g_img_consts : ms_segs B = rsegs -> errno_addr B = strtod_c.STRTOD_ERRNO ->
  forall x, alloc_statics x \/ errno_addr B <= x < errno_addr B + 4 -> in_img B x.
Proof.
  intros HSEG Herr x [[Hx|[Hx|[Hx|Hx]]]|Hx].
  - apply (g_range_img HSEG G_LIVE 8 x); [vm_compute; reflexivity | lia].
  - apply (g_range_img HSEG G_PEAK 8 x); [vm_compute; reflexivity | lia].
  - apply (g_range_img HSEG G_COUNT 8 x); [vm_compute; reflexivity | lia].
  - apply (g_range_img HSEG G_FAIL 8 x); [vm_compute; reflexivity | lia].
  - rewrite Herr in Hx. apply (g_range_img HSEG strtod_c.STRTOD_ERRNO 4 x); [vm_compute; reflexivity | lia].
Qed.

Lemma g_aux_rp : forall K L A regs mem md E gone L1 A1 regs1 mem1 md1 lo lo',
  rpost B API K L A regs mem md E gone L1 A1 regs1 mem1 md1 -> 0 <= K ->
  alloc_ceiling + K <= spZ regs -> errno_addr B + 4 <= spZ regs ->
  spZ regs <= lo -> lo' <= lo -> (st_init_done A = false -> auxv_pre B (ly_sec L) lo mem) ->
  (forall x, E x -> x < lo) ->
  st_init_done A1 = false -> auxv_pre B (ly_sec L1) lo' mem1.
Proof.
  intros K L A regs mem md E gone L1 A1 regs1 mem1 md1 lo lo'
    (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15) HK Hc Herr Hlo Hlo' Hax HElo Hd.
  pose proof alloc_ceiling_lt as Hcl.
  assert (HdA : st_init_done A = false)
    by (destruct (st_init_done A) eqn:Ed; [rewrite (C5 eq_refl) in Hd; discriminate | reflexivity]).
  destruct C4 as (_ & Hsec & _ & _). rewrite Hsec.
  apply (auxv_pre_mono B (ly_sec L) lo lo' mem1 Hlo').
  apply (g_auxv_keep (ly_sec L) lo mem mem1 (Hax HdA)).
  - intros i Hi. exact (C6 Hd i Hi).
  - intros a Ha.
    assert (Hns : ~ scratch_k B K regs a) by (unfold scratch_k; lia).
    assert (HnE : ~ E a) by (intros He; pose proof (HElo a He); lia).
    exact (proj1 (C12 a ltac:(lia) Hns HnE)).
Qed.

Definition vplace (L : layout) (A : astate) (Lam : list (Z * Z)) (S v r rk : Z) : Prop :=
  vloc L A Lam S v r rk /\ (r + 16 <= v \/ ~ lin Lam (r + 16) (rk - 16)).

Lemma g_vplace0 : forall L A mem md Lam peak cnt fail S v,
  aa_MR API L A mem md -> ledger B L A mem Lam peak cnt fail -> alloc_ceiling <= S ->
  pj_place (lin Lam) (fun a k => In (a, k) (blocks L A)) S (2 ^ 64) v ->
  exists r rk, vplace L A Lam S v r rk.
Proof.
  intros L A mem md Lam peak cnt fail S v HM HL Hc Hpl.
  pose proof alloc_ceiling_value as Hcv.
  pose proof HL as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF.
  destruct Hpl as [(H1 & H2)|[(a & k & Hb & Hnl & H1 & H2)|(a & k & Hl & H1 & H2)]].
  - exists 0, (-1). split; [left; split; [lia|]; split; [lia|]; split; reflexivity | left; lia].
  - exists a, k. split; [|right; exact Hnl].
    right. split; [exact Hb|]. split; [lia|]. split; [lia|].
    intros a' k' Hin. destruct (HF _ Hin) as (Hk' & Hb' & _). cbn [fst snd] in *.
    assert (Hne : (a' - 16, k' + 16) <> (a, k)).
    { intros E. injection E as E1 E2. apply Hnl. unfold lin.
      replace (a + 16) with a' by lia. replace (k - 16) with k' by lia. exact Hin. }
    destruct (g_disj L A mem md _ _ _ _ HM Hb' Hb Hne); lia.
  - destruct (HF _ Hl) as (Hk & Hb & _). cbn [fst snd] in *.
    exists (a - 16), (k + 16). split; [|left; lia].
    right. split; [exact Hb|]. split; [lia|]. split; [lia|].
    intros a' k' Hin. destruct (HF _ Hin) as (Hk' & Hb' & _). cbn [fst snd] in *.
    destruct (Z.eq_dec a' a) as [->|Ha'].
    + left; lia.
    + assert (Hne : (a' - 16, k' + 16) <> (a - 16, k + 16)) by (intros E; injection E; lia).
      destruct (g_disj L A mem md _ _ _ _ HM Hb' Hb Hne); lia.
Qed.

Lemma vplace_rp : forall L1 A1 Lam1 S v r rk K1 regs1 mem1 md1 E1 g1 L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2,
  vplace L1 A1 Lam1 S v r rk ->
  rpost B API K1 L1 A1 regs1 mem1 md1 E1 g1 L2 A2 regs2 mem2 md2 -> ~ g1 r rk ->
  ledger B L2 A2 mem2 Lam2 peak2 cnt2 fail2 ->
  (forall a k, In (a, k) Lam2 -> In (a, k) Lam1 \/ ~ In (a - 16, k + 16) (blocks L1 A1)) ->
  vplace L2 A2 Lam2 S v r rk.
Proof.
  intros L1 A1 Lam1 S v r rk K1 regs1 mem1 md1 E1 g1 L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2
    (HV & Hp) HP Hg HL Hsub.
  split; [exact (vloc_rp L1 A1 Lam1 S v r rk K1 regs1 mem1 md1 E1 g1 L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2
    HV HP Hg HL Hsub)|].
  destruct Hp as [Hp|Hp]; [left; exact Hp|]. right. intros Hl.
  destruct HV as [(_ & _ & _ & Erk)|(Hin & _)].
  - unfold lin in Hl. pose proof HL as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF.
    destruct (HF _ Hl) as (Hk & _). cbn [snd] in Hk. lia.
  - destruct (Hsub _ _ Hl) as [H1|H1]; [exact (Hp H1)|]. apply H1.
    replace (r + 16 - 16) with r by lia. replace (rk - 16 + 16) with rk by lia. exact Hin.
Qed.

Lemma vplace_call : forall L1 A1 Lam1 S v r rk K1 regs1 mem1 md1 E1 L2 A2 regs2 mem2 md2 g Lam2 peak2 cnt2 fail2,
  vplace L1 A1 Lam1 S v r rk ->
  call_post_k B (aa_MR API) K1 L1 A1 regs1 mem1 md1 E1 L2 A2 regs2 mem2 md2 ->
  ublocks_kept L1 A1 A2 g -> (r, rk) <> g ->
  ledger B L2 A2 mem2 Lam2 peak2 cnt2 fail2 ->
  (forall a k, In (a, k) Lam2 -> In (a, k) Lam1 \/ ~ In (a - 16, k + 16) (blocks L1 A1)) ->
  vplace L2 A2 Lam2 S v r rk.
Proof.
  intros L1 A1 Lam1 S v r rk K1 regs1 mem1 md1 E1 L2 A2 regs2 mem2 md2 g Lam2 peak2 cnt2 fail2
    (HV & Hp) HP Hub Hne HL Hsub.
  split; [exact (vloc_call L1 A1 Lam1 S v r rk K1 regs1 mem1 md1 E1 L2 A2 regs2 mem2 md2 g Lam2 peak2 cnt2 fail2
    HV HP Hub Hne HL Hsub)|].
  destruct Hp as [Hp|Hp]; [left; exact Hp|]. right. intros Hl.
  destruct HV as [(_ & _ & _ & Erk)|(Hin & _)].
  - unfold lin in Hl. pose proof HL as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF.
    destruct (HF _ Hl) as (Hk & _). cbn [snd] in Hk. lia.
  - destruct (Hsub _ _ Hl) as [H1|H1]; [exact (Hp H1)|]. apply H1.
    replace (r + 16 - 16) with r by lia. replace (rk - 16 + 16) with rk by lia. exact Hin.
Qed.

Lemma g_place_of : forall L A Lam S S' v r rk, vplace L A Lam S v r rk -> S' <= S ->
  pj_place (lin Lam) (fun a k => In (a, k) (blocks L A)) S' (2 ^ 64) v.
Proof.
  intros L A Lam S S' v r rk ([(Hs & Hv & _ & _)|(Hin & H1 & H2 & _)] & Hp) HS; [left; lia|].
  assert (Hdec : forall x y : Z * Z, {x = y} + {x <> y}).
  { intros [a1 b1] [a2 b2]. destruct (Z.eq_dec a1 a2); destruct (Z.eq_dec b1 b2);
      [left; congruence | right; congruence | right; congruence | right; congruence]. }
  destruct (in_dec Hdec (r + 16, rk - 16) Lam) as [Hl|Hl].
  - right; right. exists (r + 16), (rk - 16). split; [exact Hl|].
    destruct Hp as [Hp|Hp]; [split; lia | exfalso; exact (Hp Hl)].
  - right; left. exists r, rk. split; [exact Hin|]. split; [exact Hl|]. split; lia.
Qed.

Lemma g_rplace_blk : ms_segs B = rsegs -> errno_addr B = strtod_c.STRTOD_ERRNO ->
  forall L A Lam regs mem md peak cnt fail p c kc,
  aa_MR API L A mem md -> ledger B L A mem Lam peak cnt fail -> In (c, kc) Lam -> c <= p -> p + 56 <= c + kc ->
  alloc_ceiling <= spZ regs -> rplace B L A Lam regs mem p.
Proof.
  intros HSEG Herr L A Lam regs mem md peak cnt fail p c kc HM HL Hin H1 H2 Hc.
  pose proof (ledger_block_range B API L A mem md Lam peak cnt fail c kc HM HL Hin) as (R1 & R2 & R3).
  pose proof HL as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF.
  destruct (HF _ Hin) as (Hk & Hb & _). cbn [fst snd] in Hk, Hb.
  destruct (g_blocks_user L A _ _ Hb) as (q & Hq & Eq).
  split; [right; right; exists c, kc; split; [exact Hin|]; split; lia|].
  split; [intros Hs; exfalso; lia|].
  intros i Hi.
  assert (Hni : ~ in_img B (p + i)).
  { replace (p + i) with (c + (p + i - c)) by lia.
    apply (ledger_block_not_img B L A mem Lam peak cnt fail c kc (p + i - c) HL Hin). lia. }
  split.
  { destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ q (kc + 16) (p + i - (c - 16)) HM Hq ltac:(lia)) as (_ & _ & _ & Hno).
    rewrite Eq in Hno. replace (c - 16 + (p + i - (c - 16))) with (p + i) in Hno by lia. exact Hno. }
  split; [intros Hs; exact (Hni (g_img_consts HSEG Herr _ (or_introl Hs)))|].
  split; [intros Hs; exact (Hni (g_img_consts HSEG Herr _ (or_intror Hs)))|].
  exact Hni.
Qed.

Lemma g_vloc_nf : forall L A Lam mem md peak cnt fail S v r rk D',
  vloc L A Lam S v r rk -> aa_MR API L A mem md -> ledger B L A mem Lam peak cnt fail -> alloc_ceiling <= S ->
  pj_apart D' v -> (forall a k, In (a, k) D' -> In (a, k) Lam) -> ~ freed D' r rk.
Proof.
  intros L A Lam mem md peak cnt fail S v r rk D' HV HM HL Hc HA HD Hf. unfold freed in Hf.
  pose proof (HD _ _ Hf) as Hin.
  pose proof HL as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF.
  destruct (HF _ Hin) as (Hk & Hb & _). cbn [fst snd] in Hk, Hb.
  destruct HV as [(Hs & Hv & -> & ->)|(Hin2 & H1 & H2 & Hh)]; [lia|].
  destruct (Hh _ _ Hin) as [Hh1|Hh1]; [|lia].
  apply (HA (r + 16, rk - 16) (Z.max v (r + 16)) Hf); [unfold pj_holds; cbn [fst snd]; lia | lia].
Qed.

Lemma g_vloc_nblk : forall L A Lam mem md peak cnt fail S v r rk D',
  vloc L A Lam S v r rk -> aa_MR API L A mem md -> ledger B L A mem Lam peak cnt fail -> alloc_ceiling <= S ->
  pj_apart D' v -> (forall a k, In (a, k) D' -> In (a, k) Lam) -> forall x, v <= x < v + 56 -> ~ blk_set D' x.
Proof.
  intros L A Lam mem md peak cnt fail S v r rk D' HV HM HL Hc HA HD x Hx (a & k & Hin & Hx2).
  pose proof (HD _ _ Hin) as HinL.
  pose proof HL as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF.
  destruct (HF _ HinL) as (Hk & Hb & _). cbn [fst snd] in Hk, Hb.
  destruct (Z.eq_dec (a - 16) r) as [E1|E1]; [destruct (Z.eq_dec (k + 16) rk) as [E2|E2]|].
  - subst r rk. destruct HV as [(Hs & _ & _ & Hrk)|(_ & H1 & H2 & Hh)]; [lia|].
    destruct (Hh _ _ HinL) as [Hh1|Hh1]; [|lia].
    apply (HA (a, k) (Z.max v a) Hin); [unfold pj_holds; cbn [fst snd]; lia | lia].
  - assert (Hne : (a - 16, k + 16) <> (r, rk)) by (intros E; injection E; lia).
    destruct (vloc_disj L A Lam mem md S v r rk (a - 16) (k + 16) x HV HM Hc Hb Hne ltac:(lia)); lia.
  - assert (Hne : (a - 16, k + 16) <> (r, rk)) by (intros E; injection E; lia).
    destruct (vloc_disj L A Lam mem md S v r rk (a - 16) (k + 16) x HV HM Hc Hb Hne ltac:(lia)); lia.
Qed.

Lemma g_fst_uniq : forall (l : list (Z * Z)) a k k', List.NoDup (map fst l) -> In (a, k) l -> In (a, k') l -> k = k'.
Proof.
  induction l as [|[x y] l IH]; intros a k k' HN H1 H2; [destruct H1|].
  cbn [map] in HN. apply List.NoDup_cons_iff in HN as [Hn HN].
  destruct H1 as [E1|H1]; destruct H2 as [E2|H2].
  - injection E1 as <- <-. injection E2 as E3. exact E3.
  - injection E1 as <- <-. exfalso. apply Hn. apply (in_map fst l (x, k')) in H2. exact H2.
  - injection E2 as <- <-. exfalso. apply Hn. apply (in_map fst l (x, k)) in H1. exact H1.
  - exact (IH a k k' HN H1 H2).
Qed.

Lemma g_lam_disj : forall L A mem md Lam peak cnt fail a k a' k',
  aa_MR API L A mem md -> ledger B L A mem Lam peak cnt fail -> In (a, k) Lam -> In (a', k') Lam ->
  (a, k) <> (a', k') -> a + k <= a' - 16 \/ a' + k' <= a - 16.
Proof.
  intros L A mem md Lam peak cnt fail a k a' k' HM HL H1 H2 Hne.
  pose proof HL as (_ & _ & _ & _ & HND & HF). rewrite Forall_forall in HF.
  destruct (HF _ H1) as (Hk & Hb & _). destruct (HF _ H2) as (Hk' & Hb' & _). cbn [fst snd] in *.
  assert (HND' : List.NoDup (map fst Lam)) by (first [exact HND | apply NoDup_ListNoDup; exact HND]).
  destruct (Z.eq_dec a a') as [<-|Ha].
  - exfalso. apply Hne. rewrite (g_fst_uniq Lam a k k' HND' H1 H2). reflexivity.
  - assert (Hne' : (a - 16, k + 16) <> (a' - 16, k' + 16)) by (intros E; injection E; lia).
    destruct (g_disj L A mem md _ _ _ _ HM Hb Hb' Hne'); lia.
Qed.

Lemma g_lo2 : forall S v1 v2 (P : Z -> Prop),
  P S -> (S <= v1 -> P (v1 + 56)) -> (S <= v2 -> P (v2 + 56)) ->
  exists lo, S <= lo /\ P lo /\ (S <= v1 -> v1 + 56 <= lo) /\ (S <= v2 -> v2 + 56 <= lo).
Proof.
  intros S v1 v2 P H0 H1 H2.
  destruct (Z_le_gt_dec S v1) as [A1|A1]; destruct (Z_le_gt_dec S v2) as [A2|A2].
  - destruct (Z_le_gt_dec v1 v2) as [A3|A3].
    + exists (v2 + 56). split; [lia|]. split; [exact (H2 A2)|]. split; intros; lia.
    + exists (v1 + 56). split; [lia|]. split; [exact (H1 A1)|]. split; intros; lia.
  - exists (v1 + 56). split; [lia|]. split; [exact (H1 A1)|]. split; intros; lia.
  - exists (v2 + 56). split; [lia|]. split; [exact (H2 A2)|]. split; intros; lia.
  - exists S. split; [lia|]. split; [exact H0|]. split; intros; lia.
Qed.

End G.

Lemma wx_rsegs : MemNorm.wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Section Runs.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis HGET : pj_get_contract.
Hypothesis HMC : memcpy_contract.
Hypothesis HMS : memset_contract.

Definition K_sa (regs : bvmap 5 word) (mem : word -> option byte) (o k w kids : Z) (ms : list (list Z * jv))
    (kname : list Z) (R : bvmap 5 word) (pc : word) (m1 : word -> option byte) : Prop :=
  exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (junk : list byte),
    munch [(spZ regs + -128, spZ regs)] mem m1 /\ wmono rsegs mem m1 /\ MemNorm.ro_same rsegs mem m1 /\
    rw_cells rsegs m1 (spZ regs + -48)
      [CB 8 junk; C8 (YK11.getr regs 19); C8 (YK11.getr regs 18); C8 (YK11.getr regs 9); C8 (YK11.getr regs 8);
       C8 (YK11.getr regs 1)] /\
    (((forall nm u, In (nm, u) ms -> nm <> kname) /\
      R = mkR (Z_to_bv 64 PS_GROW_RET) (Z_to_bv 64 (spZ regs + -48)) (YK11.getr regs 3) (YK11.getr regs 4) t0 t1 t2
            (Z_to_bv 64 w) (Z_to_bv 64 o) (Z_to_bv 64 o) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 k) (YK11.getr regs 19)
            (YK11.getr regs 20) (YK11.getr regs 21) (YK11.getr regs 22) (YK11.getr regs 23) (YK11.getr regs 24)
            (YK11.getr regs 25) (YK11.getr regs 26) (YK11.getr regs 27) t3 t4 t5 t6 /\
      pc = Z_to_bv 64 PS_GROW)
     \/ (exists i v, nth_error ms i = Some (kname, v) /\
          (forall j nm u, (j < i)%nat -> nth_error ms j = Some (nm, u) -> nm <> kname) /\
      R = mkR (Z_to_bv 64 PS_FREE_RET) (Z_to_bv 64 (spZ regs + -48)) (YK11.getr regs 3) (YK11.getr regs 4) t0 t1 t2
            (Z_to_bv 64 w) (Z_to_bv 64 o) (Z_to_bv 64 (kids + 56 * Z.of_nat i)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 k)
            (Z_to_bv 64 (kids + 56 * Z.of_nat i))
            (YK11.getr regs 20) (YK11.getr regs 21) (YK11.getr regs 22) (YK11.getr regs 23) (YK11.getr regs 24)
            (YK11.getr regs 25) (YK11.getr regs 26) (YK11.getr regs 27) t3 t4 t5 t6 /\
      pc = Z_to_bv 64 PS_PJ_FREE)).

Lemma run_sa : forall regs mem lo o k w (lblk : Z -> Z -> Prop) ms D num str kids keys n cap kname,
  ms_segs B = rsegs -> MemNorm.ro_agree rsegs mem ->
  YK11.getr regs 10 = Z_to_bv 64 o -> YK11.getr regs 11 = Z_to_bv 64 k -> YK11.getr regs 12 = Z_to_bv 64 w -> o <> 0 ->
  pj_node rsegs mem lblk o (JObj ms) D -> pj_hdr rsegs mem o 6 num str kids keys n cap -> pj_cbytes rsegs mem k kname ->
  (forall a nn, lblk a nn -> 0 < a /\ a mod 8 = 0 /\ a + nn <= 2 ^ 47 /\
     disjoint_from [(a, a + nn)] (spZ regs - 128) 128) ->
  spZ regs mod 16 = 0 -> stk rsegs mem lo (spZ regs) -> lo + 128 <= spZ regs ->
  disjoint_from [(o, o + 56); (k, k + Z.of_nat (length kname) + 1)] (spZ regs - 128) 128 ->
  (forall x : word, pj_foot o D (bv_unsigned x) -> ro_addr rsegs x = false) ->
  (forall a, lo <= a < spZ regs -> ro_addr rsegs (wa a) = false) ->
  Exec.evt (ms_segs B) (fun st => exists R pc' m', st = MState.MS R fp_regs pc' fp_csr None m' (seg_rom (ms_segs B)) /\
      K_sa regs mem o k w kids ms kname R pc' m')
    (MState.MS (rmk regs) fp_regs (Z_to_bv 64 PJ_SET) fp_csr None mem (seg_rom (ms_segs B))).
Proof.
  intros regs mem lo o k w lblk ms D num str kids keys n cap kname HSEG ROA R10 R11 R12 ONZ HN HH HC HL SPA ST LO DJ
    HFO HFS. rewrite HSEG.
  pose proof (MemNorm.mem_rel_normalize rsegs mem ROA) as HR0.
  pose proof (t_hdr_norm rsegs mem o _ _ _ _ _ _ _ HH ltac:(intros x Hx; apply HFO; left; exact Hx)) as HHn.
  eapply evt_mono.
  { eapply (MemNorm.evt_normalize rsegs); [exact wx_rsegs | exact ROA |].
    unfold rmk. change (Z_to_bv 64 PJ_SET) with (Z_to_bv 64 PS_ENTRY).
    apply (ps_sa HGET); [exact R10 | exact R11 | exact R12 | exact ONZ | exact (t_node_norm rsegs mem lblk o _ D HN ROA HFO)
           | exact (t_cbytes_norm rsegs mem k kname ROA HC) | exact HL | exact SPA
           | exact (t_stk_norm rsegs mem lo _ ROA HFS ST) | exact LO | exact DJ | apply MemNorm.mem_inv_normalize]. }
  intros st (s0 & Q0 & Hrel & Hsame).
  destruct Q0 as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m1 & junk & z & MU & WM & MI & ST1 &
                  FR & HN1 & HC1 & HRES & ZR & CASES).
  assert (HK1 : pj_u64 rsegs m1 (o + 24) kids).
  { pose proof HHn as (_ & _ & _ & _ & HK & _). apply (pj_u64_eq rsegs _ m1 _ _ HK). intros x Hx. apply MU.
    cbn [disjoint_from] in DJ. cbn [outside]. unfold spZ in *. split; [lia | exact I]. }
  destruct st as [r1 f1 p1 sv1 rv1 fc1 mm1 ro1].
  destruct CASES as [(Z0 & ES)|(Z1 & ES)]; subst s0;
    pose proof Hrel as (Hr & Hf & Hp & Hsv & Hrs & Hfc & Hro & Hm); cbn in Hr, Hf, Hp, Hsv, Hrs, Hfc, Hro, Hm, Hsame;
    (assert (MUr : munch [(spZ regs + -128, spZ regs)] mem mm1)
       by exact (MemNorm.munch_rel rsegs _ mem (MemNorm.normalize rsegs mem) mm1 m1 HR0 Hm Hsame MU));
    (assert (WMr : wmono rsegs mem mm1) by exact (MemNorm.wmono_rel rsegs mem _ mm1 m1 HR0 Hm Hsame WM));
    pose proof (t_rw_rel rsegs mm1 m1 _ _ Hm FR) as FRr; subst.
  - eexists _, _, mm1. split; [reflexivity|].
    exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, junk.
    split; [exact MUr|]. split; [exact WMr|]. split; [exact Hsame|]. split; [exact FRr|].
    left. cbn [pj_get_res] in HRES.
    destruct HRES as [(Hno & _)|HH1]; [|exfalso; pose proof (ps_hit_pos m1 lblk o ms D kname 0
      ltac:(intros a nn Hb; exact (proj1 (HL a nn Hb))) HN1 HH1); lia].
    split; [exact Hno|]. split; [reflexivity | reflexivity].
  - eexists _, _, mm1. split; [reflexivity|].
    exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, junk.
    split; [exact MUr|]. split; [exact WMr|]. split; [exact Hsame|]. split; [exact FRr|].
    right. cbn [pj_get_res] in HRES.
    destruct HRES as [(_ & Z0)|(i & v & kids' & Di & Hi & Hl & Hk' & Ez & _)]; [exfalso; exact (Z1 Z0)|].
    pose proof (pj_u64_uniq rsegs m1 _ _ _ Hk' HK1) as <-. subst z.
    exists i, v. split; [exact Hi|]. split; [exact Hl|]. split; [reflexivity | reflexivity].
Qed.

Definition K_ret (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (mem : word -> option byte)
    (dst w : Z) (bs : list byte) (R : bvmap 5 word) (pc : word) (m1 : word -> option byte) : Prop :=
  exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    R = mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 /\
    pc = ret_pc ra /\
    munch [(dst, dst + 56); (w, w + 56)] mem m1 /\ wmono rsegs mem m1 /\ MemNorm.ro_same rsegs mem m1 /\
    bytes_at rsegs m1 dst bs /\ rw_cells rsegs m1 w [CB 56 (repeat (Z_to_bv 8 0) 56)].

Lemma run_sb : forall regs2 mem2 (sp ra s0 s1 s2 s3 : word) junk dst w bs jd jw,
  ms_segs B = rsegs -> MemNorm.ro_agree rsegs mem2 ->
  YK11.getr regs2 2 = Z_to_bv 64 (bv_unsigned sp + -48) -> YK11.getr regs2 8 = Z_to_bv 64 w ->
  YK11.getr regs2 19 = Z_to_bv 64 dst ->
  rw_cells rsegs mem2 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  length bs = 56%nat -> bytes_at rsegs mem2 w bs ->
  rw_cells rsegs mem2 dst [CB 56 jd] -> rw_cells rsegs mem2 w [CB 56 jw] ->
  (w + 56 <= dst \/ dst + 56 <= w) -> (dst + 56 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= dst) ->
  (w + 56 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= w) -> 48 <= bv_unsigned sp ->
  (forall i, 0 <= i < 48 -> ro_addr rsegs (wa (bv_unsigned sp + -48 + i)) = false) ->
  (forall i, 0 <= i < 56 -> ro_addr rsegs (wa (dst + i)) = false) ->
  (forall i, 0 <= i < 56 -> ro_addr rsegs (wa (w + i)) = false) ->
  Exec.evt (ms_segs B) (fun st => exists R pc' m', st = MState.MS R fp_regs pc' fp_csr None m' (seg_rom (ms_segs B)) /\
      K_ret ra sp (YK11.getr regs2 3) (YK11.getr regs2 4) s0 s1 s2 s3 (YK11.getr regs2 20) (YK11.getr regs2 21)
        (YK11.getr regs2 22) (YK11.getr regs2 23) (YK11.getr regs2 24) (YK11.getr regs2 25) (YK11.getr regs2 26)
        (YK11.getr regs2 27) mem2 dst w bs R pc' m')
    (MState.MS (rmk regs2) fp_regs (Z_to_bv 64 PS_FREE_RET) fp_csr None mem2 (seg_rom (ms_segs B))).
Proof.
  intros regs2 mem2 sp ra s0 s1 s2 s3 junk dst w bs jd jw HSEG ROA G2 G8 G19 FR LB WB RD RW DW DD WD SP RF RRD RRW.
  rewrite HSEG.
  pose proof (MemNorm.mem_rel_normalize rsegs mem2 ROA) as HR0.
  assert (FRn : rw_cells rsegs (MemNorm.normalize rsegs mem2) (bv_unsigned sp + -48)
    [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (t_rw_norm rsegs mem2 _ _ ROA); [intros i Hi; cbn [cells_size csize Nat.add] in Hi; apply RF; lia | exact FR]. }
  assert (RDn : rw_cells rsegs (MemNorm.normalize rsegs mem2) dst [CB 56 jd]).
  { apply (t_rw_norm rsegs mem2 _ _ ROA); [intros i Hi; cbn [cells_size csize] in Hi; apply RRD; lia | exact RD]. }
  assert (RWn : rw_cells rsegs (MemNorm.normalize rsegs mem2) w [CB 56 jw]).
  { apply (t_rw_norm rsegs mem2 _ _ ROA); [intros i Hi; cbn [cells_size csize] in Hi; apply RRW; lia | exact RW]. }
  pose proof (MemNorm.bytes_at_normalize rsegs mem2 w bs ROA WB) as WBn.
  eapply evt_mono.
  { eapply (MemNorm.evt_normalize rsegs); [exact wx_rsegs | exact ROA |].
    unfold rmk.
    exact (ps_sbh HMC HMS (YK11.getr regs2 1) (YK11.getr regs2 2) sp (YK11.getr regs2 3) (YK11.getr regs2 4)
      (YK11.getr regs2 5) (YK11.getr regs2 6) (YK11.getr regs2 7) (YK11.getr regs2 8) (YK11.getr regs2 9)
      (YK11.getr regs2 10) (YK11.getr regs2 11) (YK11.getr regs2 12) (YK11.getr regs2 13) (YK11.getr regs2 14)
      (YK11.getr regs2 15) (YK11.getr regs2 16) (YK11.getr regs2 17) (YK11.getr regs2 18) (YK11.getr regs2 19)
      (YK11.getr regs2 20) (YK11.getr regs2 21) (YK11.getr regs2 22) (YK11.getr regs2 23) (YK11.getr regs2 24)
      (YK11.getr regs2 25) (YK11.getr regs2 26) (YK11.getr regs2 27) (YK11.getr regs2 28) (YK11.getr regs2 29)
      (YK11.getr regs2 30) (YK11.getr regs2 31) fp_regs fp_csr (MemNorm.normalize rsegs mem2) dst w bs jd jw
      ra s0 s1 s2 s3 junk G2 G8 G19 FRn LB WBn RDn RWn DW DD WD SP (MemNorm.mem_inv_normalize rsegs _)). }
  intros st (s0' & Q0 & Hrel & Hsame).
  destruct Q0 as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m1 & ES & MU & WM & MI & DB & WZ).
  destruct st as [r1 f1 p1 sv1 rv1 fc1 mm1 ro1]. subst s0'.
  pose proof Hrel as (Hr & Hf & Hp & Hsv & Hrs & Hfc & Hro & Hm); cbn in Hr, Hf, Hp, Hsv, Hrs, Hfc, Hro, Hm, Hsame.
  pose proof (MemNorm.munch_rel rsegs _ mem2 (MemNorm.normalize rsegs mem2) mm1 m1 HR0 Hm Hsame MU) as MUr.
  pose proof (MemNorm.wmono_rel rsegs mem2 _ mm1 m1 HR0 Hm Hsame WM) as WMr.
  pose proof (proj2 (MemNorm.bytes_at_rel rsegs mm1 m1 dst bs Hm) DB) as DBr.
  pose proof (t_rw_rel rsegs mm1 m1 _ _ Hm WZ) as WZr.
  subst.
  eexists _, _, mm1. split; [reflexivity|].
  exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6.
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact MUr|]. split; [exact WMr|]. split; [exact Hsame|]. split; [exact DBr | exact WZr].
Qed.

Definition K_sdx (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 spr s0r s1r s2r s3r : word)
    (mem : word -> option byte) (o w res n keys kids : Z) (bs : list byte) (R : bvmap 5 word) (pc : word)
    (m1 : word -> option byte) : Prop :=
  exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    wmono rsegs mem m1 /\ MemNorm.ro_same rsegs mem m1 /\
    ((res = 0 /\ munch [(keys + 8 * n, keys + 8 * n + 8)] mem m1 /\
      bytes_at rsegs m1 (keys + 8 * n) (le8 (Z_to_bv 64 0)) /\
      R = mkR (Z_to_bv 64 PS_FREEW_RET) spr gp tp t0 t1 t2 s0r s1r (Z_to_bv 64 w) a1 a2 a3 a4 a5 a6 a7
            s2r s3r s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 /\ pc = Z_to_bv 64 PS_PJ_FREE)
     \/ (res <> 0 /\
      munch [(keys + 8 * n, keys + 8 * n + 8); (o + 40, o + 48); (kids + 56 * n, kids + 56 * n + 56); (w, w + 56)]
        mem m1 /\
      bytes_at rsegs m1 (keys + 8 * n) (le8 (Z_to_bv 64 res)) /\ bytes_at rsegs m1 (o + 40) (le8 (Z_to_bv 64 (n + 1))) /\
      bytes_at rsegs m1 (kids + 56 * n) bs /\ rw_cells rsegs m1 w [CB 56 (repeat (Z_to_bv 8 0) 56)] /\
      R = mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
            t3 t4 t5 t6 /\ pc = ret_pc ra)).

Lemma run_sdx : forall regs2 mem2 (sp ra s0 s1 s2 s3 : word) junk o w res n keys kids bs jd jw,
  ms_segs B = rsegs -> MemNorm.ro_agree rsegs mem2 ->
  YK11.getr regs2 2 = Z_to_bv 64 (bv_unsigned sp + -48) -> YK11.getr regs2 10 = Z_to_bv 64 res -> 0 <= res < 2 ^ 64 ->
  YK11.getr regs2 8 = Z_to_bv 64 w -> YK11.getr regs2 9 = Z_to_bv 64 o ->
  bytes_at rsegs mem2 (o + 40) (le8 (Z_to_bv 64 n)) -> bytes_at rsegs mem2 (o + 32) (le8 (Z_to_bv 64 keys)) ->
  bytes_at rsegs mem2 (o + 24) (le8 (Z_to_bv 64 kids)) ->
  wr_at rsegs mem2 (keys + 8 * n) 8 -> wr_at rsegs mem2 (o + 40) 8 ->
  0 < o -> o mod 8 = 0 -> o + 56 <= 2 ^ 64 -> 0 <= n <= 2 ^ 54 -> 0 < keys -> keys mod 8 = 0 ->
  keys + 8 * n + 8 <= 2 ^ 64 -> 0 < kids -> kids + 56 * n + 56 <= 2 ^ 64 ->
  (keys + 8 * n + 8 <= o \/ o + 56 <= keys + 8 * n) ->
  rw_cells rsegs mem2 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  length bs = 56%nat -> bytes_at rsegs mem2 w bs ->
  rw_cells rsegs mem2 (kids + 56 * n) [CB 56 jd] -> rw_cells rsegs mem2 w [CB 56 jw] ->
  (w + 56 <= kids + 56 * n \/ kids + 56 * n + 56 <= w) ->
  (kids + 56 * n + 56 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= kids + 56 * n) ->
  (w + 56 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= w) ->
  (keys + 8 * n + 8 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= keys + 8 * n) ->
  (o + 56 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= o) ->
  (keys + 8 * n + 8 <= w \/ w + 56 <= keys + 8 * n) -> (o + 56 <= w \/ w + 56 <= o) ->
  (keys + 8 * n + 8 <= kids + 56 * n \/ kids + 56 * n + 56 <= keys + 8 * n) ->
  (o + 56 <= kids + 56 * n \/ kids + 56 * n + 56 <= o) ->
  48 <= bv_unsigned sp ->
  (forall i, 0 <= i < 48 -> ro_addr rsegs (wa (bv_unsigned sp + -48 + i)) = false) ->
  (forall i, 0 <= i < 8 -> ro_addr rsegs (wa (keys + 8 * n + i)) = false) ->
  (forall i, 0 <= i < 8 -> ro_addr rsegs (wa (o + 40 + i)) = false) ->
  (forall i, 0 <= i < 56 -> ro_addr rsegs (wa (kids + 56 * n + i)) = false) ->
  (forall i, 0 <= i < 56 -> ro_addr rsegs (wa (w + i)) = false) ->
  Exec.evt (ms_segs B) (fun st => exists R pc' m', st = MState.MS R fp_regs pc' fp_csr None m' (seg_rom (ms_segs B)) /\
      K_sdx ra sp (YK11.getr regs2 3) (YK11.getr regs2 4) s0 s1 s2 s3 (YK11.getr regs2 20) (YK11.getr regs2 21)
        (YK11.getr regs2 22) (YK11.getr regs2 23) (YK11.getr regs2 24) (YK11.getr regs2 25) (YK11.getr regs2 26)
        (YK11.getr regs2 27) (YK11.getr regs2 2) (YK11.getr regs2 8) (YK11.getr regs2 9) (YK11.getr regs2 18)
        (YK11.getr regs2 19) mem2 o w res n keys kids bs R pc' m')
    (MState.MS (rmk regs2) fp_regs (Z_to_bv 64 PS_SD_RET) fp_csr None mem2 (seg_rom (ms_segs B))).
Proof.
  intros regs2 mem2 sp ra s0 s1 s2 s3 junk o w res n keys kids bs jd jw HSEG ROA G2 G10 RR G8 G9 BN BK BD WK WO
    O0 O8 O1 N0 K0 K8 K1 D0 D1 KO FR LB WB RD RW DW DD WD KD OD KW OW KK OK SP RF RK RO RRD RRW.
  rewrite HSEG.
  pose proof (MemNorm.mem_rel_normalize rsegs mem2 ROA) as HR0.
  assert (FRn : rw_cells rsegs (MemNorm.normalize rsegs mem2) (bv_unsigned sp + -48)
    [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (t_rw_norm rsegs mem2 _ _ ROA); [intros i Hi; cbn [cells_size csize Nat.add] in Hi; apply RF; lia | exact FR]. }
  assert (RDn : rw_cells rsegs (MemNorm.normalize rsegs mem2) (kids + 56 * n) [CB 56 jd]).
  { apply (t_rw_norm rsegs mem2 _ _ ROA); [intros i Hi; cbn [cells_size csize] in Hi; apply RRD; lia | exact RD]. }
  assert (RWn : rw_cells rsegs (MemNorm.normalize rsegs mem2) w [CB 56 jw]).
  { apply (t_rw_norm rsegs mem2 _ _ ROA); [intros i Hi; cbn [cells_size csize] in Hi; apply RRW; lia | exact RW]. }
  pose proof (MemNorm.bytes_at_normalize rsegs mem2 _ _ ROA WB) as WBn.
  pose proof (MemNorm.bytes_at_normalize rsegs mem2 _ _ ROA BN) as BNn.
  pose proof (MemNorm.bytes_at_normalize rsegs mem2 _ _ ROA BK) as BKn.
  pose proof (MemNorm.bytes_at_normalize rsegs mem2 _ _ ROA BD) as BDn.
  pose proof (MemNorm.wr_at_norm rsegs mem2 _ _ _ HR0 WK RK) as WKn.
  pose proof (MemNorm.wr_at_norm rsegs mem2 _ _ _ HR0 WO RO) as WOn.
  eapply evt_mono.
  { eapply (MemNorm.evt_normalize rsegs); [exact wx_rsegs | exact ROA |].
    unfold rmk.
    exact (ps_sdx HMC HMS (YK11.getr regs2 1) (YK11.getr regs2 2) sp (YK11.getr regs2 3) (YK11.getr regs2 4)
      (YK11.getr regs2 5) (YK11.getr regs2 6) (YK11.getr regs2 7) (YK11.getr regs2 8) (YK11.getr regs2 9)
      (YK11.getr regs2 10) (YK11.getr regs2 11) (YK11.getr regs2 12) (YK11.getr regs2 13) (YK11.getr regs2 14)
      (YK11.getr regs2 15) (YK11.getr regs2 16) (YK11.getr regs2 17) (YK11.getr regs2 18) (YK11.getr regs2 19)
      (YK11.getr regs2 20) (YK11.getr regs2 21) (YK11.getr regs2 22) (YK11.getr regs2 23) (YK11.getr regs2 24)
      (YK11.getr regs2 25) (YK11.getr regs2 26) (YK11.getr regs2 27) (YK11.getr regs2 28) (YK11.getr regs2 29)
      (YK11.getr regs2 30) (YK11.getr regs2 31) fp_regs fp_csr (MemNorm.normalize rsegs mem2) o w res n keys kids bs
      jd jw ra s0 s1 s2 s3 junk G2 G10 RR G8 G9 BNn BKn BDn WKn WOn O0 O8 O1 N0 K0 K8 K1 D0 D1 KO FRn LB WBn RDn RWn
      DW DD WD KD OD KW OW KK OK SP (MemNorm.mem_inv_normalize rsegs _)). }
  intros st (s0' & Q0 & Hrel & Hsame).
  destruct st as [r1 f1 p1 sv1 rv1 fc1 mm1 ro1].
  destruct Q0 as [(R0 & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m1 & MU & WM & MI & BK1 & ES)
                 |(R1 & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m1 & MU & WM & MI & BK1 & BN1 &
                   DB & WZ & ES)];
    subst s0';
    pose proof Hrel as (Hr & Hf & Hp & Hsv & Hrs & Hfc & Hro & Hm); cbn in Hr, Hf, Hp, Hsv, Hrs, Hfc, Hro, Hm, Hsame;
    pose proof (MemNorm.munch_rel rsegs _ mem2 (MemNorm.normalize rsegs mem2) mm1 m1 HR0 Hm Hsame MU) as MUr;
    pose proof (MemNorm.wmono_rel rsegs mem2 _ mm1 m1 HR0 Hm Hsame WM) as WMr;
    pose proof (proj2 (MemNorm.bytes_at_rel rsegs mm1 m1 _ _ Hm) BK1) as BKr.
  - subst. eexists _, _, mm1. split; [reflexivity|].
    exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6.
    split; [exact WMr|]. split; [exact Hsame|].
    left. split; [reflexivity|]. split; [exact MUr|]. split; [exact BKr|]. split; reflexivity.
  - pose proof (proj2 (MemNorm.bytes_at_rel rsegs mm1 m1 _ _ Hm) BN1) as BNr.
    pose proof (proj2 (MemNorm.bytes_at_rel rsegs mm1 m1 _ _ Hm) DB) as DBr.
    pose proof (t_rw_rel rsegs mm1 m1 _ _ Hm WZ) as WZr.
    subst. eexists _, _, mm1. split; [reflexivity|].
    exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6.
    split; [exact WMr|]. split; [exact Hsame|].
    right. split; [exact R1|]. split; [exact MUr|]. split; [exact BKr|]. split; [exact BNr|].
    split; [exact DBr|]. split; [exact WZr|]. split; reflexivity.
Qed.

End Runs.
