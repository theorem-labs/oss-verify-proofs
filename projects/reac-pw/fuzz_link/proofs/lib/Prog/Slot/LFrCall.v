(* The slot LLVMFuzzerTestOneInput (fuzz_link.c:764-790), plain image: the generic SR step through a callee
   whose Post is lib/Reusable/YO0d.v call_post_k (calloc, free, text_buf, text_of; mark_quietly's mq_post_k has
   the same conjuncts but the user-block one, so it goes through lfr_call_core), on top of lib/Prog/Slot/LFr.v.

   lfr_call: from LFR at the call (sp = S - 480, the callee's scratch K <= 65536 - 480 below it) to LFR at the
   return with the new heap blocks hb' and kept set T', plus what every step gives its caller: the regions
   lkeep keeps (minus the callee's footprint E) carried between the evt-level views (normalize_cj), and
   lpost_mem of the new view. Also: lfr_post_mem (lpost_mem of every LFR state), lfr_fresh (lfresh of the
   block an allocating callee hands out, from Contract.fresh_block and the allocator's disjoint blocks),
   lfresh_blk_out, lfr_gi_keep (the FILE invariant mf_gi carried), lfr_heads_img, lfr_hbk / lfr_hbk_x (lfr_call's
   live-block premise from a Post's user-block clause), and the representative lemmas (lc_rep, lc_eqv_self,
   lc_eqv_rep, lc_rp) the arm steps share.

   Shapes from libreac/fuzz_boxreg lib/Prog/LLVMFuzzerTestOneInput_fr.v (lf_fr_call) and libreac/fuzz_pcap
   lib/Prog/Slot/PTac.v (ss_FR_call, ss_malloc_step, ss_free_step); every constant is link's. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Contract Img0 FrameAPI MemFile MemFileRI.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import AllocSlots AllocRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require KindBGlue.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss MState.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import LLVMFuzzerTestOneInput_c link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LFr.
Import ListNotations.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Lists of blocks
   ========================================================================== *)

Lemma lc_pw_perm : forall {X : Type} (R : X -> X -> Prop), (forall a b, R a b -> R b a) ->
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

Lemma lc_pw_app : forall {X : Type} (R : X -> X -> Prop) l1 l2, pairwise R (l1 ++ l2) ->
  forall x y, In x l1 -> In y l2 -> R x y.
Proof.
  intros X R l1. induction l1 as [|a l1 IH]; intros l2 H x y Hx Hy; [destruct Hx|].
  destruct H as [H1 H2]. destruct Hx as [<-|Hx].
  - apply H1. apply in_or_app. right. exact Hy.
  - exact (IH l2 H2 x y Hx Hy).
Qed.

Lemma lc_pw_mid : forall {X : Type} (R : X -> X -> Prop) l1 x l2, pairwise R (l1 ++ x :: l2) ->
  forall y, In y (l1 ++ l2) -> R y x \/ R x y.
Proof.
  intros X R l1. induction l1 as [|a l1 IH]; intros x l2 H y Hy.
  - cbn [app] in H, Hy. destruct H as [H1 _]. right. exact (H1 y Hy).
  - cbn [app] in H, Hy. destruct H as [H1 H2]. destruct Hy as [<-|Hy].
    + left. apply H1. apply in_or_app. right. left. reflexivity.
    + exact (IH x l2 H2 y Hy).
Qed.

Lemma lc_rd_sym : forall u v : Z * Z, ranges_disjoint u v -> ranges_disjoint v u.
Proof. intros u v. unfold ranges_disjoint. lia. Qed.

Lemma lc_nodup_fst0 : forall (l : list (Z * Z)) a k n, List.NoDup (map fst l) -> In (a, k) l -> In (a, n) l -> k = n.
Proof.
  induction l as [|[a0 k0] l IH]; intros a k n Hnd H1 H2; [destruct H1|].
  cbn [map fst] in Hnd. apply List.NoDup_cons_iff in Hnd as [Hn Hnd].
  destruct H1 as [E1|H1]; destruct H2 as [E2|H2].
  - congruence.
  - exfalso. apply Hn. apply in_map_iff. exists (a, n). split; [cbn; congruence | exact H2].
  - exfalso. apply Hn. apply in_map_iff. exists (a, k). split; [cbn; congruence | exact H1].
  - exact (IH a k n Hnd H1 H2).
Qed.

(* the allocator's blocks_nodup is stated with stdpp's NoDup *)
Lemma lc_nodup_fst : forall (l : list (Z * Z)) a k n, NoDup (map fst l) -> In (a, k) l -> In (a, n) l -> k = n.
Proof.
  intros l a k n Hnd. exact (lc_nodup_fst0 l a k n (proj1 (stdpp.base.NoDup_ListNoDup _) Hnd)).
Qed.

(* ==========================================================================
   2. The evt-level view: normalize_cj keeps equal bytes and writability equal
   ========================================================================== *)

Lemma lc_norm_carry : forall (m m' : word -> option byte) a,
  mbyte rsegs m' a = mbyte rsegs m a -> (writable_at rsegs m a <-> writable_at rsegs m' a) ->
  mbyte rsegs (normalize_cj rsegs m') a = mbyte rsegs (normalize_cj rsegs m) a /\
  (writable_at rsegs (normalize_cj rsegs m) a <-> writable_at rsegs (normalize_cj rsegs m') a).
Proof.
  intros m m' a H1 H2. unfold mbyte, writable_at, wview, normalize_cj in *. cbv beta in *.
  destruct (cj_drop rsegs (Z_to_bv 64 a)); [split; [reflexivity | tauto] | split; [exact H1 | exact H2]].
Qed.

Lemma lc_norm_keep : forall (m : word -> option byte) a, cj_drop rsegs (Z_to_bv 64 a) = false ->
  mbyte rsegs (normalize_cj rsegs m) a = mbyte rsegs m a /\
  (writable_at rsegs (normalize_cj rsegs m) a <-> writable_at rsegs m a).
Proof.
  intros m a E. unfold mbyte, writable_at, wview, normalize_cj. cbv beta. rewrite E. cbv iota.
  split; [reflexivity | tauto].
Qed.

Lemma lc_cj_keep : forall a, 0 <= a < TASK_SIZE -> Mem.ro_addr rsegs (Z_to_bv 64 a) = false ->
  cj_drop rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha Hro. apply (cj_drop_false_intro rsegs); [exact Hro|]. right.
  rewrite MState.unsigned_lit by (unfold TASK_SIZE in *; lia). lia.
Qed.

Lemma lc_ro_hi : forall a, LF_TOP <= a < 2 ^ 64 -> Mem.ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha. unfold Mem.ro_addr. rewrite (MState.unsigned_lit a ltac:(unfold LF_TOP in Ha; lia)).
  destruct (find_segment rsegs a 1) as [seg|] eqn:E; [|reflexivity].
  exfalso. pose proof (lfr_find_top a 1 seg E). unfold LF_TOP in *. lia.
Qed.

Lemma lc_seg_none : forall B a, ms_segs B = rsegs -> ~ in_img B a -> find_segment rsegs a 1 = None.
Proof.
  intros B a HS Hn. destruct (find_segment rsegs a 1) as [seg|] eqn:E; [|reflexivity].
  exfalso. exact (Hn (lfr_find_img B a seg HS E)).
Qed.

(* outside the image a byte is writable exactly when it is present: equal bytes give equal writability *)
Lemma lc_nonimg_wr : forall B (m m' : word -> option byte) a, ms_segs B = rsegs -> ~ in_img B a ->
  0 <= a < 2 ^ 64 -> present m a -> mbyte rsegs m' a = mbyte rsegs m a ->
  (writable_at rsegs m a <-> writable_at rsegs m' a).
Proof.
  intros B m m' a HS Hn Ha [b Hb] E.
  assert (Hr : YK11.seg_rom rsegs (Z_to_bv 64 a) = None).
  { exact (MemNorm.seg_rom_unmapped rsegs (Z_to_bv 64 a)
      ltac:(rewrite (MState.unsigned_lit a Ha); exact (lc_seg_none B a HS Hn))). }
  unfold writable_at. rewrite (lfr_wview_out B m a HS Hn Ha), (lfr_wview_out B m' a HS Hn Ha), Hb.
  unfold mbyte in E. rewrite Hb in E.
  assert (Hm' : m' (Z_to_bv 64 a) <> None).
  { intros E'. rewrite E', Hr in E. cbn in E. discriminate E. }
  split; intros _; [exact Hm' | discriminate].
Qed.

(* the errno word (0x75564, .tbss) is not read-only *)
Lemma lc_errno_ro : forallb (fun i => negb (Mem.ro_addr rsegs (Z_to_bv 64 (A_ERRNO + Z.of_nat i)))) (seq 0 4) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lc_errno_keep : forall a, A_ERRNO <= a < A_ERRNO + 4 -> cj_drop rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha. apply lc_cj_keep; [unfold A_ERRNO, A_TP, ERRNO_TP_OFF, TASK_SIZE in *; lia|].
  pose proof lc_errno_ro as H. rewrite forallb_forall in H.
  specialize (H (Z.to_nat (a - A_ERRNO)) ltac:(apply in_seq; lia)).
  replace (A_ERRNO + Z.of_nat (Z.to_nat (a - A_ERRNO))) with a in H by lia.
  apply negb_true_iff in H. exact H.
Qed.

(* the image's reserved segments cover [0x10000, 0x97000) without a hole; [0x21000, 0x97000) is the last *)
Lemma lc_img_chk : existsb (fun s => (bv_unsigned (fst s) <=? 0x21000) && (LF_TOP <=? bv_unsigned (fst s) + bv_unsigned (snd s)))
  (segments_reserved rsegs) = true.
Proof. vm_compute. reflexivity. Qed.

(* ==========================================================================
   3. The representative of a cut (the arm files' cut predicates are in mkR form; LDefs eqv_cl)
   ========================================================================== *)

Lemma lc_getr : forall R R' r, Regs6ss.xregs_eqv R R' -> YK11.getr R' r = YK11.getr R r.
Proof.
  intros R R' r H. unfold YK11.getr. destruct (bv_eqb r 0) eqn:E; [reflexivity|].
  symmetry. apply H. rewrite <- bv_eqb0_is_x0. exact E.
Qed.

Lemma lc_rp : forall R regs regs', Regs6ss.xregs_eqv R regs -> regs_preserved regs regs' -> regs_preserved R regs'.
Proof. intros R regs regs' HR H r Hr. rewrite (H r Hr). exact (lc_getr R regs _ HR). Qed.

Lemma lc_rep : forall (P : machine_state -> Prop) (fx' : YK11.FPState) regs pc mem,
  eqv_cl P (lcanon fx' regs pc mem) ->
  exists R, P (MState.MS R (@fp_regs fx') (Z_to_bv 64 pc) (@fp_csr fx') None (normalize_cj rsegs mem) (seg_rom rsegs)) /\
    Regs6ss.xregs_eqv R regs.
Proof.
  intros P fx' regs pc mem (c0 & Hc & Hr & HF & Hpc & Hsv & Hrv & Hfc & Hm & Hro).
  destruct c0 as [R F pc0 sv rv fc m ro]. cbn in Hr, HF, Hpc, Hsv, Hrv, Hfc, Hm, Hro. subst.
  exists R. split; [exact Hc | exact Hr].
Qed.

Lemma lc_eqv_rep : forall (P : machine_state -> Prop) (fx' : YK11.FPState) R regs pc mem,
  Regs6ss.xregs_eqv R regs ->
  P (MState.MS R (@fp_regs fx') (Z_to_bv 64 pc) (@fp_csr fx') None (normalize_cj rsegs mem) (seg_rom rsegs)) ->
  eqv_cl P (lcanon fx' regs pc mem).
Proof.
  intros P fx' R regs pc mem HR H.
  exists (MState.MS R (@fp_regs fx') (Z_to_bv 64 pc) (@fp_csr fx') None (normalize_cj rsegs mem) (seg_rom rsegs)).
  split; [exact H|]. split; [exact HR|]. cbn. repeat split.
Qed.

Lemma lc_eqv_self : forall (P : machine_state -> Prop) (fx' : YK11.FPState) regs pc mem,
  P (lcanon fx' regs pc mem) -> eqv_cl P (lcanon fx' regs pc mem).
Proof.
  intros P fx' regs pc mem H. apply (lc_eqv_rep P fx' regs regs pc mem); [intros r _; reflexivity | exact H].
Qed.

(* ==========================================================================
   4. The frame step
   ========================================================================== *)

Section LC.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FF : LFF B API.
Local Notation segs := (ms_segs B).
Local Notation MR := (aa_MR API).

Lemma lc_segs : ms_segs B = rsegs.
Proof. exact (lff_segs B API FF). Qed.

Lemma lc_laws : MR_laws B MR.
Proof. exact (aa_laws API). Qed.

(* AllocExtra is a law of MR alone: take it from the frame's allocator record at any FP state *)
Lemma lc_ax : AllocExtra B MR.
Proof. exact (@lff_ax YK11.fx0 rc B API SH SK FF). Qed.

Lemma lc_fa : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.
Proof. exact (lff_alloc B API FF). Qed.

Lemma lc_ceil : LF_TOP < YM05.alloc_ceiling /\ YM05.alloc_ceiling < 2 ^ 47.
Proof. pose proof (@YM05.alloc_ceiling_val rc) as H. unfold LF_TOP. split; lia. Qed.

(* what ENTRY's premises give of the stack and the entry blocks *)
Lemma lc_gv : forall g, LGV B API g ->
  YM05.alloc_ceiling + SLOT_STACK <= lg_S g /\ lg_S g mod 16 = 0 /\ lg_S g <= 2 ^ 47 /\
  MR (lg_L g) (lg_A g) (lg_mem g) (lg_md g) /\ tb_live (lg_L g) (lg_A g) (lg_T g).
Proof.
  intros g (Hpre & _ & Htb & _).
  destruct Hpre as (HP & _ & _ & _ & _ & _ & _ & _ & _ & H47).
  destruct HP as (HM & _ & _ & _ & _ & H16 & Hc & _).
  unfold lg_S. split; [exact Hc|]. split; [exact H16|]. split; [exact H47|]. split; [exact HM | exact Htb].
Qed.

Lemma lc_blk : forall L A mem md a k i, MR L A mem md -> In (a, k) (blocks L A) -> 0 <= i < k ->
  present mem (a + i) /\ 4096 <= a /\ a + k <= YM05.alloc_ceiling /\ ~ owned B L A (a + i) /\ ~ in_img B (a + i).
Proof.
  intros L A mem md a k i HM Hin Hi. apply blocks_In in Hin as (p & <- & Hp).
  destruct (mr_blocks B MR lc_laws L A mem md p k i HM Hp Hi) as (H1 & H2 & H3 & H4).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  exact (ax_blocks_img lc_ax L A mem md p k i HM Hp Hi).
Qed.

Lemma lc_pw : forall L A mem md l, MR L A mem md -> Permutation (blocks L A) l -> pairwise ranges_disjoint l.
Proof.
  intros L A mem md l HM HP. apply (lc_pw_perm ranges_disjoint lc_rd_sym (blocks L A) l HP).
  exact (mr_blocks_disjoint B MR lc_laws L A mem md HM).
Qed.

Lemma lc_hb_b0 : forall L A mem md hb b0 x y, MR L A mem md -> Permutation (blocks L A) (hb ++ b0) ->
  In x hb -> In y b0 -> ranges_disjoint x y.
Proof.
  intros L A mem md hb b0 x y HM HP Hx Hy. exact (lc_pw_app ranges_disjoint hb b0 (lc_pw L A mem md _ HM HP) x y Hx Hy).
Qed.

(* a block of the kept set is a live block *)
Lemma lc_T_blk : forall g hb T L A mem md t, LFR B API g hb T L A mem md -> In t T -> In t (blocks L A).
Proof.
  intros g hb T L A mem md t HF Ht.
  destruct HF as (HGV & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP & HKT & _).
  destruct (lc_gv g HGV) as (_ & _ & _ & _ & (_ & Htb)).
  apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app.
  destruct HKT as [(_ & ->) | (_ & [-> | (f & -> & Hf)])].
  - right. exact (Htb t Ht).
  - destruct Ht.
  - left. destruct Ht as [<- | []]. exact Hf.
Qed.

Lemma lc_lkeep_mono : forall g hb hb' x, incl hb' hb -> lkeep B g hb' x -> lkeep B g hb x.
Proof.
  intros g hb hb' x Hi [H|[H|[(t & k & Hin & Hx)|H]]]; [left; exact H | right; left; exact H | | right; right; right; exact H].
  right. right. left. exists t, k. split; [exact (Hi _ Hin) | exact Hx].
Qed.

(* the three words mf_gi reads outside the FILE block (g_sink, g_say, ofl_head) are image bytes the allocator
   does not own *)
Lemma lfr_heads_img : forall a, mf_head_addr link_mf a -> lf_img B a.
Proof.
  intros a Ha. cbv [mf_head_addr link_mf mf_sink_addr mf_say_addr] in Ha.
  pose proof FF as (_ & _ & _ & _ & _ & _ & GU & GO & CTX & LCK & LIBC & SCL & SMC & MDC & DBR & TP & EOFF & _ & VML
    & DBL & OFH & _).
  rewrite OFH in Ha.
  split.
  { pose proof lc_img_chk as H. apply existsb_exists in H as (s & Hs & Hb).
    apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    split; [rewrite lc_segs; exact lfr_rsegs_nonnil|]. exists s. rewrite lc_segs. split; [exact Hs | unfold LF_TOP in *; lia]. }
  split; [unfold static_owned, vml_lo, vml_len; rewrite LCK, LIBC, GO, GU, DBR, SCL, SMC, MDC, VML, DBL; lia|].
  split; [rewrite CTX; unfold CTX_SIZE; lia|].
  unfold errno_addr. rewrite TP, EOFF. lia.
Qed.

(* the FILE invariant is local to the three heads and the FILE block's first MF_ZEROED bytes *)
Lemma lfr_gi_keep : forall T (mem mem' : word -> option byte), mf_gi B link_mf T mem ->
  (forall a, mf_head_addr link_mf a -> mbyte segs mem' a = mbyte segs mem a) ->
  (forall f x, T = [(f, MF_BLOCK)] -> f <= x < f + MF_ZEROED -> mbyte segs mem' x = mbyte segs mem x) ->
  mf_gi B link_mf T mem'.
Proof.
  intros T mem mem' H Hh Hb. destruct H as [(H0 & HT) | (f & Hf & HT & Hm)].
  - left. split; [eapply mf_heads_frame; [exact Hh | exact H0] | exact HT].
  - right. exists f. split; [eapply mf_heads_frame; [exact Hh | exact Hf]|]. split; [exact HT|].
    eapply memfile_at_frame; [|exact Hm]. intros x Hx. exact (Hb f x HT Hx).
Qed.

(* The conjuncts of call_post_k (YO0d.v:401-413) the frame step reads: all but layout_le, the block addresses'
   stability, regs_preserved and the user-block clause (mark_quietly's mq_post_k has these as they are). *)
Definition lcall_post (K : Z) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (E : Z -> Prop) (L' : layout) (A' : astate) (mem' : word -> option byte) (md' : Model) : Prop :=
  MR L' A' mem' md' /\ WF A' /\ bounded A' /\
  (exists vm', md' = with_vmmaps vm' md) /\
  (forall a, (YM05.alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) ->
     ~ owned B L A a -> ~ owned B L' A' a -> ~ scratch_k B K regs a -> ~ E a ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall a, scratch_k B K regs a -> writable_at segs mem' a).

Lemma lcall_post_k : forall K L A regs mem md E L' A' regs' mem' md',
  call_post_k B MR K L A regs mem md E L' A' regs' mem' md' -> lcall_post K L A regs mem md E L' A' mem' md'.
Proof.
  intros K L A regs mem md E L' A' regs' mem' md' (H1 & H2 & H3 & _ & _ & _ & H7 & H8 & _ & H10).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H7|]. split; [exact H8 | exact H10].
Qed.

(* the callee's frame clause at the slot's call: the high memory outside its scratch and the image bytes the
   allocator does not own keep their bytes and writability, unless the callee writes them (E) *)
Lemma lc_frame : forall g hb T L A mem md regs K E L' A' mem' md',
  LFR B API g hb T L A mem md -> spZ regs = lg_S g - SLOT_FRAME -> 0 <= K <= SLOT_STACK - SLOT_FRAME ->
  lcall_post K L A regs mem md E L' A' mem' md' ->
  forall a, ((YM05.alloc_ceiling <= a < 2 ^ 64 /\ ~ (lg_S g - SLOT_FRAME - K <= a < lg_S g - SLOT_FRAME)) \/
             lf_img B a) -> ~ E a ->
  mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a).
Proof.
  intros g hb T L A mem md regs K E L' A' mem' md' HF Hsp HK HC a Ha HE.
  destruct HF as (HGV & HM & _).
  destruct (lc_gv g HGV) as (HS & _ & HS47 & _).
  destruct HC as (HM' & _ & _ & _ & HFR & _).
  pose proof lc_ceil as [HC1 HC2]. unfold LF_TOP in HC1. pose proof (lff_errc B API FF) as HER.
  unfold SLOT_STACK, SLOT_FRAME in *.
  destruct Ha as [[Ha Hns] | (Hi & Hso & Hctx & Her)].
  - apply HFR; [left; exact Ha | | | | exact HE].
    + intros Ho. pose proof (mr_owned_low B MR lc_laws L A mem md a HM Ho). lia.
    + intros Ho. pose proof (mr_owned_low B MR lc_laws L' A' mem' md' a HM' Ho). lia.
    + unfold scratch_k. rewrite Hsp. lia.
  - pose proof (lfr_in_img_top B a lc_segs Hi) as Ht.
    assert (Hno : forall L1 A1 mem1 md1, MR L1 A1 mem1 md1 -> ~ owned B L1 A1 a).
    { intros L1 A1 mem1 md1 HM1 [Ho|Ho]; [exact (Hctx (ax_img lc_ax L1 A1 mem1 md1 a HM1 Hi Ho)) | exact (Hso Ho)]. }
    apply HFR; [right; exact Hi | exact (Hno _ _ _ _ HM) | exact (Hno _ _ _ _ HM') | | exact HE].
    unfold scratch_k. rewrite Hsp. intros [Hs|Hs]; [unfold LF_TOP in *; lia | exact (Her Hs)].
Qed.

(* every LFR state's view has what the evt segments ask of memory after an allocator call *)
Lemma lfr_post_mem : forall g hb T L A mem md, LFR B API g hb T L A mem md -> lpost_mem g (normalize_cj rsegs mem).
Proof.
  intros g hb T L A mem md HF. pose proof lc_segs as SEG.
  destruct HF as (HGV & HM & _ & _ & _ & _ & _ & _ & _ & Hwin & Her & _ & HRO & _).
  destruct (lc_gv g HGV) as (HS & _ & HS47 & _).
  pose proof lc_ceil as [HC1 HC2]. unfold LF_TOP in HC1. rewrite SEG in Hwin, Her, HRO.
  split; [exact (mem_inv_cj_inv rsegs _ (mem_inv_cj_normalize rsegs mem))|].
  split; [exact (mem_inv_cj_task rsegs _ (mem_inv_cj_normalize rsegs mem))|].
  split.
  { apply lfr_stk; [clear - HS HC1; unfold SLOT_STACK, LF_TOP in *; lia | unfold SLOT_FRAME; lia |].
    intros a Ha. assert (HCJ : cj_drop rsegs (Z_to_bv 64 a) = false).
    { apply lc_cj_keep; [clear - Ha HS HS47 HC1; unfold TASK_SIZE, SLOT_STACK, SLOT_FRAME in *; lia|].
      apply lc_ro_hi. clear - Ha HS HS47 HC1. unfold LF_TOP, SLOT_STACK, SLOT_FRAME in *. lia. }
    apply (proj2 (proj2 (lc_norm_keep mem a HCJ))). apply Hwin. clear - Ha. unfold SLOT_FRAME, SLOT_STACK in *. lia. }
  split.
  { split; [unfold A_ERRNO, A_TP, ERRNO_TP_OFF; lia|]. split; [unfold A_ERRNO, A_TP, ERRNO_TP_OFF; lia|].
    intros i Hi. pose proof (lc_errno_keep (A_ERRNO + i) ltac:(lia)) as HCJ.
    exact (proj2 (proj2 (lc_norm_keep mem (A_ERRNO + i) HCJ))
      (Her (A_ERRNO + i) ltac:(rewrite (lff_errno B API FF); lia))). }
  destruct (ax_statics lc_ax L A mem md HM) as (G1 & (gv & Hgv & G2) & _).
  rewrite SEG, (lff_got B API FF), (lff_guard B API FF) in G1. rewrite SEG, (lff_guard B API FF) in G2.
  split.
  - apply (bytes_at_normalize_cj_low rsegs mem); [exact HRO | rewrite Mem.length_le8; unfold A_GOT_GUARD_S, TASK_SIZE; lia |].
    apply (KindBGlue.word_mem_le8 rsegs); [exact G1 | unfold A_GUARD_S; lia | unfold A_GOT_GUARD_S; lia | unfold A_GOT_GUARD_S; lia].
  - exists (Z_to_bv 64 gv). apply (bytes_at_normalize_cj_low rsegs mem); [exact HRO | rewrite Mem.length_le8; unfold A_GUARD_S, TASK_SIZE; lia |].
    apply (KindBGlue.word_mem_le8 rsegs); [exact G2 | exact Hgv | unfold A_GUARD_S; lia | unfold A_GUARD_S; lia].
Qed.

(* THE GENERIC STEP, over the conjuncts of the callee's Post it reads. The callee runs at sp = S - 480 with its
   scratch K below; it writes E: above the allocator's ceiling only inside the slot's stack window, in the
   image only where the frame lets a call change it (outside lf_img, or in llvm_G), and in the entry blocks
   only the kept ones (T0). The caller gives the bytes of the live blocks outside E (call_post_k's user-block
   clause, or the contract's blocks_kept), and the accounting at the return (st_init_done, ro_agree, the bound,
   the blocks, the kept set, the FILE invariant). *)
Lemma lfr_call_core : forall g hb T L A mem md regs K E L' A' mem' md' hb' T',
  LFR B API g hb T L A mem md ->
  spZ regs = lg_S g - SLOT_FRAME -> 0 <= K <= SLOT_STACK - SLOT_FRAME ->
  lcall_post K L A regs mem md E L' A' mem' md' ->
  (forall a, E a -> YM05.alloc_ceiling <= a -> lg_S g - SLOT_STACK <= a < lg_S g) ->
  (forall a, E a -> lf_img B a -> in_globals llvm_G a) ->
  (forall a, lg_S g - SLOT_STACK <= a < lg_S g -> E a \/ ~ E a) ->
  (forall a, E a -> lg_S g - SLOT_STACK <= a < lg_S g -> writable_at segs mem' a) ->
  (forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> ~ E (a + i) ->
     mbyte segs mem' (a + i) = mbyte segs mem (a + i)) ->
  (forall a k i, In (a, k) (blocks (lg_L g) (lg_A g)) -> ~ In (a, k) (lg_T g) -> 0 <= i < k -> ~ E (a + i)) ->
  st_init_done A' = true -> ro_agree segs mem' ->
  res_ok_slots A' (sb_hb (lg_b g) hb') ->
  Permutation (blocks L' A') (hb' ++ blocks (lg_L g) (lg_A g)) ->
  lkept g hb' T' -> mf_gi B link_mf T' mem' ->
  LFR B API g hb' T' L' A' mem' md' /\
  lcarry (fun x => lkeep B g hb x /\ ~ E x) (normalize_cj rsegs mem) (normalize_cj rsegs mem') /\
  lpost_mem g (normalize_cj rsegs mem').
Proof.
  intros g hb T L A mem md regs K E L' A' mem' md' hb' T' HF Hsp HK HC HEhi HEimg HEd HEw HBK HE0
    HID' HRO' HRS' HP' HKT' HGI'.
  pose proof (lc_frame g hb T L A mem md regs K E L' A' mem' md' HF Hsp HK HC) as KEEP.
  pose proof HF as (HGV & HM & HW & HBD & HID & (vm & Hmd) & Hhi & Himg & Hb0 & Hwin & Her & Hgd & HRO & HRS & HP
    & HKT & HGI).
  destruct (lc_gv g HGV) as (HS & HS16 & HS47 & HM0 & Htb).
  pose proof HC as (HM' & HW' & HBD' & (vm' & Hmd') & _ & HSC).
  pose proof lc_ceil as [HC1 HC2]. unfold LF_TOP in HC1. pose proof (lff_errc B API FF) as HER. pose proof lc_segs as SEG.
  assert (HLF : LFR B API g hb' T' L' A' mem' md').
  { split; [exact HGV|]. split; [exact HM'|]. split; [exact HW'|]. split; [exact HBD'|]. split; [exact HID'|].
    split; [exists vm'; rewrite Hmd', Hmd; reflexivity|].
    split.
    { intros a Ha Hns. assert (HnE : ~ E a) by (intros He; pose proof (HEhi a He (proj1 Ha)); lia).
      assert (Hr : ~ (lg_S g - SLOT_FRAME - K <= a < lg_S g - SLOT_FRAME))
        by (unfold SLOT_STACK, SLOT_FRAME in *; lia).
      destruct (KEEP a (or_introl (conj Ha Hr)) HnE) as [E1 E2].
      destruct (Hhi a Ha Hns) as [F1 F2]. split; [rewrite E1; exact F1 | rewrite F2; exact E2]. }
    split.
    { intros a Ha HnG. assert (HnE : ~ E a) by (intros He; exact (HnG (HEimg a He Ha))).
      destruct (KEEP a (or_intror Ha) HnE) as [E1 E2].
      destruct (Himg a Ha HnG) as [F1 F2]. split; [rewrite E1; exact F1 | rewrite F2; exact E2]. }
    split.
    { intros a k i Hin HnT Hi.
      assert (Hin' : In (a, k) (blocks L A))
        by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact Hin).
      rewrite (HBK a k i Hin' Hi (HE0 a k i Hin HnT Hi)). exact (Hb0 a k i Hin HnT Hi). }
    split.
    { intros a Ha.
      assert (Hlo : forall a, lg_S g - SLOT_STACK <= a < lg_S g -> ~ (spZ regs - K <= a < spZ regs) ->
        YM05.alloc_ceiling <= a < 2 ^ 64 /\ ~ (lg_S g - SLOT_FRAME - K <= a < lg_S g - SLOT_FRAME)).
      { intros a0 Ha0 Hn0. rewrite Hsp in Hn0. unfold SLOT_STACK, SLOT_FRAME in *. lia. }
      destruct (Z_lt_le_dec a (spZ regs - K)) as [L1|L1]; [|destruct (Z_lt_le_dec a (spZ regs)) as [L2|L2]].
      - destruct (HEd a Ha) as [He|He]; [exact (HEw a He Ha)|].
        destruct (KEEP a (or_introl (Hlo a Ha ltac:(lia))) He) as [_ E2]. apply E2. exact (Hwin a Ha).
      - apply HSC. unfold scratch_k. left. lia.
      - destruct (HEd a Ha) as [He|He]; [exact (HEw a He Ha)|].
        destruct (KEEP a (or_introl (Hlo a Ha ltac:(lia))) He) as [_ E2]. apply E2. exact (Hwin a Ha). }
    split; [intros a Ha; apply HSC; unfold scratch_k; right; exact Ha|].
    split.
    { intros i Hi. destruct (ax_statics lc_ax L A mem md HM) as (G1 & _).
      destruct (ax_statics lc_ax L' A' mem' md' HM') as (G2 & _).
      rewrite <- (Hgd i Hi). replace i with (Z.of_nat (Z.to_nat i)) by lia.
      rewrite (G2 (Z.to_nat i) ltac:(lia)), (G1 (Z.to_nat i) ltac:(lia)). reflexivity. }
    split; [exact HRO'|]. split; [exact HRS'|]. split; [exact HP'|]. split; [exact HKT' | exact HGI']. }
  split; [exact HLF|]. split; [|exact (lfr_post_mem g hb' T' L' A' mem' md' HLF)].
  intros x [Hk HnE].
  assert (H : mbyte segs mem' x = mbyte segs mem x /\ (writable_at segs mem x <-> writable_at segs mem' x)).
  { destruct Hk as [Hx | [Hx | [(t & k & Hin & Hx) | (t & k & Hin & Hx)]]].
    - apply (KEEP x); [left; unfold SLOT_STACK, SLOT_FRAME in *; lia | exact HnE].
    - exact (KEEP x (or_intror Hx) HnE).
    - assert (Hin' : In (t, k) (blocks L A))
        by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact Hin).
      destruct (lc_blk L A mem md t k (x - t) HM Hin' ltac:(lia)) as (Hpr & H1 & H2 & _ & Hni).
      pose proof (HBK t k (x - t) Hin' ltac:(lia)) as Hb.
      replace (t + (x - t)) with x in Hpr, Hni, Hb by lia. specialize (Hb HnE).
      split; [exact Hb|]. rewrite SEG in *. apply (lc_nonimg_wr B mem mem' x SEG Hni); [lia | exact Hpr | exact Hb].
    - assert (Hin' : In (t, k) (blocks L A))
        by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact Hin).
      destruct (lc_blk L A mem md t k (x - t) HM Hin' ltac:(lia)) as (Hpr & H1 & H2 & _ & Hni).
      pose proof (HBK t k (x - t) Hin' ltac:(lia)) as Hb.
      replace (t + (x - t)) with x in Hpr, Hni, Hb by lia. specialize (Hb HnE).
      split; [exact Hb|]. rewrite SEG in *. apply (lc_nonimg_wr B mem mem' x SEG Hni); [lia | exact Hpr | exact Hb]. }
  rewrite SEG in H. exact (lc_norm_carry mem mem' x (proj1 H) (proj2 H)).
Qed.

(* THE GENERIC STEP through a callee whose Post is call_post_k *)
Lemma lfr_call : forall g hb T L A mem md regs K E L' A' regs' mem' md' hb' T',
  LFR B API g hb T L A mem md ->
  spZ regs = lg_S g - SLOT_FRAME -> 0 <= K <= SLOT_STACK - SLOT_FRAME ->
  call_post_k B MR K L A regs mem md E L' A' regs' mem' md' ->
  (forall a, E a -> YM05.alloc_ceiling <= a -> lg_S g - SLOT_STACK <= a < lg_S g) ->
  (forall a, E a -> lf_img B a -> in_globals llvm_G a) ->
  (forall a, lg_S g - SLOT_STACK <= a < lg_S g -> E a \/ ~ E a) ->
  (forall a, E a -> lg_S g - SLOT_STACK <= a < lg_S g -> writable_at segs mem' a) ->
  (forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> ~ E (a + i) ->
     mbyte segs mem' (a + i) = mbyte segs mem (a + i)) ->
  (forall a k i, In (a, k) (blocks (lg_L g) (lg_A g)) -> ~ In (a, k) (lg_T g) -> 0 <= i < k -> ~ E (a + i)) ->
  st_init_done A' = true -> ro_agree segs mem' ->
  res_ok_slots A' (sb_hb (lg_b g) hb') ->
  Permutation (blocks L' A') (hb' ++ blocks (lg_L g) (lg_A g)) ->
  lkept g hb' T' -> mf_gi B link_mf T' mem' ->
  LFR B API g hb' T' L' A' mem' md' /\
  lcarry (fun x => lkeep B g hb x /\ ~ E x) (normalize_cj rsegs mem) (normalize_cj rsegs mem') /\
  lpost_mem g (normalize_cj rsegs mem').
Proof.
  intros g hb T L A mem md regs K E L' A' regs' mem' md' hb' T' HF Hsp HK HC.
  exact (lfr_call_core g hb T L A mem md regs K E L' A' mem' md' hb' T' HF Hsp HK
    (lcall_post_k K L A regs mem md E L' A' regs' mem' md' HC)).
Qed.

(* lfr_call's premise on the live blocks' bytes outside E, from a Post's user-block clause that excepts X (inside
   E) and a contract's "every old user block stays" (malloc_ret; text_buf / text_of / mark_quietly as amended) *)
Lemma lfr_hbk_x : forall (X E : Z -> Prop) L A A' (mem mem' : word -> option byte),
  (forall p n i, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A') -> 0 <= i < n -> ~ X (ptr_addr L p + i) ->
     mbyte segs mem' (ptr_addr L p + i) = mbyte segs mem (ptr_addr L p + i)) ->
  (forall x, X x -> E x) ->
  (forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')) ->
  forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> ~ E (a + i) ->
    mbyte segs mem' (a + i) = mbyte segs mem (a + i).
Proof.
  intros X E L A A' mem mem' HU HX HP a k i Hin Hi HnE.
  apply blocks_In in Hin as (p & <- & Hp).
  apply (HU p k i Hp (HP p k Hp) Hi). intros Hx. exact (HnE (HX _ Hx)).
Qed.

Lemma lfr_hbk : forall K L A regs mem md E L' A' regs' mem' md',
  call_post_k B MR K L A regs mem md E L' A' regs' mem' md' ->
  (forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')) ->
  forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> ~ E (a + i) ->
    mbyte segs mem' (a + i) = mbyte segs mem (a + i).
Proof.
  intros K L A regs mem md E L' A' regs' mem' md' HC HP.
  destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & HU & _).
  apply (lfr_hbk_x (fun _ => False) E L A A' mem mem'); [| intros x [] | exact HP].
  intros p n i H1 H2 H3 _. exact (HU p n i H1 H2 H3).
Qed.

(* the block an allocating callee hands out is fresh for the slot (LFr lfresh) *)
Lemma lfr_fresh : forall g hb L A L' A' mem' md' b1 b2 r n,
  LGV B API g -> Permutation (blocks L A) (hb ++ blocks (lg_L g) (lg_A g)) ->
  MR L' A' mem' md' -> blocks L' A' = b1 ++ (r, n) :: b2 -> blocks L A = b1 ++ b2 ->
  r <> 0 -> fresh_block B r n -> lfresh B g hb r n.
Proof.
  intros g hb L A L' A' mem' md' b1 b2 r n HGV HP HM' E' E Hr0 (H1 & H2 & H3).
  destruct (lc_gv g HGV) as (HS & _).
  pose proof (mr_blocks_disjoint B MR lc_laws L' A' mem' md' HM') as Hpw. rewrite E' in Hpw.
  assert (D : forall a k, In (a, k) (blocks L A) -> r + n <= a \/ a + k <= r).
  { intros a k Hin. rewrite E in Hin.
    destruct (lc_pw_mid ranges_disjoint b1 (r, n) b2 Hpw (a, k) Hin) as [D|D];
      unfold ranges_disjoint in D; cbn [fst snd] in D; lia. }
  split; [exact Hr0|]. split; [exact H1|]. split; [unfold SLOT_STACK in *; lia|]. split; [exact H3|].
  split.
  - intros a k Hin. apply D. apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hin.
  - intros a k Hin. apply D. apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. exact Hin.
Qed.

Lemma lfresh_blk_out : forall g hb r n, lfresh B g hb r n -> blk_out (lg_S g) r n.
Proof.
  intros g hb r n (_ & H1 & H2 & H3 & _). split; [exact H1|]. split; [unfold SLOT_STACK, SLOT_STACK_Z in *; lia|].
  intros i Hi s Hs Hr. apply (H3 i Hi). split; [rewrite lc_segs; exact lfr_rsegs_nonnil|].
  exists s. split; [rewrite lc_segs; exact Hs | exact Hr].
Qed.

End LC.
