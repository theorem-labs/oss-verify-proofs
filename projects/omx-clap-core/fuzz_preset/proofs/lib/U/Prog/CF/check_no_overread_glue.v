From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract Img0 KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger ReaderRes GIInit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import check_no_overread_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import fuzz_alloc_ran_out_c.
Import ListNotations.
Local Open Scope Z_scope.

Lemma cno_with_vmmaps_twice : forall v1 v2 md, with_vmmaps v2 (with_vmmaps v1 md) = with_vmmaps v2 md.
Proof. intros v1 v2 md. destruct md as [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma cno_with_vmmaps_self : forall md, md = with_vmmaps (m_vmmaps md) md.
Proof. intros md. destruct md as [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma cno_lsum_perm : forall l l', Permutation l l' -> lsum l = lsum l'.
Proof.
  intros l l' H. induction H as [|[a k] l l' H IH|[a k] [b j] l|l l' l'' H1 IH1 H2 IH2]; cbn [lsum]; lia.
Qed.

Lemma cno_dl_of : forall T D, Permutation (map snd D) (map Z.of_nat (lsz T)) -> Z.of_nat (length D) = nlive T ->
  cno_dl T D.
Proof. intros T D H1 H2. unfold cno_dl. split; assumption. Qed.

Lemma cno_dl_perm : forall T D D', Permutation D D' -> cno_dl T D -> cno_dl T D'.
Proof.
  intros T D D' HP (H1 & H2). unfold cno_dl. rewrite <- (Permutation_length HP). split; [|exact H2].
  exact (Permutation_trans (Permutation_sym (Permutation_map snd HP)) H1).
Qed.

Lemma cno_k_le : 10096 <= CNO_K <= 2 ^ 20.
Proof. split; unfold Z.le; vm_compute; discriminate. Qed.

Section G.
Context {fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Local Abbreviation segs := (ms_segs B).
Hypothesis HS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B MR.
Hypothesis CTX : ctx_owned B API.
Hypothesis HG : globals_free B API omx_G.

Lemma cno_img : img_low B.
Proof.
  apply (img_low_of_check B 140735332483072).
  - unfold img_check. rewrite HS. vm_compute. reflexivity.
  - pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value. lia.
Qed.

Lemma cno_img_low : forall a, in_img B a -> 0 <= a < alloc_ceiling.
Proof. exact (proj1 cno_img). Qed.

Lemma cno_in_blocks : forall L A a k, In (a, k) (blocks L A) -> exists p, In (p, k) (user_blocks A) /\ ptr_addr L p = a.
Proof.
  intros L A a k H. unfold blocks in H. apply in_map_iff in H as ([p k'] & E & Hin). cbn in E.
  inversion E; subst. exists p. split; [exact Hin | reflexivity].
Qed.

Lemma cno_ub_blocks : forall L A p k, In (p, k) (user_blocks A) -> In (ptr_addr L p, k) (blocks L A).
Proof. intros L A p k H. unfold blocks. apply in_map_iff. exists (p, k). split; [reflexivity | exact H]. Qed.

Lemma cno_block_facts : forall L A mem md a k i, MR L A mem md -> In (a, k) (blocks L A) -> 0 <= i < k ->
  present mem (a + i) /\ 4096 <= a /\ a + k <= alloc_ceiling /\ ~ owned B L A (a + i) /\ ~ in_img B (a + i).
Proof.
  intros L A mem md a k i HM Hin Hi. destruct (cno_in_blocks L A a k Hin) as (p & Hp & <-).
  destruct (mr_blocks _ _ (aa_laws API) L A mem md p k i HM Hp Hi) as (H1 & H2 & H3 & H4).
  repeat split; try assumption. exact (ax_blocks_img AX L A mem md p k i HM Hp Hi).
Qed.

Lemma cno_block_range : forall L A mem md a k, MR L A mem md -> In (a, k) (blocks L A) ->
  4096 <= a /\ a + k <= alloc_ceiling.
Proof.
  intros L A mem md a k HM Hin. destruct (cno_in_blocks L A a k Hin) as (p & Hp & <-).
  exact (mr_blocks_range _ _ (aa_laws API) L A mem md p k HM Hp).
Qed.

Lemma cno_pairwise_in : forall {T : Type} (R : T -> T -> Prop) l x y,
  pairwise R l -> In x l -> In y l -> x <> y -> R x y \/ R y x.
Proof.
  intros T R l. induction l as [|z l IH]; intros x y HP Hx Hy Hne; cbn in *; [destruct Hx|].
  destruct HP as [Hz HP]. destruct Hx as [<-|Hx], Hy as [<-|Hy].
  - congruence.
  - left. apply Hz. exact Hy.
  - right. apply Hz. exact Hx.
  - apply IH; assumption.
Qed.

Lemma cno_blocks_sep : forall L A m md x y, MR L A m md -> In x (blocks L A) -> In y (blocks L A) -> x <> y ->
  fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof.
  intros L A m md x y HM Hx Hy Hne.
  destruct (cno_pairwise_in _ _ x y (mr_blocks_disjoint _ _ (aa_laws API) L A m md HM) Hx Hy Hne) as [H|H];
    unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YO0f.ranges_disjoint in H; lia.
Qed.

Lemma cno_never_owned_img : forall L A m md a, MR L A m md -> in_img B a -> ~ static_owned B a ->
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) -> ~ owned B L A a.
Proof.
  intros L A m md a HM Hi Hs Hc [Ho|Ho]; [|exact (Hs Ho)].
  exact (Hc (ax_img AX L A m md a HM Hi Ho)).
Qed.

Lemma cno_statics_img : forall a, alloc_statics a -> in_globals omx_G a.
Proof.
  intros a Ha. unfold alloc_statics in Ha. unfold in_globals, omx_G.
  destruct Ha as [H|[H|[H|H]]].
  - exists G_LIVE, 8. split; [left; reflexivity | exact H].
  - exists G_PEAK, 8. split; [right; left; reflexivity | exact H].
  - exists G_COUNT, 8. split; [right; right; left; reflexivity | exact H].
  - exists G_FAIL, 8. split; [right; right; right; left; reflexivity | exact H].
Qed.

Lemma cno_statics_free : forall a, alloc_statics a ->
  in_img B a /\ 0 <= a < alloc_ceiling /\ ~ (errno_addr B <= a < errno_addr B + 4) /\
  forall L A mem md, MR L A mem md -> ~ owned B L A a /\ forall p n, In (p, n) (blocks L A) -> ~ (p <= a < p + n).
Proof.
  intros a Ha. destruct (HG a (cno_statics_img a Ha)) as (H1 & H2 & _ & H4 & H5). auto.
Qed.

(* g_ran_out (fuzz_alloc_ran_out_c.G_RAN_OUT, the same address as LedgerCells.GL_RAN_OUT) is entry 5 of omx_G and
   g_own_ran_out (LedgerCells.GL_OWN_RAN_OUT) is entry 7 (GIInit.omx_G = LedgerCells.GL_cells), so HG covers both. *)
Lemma cno_gro_free : forall a, G_RAN_OUT <= a < G_RAN_OUT + 1 ->
  in_img B a /\ 0 <= a < alloc_ceiling /\ ~ (errno_addr B <= a < errno_addr B + 4) /\
  forall L A mem md, MR L A mem md -> ~ owned B L A a /\ forall p n, In (p, n) (blocks L A) -> ~ (p <= a < p + n).
Proof.
  intros a Ha.
  assert (Hin : in_globals omx_G a).
  { unfold in_globals. exists GL_RAN_OUT, 8. split; [|change GL_RAN_OUT with G_RAN_OUT; lia].
    unfold omx_G. cbn [In]. repeat first [left; reflexivity | right]. }
  destruct (HG a Hin) as (H1 & H2 & _ & H4 & H5). auto.
Qed.

Lemma cno_own_free : forall a, GL_OWN_RAN_OUT <= a < GL_OWN_RAN_OUT + 1 ->
  in_img B a /\ 0 <= a < alloc_ceiling /\ ~ (errno_addr B <= a < errno_addr B + 4) /\
  forall L A mem md, MR L A mem md -> ~ owned B L A a /\ forall p n, In (p, n) (blocks L A) -> ~ (p <= a < p + n).
Proof.
  intros a Ha.
  assert (Hin : in_globals omx_G a).
  { unfold in_globals. exists GL_OWN_RAN_OUT, 8. split; [|lia].
    unfold omx_G. cbn [In]. repeat first [left; reflexivity | right]. }
  destruct (HG a Hin) as (H1 & H2 & _ & H4 & H5). auto.
Qed.

(* Neither ran-out byte is one of the four ledger words. *)
Lemma cno_gro_statics : forall a, G_RAN_OUT <= a < G_RAN_OUT + 1 -> ~ alloc_statics a.
Proof. intros a Ha Hs. unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL, G_RAN_OUT in *. lia. Qed.

Lemma cno_own_statics : forall a, GL_OWN_RAN_OUT <= a < GL_OWN_RAN_OUT + 1 -> ~ alloc_statics a.
Proof. intros a Ha Hs. unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL, GL_OWN_RAN_OUT in *. lia. Qed.

Lemma cno_writes_free : forall a, cno_writes a ->
  in_img B a /\ 0 <= a < alloc_ceiling /\ ~ (errno_addr B <= a < errno_addr B + 4) /\
  forall L A mem md, MR L A mem md -> ~ owned B L A a /\ forall p n, In (p, n) (blocks L A) -> ~ (p <= a < p + n).
Proof. intros a [Ha|Ha]; [exact (cno_statics_free a Ha) | exact (cno_gro_free a Ha)]. Qed.

Variables (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Hypothesis PRE0 : call_pre_k B MR CNO_K L0 A0 regs0 mem0 md0.

(* The frame invariant of the walk keeps every byte off the frame and off the new blocks at its entry value except the
   four ledger words (alloc_statics): so g_ran_out and g_own_ran_out keep their entry bytes through the whole call. *)

Definition cj (L : layout) (A : astate) (mem : word -> option byte) (md : Model) : Prop :=
  MR L A mem md /\ WF A /\ bounded A /\ layout_le A0 L0 L /\
  (st_init_done A0 = true -> st_init_done A = true) /\
  (st_init_done A = false -> forall i, 0 <= i < 8 ->
     mbyte segs mem (ms_libc B + 8 + i) = mbyte segs mem0 (ms_libc B + 8 + i)) /\
  (length (st_regions A0) <= length (st_regions A))%nat /\
  (forall p n, In (p, n) (user_blocks A0) -> In (p, n) (user_blocks A) /\ ptr_addr L p = ptr_addr L0 p) /\
  (exists vm, md = with_vmmaps vm md0) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ scratch_k B CNO_K regs0 a -> ~ alloc_statics a ->
     mbyte segs mem a = mbyte segs mem0 a /\ (writable_at segs mem0 a <-> writable_at segs mem a)) /\
  (forall a, in_img B a -> (forall L1 A1 m1 md1, MR L1 A1 m1 md1 -> ~ owned B L1 A1 a) ->
     ~ scratch_k B CNO_K regs0 a -> ~ alloc_statics a ->
     mbyte segs mem a = mbyte segs mem0 a /\ (writable_at segs mem0 a <-> writable_at segs mem a)) /\
  (forall p n i, In (p, n) (user_blocks A0) -> 0 <= i < n -> ~ alloc_statics (ptr_addr L0 p + i) ->
     mbyte segs mem (ptr_addr L0 p + i) = mbyte segs mem0 (ptr_addr L0 p + i)) /\
  (forall a, scratch_k B CNO_K regs0 a -> writable_at segs mem a) /\
  ro_agree segs mem.

Lemma cj_init : ro_agree segs mem0 -> cj L0 A0 mem0 md0.
Proof.
  intros RA. destruct PRE0 as (HM & HWF & HBD & _ & _ & _ & _ & HW & _ & HER & _).
  split; [exact HM|]. split; [exact HWF|]. split; [exact HBD|]. split; [apply layout_le_refl|].
  split; [tauto|]. split; [intros; reflexivity|]. split; [lia|].
  split; [intros p n H; split; [exact H | reflexivity]|].
  split; [exists (m_vmmaps md0); apply cno_with_vmmaps_self|].
  split; [intros; split; [reflexivity | tauto]|].
  split; [intros; split; [reflexivity | tauto]|].
  split; [intros; reflexivity|].
  split; [intros a [Ha|Ha]; [apply HW | apply HER]; exact Ha|].
  exact RA.
Qed.

Lemma cj_final : forall L A mem md regs',
  cj L A mem md -> regs_preserved regs0 regs' ->
  rpost B API CNO_K L0 A0 regs0 mem0 md0 cno_writes (fun _ _ => False) L A regs' mem md.
Proof.
  intros L A mem md regs' (HM & HWF & HBD & HLY & HI & HLB & HLN & HUB & HMD & HHI & HIM & HB0 & HSC & HRA) RP.
  split; [exact HM|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact HLY|].
  split; [exact HI|]. split; [exact HLB|]. split; [exact HLN|].
  split; [intros p n H _; exact (proj1 (HUB p n H))|].
  split; [intros p n H _; exact (proj2 (HUB p n H))|].
  split; [exact RP|]. split; [exact HMD|].
  split; [intros a Ha Hs Hw; exact (HHI a Ha Hs (fun H => Hw (or_introl H)))|].
  split; [intros a Ha Ho Hs Hw; exact (HIM a Ha Ho Hs (fun H => Hw (or_introl H)))|].
  split; [intros p n i H _ Hi HE; exact (HB0 p n i H Hi (fun H' => HE (or_introl H')))|].
  exact HSC.
Qed.

Lemma cj_blocks0 : forall L A mem md a k, cj L A mem md -> In (a, k) (blocks L0 A0) -> In (a, k) (blocks L A).
Proof.
  intros L A mem md a k J Hin. destruct J as (_ & _ & _ & _ & _ & _ & _ & HUB & _).
  destruct (cno_in_blocks L0 A0 a k Hin) as (p & Hp & <-). destruct (HUB p k Hp) as [H1 H2].
  rewrite <- H2. apply cno_ub_blocks. exact H1.
Qed.

Lemma cj_mem0 : forall L A mem md a k i, cj L A mem md -> In (a, k) (blocks L0 A0) -> 0 <= i < k ->
  mbyte segs mem (a + i) = mbyte segs mem0 (a + i).
Proof.
  intros L A mem md a k i J Hin Hi. pose proof J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HB0 & _).
  destruct (cno_in_blocks L0 A0 a k Hin) as (p & Hp & <-). apply (HB0 p k i Hp Hi).
  destruct PRE0 as (HM0 & _).
  destruct (cno_block_facts L0 A0 mem0 md0 _ k i HM0 Hin Hi) as (_ & _ & _ & _ & Hni).
  intros Hs. exact (Hni (proj1 (cno_statics_free _ Hs))).
Qed.

(* An image run below the stack that no allocator state owns and that holds no ledger word keeps its entry bytes. *)
Lemma cj_bytes_keep : forall L A mem md c bs, cj L A mem md -> Mem.bytes_at segs mem0 c bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) ->
     in_img B (c + i) /\ c + i < alloc_ceiling /\ ~ (errno_addr B <= c + i < errno_addr B + 4) /\
     (forall L1 A1 m1 md1, MR L1 A1 m1 md1 -> ~ owned B L1 A1 (c + i)) /\ ~ alloc_statics (c + i)) ->
  Mem.bytes_at segs mem c bs.
Proof.
  intros L A mem md c bs J (H0 & H1 & H) HC.
  pose proof J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HIM & _).
  pose proof PRE0 as (_ & _ & _ & _ & _ & HK & _). pose proof cno_k_le as HKv.
  split; [exact H0|]. split; [exact H1|]. intros i Hi. rewrite <- (H i Hi).
  destruct (HC (Z.of_nat i) ltac:(lia)) as (Hi1 & Hlo & Her & Hown & Hst).
  assert (Hsc : ~ scratch_k B CNO_K regs0 (c + Z.of_nat i)) by (unfold scratch_k; lia).
  pose proof (proj1 (HIM _ Hi1 Hown Hsc Hst)) as E. unfold mbyte in E. exact E.
Qed.

Lemma cj_gro : forall L A mem md, cj L A mem md ->
  Mem.bytes_at segs mem0 G_RAN_OUT (Mem.le1 (Z_to_bv 64 0)) -> Mem.bytes_at segs mem G_RAN_OUT (Mem.le1 (Z_to_bv 64 0)).
Proof.
  intros L A mem md J HB. apply (cj_bytes_keep L A mem md _ _ J HB). rewrite Mem.length_le1. intros i Hi.
  destruct (cno_gro_free (G_RAN_OUT + i) ltac:(lia)) as (H1 & H2 & H3 & H4).
  split; [exact H1|]. split; [lia|]. split; [exact H3|].
  split; [intros L1 A1 m1 md1 HM1; exact (proj1 (H4 L1 A1 m1 md1 HM1))|].
  apply cno_gro_statics. lia.
Qed.

Lemma cj_own : forall L A mem md, cj L A mem md ->
  Mem.bytes_at segs mem0 GL_OWN_RAN_OUT (Mem.le1 (Z_to_bv 64 0)) ->
  Mem.bytes_at segs mem GL_OWN_RAN_OUT (Mem.le1 (Z_to_bv 64 0)).
Proof.
  intros L A mem md J HB. apply (cj_bytes_keep L A mem md _ _ J HB). rewrite Mem.length_le1. intros i Hi.
  destruct (cno_own_free (GL_OWN_RAN_OUT + i) ltac:(lia)) as (H1 & H2 & H3 & H4).
  split; [exact H1|]. split; [lia|]. split; [exact H3|].
  split; [intros L1 A1 m1 md1 HM1; exact (proj1 (H4 L1 A1 m1 md1 HM1))|].
  apply cno_own_statics. lia.
Qed.

Lemma cj_kindA : forall L A mem md mem' W,
  cj L A mem md -> Frame.munch W mem mem' -> Frame.wmono segs mem mem' -> ro_agree segs mem' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x -> (spZ regs0 - CNO_K <= x < spZ regs0) \/
     (exists r k, In (r, k) (blocks L A) /\ ~ In (r, k) (blocks L0 A0) /\ r <= x < r + k /\ present mem' x)) ->
  cj L A mem' md.
Proof.
  intros L A mem md mem' W J MU WM RA' CLS.
  pose proof J as (HM & HWF & HBD & HLY & HI & HLB & HLN & HUB & HMD & HHI & HIM & HB0 & HSC & HRA).
  pose proof PRE0 as (HM0 & _ & _ & _ & _ & HK & HK63 & _).
  pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_lt as Hac. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as Hacv.
  assert (OUT : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs0 - CNO_K <= x < spZ regs0) ->
            (forall r k, In (r, k) (blocks L A) -> ~ In (r, k) (blocks L0 A0) -> ~ (r <= x < r + k)) ->
            Frame.outside W x).
  { intros x Hx H1 H2. destruct (kb_outside_dec W x) as [Ho|Ho]; [exact Ho|].
    exfalso. destruct (CLS x Hx Ho) as [H|(r & k & Hr & Hr0 & Hrx & _)]; [exact (H1 H) | exact (H2 r k Hr Hr0 Hrx)]. }
  assert (OWN : forall a, owned B L A a -> 0 <= a < alloc_ceiling /\ Frame.outside W a).
  { intros a Ho. pose proof (mr_owned_low _ _ (aa_laws API) L A mem md a HM Ho) as Hl. split; [exact Hl|].
    apply OUT; [lia | lia |]. intros r k Hr _ Hrx.
    destruct (cno_block_facts L A mem md r k (a - r) HM Hr ltac:(lia)) as (_ & _ & _ & Hno & _).
    replace (r + (a - r)) with a in Hno by lia. exact (Hno Ho). }
  split.
  { destruct (mr_model _ _ (aa_laws API) L A mem md HM) as (Hh & Hl & Hm).
    eapply (mr_frame _ _ (aa_laws API) L A mem mem' md md HM).
    - intros a Ho. destruct (OWN a Ho) as [Hl0 Hout]. apply (mbyte_munch _ W); [exact MU | lia | exact Hout].
    - intros a Ho Hp. destruct (OWN a Ho) as [Hl0 Hout]. apply (present_munch W mem); [exact MU | lia | exact Hout | exact Hp].
    - intros p n i Hin Hi. destruct (mr_blocks _ _ (aa_laws API) L A mem md p n i HM Hin Hi) as (Hp & H1 & H2 & _).
      destruct (kb_outside_dec W (ptr_addr L p + i)) as [Ho|Ho].
      + apply (present_munch W mem); [exact MU | lia | exact Ho | exact Hp].
      + destruct (CLS (ptr_addr L p + i) ltac:(lia) Ho) as [Hst | (r & k & _ & _ & _ & Hpr)]; [lia | exact Hpr].
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hm. }
  split; [exact HWF|]. split; [exact HBD|]. split; [exact HLY|]. split; [exact HI|].
  split.
  { intros Hf i Hi. rewrite <- (HLB Hf i Hi).
    assert (Ho : owned B L A (ms_libc B + 8 + i)) by (right; unfold static_owned; right; right; left; lia).
    destruct (OWN _ Ho) as [Hl0 Hout]. apply (mbyte_munch _ W); [exact MU | lia | exact Hout]. }
  split; [exact HLN|]. split; [exact HUB|]. split; [exact HMD|].
  split.
  { intros a Ha Hsc Hst. destruct (HHI a Ha Hsc Hst) as [E1 E2].
    assert (Hout : Frame.outside W a).
    { apply OUT; [lia | intros H; apply Hsc; left; exact H |]. intros r k Hr _ Hrx.
      pose proof (cno_block_range L A mem md r k HM Hr). lia. }
    split; [rewrite (mbyte_munch _ W mem mem' a MU ltac:(lia) Hout); exact E1|].
    rewrite E2. apply (writable_munch _ W mem mem' a MU ltac:(lia) Hout). }
  split.
  { intros a Ha Hno Hsc Hst. destruct (HIM a Ha Hno Hsc Hst) as [E1 E2].
    pose proof (cno_img_low a Ha) as Hal.
    assert (Hout : Frame.outside W a).
    { apply OUT; [lia | lia |]. intros r k Hr _ Hrx.
      destruct (cno_block_facts L A mem md r k (a - r) HM Hr ltac:(lia)) as (_ & _ & _ & _ & Hni).
      replace (r + (a - r)) with a in Hni by lia. exact (Hni Ha). }
    split; [rewrite (mbyte_munch _ W mem mem' a MU ltac:(lia) Hout); exact E1|].
    rewrite E2. apply (writable_munch _ W mem mem' a MU ltac:(lia) Hout). }
  split.
  { intros p n i Hin Hi Hst. rewrite <- (HB0 p n i Hin Hi Hst).
    destruct (HUB p n Hin) as [HinA Hptr].
    pose proof (cno_ub_blocks L A p n HinA) as HinB. rewrite Hptr in HinB.
    destruct (cno_block_facts L A mem md _ n i HM HinB Hi) as (_ & H4 & Hc & _).
    assert (Hout : Frame.outside W (ptr_addr L0 p + i)).
    { apply OUT; [lia | lia |]. intros r k Hr Hr0 Hrx.
      assert (Hne : (ptr_addr L0 p, n) <> (r, k)).
      { intros E. apply Hr0. rewrite <- E. apply cno_ub_blocks. exact Hin. }
      destruct (cno_blocks_sep L A mem md _ _ HM HinB Hr Hne) as [D|D]; cbn [fst snd] in D; lia. }
    apply (mbyte_munch _ W); [exact MU | lia | exact Hout]. }
  split; [intros a Hs; apply WM; apply HSC; exact Hs|].
  exact RA'.
Qed.

Lemma cno_layout_trans : forall L A L', layout_le A0 L0 L -> layout_le A L L' ->
  (length (st_regions A0) <= length (st_regions A))%nat -> layout_le A0 L0 L'.
Proof.
  intros L A L' (E1 & E2 & E3 & E4) (F1 & F2 & F3 & F4) Hl.
  split; [congruence|]. split; [congruence|]. split; [congruence|].
  intros r Hr. rewrite F4 by lia. apply E4. exact Hr.
Qed.

Lemma cj_callpost : forall L A mem md Kc regs_c Ec L' A' regs' mem' md',
  cj L A mem md -> call_post_k B MR Kc L A regs_c mem md Ec L' A' regs' mem' md' ->
  spZ regs0 - CNO_K <= spZ regs_c - Kc -> spZ regs_c <= spZ regs0 ->
  (forall a, Ec a -> a < alloc_ceiling /\ ~ in_img B a) ->
  (forall p n, In (p, n) (user_blocks A0) -> In (p, n) (user_blocks A')) ->
  st_init_done A' = true ->
  (length (st_regions A) <= length (st_regions A'))%nat ->
  ro_agree segs mem' ->
  cj L' A' mem' md'.
Proof.
  intros L A mem md Kc regs_c Ec L' A' regs' mem' md' J CP Hk1 Hk2 HE HSURV HINIT HLEN RA'.
  pose proof J as (HM & HWF & HBD & HLY & HI & HLB & HLN & HUB & (vm & HMD) & HHI & HIM & HB0 & HSC & HRA).
  destruct CP as (HM' & HWF' & HBD' & HLY' & HPTR & _ & (vm' & HMD') & HFR & HBK & HSC').
  pose proof PRE0 as (HM0 & _ & _ & _ & _ & HK & HK63 & _). pose proof cno_k_le as HKv.
  pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_lt as Hac. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as Hacv.
  assert (NSC : forall a, ~ scratch_k B CNO_K regs0 a -> ~ scratch_k B Kc regs_c a).
  { intros a H1 H2. apply H1. unfold scratch_k in *. destruct H2 as [H2|H2]; [left; lia | right; exact H2]. }
  split; [exact HM'|]. split; [exact HWF'|]. split; [exact HBD'|].
  split; [exact (cno_layout_trans L A L' HLY HLY' HLN)|].
  split; [intros _; exact HINIT|].
  split; [intros H; congruence|].
  split; [lia|].
  split.
  { intros p n Hp. destruct (HUB p n Hp) as [HA Hptr]. split; [exact (HSURV p n Hp)|].
    rewrite (HPTR p n HA (HSURV p n Hp)). exact Hptr. }
  split; [exists vm'; rewrite HMD', HMD; apply cno_with_vmmaps_twice|].
  split.
  { intros a Ha Hsc Hst. destruct (HHI a Ha Hsc Hst) as [E1 E2].
    destruct (HFR a (or_introl Ha)) as [F1 F2].
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM Ho). lia.
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM' Ho). lia.
    - exact (NSC a Hsc).
    - intros He. destruct (HE a He). lia.
    - split; [rewrite F1; exact E1 | rewrite E2; exact F2]. }
  split.
  { intros a Ha Hno Hsc Hst. destruct (HIM a Ha Hno Hsc Hst) as [E1 E2].
    destruct (HFR a (or_intror Ha)) as [F1 F2].
    - exact (Hno L A mem md HM).
    - exact (Hno L' A' mem' md' HM').
    - exact (NSC a Hsc).
    - intros He. destruct (HE a He) as [_ Hn]. exact (Hn Ha).
    - split; [rewrite F1; exact E1 | rewrite E2; exact F2]. }
  split.
  { intros p n i Hp Hi Hst. destruct (HUB p n Hp) as [HA Hptr]. rewrite <- Hptr.
    rewrite (HBK p n i HA (HSURV p n Hp) Hi). rewrite Hptr. exact (HB0 p n i Hp Hi Hst). }
  split.
  { intros a Hs.
    assert (D : scratch_k B Kc regs_c a \/ ~ scratch_k B Kc regs_c a).
    { unfold scratch_k. destruct (Z_le_gt_dec (spZ regs_c - Kc) a); destruct (Z_lt_ge_dec a (spZ regs_c));
        destruct (Z_le_gt_dec (errno_addr B) a); destruct (Z_lt_ge_dec a (errno_addr B + 4));
        first [left; lia | right; lia]. }
    destruct D as [D|D]; [exact (HSC' a D)|].
    destruct Hs as [Hs|Hs]; [|exfalso; apply D; right; exact Hs].
    assert (Hhi : alloc_ceiling <= a < 2 ^ 64) by lia.
    destruct (HFR a (or_introl Hhi)) as [_ F2].
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM Ho). lia.
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM' Ho). lia.
    - exact D.
    - intros He. destruct (HE a He). lia.
    - apply F2. apply HSC. left. exact Hs. }
  exact RA'.
Qed.

Lemma cj_rpost : forall L A mem md Kc regs_c Ec gc L' A' regs' mem' md',
  cj L A mem md -> rpost B API Kc L A regs_c mem md Ec gc L' A' regs' mem' md' ->
  spZ regs0 - CNO_K <= spZ regs_c - Kc -> spZ regs_c <= spZ regs0 ->
  (forall a, Ec a -> alloc_statics a \/ (spZ regs0 - CNO_K <= a < spZ regs0 /\ writable_at segs mem' a) \/
     (a < alloc_ceiling /\ ~ in_img B a /\
      forall p n, In (p, n) (user_blocks A0) -> ~ (ptr_addr L0 p <= a < ptr_addr L0 p + n))) ->
  (forall p n, In (p, n) (user_blocks A0) -> ~ gc (ptr_addr L0 p) n) ->
  ro_agree segs mem' ->
  cj L' A' mem' md'.
Proof.
  intros L A mem md Kc regs_c Ec gc L' A' regs' mem' md' J RP Hk1 Hk2 HE HG0 RA'.
  pose proof J as (HM & HWF & HBD & HLY & HI & HLB & HLN & HUB & (vm & HMD) & HHI & HIM & HB0 & HSC & HRA).
  destruct RP as (HM' & HWF' & HBD' & HLY' & HI' & HLB' & HLN' & HSV & HPTR & _ & (vm' & HMD') & HFR & HFI & HBK & HSC').
  pose proof PRE0 as (HM0 & _ & _ & _ & _ & HK & HK63 & _). pose proof cno_k_le as HKv.
  pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_lt as Hac. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as Hacv.
  assert (NSC : forall a, ~ scratch_k B CNO_K regs0 a -> ~ scratch_k B Kc regs_c a).
  { intros a H1 H2. apply H1. unfold scratch_k in *. destruct H2 as [H2|H2]; [left; lia | right; exact H2]. }
  assert (SLOW : forall a, alloc_statics a -> a < alloc_ceiling /\ in_img B a).
  { intros a Ha. destruct (cno_statics_free a Ha) as (H1 & H2 & _). split; [lia | exact H1]. }
  split; [exact HM'|]. split; [exact HWF'|]. split; [exact HBD'|].
  split; [exact (cno_layout_trans L A L' HLY HLY' HLN)|].
  split; [intros H; exact (HI' (HI H))|].
  split.
  { intros Hf i Hi. assert (Hf0 : st_init_done A = false).
    { destruct (st_init_done A) eqn:E; [|reflexivity]. rewrite (HI' eq_refl) in Hf. discriminate. }
    rewrite (HLB' Hf i Hi). exact (HLB Hf0 i Hi). }
  split; [lia|].
  split.
  { intros p n Hp. destruct (HUB p n Hp) as [HA Hptr].
    assert (HA' : In (p, n) (user_blocks A')) by (apply (HSV p n HA); rewrite Hptr; exact (HG0 p n Hp)).
    split; [exact HA'|]. rewrite (HPTR p n HA HA'). exact Hptr. }
  split; [exists vm'; rewrite HMD', HMD; apply cno_with_vmmaps_twice|].
  split.
  { intros a Ha Hsc Hst. destruct (HHI a Ha Hsc Hst) as [E1 E2].
    assert (HnE : ~ Ec a).
    { intros He. destruct (HE a He) as [H|[(H & _)|(H & _)]]; [exact (Hst H) | apply Hsc; left; exact H | lia]. }
    destruct (HFR a Ha (NSC a Hsc) HnE) as [F1 F2].
    split; [rewrite F1; exact E1 | rewrite E2; exact F2]. }
  split.
  { intros a Ha Hno Hsc Hst. destruct (HIM a Ha Hno Hsc Hst) as [E1 E2].
    pose proof (cno_img_low a Ha) as Hal.
    assert (HnE : ~ Ec a).
    { intros He. destruct (HE a He) as [H|[(H & _)|(_ & H & _)]]; [exact (Hst H) | lia | exact (H Ha)]. }
    destruct (HFI a Ha Hno (NSC a Hsc) HnE) as [F1 F2].
    split; [rewrite F1; exact E1 | rewrite E2; exact F2]. }
  split.
  { intros p n i Hp Hi Hst. destruct (HUB p n Hp) as [HA Hptr].
    assert (HA' : In (p, n) (user_blocks A')) by (apply (HSV p n HA); rewrite Hptr; exact (HG0 p n Hp)).
    pose proof (cno_ub_blocks L0 A0 p n Hp) as HB0b.
    destruct (cno_block_range L0 A0 mem0 md0 _ n HM0 HB0b) as [Hb1 Hb2].
    assert (HnE : ~ Ec (ptr_addr L p + i)).
    { rewrite Hptr. intros He. destruct (HE _ He) as [H|[(H & _)|(_ & _ & H)]]; [exact (Hst H) | lia |].
      exact (H p n Hp ltac:(lia)). }
    rewrite <- Hptr. rewrite (HBK p n i HA HA' Hi HnE). rewrite Hptr. exact (HB0 p n i Hp Hi Hst). }
  split.
  { intros a Hs.
    assert (D : scratch_k B Kc regs_c a \/ ~ scratch_k B Kc regs_c a).
    { unfold scratch_k. destruct (Z_le_gt_dec (spZ regs_c - Kc) a); destruct (Z_lt_ge_dec a (spZ regs_c));
        destruct (Z_le_gt_dec (errno_addr B) a); destruct (Z_lt_ge_dec a (errno_addr B + 4));
        first [left; lia | right; lia]. }
    destruct D as [D|D]; [exact (HSC' a D)|].
    destruct Hs as [Hs|Hs]; [|exfalso; apply D; right; exact Hs].
    assert (Hhi : alloc_ceiling <= a < 2 ^ 64).
    { lia. }
    unfold writable_at. intros Hn.
    assert (HnE : ~ Ec a).
    { intros He. destruct (HE a He) as [H|[(_ & H)|(H & _)]]; [destruct (SLOW a H); lia | exact (H Hn) | lia]. }
    destruct (HFR a Hhi D HnE) as [_ F2]. exact (proj1 F2 (HSC a (or_introl Hs)) Hn). }
  exact RA'.
Qed.

Lemma cno_lblock0 : forall L A mem md a k, cj L A mem md -> lblock B L0 A0 mem0 a k -> lblock B L A mem a k.
Proof.
  intros L A mem md a k J (Hk & Hin & Hw & Hni). split; [exact Hk|]. split; [exact (cj_blocks0 L A mem md _ _ J Hin)|].
  split; [|exact Hni]. intros j Hj. rewrite <- (Hw j Hj).
  exact (cj_mem0 L A mem md (a - 16) (k + 16) (Z.of_nat j) J Hin ltac:(lia)).
Qed.

Lemma cno_ledger_cj : forall L A mem md Lam pk0 ct0 fl0 pk ct fl,
  ledger B L0 A0 mem0 Lam pk0 ct0 fl0 -> cj L A mem md ->
  alloc_words B mem (lsum Lam) pk ct fl -> lsum Lam <= pk < 2 ^ 64 -> 0 <= ct < 2 ^ 64 -> 0 <= fl < 2 ^ 64 ->
  ledger B L A mem Lam pk ct fl.
Proof.
  intros L A mem md Lam pk0 ct0 fl0 pk ct fl (_ & _ & _ & _ & ND & FA) J AW P C F.
  split; [exact AW|]. split; [exact P|]. split; [exact C|]. split; [exact F|]. split; [exact ND|].
  eapply Forall_impl; [|exact FA]. intros [a k] H. exact (cno_lblock0 L A mem md a k J H).
Qed.

End G.

Lemma cno_ledger_perm : forall {fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.RunCeil} B L A mem Lam Lam' pk ct fl,
  Permutation Lam Lam' -> ledger B L A mem Lam pk ct fl -> ledger B L A mem Lam' pk ct fl.
Proof.
  intros fx rc B L A mem Lam Lam' pk ct fl HP (AW & P & C & F & ND & FA).
  rewrite (cno_lsum_perm Lam Lam' HP) in AW, P.
  split; [exact AW|]. split; [exact P|]. split; [exact C|]. split; [exact F|].
  split; [apply NoDup_ListNoDup; apply (Permutation_NoDup (Permutation_map fst HP)); apply NoDup_ListNoDup; exact ND|].
  rewrite Forall_forall in FA |- *. intros x Hx. apply FA. apply (Permutation_in x (Permutation_sym HP)). exact Hx.
Qed.

Lemma cno_nodup_fst : forall {X Y : Type} (l : list (X * Y)) x y y', List.NoDup (map fst l) -> In (x, y) l -> In (x, y') l -> y = y'.
Proof.
  intros X Y l. induction l as [|[a b] l IH]; intros x y y' ND H1 H2; [destruct H1|].
  cbn [map fst] in ND. inversion ND as [|? ? Hn ND']; subst.
  destruct H1 as [E1|H1], H2 as [E2|H2].
  - inversion E1; inversion E2; subst. reflexivity.
  - inversion E1; subst. exfalso. apply Hn. apply in_map_iff. exists (x, y'). split; [reflexivity | exact H2].
  - inversion E2; subst. exfalso. apply Hn. apply in_map_iff. exists (x, y). split; [reflexivity | exact H1].
  - exact (IH x y y' ND' H1 H2).
Qed.
