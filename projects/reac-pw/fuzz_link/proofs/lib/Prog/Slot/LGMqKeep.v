(* The slot's mark step glue, plain image: the regions a call cut of mark_quietly (0x13dac, 0x13c70) hands
   to its return cut. lgmq_reg is the part of the loop-head memory mark_quietly does not write: the frame,
   g_nl from if_name on, g_names, long_alias and its 3 slack bytes, the odd and texts tables, the odd and
   policy strings, the md block, the payload, and the mk block when a0 = 0. lgmq_keep puts it inside the
   step's carry (lkeep minus mq_writes); the rest carries each view the return cuts read. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss MState.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import LLVMFuzzerTestOneInput_c link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import memfile_c reac_served_mark_c mark_quietly_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require StdioModel.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LEDefs LFr LFrEn LFrLo
  LFrMqDefs LGlue.
Import ListNotations.
Local Open Scope Z_scope.

Definition lgmq_reg (E : lenv) (a0 : Z) (x : Z) : Prop :=
  lo_rng (e_S E - SLOT_FRAME) SLOT_FRAME x \/
  lo_rng (A_G_NL + NK_IF_NAME) (NK_SIZE - NK_IF_NAME) x \/
  lo_rng A_G_NAMES G_NAMES_SIZE x \/
  lo_rng A_LONG_ALIAS (LONG_ALIAS_SIZE + 3) x \/
  lo_rng A_ODD 48 x \/
  lo_rng A_TEXTS 88 x \/
  lo_odd_str x \/
  lo_pol_reg x \/
  lo_rng (e_md E) MD_SIZE x \/
  lo_rng (e_p0 E) (Z.of_nat (length (e_pl E))) x \/
  (a0 = 0 /\ lo_rng (e_mk E) MK_SIZE x).

(* ---- arithmetic: where the regions of lgmq_reg lie against what mark_quietly writes ---- *)

Lemma lgmq_kp_md_pos : 1 <= MD_SIZE.
Proof. unfold MD_SIZE. lia. Qed.

Lemma lgmq_kp_mk_pos : 1 <= MK_SIZE.
Proof. unfold MK_SIZE. lia. Qed.

Lemma lgmq_kp_md_ne : MD_SIZE <> MF_BLOCK.
Proof. unfold MD_SIZE, MF_BLOCK. lia. Qed.

Lemma lgmq_kp_mk_ne : MK_SIZE <> MF_BLOCK.
Proof. unfold MK_SIZE, MF_BLOCK. lia. Qed.

(* a range wholly below or above the image, apart from the marks block and from the FILE *)
Lemma lgmq_kp_blk_nw : forall a0 s p n x, (p + n <= 0x10000 \/ 0x97000 <= p) ->
  (a0 <> 0 -> a0 + MK_SIZE <= p \/ p + n <= a0) -> (s + MF_BLOCK <= p \/ p + n <= s) ->
  p <= x < p + n -> ~ mq_writes a0 s x.
Proof.
  intros a0 s p n x Hi Hm Hf Hx Hw.
  destruct Hw as [H|[H|[H|[H|[H|[[Ha H]|H]]]]]].
  - unfold A_G_NL, NK_N_SENT in H. lia.
  - unfold A_G_SINK in H. lia.
  - unfold A_G_SAY in H. lia.
  - unfold A_G_SAID, SAID_SIZE in H. lia.
  - unfold StdioModel.A_OFL_HEAD in H. lia.
  - specialize (Hm Ha). lia.
  - unfold FILE_BLOCK in H. unfold MF_BLOCK in Hf. lia.
Qed.

(* the image bytes of lgmq_reg: .rodata strings, the two .data.rel.ro tables, g_nl from if_name on up to
   long_alias + 3 *)
Lemma lgmq_kp_img_nw : forall a0 s x, (a0 <> 0 -> a0 + MK_SIZE <= 0x10000 \/ 0x97000 <= a0) ->
  mf_place_ok s ->
  (0x102a2 <= x < 0x105a1 \/ 0x207c0 <= x < 0x20848 \/ A_G_NL + NK_IF_NAME <= x < 0x74528) ->
  ~ mq_writes a0 s x.
Proof.
  intros a0 s x Hm Hp Hx Hw. unfold mf_place_ok, IMG_LO, IMG_TOP in Hp. unfold A_G_NL, NK_IF_NAME in Hx.
  destruct Hw as [H|[H|[H|[H|[H|[[Ha H]|H]]]]]].
  - unfold A_G_NL, NK_N_SENT in H. lia.
  - unfold A_G_SINK in H. lia.
  - unfold A_G_SAY in H. lia.
  - unfold A_G_SAID, SAID_SIZE in H. lia.
  - unfold StdioModel.A_OFL_HEAD in H. lia.
  - specialize (Hm Ha). lia.
  - unfold FILE_BLOCK in H. unfold MF_BLOCK in Hp. lia.
Qed.

(* the frame: above the image, above the marks block and the FILE (both below the stack window) *)
Lemma lgmq_kp_frame_nw : forall S mk a0 s x, 0x960e0 + SLOT_STACK_Z <= S ->
  (a0 <> 0 -> a0 = mk) -> mk + MK_SIZE <= S - SLOT_STACK_Z -> s + MF_BLOCK <= S - SLOT_STACK_Z ->
  lo_rng (S - SLOT_FRAME) SLOT_FRAME x -> ~ mq_writes a0 s x.
Proof.
  intros S mk a0 s x HS Hm Hk Hs Hx. apply (lgmq_kp_blk_nw a0 s (S - SLOT_FRAME) SLOT_FRAME x).
  - right. unfold SLOT_STACK_Z, SLOT_FRAME in *. lia.
  - intros Ha. rewrite (Hm Ha). left. unfold SLOT_STACK_Z, SLOT_FRAME in *. lia.
  - left. unfold SLOT_STACK_Z, SLOT_FRAME in *. lia.
  - exact Hx.
Qed.

(* lgmq_reg by kind: image, frame, md, payload, mk (a0 = 0) *)
Lemma lgmq_kp_cases : forall E a0 x, lgmq_reg E a0 x ->
  (0x102a2 <= x < 0x105a1 \/ 0x207c0 <= x < 0x20848 \/ A_G_NL + NK_IF_NAME <= x < 0x74528) \/
  lo_rng (e_S E - SLOT_FRAME) SLOT_FRAME x \/ lo_rng (e_md E) MD_SIZE x \/
  lo_rng (e_p0 E) (Z.of_nat (length (e_pl E))) x \/ (a0 = 0 /\ lo_rng (e_mk E) MK_SIZE x).
Proof.
  intros E a0 x Hx.
  destruct Hx as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]].
  - right; left. exact H.
  - left. unfold lo_rng, A_G_NL, NK_IF_NAME, NK_SIZE in *. lia.
  - left. unfold lo_rng, A_G_NAMES, G_NAMES_SIZE, A_G_NL, NK_IF_NAME in *. lia.
  - left. unfold lo_rng, A_LONG_ALIAS, LONG_ALIAS_SIZE, A_G_NL, NK_IF_NAME in *. lia.
  - left. unfold lo_rng, A_ODD in *. lia.
  - left. unfold lo_rng, A_TEXTS in *. lia.
  - left. unfold lo_odd_str, lo_rng in *. lia.
  - left. unfold lo_pol_reg, lo_rng, A_PREFIX, A_SERVED, A_VLAN, A_EMPTY in *. lia.
  - right; right; left. exact H.
  - right; right; right; left. exact H.
  - right; right; right; right. exact H.
Qed.

(* lgmq_reg lies in LFrLo's lh_reg *)
Lemma lgmq_kp_lh : forall E a0 x, lgmq_reg E a0 x -> lh_reg E x.
Proof.
  intros E a0 x Hx.
  destruct Hx as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[_ H]]]]]]]]]]].
  - apply lh_reg_frame. exact H.
  - apply lh_reg_gnl. unfold lo_rng, NK_IF_NAME, NK_SIZE in *. lia.
  - apply lh_reg_gnames. exact H.
  - apply lh_reg_la. exact H.
  - apply lh_reg_oddtab. exact H.
  - apply lh_reg_texts. exact H.
  - apply lh_reg_oddstr. exact H.
  - apply lh_reg_pol. exact H.
  - apply lh_reg_md. exact H.
  - apply lh_reg_pl. exact H.
  - apply lh_reg_mk. exact H.
Qed.

(* ==========================================================================
   1. lgmq_reg lies in the step's carry
   ========================================================================== *)

Section KP.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FF : LFF B API.

Lemma lgmq_keep : forall g md mk hb T sink sink' a0 x,
  lenv_ok (lg_E g md mk) -> hb_inv g (lg_E g md mk) hb T ->
  In (e_p0 (lg_E g md mk), Z.of_nat (length (e_pl (lg_E g md mk)))) (blocks (lg_L g) (lg_A g)) ->
  ~ In (e_p0 (lg_E g md mk), Z.of_nat (length (e_pl (lg_E g md mk)))) (lg_T g) ->
  lmq_sink B g hb T sink -> (a0 = 0 \/ a0 = mk) ->
  (sink <> 0 -> sink' = sink) -> (sink = 0 -> lfresh B g hb sink' MF_BLOCK) -> mf_place_ok sink' ->
  lgmq_reg (lg_E g md mk) a0 x -> lkeep B g hb x /\ ~ mq_writes a0 sink' x.
Proof using FF.
  intros g md mk hb T sink sink' a0 x HE HI Hp0 Hp0T HS Ha0 HS1 HS0 Hpl Hx.
  set (E := lg_E g md mk) in *.
  assert (ES : e_S E = lg_S g) by reflexivity.
  assert (Ha0' : a0 = 0 \/ a0 = e_mk E) by exact Ha0.
  clear Ha0.
  assert (Hmd : In (e_md E, MD_SIZE) hb).
  { apply (Permutation_in _ (Permutation_sym HI)). left. reflexivity. }
  assert (Hmk : In (e_mk E, MK_SIZE) hb).
  { apply (Permutation_in _ (Permutation_sym HI)). right. left. reflexivity. }
  split.
  { apply (lh_reg_keep_ok B API SH SK g hb E x FF HE ES Hmd Hmk).
    - intros y Hy. exists (e_p0 E), (Z.of_nat (length (e_pl E))). split; [exact Hp0 | exact Hy].
    - exact (lgmq_kp_lh E a0 x Hx). }
  (* the FILE sink': below the stack window, apart from md, mk and the payload *)
  assert (FS : sink' + MF_BLOCK <= lg_S g - SLOT_STACK_Z /\
    (forall a k, In (a, k) hb -> k <> MF_BLOCK -> sink' + MF_BLOCK <= a \/ a + k <= sink') /\
    (sink' + MF_BLOCK <= e_p0 E \/ e_p0 E + Z.of_nat (length (e_pl E)) <= sink')).
  { destruct (Z.eq_dec sink 0) as [Z0|Z0].
    - destruct (HS0 Z0) as (_ & _ & F1 & _ & F2 & F3).
      split; [exact F1|]. split.
      + intros a k Hin _. exact (F2 a k Hin).
      + exact (F3 _ _ Hp0).
    - pose proof (HS1 Z0) as ->.
      destruct HS as [(_ & H0) | (_ & _ & F1 & _ & _ & F2 & F3 & F4)]; [contradiction|].
      split; [exact F1|]. split.
      + intros a k Hin Hk. apply (F2 a k Hin). intros Heq. injection Heq as _ Hk'. exact (Hk Hk').
      + apply (F3 _ _ Hp0). intros Heq. apply Hp0T.
        assert (Hb : In (sink, MF_BLOCK) (blocks (lg_L g) (lg_A g))) by (rewrite <- Heq; exact Hp0).
        rewrite Heq, (F4 Hb). left. reflexivity. }
  destruct FS as (F1 & F2 & F3).
  assert (F1' : sink' + MF_BLOCK <= e_S E - SLOT_STACK_Z) by (rewrite ES; exact F1).
  pose proof (F2 _ _ Hmd lgmq_kp_md_ne) as Fmd.
  pose proof (F2 _ _ Hmk lgmq_kp_mk_ne) as Fmk.
  clear F2 F1.
  destruct HE as (HS0' & _ & _ & (_ & Bmd2 & Bmd3) & (_ & Bmk2 & Bmk3) & _ & _ & Dmm & (Hl1 & _) &
    (_ & _ & Bp3) & _ & Dpk & _).
  pose proof (le_img_free _ _ Bmd3 lgmq_kp_md_pos) as Imd.
  pose proof (le_img_free _ _ Bmk3 lgmq_kp_mk_pos) as Imk.
  pose proof (le_img_free _ _ Bp3 Hl1) as Ip.
  assert (Ma0 : a0 <> 0 -> a0 = e_mk E).
  { intros Ha. destruct Ha0' as [H0|H0]; [contradiction | exact H0]. }
  assert (Mk : a0 <> 0 -> a0 + MK_SIZE <= 0x10000 \/ 0x97000 <= a0).
  { intros Ha. rewrite (Ma0 Ha). exact Imk. }
  destruct (lgmq_kp_cases E a0 x Hx) as [H|[H|[H|[H|[Hz H]]]]].
  - exact (lgmq_kp_img_nw a0 sink' x Mk Hpl H).
  - exact (lgmq_kp_frame_nw (e_S E) (e_mk E) a0 sink' x HS0' Ma0 Bmk2 F1' H).
  - apply (lgmq_kp_blk_nw a0 sink' (e_md E) MD_SIZE x Imd); [|exact Fmd|exact H].
    intros Ha. rewrite (Ma0 Ha). destruct Dmm as [D|D]; [right|left]; exact D.
  - apply (lgmq_kp_blk_nw a0 sink' (e_p0 E) (Z.of_nat (length (e_pl E))) x Ip); [|exact F3|exact H].
    intros Ha. rewrite (Ma0 Ha). destruct Dpk as [D|D]; [right|left]; exact D.
  - apply (lgmq_kp_blk_nw a0 sink' (e_mk E) MK_SIZE x Imk); [|exact Fmk|exact H].
    intros Ha. exfalso. exact (Ha Hz).
Qed.

End KP.

(* ==========================================================================
   2. The views the return cuts read, across lcarry (lgmq_reg E a0)
   ========================================================================== *)

Lemma lgmq_views : forall E a0 m m', lcarry (lgmq_reg E a0) m m' ->
  gnames_at m -> odd_at m -> policy_ro m -> la_ok m -> texts_at m -> ifptrs_at m ->
  gnames_at m' /\ odd_at m' /\ policy_ro m' /\ la_ok m' /\ texts_at m' /\ ifptrs_at m'.
Proof.
  intros E a0 m m' C Gn Od Po La Tx Ip.
  split; [|split; [|split; [|split; [|split]]]].
  - apply (ml_use _ _ _ m m' ml_gnames_at C); [|exact Gn]. intros x Hx. do 2 right; left. exact Hx.
  - apply (ml_use _ _ _ m m' ml_odd_at C); [|exact Od].
    intros x [Hx|Hx]; [do 4 right; left | do 6 right; left]; exact Hx.
  - apply (ml_use _ _ _ m m' ml_policy_ro C); [|exact Po]. intros x Hx. do 7 right; left. exact Hx.
  - apply (ml_use _ _ _ m m' ml_la_ok C); [|exact La]. intros x Hx. do 3 right; left. exact Hx.
  - apply (ml_use _ _ _ m m' ml_texts_at C); [|exact Tx]. intros x Hx. do 5 right; left. exact Hx.
  - apply (ml_use _ _ _ m m' ml_ifptrs_at C); [|exact Ip]. intros x Hx. right; left.
    unfold lo_rng, NK_SIZE, NK_IF_NAME in *. lia.
Qed.

Lemma lgmq_frame_cells : forall E a0 m m' a cs,
  e_S E - SLOT_FRAME <= a -> a + Z.of_nat (cells_size cs) <= e_S E -> lcarry (lgmq_reg E a0) m m' ->
  rw_cells rsegs m a cs -> rw_cells rsegs m' a cs.
Proof.
  intros E a0 m m' a cs H1 H2 C H.
  apply (ml_use _ _ _ m m' (ml_rw_cells a cs) C); [|exact H].
  intros x Hx. left. unfold lo_rng in *. lia.
Qed.

Lemma lgmq_frame_bytes : forall E a0 m m' a bs,
  e_S E - SLOT_FRAME <= a -> a + Z.of_nat (length bs) <= e_S E -> lcarry (lgmq_reg E a0) m m' ->
  bytes_at rsegs m a bs -> bytes_at rsegs m' a bs.
Proof.
  intros E a0 m m' a bs H1 H2 C H.
  apply (ml_use _ _ _ m m' (ml_bytes_at a bs) C); [|exact H].
  intros x Hx. left. unfold lo_rng in *. lia.
Qed.

Lemma lgmq_model : forall E a0 m m' mbs, lcarry (lgmq_reg E a0) m m' ->
  model_at m (e_md E) mbs -> model_at m' (e_md E) mbs.
Proof.
  intros E a0 m m' mbs C H.
  apply (ml_use _ _ _ m m' (ml_model_at (e_md E) mbs) C); [|exact H].
  intros x Hx. do 8 right; left. exact Hx.
Qed.

Lemma lgmq_payload : forall E a0 m m', lcarry (lgmq_reg E a0) m m' ->
  bytes_at rsegs m (e_p0 E) (e_pl E) -> bytes_at rsegs m' (e_p0 E) (e_pl E).
Proof.
  intros E a0 m m' C H.
  apply (ml_use _ _ _ m m' (ml_bytes_at (e_p0 E) (e_pl E)) C); [|exact H].
  intros x Hx. do 9 right; left. exact Hx.
Qed.

Lemma lgmq_cursor : forall E a0 m m' P N, lcarry (lgmq_reg E a0) m m' ->
  cursor_ok m (e_p0 E) (e_pl E) P N -> cursor_ok m' (e_p0 E) (e_pl E) P N.
Proof.
  intros E a0 m m' P N C H.
  apply (ml_use _ _ _ m m' (ml_cursor_ok (e_p0 E) (e_pl E) P N) C); [|exact H].
  intros x Hx. do 9 right; left. exact Hx.
Qed.

Lemma lgmq_marks0 : forall E m m' gbs, lcarry (lgmq_reg E 0) m m' ->
  marks_at m (e_mk E) gbs -> marks_at m' (e_mk E) gbs.
Proof.
  intros E m m' gbs C H.
  apply (ml_use _ _ _ m m' (ml_marks_at (e_mk E) gbs) C); [|exact H].
  intros x Hx. do 10 right. split; [reflexivity | exact Hx].
Qed.

Lemma lgmq_iftab : forall E a0 m m' kbs, lcarry (lgmq_reg E a0) m m' ->
  iftab_at m kbs link_tab -> ifptrs_at m -> iftab_at m' kbs link_tab.
Proof.
  intros E a0 m m' kbs C H Hp.
  assert (R : iftab_at m' kbs link_tab /\ ifptrs_at m').
  { apply (ml_use _ _ _ m m' (ml_iftab kbs) C); [|exact (conj H Hp)].
    intros x [Hx|[Hx|[Hx|Hx]]].
    - right; left. unfold lo_rng, NK_SIZE, NK_IF_NAME in *. lia.
    - right; left. unfold lo_rng, NK_SIZE, NK_IF_NAME, NK_IF_INDEX in *. lia.
    - do 2 right; left. exact Hx.
    - do 6 right; left. exact Hx. }
  exact (proj1 R).
Qed.

(* the machine facts and errno / guard at the return come from the step's lpost_mem *)
Lemma lgmq_mach : forall g md mk m', lpost_mem g m' ->
  mem_inv rsegs m' /\ MemNorm.task_mem rsegs m' /\
  stk rsegs m' (e_S (lg_E g md mk) - SLOT_STACK_Z) (e_S (lg_E g md mk) - SLOT_FRAME) /\
  wr_at rsegs m' A_ERRNO 4 /\ guard_m m'.
Proof.
  intros g md mk m' (H1 & H2 & H3 & H4 & H5).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4 | exact H5].
Qed.

Print Assumptions lgmq_keep.
Print Assumptions lgmq_views.
Print Assumptions lgmq_frame_cells.
Print Assumptions lgmq_frame_bytes.
Print Assumptions lgmq_model.
Print Assumptions lgmq_payload.
Print Assumptions lgmq_cursor.
Print Assumptions lgmq_marks0.
Print Assumptions lgmq_iftab.
Print Assumptions lgmq_mach.
