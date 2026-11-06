(* ARM 1 (op_write) at the SR level, part 1: what the arm's two allocator-facing calls (text_of at
   0x13fb4, free at 0x1405c) ask of the SR frame, and the facts that carry the arm's cut predicates
   across them (LC1Defs.c1_13fb8 at 0x13fb8, LC1Defs.c1_14060 at 0x14060).

   The arm's cut predicates read the frame cells [S - 480, S), the saved bytes, g_nl, g_names,
   long_alias, the two pointer tables, the policy strings, the model block, the marks block and the
   payload (LFrLo.lh_reg). An allocator call keeps every one of them (LFr.lkeep) except the two frame
   cells the callee itself writes: the cursor (S - 480 + 64, 16 bytes) and the `own` cell
   (S - 480 + 120, 8 bytes). `lg1_wins` names those two windows and `lg1_keep_reg` the rest, which is
   what `lg1_lh_mem_carry` moves from the call state to the return state. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Spec Require StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import LLVMFuzzerTestOneInput_c link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import
  LDefs LC1Defs LC1Call LC1ALib LFr LFrLo LFrEn LGlue.
Import ListNotations.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Bytes and cells
   ========================================================================== *)

Lemma lg1_app_split : forall (l1 l2 r1 r2 : list byte), length l1 = length r1 ->
  l1 ++ l2 = r1 ++ r2 -> l1 = r1 /\ l2 = r2.
Proof.
  intros l1 l2 r1 r2 HL H.
  assert (A : firstn (length l1) (l1 ++ l2) = firstn (length l1) (r1 ++ r2)) by (rewrite H; reflexivity).
  assert (Bk : skipn (length l1) (l1 ++ l2) = skipn (length l1) (r1 ++ r2)) by (rewrite H; reflexivity).
  rewrite firstn_app_exact in A. rewrite HL in A. rewrite firstn_app_exact in A.
  rewrite skipn_app_exact in Bk. rewrite HL in Bk. rewrite skipn_app_exact in Bk.
  split; [exact A | exact Bk].
Qed.

Lemma lg1_le8_of : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (bytes_le_to_Z_nonneg bs) as H0.
  pose proof (bytes_le_to_Z_bound bs) as H1. rewrite HL in H1.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in H1.
  rewrite unsigned_lit by lia. rewrite <- HL. apply StrFun.Z_to_le_bytes_to_Z.
Qed.

(* eight writable bytes read as one word *)
Lemma lg1_cb8_c8 : forall m a bs, rw_cells rsegs m a [CB 8 bs] -> exists w, rw_cells rsegs m a [C8 w].
Proof.
  intros m a bs [[Hwf Hb] Hw]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [HL _].
  exists (le_bytes_to_word bs). split; [split|].
  - cbn [cells_wf cell_wf]. tauto.
  - cbn [cells_bytes cbytes] in Hb |- *. rewrite (lg1_le8_of bs HL). exact Hb.
  - cbn [cells_size csize] in Hw |- *. exact Hw.
Qed.

Lemma lg1_c8_bytes : forall m a w, rw_cells rsegs m a [C8 w] -> bytes_at rsegs m a (le8 w).
Proof.
  intros m a w [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
Qed.

Lemma lg1_c8c8_det : forall m a x y x' y',
  rw_cells rsegs m a [C8 x; C8 y] -> rw_cells rsegs m a [C8 x'; C8 y'] -> x = x' /\ y = y'.
Proof.
  intros m a x y x' y' [[_ H1] _] [[_ H2] _]. cbn [cells_bytes cbytes] in H1, H2.
  assert (E : le8 x ++ le8 y ++ [] = le8 x' ++ le8 y' ++ []).
  { eapply c1a_ba_det; [exact H1 | exact H2|].
    rewrite !length_app, !length_le8. reflexivity. }
  destruct (lg1_app_split _ _ _ _ ltac:(rewrite !length_le8; reflexivity) E) as [E1 E2].
  rewrite !app_nil_r in E2.
  split; [exact (c1a_le8_inj _ _ E1) | exact (c1a_le8_inj _ _ E2)].
Qed.

Lemma lg1_hb_bytes_perm : forall h h', Permutation h h' -> hb_bytes h = hb_bytes h'.
Proof.
  intros h h' HP.
  induction HP as [|x l l' _ IH|x y l|l l' l'' _ IH1 _ IH2]; rewrite ?hb_bytes_cons.
  - reflexivity.
  - rewrite IH. reflexivity.
  - ring.
  - rewrite IH1, IH2. reflexivity.
Qed.

(* ==========================================================================
   2. The two frame windows a text_of / free call may write
   ========================================================================== *)

Definition lg1_wins (E : lenv) (x : Z) : Prop :=
  (e_S E - SLOT_FRAME + FO_P <= x < e_S E - SLOT_FRAME + FO_P + 16) \/
  (e_S E - SLOT_FRAME + FO_B256 <= x < e_S E - SLOT_FRAME + FO_B256 + 8).

Definition lg1_keep_reg (E : lenv) (x : Z) : Prop := lh_reg E x /\ ~ lg1_wins E x.

Lemma lg1_nowin_lo : forall E x, x < e_S E - SLOT_STACK_Z -> ~ lg1_wins E x.
Proof. intros E x Hx [H|H]; unfold FO_P, FO_B256, SLOT_FRAME, SLOT_STACK_Z in *; lia. Qed.

Lemma lg1_nowin_hi : forall E x, e_S E - 104 <= x -> ~ lg1_wins E x.
Proof. intros E x Hx [H|H]; unfold FO_P, FO_B256, SLOT_FRAME in *; lia. Qed.

Lemma lg1_nowin_img : forall E x, lenv_ok E -> x < 0x960e0 -> ~ lg1_wins E x.
Proof.
  intros E x HE Hx. apply lg1_nowin_lo. destruct HE as (H1 & _). unfold SLOT_STACK_Z in *. lia.
Qed.

(* ==========================================================================
   3. The loop-head memory across an allocator call that rewrites the two windows
   ========================================================================== *)

Lemma lg1_lh_mem_carry : forall (E : lenv) (i P N P' N' own : Z) (kbs mbs gbs : list byte)
    (m m' : word -> option byte),
  lenv_ok E -> lh_mem E i P N kbs mbs gbs m ->
  lcarry (lg1_keep_reg E) m m' ->
  wr_at rsegs m' A_ERRNO 4 -> guard_m m' ->
  rw_cells rsegs m' (e_S E - SLOT_FRAME + FO_P) [C8 (wz P'); C8 (wz N')] ->
  rw_cells rsegs m' (e_S E - SLOT_FRAME + FO_B256) [C8 (wz own)] ->
  (exists k, 0 <= k <= Z.of_nat (length (e_pl E)) /\ P' = e_p0 E + k /\ N' = Z.of_nat (length (e_pl E)) - k) ->
  lh_mem E i P' N' kbs mbs gbs m'.
Proof.
  intros E i P N P' N' own kbs mbs gbs m m' HE HL C HER HGU HCUR HOWN HK.
  pose proof HE as (HS1 & HS2 & HS3 & (Hmd1 & Hmd2 & _) & (Hmk1 & Hmk2 & _) & _ & _ & _ & Hpl &
                    (Hp1 & Hp2 & _) & _ & _ & Hsav).
  assert (HSZ : Z.of_nat (length (e_saved E)) = 104) by (rewrite Hsav; reflexivity).
  destruct HL as ((j0 & j1 & j2 & nc & HF) & HSV & HNK & HNW & HIF & H6 & H7 & H8 & H9 & HGN & HOD & HPO &
                  HLA & HTX & HIP & HMD & HMW & HMK & HKW & HKA & (HPL & _) & _ & _).
  (* the frame: the head cells, the 40-byte block and the tail of the 256-byte block are carried;
     the cursor cells and the own cell come from the call's post *)
  assert (FR' : exists j0' j1' j2' nc',
            rw_cells rsegs m' (e_S E - SLOT_FRAME) (lh_cells (e_md E) (e_mk E) P' nc' j0' j1' j2')).
  { unfold lh_cells in HF. apply c1a_frame_split in HF. destruct HF as (F1 & _ & F3).
    change [CB 40 j1; CB 256 j2] with ([CB 40 j1] ++ [CB 256 j2]) in F3.
    apply c1a_rwc_split in F3. destruct F3 as [F3a F3b].
    change (Z.of_nat (cells_size [CB 40 j1])) with 40 in F3b.
    replace (e_S E - SLOT_FRAME + 80 + 40) with (e_S E - SLOT_FRAME + FO_B256) in F3b
      by (unfold FO_B256; lia).
    pose proof (rw_cells_split_CB rsegs m (e_S E - SLOT_FRAME + FO_B256) [] 256 j2 [] [8%nat; 248%nat]
                  F3b eq_refl) as F3s.
    cbn [app mk_CB_cells] in F3s.
    change [CB 8 (firstn 8 j2); CB 248 (firstn 248 (skipn 8 j2))]
      with ([CB 8 (firstn 8 j2)] ++ [CB 248 (firstn 248 (skipn 8 j2))]) in F3s.
    apply c1a_rwc_split in F3s. destruct F3s as [_ F3t].
    change (Z.of_nat (cells_size [CB 8 (firstn 8 j2)])) with 8 in F3t.
    assert (F1' : rw_cells rsegs m' (e_S E - SLOT_FRAME) (c1a_cs1 j0 (wz A_ODD) (wz (e_md E + MD_MARK))
                    (wz A_EMPTY) (wz (e_mk E)) (wz A_G_NAMES) (wz A_JT) (wz GNL42))).
    { apply (ml_use _ _ _ m m' (ml_rw_cells _ _) C); [|exact F1].
      intros x Hx. change (Z.of_nat (cells_size (c1a_cs1 _ _ _ _ _ _ _ _))) with 64 in Hx.
      split; [apply lh_reg_frame; unfold lo_rng, SLOT_FRAME in *; lia|].
      intros [HW|HW]; unfold lo_rng, FO_P, FO_B256, SLOT_FRAME in *; lia. }
    assert (F3a' : rw_cells rsegs m' (e_S E - SLOT_FRAME + 80) [CB 40 j1]).
    { apply (ml_use _ _ _ m m' (ml_rw_cells _ _) C); [|exact F3a].
      intros x Hx. change (Z.of_nat (cells_size [CB 40 j1])) with 40 in Hx.
      split; [apply lh_reg_frame; unfold lo_rng, SLOT_FRAME in *; lia|].
      intros [HW|HW]; unfold lo_rng, FO_P, FO_B256, SLOT_FRAME in *; lia. }
    assert (F3t' : rw_cells rsegs m' (e_S E - SLOT_FRAME + FO_B256 + 8)
                     [CB 248 (firstn 248 (skipn 8 j2))]).
    { apply (ml_use _ _ _ m m' (ml_rw_cells _ _) C); [|exact F3t].
      intros x Hx. change (Z.of_nat (cells_size [CB 248 (firstn 248 (skipn 8 j2))])) with 248 in Hx.
      split; [apply lh_reg_frame; unfold lo_rng, FO_B256, SLOT_FRAME in *; lia|].
      intros [HW|HW]; unfold lo_rng, FO_P, FO_B256, SLOT_FRAME in *; lia. }
    assert (FB : rw_cells rsegs m' (e_S E - SLOT_FRAME + FO_B256)
                   ([C8 (wz own)] ++ [CB 248 (firstn 248 (skipn 8 j2))])).
    { apply (c1a_rwc_join m' (e_S E - SLOT_FRAME + FO_B256) [C8 (wz own)]
               [CB 248 (firstn 248 (skipn 8 j2))] (e_S E - SLOT_FRAME + FO_B256 + 8) HOWN);
        [cbn [cells_size csize Nat.add]; lia | exact F3t']. }
    pose proof (rw_cells_merge rsegs m' (e_S E - SLOT_FRAME + FO_B256) []
                  [C8 (wz own); CB 248 (firstn 248 (skipn 8 j2))] [] FB) as FM.
    cbn [app cells_size csize Nat.add] in FM.
    exists j0, j1, (cells_bytes [C8 (wz own); CB 248 (firstn 248 (skipn 8 j2))]), N'.
    unfold lh_cells. apply c1a_frame_join; [exact F1' | exact HCUR |].
    change [CB 40 j1; CB 256 (cells_bytes [C8 (wz own); CB 248 (firstn 248 (skipn 8 j2))])]
      with ([CB 40 j1] ++ [CB 256 (cells_bytes [C8 (wz own); CB 248 (firstn 248 (skipn 8 j2))])]).
    apply (c1a_rwc_join m' (e_S E - SLOT_FRAME + 80) [CB 40 j1]
             [CB 256 (cells_bytes [C8 (wz own); CB 248 (firstn 248 (skipn 8 j2))])]
             (e_S E - SLOT_FRAME + FO_B256) F3a');
      [cbn [cells_size csize Nat.add]; unfold FO_B256; lia | exact FM]. }
  assert (SV : bytes_at rsegs m' (e_S E - 104) (e_saved E)).
  { apply (ml_use _ _ _ m m' (ml_bytes_at _ _) C); [|exact HSV].
    intros x Hx. split; [apply lh_reg_saved; exact Hx|].
    apply lg1_nowin_hi. unfold lo_rng in Hx. lia. }
  assert (NK : nlk_at m' kbs).
  { apply (ml_use _ _ _ m m' (ml_nlk_at kbs) C); [|exact HNK].
    intros x Hx. split; [apply lh_reg_gnl; exact Hx|].
    apply lg1_nowin_img; [exact HE|]. unfold lo_rng, A_G_NL, NK_SIZE in Hx. lia. }
  assert (ITIP : iftab_at m' kbs link_tab /\ ifptrs_at m').
  { apply (ml_use _ _ _ m m' (ml_iftab kbs) C); [|exact (conj HIF HIP)].
    intros x Hx. split; [exact (lo_iftab_lh E x Hx)|].
    apply lg1_nowin_img; [exact HE|].
    unfold lo_iftab_reg, lo_odd_str, lo_rng, A_G_NL, NK_IF_NAME, NK_IF_INDEX, A_G_NAMES,
      G_NAMES_SIZE in Hx. lia. }
  destruct ITIP as [IT IP].
  assert (GN : gnames_at m').
  { apply (ml_use _ _ _ m m' ml_gnames_at C); [|exact HGN].
    intros x Hx. split; [apply lh_reg_gnames; exact Hx|].
    apply lg1_nowin_img; [exact HE|]. unfold lo_rng, A_G_NAMES, G_NAMES_SIZE in Hx. lia. }
  assert (OD : odd_at m').
  { apply (ml_use _ _ _ m m' ml_odd_at C); [|exact HOD].
    intros x Hx. split.
    - destruct Hx as [Hx|Hx]; [apply lh_reg_oddtab; exact Hx | apply lh_reg_oddstr; exact Hx].
    - apply lg1_nowin_img; [exact HE|].
      unfold lo_odd_reg, lo_odd_str, lo_rng, A_ODD in Hx. lia. }
  assert (PO : policy_ro m').
  { apply (ml_use _ _ _ m m' ml_policy_ro C); [|exact HPO].
    intros x Hx. split; [apply lh_reg_pol; exact Hx|].
    apply lg1_nowin_img; [exact HE|].
    unfold lo_pol_reg, lo_rng, A_PREFIX, A_SERVED, A_VLAN, A_EMPTY in Hx. lia. }
  assert (LA : la_ok m').
  { apply (ml_use _ _ _ m m' ml_la_ok C); [|exact HLA].
    intros x Hx. split; [apply lh_reg_la; exact Hx|].
    apply lg1_nowin_img; [exact HE|].
    unfold lo_rng, A_LONG_ALIAS, LONG_ALIAS_SIZE in Hx. lia. }
  assert (TX : texts_at m').
  { apply (ml_use _ _ _ m m' ml_texts_at C); [|exact HTX].
    intros x Hx. split; [apply lh_reg_texts; exact Hx|].
    apply lg1_nowin_img; [exact HE|]. unfold lo_rng, A_TEXTS in Hx. lia. }
  assert (MD : model_at m' (e_md E) mbs).
  { apply (ml_use _ _ _ m m' (ml_model_at _ _) C); [|exact HMD].
    intros x Hx. split; [apply lh_reg_md; exact Hx|].
    apply lg1_nowin_lo. unfold lo_rng in Hx. lia. }
  assert (MK : marks_at m' (e_mk E) gbs).
  { apply (ml_use _ _ _ m m' (ml_marks_at _ _) C); [|exact HMK].
    intros x Hx. split; [apply lh_reg_mk; exact Hx|].
    apply lg1_nowin_lo. unfold lo_rng in Hx. lia. }
  assert (CU : cursor_ok m' (e_p0 E) (e_pl E) P' N').
  { split; [|exact HK].
    apply (ml_use _ _ _ m m' (ml_bytes_at _ _) C); [|exact HPL].
    intros x Hx. split; [apply lh_reg_pl; exact Hx|].
    apply lg1_nowin_lo. unfold lo_rng in Hx. lia. }
  exact (conj FR' (conj SV (conj NK (conj HNW (conj IT (conj H6 (conj H7 (conj H8 (conj H9 (conj GN
          (conj OD (conj PO (conj LA (conj TX (conj IP (conj MD (conj HMW (conj MK (conj HKW (conj HKA
          (conj CU (conj HER HGU)))))))))))))))))))))).
Qed.

(* ==========================================================================
   4. The canonical register map of a return state
   ========================================================================== *)

Lemma lg1_eqv_canon : forall (Q : machine_state -> Prop) regs F pc fc m,
  Q (MS (Regs6ss.mkR_of regs) F pc fc None m (seg_rom rsegs)) ->
  eqv_cl Q (MS regs F pc fc None m (seg_rom rsegs)).
Proof.
  intros Q regs F pc fc m H.
  exists (MS (Regs6ss.mkR_of regs) F pc fc None m (seg_rom rsegs)). split; [exact H|].
  split; [apply Regs6ss.xregs_eqv_sym, Regs6ss.mkR_of_eqv|].
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MState.MS].
  repeat split; reflexivity.
Qed.

(* ==========================================================================
   5. The slot's blocks at a cut of the arm
   ========================================================================== *)


Lemma lg1_opt_in : forall (t : Z * Z) r n hb, In t hb -> In t (opt_hb r n hb).
Proof.
  intros t r n hb H. unfold opt_hb. destruct (r =? 0); [exact H | right; exact H].
Qed.

Lemma lg1_hb_md : forall g E hb T, hb_inv g E hb T -> In (e_md E, MD_SIZE) hb.
Proof.
  intros g E hb T HI. apply (Permutation_in _ (Permutation_sym HI)). left. reflexivity.
Qed.

Lemma lg1_hb_mk : forall g E hb T, hb_inv g E hb T -> In (e_mk E, MK_SIZE) hb.
Proof.
  intros g E hb T HI. apply (Permutation_in _ (Permutation_sym HI)). right. left. reflexivity.
Qed.

Lemma lg1_room : forall g E hb T, hb_inv g E hb T -> (T = [] \/ exists f, T = [(f, MF_BLOCK)]) ->
  lroom_hb hb.
Proof.
  intros g E hb T HI HT.
  assert (HL : length hb = length ((e_md E, MD_SIZE) :: (e_mk E, MK_SIZE) :: hx g T))
    by (apply Permutation_length; exact HI).
  pose proof (lg1_hb_bytes_perm hb _ HI) as HB.
  assert (HX : hx g T = [] \/ exists f, hx g T = [(f, MF_BLOCK)]).
  { unfold hx. destruct (lg_T g) as [|y T0]; [exact HT | left; reflexivity]. }
  split.
  - rewrite HL. cbn [length]. destruct HX as [HE | (f & HE)]; rewrite HE; cbn [length]; lia.
  - rewrite HB, !hb_bytes_cons. cbn [snd].
    destruct HX as [HE | (f & HE)]; rewrite HE; unfold hb_bytes; cbn [map fold_right snd];
      unfold MD_SIZE, MK_SIZE, MF_BLOCK; lia.
Qed.

(* md and mk are the arm's own blocks at every cut of the arm, kept nowhere *)
Lemma lg1_hp : forall g E hb T r n, hb_inv g E hb T -> (T = [] \/ exists f, T = [(f, MF_BLOCK)]) ->
  forall t, In t (c1_hp E) -> In t (opt_hb r n hb) /\ ~ In t T.
Proof.
  intros g E hb T r n HI HT t Ht.
  destruct (hp_md_mk g E hb T HI HT t Ht) as [H1 H2].
  split; [apply lg1_opt_in; exact H1 | exact H2].
Qed.

Section G1L.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FF : LFF B API.

(* ==========================================================================
   6. The cut: an ms_eqv closure and a pure side condition
   ========================================================================== *)

Lemma lg1_cut_eqv : forall g pc hb T (Q : machine_state -> Prop) c,
  CUT B API g pc hb T (eqv_cl Q) c -> CUT B API g pc hb T Q c.
Proof.
  intros g pc hb T Q c (fx' & L & A & regs & mem & md & Ec & Hf & HL & He).
  exists fx', L, A, regs, mem, md. split; [exact Ec|]. split; [exact Hf|]. split; [exact HL|].
  exact (eqv_cl_idem Q _ He).
Qed.

Lemma lg1_cut_and : forall g pc hb T (A0 : Prop) (Q : machine_state -> Prop) c,
  CUT B API g pc hb T (fun ms => Q ms /\ A0) c -> A0 /\ CUT B API g pc hb T Q c.
Proof.
  intros g pc hb T A0 Q c HC. split.
  - destruct HC as (fx' & L & A & regs & mem & md & _ & _ & _ & (c0 & (_ & HA) & _)). exact HA.
  - exact (cut_mono B API g pc hb T _ _ c (fun ms H => proj1 H) HC).
Qed.

(* ==========================================================================
   7. The loop-head region lies in what an allocator call keeps
   ========================================================================== *)

Lemma lg1_env_S : forall g md mk, e_S (lg_E g md mk) = lg_S g.
Proof. intros g md mk. reflexivity. Qed.

Lemma lg1_pl_blk0 : forall g md mk y, LGV B API g -> lenv_ok (lg_E g md mk) ->
  e_p0 (lg_E g md mk) <= y < e_p0 (lg_E g md mk) + Z.of_nat (length (e_pl (lg_E g md mk))) ->
  in_blk0 g y.
Proof.
  intros g md mk y HV HE Hy.
  change (e_p0 (lg_E g md mk)) with (len_p0 g) in Hy.
  change (e_pl (lg_E g md mk)) with (lg_pl g) in Hy.
  pose proof (len_ghost_ok B API FF g HV) as (_ & _ & _ & Hn & _ & Hcase).
  destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & Hpl & _).
  change (e_pl (lg_E g md mk)) with (lg_pl g) in Hpl.
  assert (Hn0 : 0 < lg_n g) by lia.
  destruct (Hcase Hn0) as (Ep & _).
  destruct HV as ((Hpre & _) & _).
  destruct Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hc & _).
  destruct Hc as [(Hz & _) | (_ & q & Hq & Hp)]; [lia|].
  exists (ptr_addr (lg_L g) q), (lg_n g). split.
  - unfold blocks. apply in_map_iff. exists (q, lg_n g). split; [reflexivity | exact Hq].
  - rewrite Hp. rewrite Ep in Hy. lia.
Qed.

Lemma lg1_keep : forall g md mk hb x, LGV B API g -> lenv_ok (lg_E g md mk) ->
  In (md, MD_SIZE) hb -> In (mk, MK_SIZE) hb ->
  lh_reg (lg_E g md mk) x -> lkeep B g hb x.
Proof.
  intros g md mk hb x HV HE Hmd Hmk Hx.
  apply (lh_reg_keep_ok B API SH SK g hb (lg_E g md mk) x FF HE (lg1_env_S g md mk));
    [exact Hmd | exact Hmk | | exact Hx].
  intros y Hy. exact (lg1_pl_blk0 g md mk y HV HE Hy).
Qed.

End G1L.
