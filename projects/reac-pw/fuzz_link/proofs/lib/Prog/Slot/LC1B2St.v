(* Segment B2 of the op_write arm: the memory the segment carries, and how a call moves it.
   `c1b2_rest` is everything the loop head's memory says apart from the fake kernel, `c1b2_nl` is
   the fake kernel's part, and `c1b2_car` is the whole state the walk carries from the alias
   writer's return to the call of free. A call of this segment writes only inside its own stack
   frame, the head of g_nl and errno (`c1b2_win`), or only inside its frame (`c1b2_winf`).
   Each region of memory misses such a window for an arithmetic reason alone: that is what
   `c1b2_out_of`, `c1b2_outf_of` and `c1b2_out_al` say, each with a context small enough that the
   arithmetic stays cheap. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Classical.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import
  PropExec MState Mem Cells Exec Frame Step Tac Bytes Arr.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import
  LDefs LC1Defs LC1Call LC1B2Lib LC1B2Tab.
Import ListNotations.
Local Open Scope Z_scope.

(* ==========================================================================
   1. The two halves of the loop head's memory
   ========================================================================== *)

Definition c1b2_rest (E : lenv) (P N : Z) (mbs gbs : list byte) (m : word -> option byte) : Prop :=
  (exists j0 j1 j2 nc, rw_cells rsegs m (e_S E - SLOT_FRAME) (lh_cells (e_md E) (e_mk E) P nc j0 j1 j2)) /\
  bytes_at rsegs m (e_S E - 104) (e_saved E) /\
  gnames_at m /\ odd_at m /\ policy_ro m /\
  la_ok m /\ texts_at m /\ ifptrs_at m /\
  model_at m (e_md E) mbs /\ model_wf mbs /\
  marks_at m (e_mk E) gbs /\ marks_wf gbs /\ marks_are gbs mbs /\
  cursor_ok m (e_p0 E) (e_pl E) P N /\
  wr_at rsegs m A_ERRNO 4 /\ guard_m m.

Definition c1b2_nl (i : Z) (kbs : list byte) (m : word -> option byte) : Prop :=
  nlk_at m kbs /\ nlk_wf kbs /\ iftab_at m kbs link_tab /\
  nk_open kbs = 0 /\ nk_misuse kbs = 0 /\ nk_opened kbs = nk_closed kbs /\ nk_opened kbs <= 64 * i.

Lemma c1b2_lh_split : forall E i P N kbs mbs gbs m, lh_mem E i P N kbs mbs gbs m ->
  c1b2_rest E P N mbs gbs m /\ c1b2_nl i kbs m.
Proof.
  intros E i P N kbs mbs gbs m H. unfold lh_mem in H.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15
                 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23).
  split; unfold c1b2_rest, c1b2_nl.
  - do 15 (split; [assumption|]). assumption.
  - do 6 (split; [assumption|]). assumption.
Qed.

Lemma c1b2_lh_join : forall E i P N kbs mbs gbs m,
  c1b2_rest E P N mbs gbs m -> c1b2_nl i kbs m -> lh_mem E i P N kbs mbs gbs m.
Proof.
  intros E i P N kbs mbs gbs m HR HN. unfold c1b2_rest in HR. unfold c1b2_nl in HN.
  destruct HR as (A1 & A2 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23).
  destruct HN as (B3 & B4 & B5 & B6 & B7 & B8 & B9).
  unfold lh_mem. do 22 (split; [assumption|]). assumption.
Qed.

(* ==========================================================================
   2. What a call of this segment may write, and what that misses
   ========================================================================== *)

Definition c1b2_win (E : lenv) (W : list ivl) : Prop :=
  forall x, ~ outside W x ->
    (e_S E - SLOT_STACK_Z <= x < e_S E - SLOT_FRAME) \/
    (A_G_NL <= x < A_G_NL + NK_N_SENT + 4) \/ (A_ERRNO <= x < A_ERRNO + 4).

Definition c1b2_winf (E : lenv) (W : list ivl) : Prop :=
  forall x, ~ outside W x -> e_S E - SLOT_STACK_Z <= x < e_S E - SLOT_FRAME.

Lemma c1b2_winf_win : forall E W, c1b2_winf E W -> c1b2_win E W.
Proof. intros E W H x Hx. left. exact (H x Hx). Qed.

(* [A_G_NL, A_G_NL + NK_N_SENT + 4) = [203648, 474668); A_ERRNO = 480612 *)
Lemma c1b2_out_of : forall E W a n, c1b2_win E W -> 0x960e0 + 65536 <= e_S E ->
  (a + n <= 203648 \/ (474668 <= a /\ a + n <= 480612) \/
   (480616 <= a /\ a + n <= e_S E - 65536) \/ (e_S E - 480 <= a /\ a + n <= e_S E)) ->
  c1b2_out W a n.
Proof.
  intros E W a n HW HS HO x Hx. apply NNPP. intros HC.
  destruct (HW x HC) as [H|[H|H]];
    unfold A_G_NL, NK_N_SENT, A_ERRNO, A_TP, ERRNO_TP_OFF, SLOT_STACK_Z, SLOT_FRAME in H; lia.
Qed.

Lemma c1b2_outf_of : forall E W a n, c1b2_winf E W -> 0x960e0 + 65536 <= e_S E ->
  (a + n <= e_S E - 65536 \/ (e_S E - 480 <= a /\ a + n <= e_S E)) -> c1b2_out W a n.
Proof.
  intros E W a n HW HS HO x Hx. apply NNPP. intros HC.
  pose proof (HW x HC) as H. unfold SLOT_STACK_Z, SLOT_FRAME in H. lia.
Qed.

(* the alias text_of answered: al_ok says where it is not *)
Lemma c1b2_out_al : forall E W a n, c1b2_win E W ->
  apart a n (e_S E - SLOT_STACK_Z) SLOT_STACK_Z -> apart_gnl a n -> apart a n A_ERRNO 4 ->
  c1b2_out W a n.
Proof.
  intros E W a n HW D1 D2 D3 x Hx. apply NNPP. intros HC.
  unfold apart in D1, D3. unfold apart_gnl in D2.
  destruct (HW x HC) as [H|[H|H]];
    unfold A_G_NL, NK_SIZE, NK_N_SENT, A_ERRNO, A_TP, ERRNO_TP_OFF, SLOT_STACK_Z, SLOT_FRAME in *; lia.
Qed.

(* ==========================================================================
   3. Moving the two halves across a call
   ========================================================================== *)

Lemma c1b2_rest_keep : forall E P N mbs gbs m m' W,
  lenv_ok E -> c1b2_rest E P N mbs gbs m -> munch W m m' -> wmono rsegs m m' ->
  c1b2_win E W -> c1b2_rest E P N mbs gbs m'.
Proof.
  intros E P N mbs gbs m m' W HE HR MU WM HW.
  unfold lenv_ok in HE.
  destruct HE as (L1 & L2 & L3 & BMD & BMK & L6 & L7 & L8 & PLN & BP0 & L11 & L12 & LS).
  assert (SS : 0x960e0 + 65536 <= e_S E) by (unfold SLOT_STACK_Z in L1; lia).
  assert (MDH : e_md E + 8856 <= e_S E - 65536).
  { pose proof (c1b2_blk_hi _ _ _ BMD) as H. unfold MD_SIZE, SLOT_STACK_Z in H. lia. }
  assert (MKH : e_mk E + 516 <= e_S E - 65536).
  { pose proof (c1b2_blk_hi _ _ _ BMK) as H. unfold MK_SIZE, SLOT_STACK_Z in H. lia. }
  assert (PPH : e_p0 E + Z.of_nat (length (e_pl E)) <= e_S E - 65536).
  { pose proof (c1b2_blk_hi _ _ _ BP0) as H. unfold SLOT_STACK_Z in H. lia. }
  assert (GMD : e_md E + 8856 <= 65536 \/ 614112 <= e_md E).
  { pose proof c1b2_pages_ge as PG. destruct BMD as (B1 & B2 & BF).
    destruct (c1b2_img_free_bound (e_md E) MD_SIZE ltac:(lia) ltac:(unfold MD_SIZE; lia) BF) as [H|H].
    - left. unfold MD_SIZE in H. lia.
    - right. lia. }
  assert (GMK : e_mk E + 516 <= 65536 \/ 614112 <= e_mk E).
  { pose proof c1b2_pages_ge as PG. destruct BMK as (B1 & B2 & BF).
    destruct (c1b2_img_free_bound (e_mk E) MK_SIZE ltac:(lia) ltac:(unfold MK_SIZE; lia) BF) as [H|H].
    - left. unfold MK_SIZE in H. lia.
    - right. lia. }
  assert (GP0 : e_p0 E + Z.of_nat (length (e_pl E)) <= 65536 \/ 614112 <= e_p0 E).
  { pose proof c1b2_pages_ge as PG. destruct BP0 as (B1 & B2 & BF).
    destruct (c1b2_img_free_bound (e_p0 E) (Z.of_nat (length (e_pl E))) ltac:(lia) ltac:(lia) BF)
      as [H|H]; [left; lia | right; lia]. }
  clear L1 L2 L3 BMD BMK BP0 L6 L7 L8 L11 L12.
  destruct HR as (HFR & HSV & HGN & HOD & HPO & HLA & HTX & HIF & HMD & HMDW & HMK & HMKW & HMA & HCU & HER & HGU).
  assert (A1 : exists j0 j1 j2 nc,
            rw_cells rsegs m' (e_S E - SLOT_FRAME) (lh_cells (e_md E) (e_mk E) P nc j0 j1 j2)).
  { destruct HFR as (j0 & j1 & j2 & nc & HC). exists j0, j1, j2, nc.
    eapply c1b2_rwc_tr; [exact HC | exact MU | exact WM |].
    assert (CS : cells_size (lh_cells (e_md E) (e_mk E) P nc j0 j1 j2) = 376%nat) by reflexivity.
    rewrite CS. eapply c1b2_out_of; [exact HW | exact SS |].
    right; right; right. unfold SLOT_FRAME. lia. }
  assert (A2 : bytes_at rsegs m' (e_S E - 104) (e_saved E)).
  { eapply c1b2_bytes_tr; [exact HSV | exact MU |]. rewrite LS.
    eapply c1b2_out_of; [exact HW | exact SS |]. right; right; right. unfold SLOT_FRAME. lia. }
  assert (A3 : gnames_at m').
  { intros k Hk. destruct (HGN k Hk) as (rest & HB & HL). exists rest. split; [|exact HL].
    eapply c1b2_bytes_tr; [exact HB | exact MU |]. rewrite HL.
    eapply c1b2_out_of; [exact HW | exact SS |]. right; left. unfold A_G_NAMES. lia. }
  assert (A4 : odd_at m').
  { intros k Hk. destruct (HOD k Hk) as [HU HC]. pose proof (c1b2_odd_rng k Hk) as [R1 R2]. split.
    - eapply c1b2_u64_tr; [exact HU | exact MU |].
      eapply c1b2_out_of; [exact HW | exact SS |]. left. unfold A_ODD. lia.
    - eapply c1b2_cstr_tr; [exact HC | exact MU |].
      eapply c1b2_out_of; [exact HW | exact SS |]. left. lia. }
  assert (A5 : policy_ro m').
  { destruct HPO as (P1 & P2 & P3 & P4).
    assert (K1 : Z.of_nat (length S_PREFIX) = 8) by reflexivity.
    assert (K2 : Z.of_nat (length S_SERVED) = 14) by reflexivity.
    assert (K3 : Z.of_nat (length S_VLAN) = 4) by reflexivity.
    split; [|split; [|split]].
    - eapply c1b2_cstr_tr; [exact P1 | exact MU |]. rewrite K1.
      eapply c1b2_out_of; [exact HW | exact SS |]. left. unfold A_PREFIX. lia.
    - eapply c1b2_cstr_tr; [exact P2 | exact MU |]. rewrite K2.
      eapply c1b2_out_of; [exact HW | exact SS |]. left. unfold A_SERVED. lia.
    - eapply c1b2_cstr_tr; [exact P3 | exact MU |]. rewrite K3.
      eapply c1b2_out_of; [exact HW | exact SS |]. left. unfold A_VLAN. lia.
    - eapply c1b2_cstr_tr; [exact P4 | exact MU |]. cbn [length].
      eapply c1b2_out_of; [exact HW | exact SS |]. left. unfold A_EMPTY. lia. }
  assert (A6 : la_ok m').
  { destruct HLA as (la & sl & HC & HB & HL). exists la, sl. split; [|split; [|exact HL]].
    - eapply c1b2_rwc_tr; [exact HC | exact MU | exact WM |].
      assert (CS : cells_size [CB (Z.to_nat 300) la; C1 (zb 0)] = 301%nat) by reflexivity.
      rewrite CS. eapply c1b2_out_of; [exact HW | exact SS |].
      right; left. unfold A_LONG_ALIAS. lia.
    - eapply c1b2_bytes_tr; [exact HB | exact MU |]. rewrite HL.
      eapply c1b2_out_of; [exact HW | exact SS |].
      right; left. unfold A_LONG_ALIAS, LONG_ALIAS_SIZE. lia. }
  assert (A7 : texts_at m').
  { intros k Hk. eapply c1b2_u64_tr; [exact (HTX k Hk) | exact MU |].
    eapply c1b2_out_of; [exact HW | exact SS |]. left. unfold A_TEXTS. lia. }
  assert (A8 : ifptrs_at m').
  { intros k Hk. eapply c1b2_u64_tr; [exact (HIF k Hk) | exact MU |].
    eapply c1b2_out_of; [exact HW | exact SS |].
    right; left. unfold A_G_NL, NK_IF_NAME. lia. }
  assert (A9 : model_at m' (e_md E) mbs).
  { destruct HMD as [HU HL]. split; [|exact HL].
    eapply c1b2_u8arr_tr; [exact HU | exact MU | exact WM |]. rewrite HL.
    eapply c1b2_out_of; [exact HW | exact SS |].
    destruct GMD as [G|G]; [left; unfold MD_SIZE; lia | right; right; left; unfold MD_SIZE; lia]. }
  assert (A11 : marks_at m' (e_mk E) gbs).
  { destruct HMK as [HU HL]. split; [|exact HL].
    eapply c1b2_u8arr_tr; [exact HU | exact MU | exact WM |]. rewrite HL.
    eapply c1b2_out_of; [exact HW | exact SS |].
    destruct GMK as [G|G]; [left; unfold MK_SIZE; lia | right; right; left; unfold MK_SIZE; lia]. }
  assert (A14 : cursor_ok m' (e_p0 E) (e_pl E) P N).
  { destruct HCU as [HB HK]. split; [|exact HK].
    eapply c1b2_bytes_tr; [exact HB | exact MU |].
    eapply c1b2_out_of; [exact HW | exact SS |].
    destruct GP0 as [G|G]; [left; lia | right; right; left; lia]. }
  assert (A15 : wr_at rsegs m' A_ERRNO 4) by (eapply wr_at_transport; eassumption).
  assert (A16 : guard_m m').
  { destruct HGU as [HB1 [c HB2]]. split.
    - eapply c1b2_bytes_tr; [exact HB1 | exact MU |]. rewrite length_le8.
      eapply c1b2_out_of; [exact HW | exact SS |]. left. unfold A_GOT_GUARD_S. lia.
    - exists c. eapply c1b2_bytes_tr; [exact HB2 | exact MU |]. rewrite length_le8.
      eapply c1b2_out_of; [exact HW | exact SS |]. right; right; left. unfold A_GUARD_S. lia. }
  unfold c1b2_rest. do 15 (split; [assumption|]). assumption.
Qed.

Lemma c1b2_nl_keep : forall E i kbs m m' W,
  lenv_ok E -> c1b2_nl i kbs m -> ifptrs_at m -> munch W m m' -> wmono rsegs m m' ->
  c1b2_winf E W -> c1b2_nl i kbs m'.
Proof.
  intros E i kbs m m' W HE HN HP MU WM HW.
  assert (L1 : 0x960e0 + 65536 <= e_S E) by (unfold lenv_ok, SLOT_STACK_Z in HE; lia).
  clear HE.
  destruct HN as (HK & HWF & HT & H1 & H2 & H3 & H4).
  assert (B1 : nlk_at m' kbs).
  { destruct HK as [HU HL]. split; [|exact HL].
    eapply c1b2_u8arr_tr; [exact HU | exact MU | exact WM |]. rewrite HL.
    eapply c1b2_outf_of; [exact HW | exact L1 |]. left. unfold A_G_NL, NK_SIZE. lia. }
  assert (B2 : iftab_at m' kbs link_tab).
  { destruct HT as (T1 & T2 & T3). split; [exact T1|]. split; [exact T2|].
    intros k nm ix HEk.
    destruct (c1b2_iftab_ptr m kbs k nm ix HP (conj T1 (conj T2 T3)) HEk)
      as (Hk & HU & HC & HU32 & Hix).
    pose proof (c1b2_ptr_rng k Hk) as HR. pose proof (c1b2_nml_le k Hk) as HL.
    destruct (c1b2_tab_nth k nm ix HEk) as [_ HN2].
    split; [exact Hix|]. exists (c1b2_ptr k). split; [|split; [|split]].
    - eapply c1b2_u64_tr; [exact HU | exact MU |].
      eapply c1b2_outf_of; [exact HW | exact L1 |]. left. unfold A_G_NL, NK_IF_NAME. lia.
    - unfold A_G_NAMES, G_NAMES_SIZE in HR. lia.
    - eapply c1b2_cstr_tr; [exact HC | exact MU |].
      eapply c1b2_outf_of; [exact HW | exact L1 |]. left.
      unfold A_G_NAMES, G_NAMES_SIZE in HR. lia.
    - eapply c1b2_u32_tr; [exact HU32 | exact MU |].
      eapply c1b2_outf_of; [exact HW | exact L1 |]. left. unfold A_G_NL, NK_IF_INDEX. lia. }
  unfold c1b2_nl. do 6 (split; [assumption|]). assumption.
Qed.

(* ==========================================================================
   4. task_mem and the segment footprint across a call
   ========================================================================== *)

Lemma c1b2_task_keep : forall E m m' W,
  lenv_ok E -> MemNorm.task_mem rsegs m -> munch W m m' -> c1b2_win E W ->
  MemNorm.task_mem rsegs m'.
Proof.
  intros E m m' W HE TM MU HW.
  assert (L1 : 0x960e0 + 65536 <= e_S E <= 2 ^ 47)
    by (unfold lenv_ok, SLOT_STACK_Z in HE; lia).
  clear HE. intros a b Ea.
  destruct (classic (outside W (bv_unsigned a))) as [H|H].
  - rewrite (MU a H) in Ea. exact (TM a b Ea).
  - right. change TASK_SIZE with (2 ^ 47).
    destruct (HW _ H) as [K|[K|K]];
      unfold A_G_NL, NK_N_SENT, A_ERRNO, A_TP, ERRNO_TP_OFF, SLOT_STACK_Z, SLOT_FRAME in K; lia.
Qed.

Lemma c1b2_fp_keep : forall E m0 m m' W,
  lenv_ok E -> seg_fp (e_S E) (c1_hp E) m0 m -> munch W m m' -> wmono rsegs m m' ->
  c1b2_win E W -> seg_fp (e_S E) (c1_hp E) m0 m'.
Proof.
  intros E m0 m m' W HE FP MU WM HW.
  assert (L1 : 0x960e0 + 65536 <= e_S E) by (unfold lenv_ok, SLOT_STACK_Z in HE; lia).
  clear HE.
  eapply seg_fp_call; [exact FP | exact MU | exact WM |].
  intros x Hx HC. destruct (HW _ HC) as [H|[H|H]]; unfold own_w.
  - left. unfold SLOT_STACK_Z, SLOT_FRAME in *. lia.
  - right. left. unfold NK_N_SENT, NK_SIZE in *. lia.
  - right. right. right. right. left. lia.
Qed.

(* ==========================================================================
   5. The state the walk carries
   ========================================================================== *)

Definition c1b2_car (E : lenv) (i own s : Z) (t sl : list byte)
    (P N : Z) (kbs mbs gbs : list byte) (m0 m : word -> option byte) : Prop :=
  c1b2_rest E P N mbs gbs m /\ c1b2_nl (i + 1) kbs m /\
  rw_cells rsegs m (e_S E - SLOT_FRAME + FO_P) [C8 (wz P); C8 (wz N)] /\
  bytes_at rsegs m (e_S E - SLOT_FRAME + FO_B256) (le8 (wz own)) /\
  al_ok E m s t sl /\
  mem_inv rsegs m /\ MemNorm.task_mem rsegs m /\
  stk rsegs m (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME) /\
  seg_fp (e_S E) (c1_hp E) m0 m.

Lemma c1b2_cells_keep : forall E P N m m' W,
  lenv_ok E -> rw_cells rsegs m (e_S E - SLOT_FRAME + FO_P) [C8 (wz P); C8 (wz N)] ->
  munch W m m' -> wmono rsegs m m' -> c1b2_win E W ->
  rw_cells rsegs m' (e_S E - SLOT_FRAME + FO_P) [C8 (wz P); C8 (wz N)].
Proof.
  intros E P N m m' W HE HC MU WM HW.
  assert (L1 : 0x960e0 + 65536 <= e_S E) by (unfold lenv_ok, SLOT_STACK_Z in HE; lia).
  clear HE.
  eapply c1b2_rwc_tr; [exact HC | exact MU | exact WM |].
  assert (CS : cells_size [C8 (wz P); C8 (wz N)] = 16%nat) by reflexivity. rewrite CS.
  eapply c1b2_out_of; [exact HW | exact L1 |].
  right; right; right. unfold FO_P, SLOT_FRAME. lia.
Qed.

Lemma c1b2_own_keep : forall E own m m' W,
  lenv_ok E -> bytes_at rsegs m (e_S E - SLOT_FRAME + FO_B256) (le8 (wz own)) ->
  munch W m m' -> c1b2_win E W ->
  bytes_at rsegs m' (e_S E - SLOT_FRAME + FO_B256) (le8 (wz own)).
Proof.
  intros E own m m' W HE HB MU HW.
  assert (L1 : 0x960e0 + 65536 <= e_S E) by (unfold lenv_ok, SLOT_STACK_Z in HE; lia).
  clear HE.
  eapply c1b2_bytes_tr; [exact HB | exact MU |]. rewrite length_le8.
  eapply c1b2_out_of; [exact HW | exact L1 |].
  right; right; right. unfold FO_B256, SLOT_FRAME. lia.
Qed.

Lemma c1b2_al_keep : forall E s t sl m m' W,
  lenv_ok E -> al_ok E m s t sl -> munch W m m' -> c1b2_win E W -> al_ok E m' s t sl.
Proof.
  intros E s t sl m m' W HE HA MU HW.
  destruct HA as (N0 & HB & HNN & HTL & HSL & D1 & D2 & D3 & D4 & D5).
  unfold al_ok. split; [exact N0|].
  split.
  { eapply c1b2_bytes_tr; [exact HB | exact MU |].
    rewrite length_app. cbn [length].
    replace (Z.of_nat (length t + S (length sl)))
      with (Z.of_nat (length t) + 1 + Z.of_nat (length sl)) by lia.
    eapply c1b2_out_al; [exact HW | exact D1 | exact D2 | exact D5]. }
  split; [exact HNN|]. split; [exact HTL|]. split; [exact HSL|].
  split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [exact D4|]. exact D5.
Qed.

(* a call that writes only inside its own frame keeps the whole carried state *)
Lemma c1b2_car_keep : forall E i own s t sl P N kbs mbs gbs m0 m m' W,
  lenv_ok E -> c1b2_car E i own s t sl P N kbs mbs gbs m0 m ->
  munch W m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  stk rsegs m' (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME) ->
  c1b2_winf E W ->
  c1b2_car E i own s t sl P N kbs mbs gbs m0 m'.
Proof.
  intros E i own s t sl P N kbs mbs gbs m0 m m' W HE HC MU WM MI ST HWF.
  pose proof (c1b2_winf_win E W HWF) as HW.
  destruct HC as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9).
  assert (HIF : ifptrs_at m).
  { unfold c1b2_rest in R1.
    destruct R1 as (_ & _ & _ & _ & _ & _ & _ & X & _). exact X. }
  unfold c1b2_car.
  split; [eapply c1b2_rest_keep; eassumption|].
  split; [eapply c1b2_nl_keep; eassumption|].
  split; [eapply c1b2_cells_keep; eassumption|].
  split; [eapply c1b2_own_keep; eassumption|].
  split; [eapply c1b2_al_keep; eassumption|].
  split; [exact MI|].
  split; [eapply c1b2_task_keep; eassumption|].
  split; [exact ST|].
  eapply c1b2_fp_keep; eassumption.
Qed.

(* the alias writer: the fake kernel is the one its Post hands back *)
Lemma c1b2_car_alias : forall E i own s t sl P N kbs' mbs gbs m0 m m' W,
  lenv_ok E ->
  c1b2_rest E P N mbs gbs m ->
  rw_cells rsegs m (e_S E - SLOT_FRAME + FO_P) [C8 (wz P); C8 (wz N)] ->
  bytes_at rsegs m (e_S E - SLOT_FRAME + FO_B256) (le8 (wz own)) ->
  al_ok E m s t sl -> MemNorm.task_mem rsegs m -> seg_fp (e_S E) (c1_hp E) m0 m ->
  munch W m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  stk rsegs m' (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME) -> c1b2_win E W ->
  nlk_at m' kbs' -> nlk_wf kbs' -> iftab_at m' kbs' link_tab ->
  nk_open kbs' = 0 -> nk_misuse kbs' = 0 -> nk_opened kbs' = nk_closed kbs' ->
  nk_opened kbs' <= 64 * (i + 1) ->
  c1b2_car E i own s t sl P N kbs' mbs gbs m0 m'.
Proof.
  intros E i own s t sl P N kbs' mbs gbs m0 m m' W HE REST CELLS OWN AL TM FP MU WM MI ST HW
         K1 K2 K3 K4 K5 K6 K7.
  assert (NL' : c1b2_nl (i + 1) kbs' m').
  { unfold c1b2_nl. do 6 (split; [assumption|]). assumption. }
  unfold c1b2_car.
  split; [eapply c1b2_rest_keep; eassumption|].
  split; [exact NL'|].
  split; [eapply c1b2_cells_keep; eassumption|].
  split; [eapply c1b2_own_keep; eassumption|].
  split; [eapply c1b2_al_keep; eassumption|].
  split; [exact MI|].
  split; [eapply c1b2_task_keep; eassumption|].
  split; [exact ST|].
  eapply c1b2_fp_keep; eassumption.
Qed.

(* ==========================================================================
   6. The two cuts inside the segment, and its post
   ========================================================================== *)

(* the readings under which the alias writer opened no socket (its Post's refusal clause, read at
   this call site: the name is NULL or empty, the alias is too long, or the name is not in the
   table) *)
Definition c1b2_ref (nb : Z) (t : list byte) : Prop :=
  sel_name nb = None \/ sel_name nb = Some [] \/ ALIAS_MAX <= Z.of_nat (length t)
  \/ (forall s, sel_name nb = Some s -> index_of link_tab s = 0).

(* 0x14010: check_socket has returned; the refusal test begins. s2 is name_of's answer, s3 the
   model's code, s4 g_nl.opened as it was before the library wrote, s5 the alias, s6 the
   library's code. *)
Definition c1b2_s10 (E : lenv) (i : Z) (gp : word) (own nb rm op0 s rl : Z)
    (t sl : list byte) (m0 : word -> option byte) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (P N : Z) (kbs mbs gbs : list byte),
    ms = MS (mkR ra (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (wz (sel_ptr nb)) (wz rm) (wz op0) (wz s) (wz rl) (wz (e_mk E)) (wz 0xab) (wz 4)
                 (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6)
            F (wz 0x14010) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\ 0 <= nb < 256 /\ 0 <= N /\
    rm = norm_rc rl /\ - 2 ^ 31 <= rl < 2 ^ 31 /\ 0 <= op0 < 2 ^ 31 /\
    requests_are kbs mbs /\ (c1b2_ref nb t -> nk_opened kbs = op0) /\
    c1b2_car E i own s t sl P N kbs mbs gbs m0 m.

(* 0x14044: the refusal test is over; check_write and check_requests are left *)
Definition c1b2_s44 (E : lenv) (i : Z) (gp : word) (own nb rm op0 s rl : Z)
    (t sl : list byte) (m0 : word -> option byte) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (P N : Z) (kbs mbs gbs : list byte),
    ms = MS (mkR ra (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (wz (sel_ptr nb)) (wz rm) (wz op0) (wz s) (wz rl) (wz (e_mk E)) (wz 0xab) (wz 4)
                 (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6)
            F (wz 0x14044) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\ 0 <= N /\
    rm = norm_rc rl /\ - 2 ^ 31 <= rl < 2 ^ 31 /\
    requests_are kbs mbs /\
    c1b2_car E i own s t sl P N kbs mbs gbs m0 m.

(* what the segment owes at the call of free: LC1Defs' cut and the footprint against the memory
   the segment started from *)
Definition c1b2_post (E : lenv) (i : Z) (gp : word) (own : Z) (m0 : word -> option byte)
    (ms' : machine_state) : Prop :=
  c1_173d4 E i gp own ms' /\ seg_fp (e_S E) (c1_hp E) m0 (ms_mem ms').
