(* The slot's ENTRY (arm `en`, prefix LE): the two segments between the second calloc and the loop head.

     E1  0x13998  mv s0, a0 ; a0 = 1 ; a1 = 516 ; jal calloc        -> le_cut2 (the call calloc (1, 516))
     E2  0x139a8  the two null checks, the size check, the loop's registers and the six frame cells
                  -> lh_ms at 0x13a1c (size >= 1) or ex_ms at 0x1413c (size = 0)

   and le_env_ok, the placement the loop head's environment needs.

   E2 stores only into the frame [S - 480 + 16, S - 480 + 64), inside the stack window
   [S - 65536, S); every other fact it keeps lies below that window (the image ends at 0x960e0, the
   two blocks and the payload below S - 65536), so it is carried by `munch` (section 2). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import
  PropExec MState Mem Cells Exec Step Frame Tac Bytes Arr Image FP.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0 MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Spec Require StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec link_mem printf_facts_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LEDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Small facts
   ========================================================================== *)

Lemma bv_eqb_lit_ne0 : forall a, 0 < a < 2 ^ 64 -> bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 0) = false.
Proof.
  intros a Ha. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia.
Qed.

Lemma bv_eqb_lit_eq0 : forall a, a = 0 -> bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 0) = true.
Proof. intros a ->. reflexivity. Qed.

Lemma lr_bytes_length : forall R, length (lr_bytes R) = 104%nat.
Proof. intros R. unfold lr_bytes, saved_bytes. rewrite !app_length, !length_le8. reflexivity. Qed.

(* the plain image's reserved segments all end at or below A_IMG_TOP = 0x97000 *)
Lemma pf_img_above : forall a n, A_IMG_TOP <= a -> pf_img_free a n.
Proof.
  intros a n Ha i Hi s Hs.
  assert (B : forallb (fun s => bv_unsigned (fst s) + bv_unsigned (snd s) <=? 0x97000)
                (segments_reserved rsegs) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in B. specialize (B s Hs). apply Z.leb_le in B.
  unfold A_IMG_TOP in Ha. lia.
Qed.

Lemma le8_bytes8 : forall bs, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs Hl. unfold le8, word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 ?x) with (x mod 2^64).
  rewrite Z_to_le_bytes_mod by (cbn; lia). rewrite <- Hl. apply StrFun.Z_to_le_bytes_to_Z.
Qed.

Lemma u64_at_det : forall m a p q,
  u64_at m a p -> u64_at m a q -> 0 <= p < 2 ^ 64 -> 0 <= q < 2 ^ 64 -> p = q.
Proof.
  intros m a p q Hp Hq Rp Rq. unfold u64_at in *.
  pose proof (bytes_at_det m a _ _ Hp Hq ltac:(rewrite !length_le8; reflexivity)) as E.
  apply (f_equal le_bytes_to_word) in E. rewrite !le_bytes_to_word_le8 in E.
  unfold wz in E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. exact E.
Qed.

(* the 64 rows of the interface table: each name pointer is below 0x75000, each name at most 16 bytes *)
Lemma link_ptrs_lo : forall i, (i < 64)%nat -> 0 <= nth i link_ptrs 0 <= 0x75000.
Proof.
  assert (B : forallb (fun i => (0 <=? nth i link_ptrs 0) && (nth i link_ptrs 0 <=? 0x75000))
                (seq 0 64) = true) by (vm_compute; reflexivity).
  intros i Hi. rewrite forallb_forall in B. specialize (B i (proj2 (in_seq 64 0 i) ltac:(lia))).
  apply andb_true_iff in B. destruct B as [B1 B2]. apply Z.leb_le in B1, B2. lia.
Qed.

Lemma link_tab_names : forall i nm ix, nth_error link_tab i = Some (nm, ix) ->
  (length nm <= 16)%nat /\ (i < 64)%nat.
Proof.
  assert (B : forallb (fun i => match nth_error link_tab i with
                                | Some (nm, _) => Nat.leb (length nm) 16 | None => true end)
                (seq 0 64) = true) by (vm_compute; reflexivity).
  assert (Lt : length link_tab = 64%nat) by (vm_compute; reflexivity).
  intros i nm ix Hn.
  assert (Hi : (i < 64)%nat) by (rewrite <- Lt; apply nth_error_Some; rewrite Hn; discriminate).
  split; [|exact Hi].
  rewrite forallb_forall in B. specialize (B i (proj2 (in_seq 64 0 i) ltac:(lia))). rewrite Hn in B.
  apply Nat.leb_le in B. exact B.
Qed.

(* ==========================================================================
   2. Facts below the stack window survive a run that writes only inside it
   ========================================================================== *)

Lemma lo_bytes : forall L H m m' A bs,
  munch [(L, H)] m m' -> A + Z.of_nat (length bs) <= L ->
  bytes_at rsegs m A bs -> bytes_at rsegs m' A bs.
Proof.
  intros L H m m' A bs MU HA HB.
  apply (bytes_at_transport rsegs [(L, H)] m m' A bs HB MU).
  cbn [disjoint_from]. split; [lia | exact I].
Qed.

Lemma lo_u8arr : forall L H m m' A bs,
  munch [(L, H)] m m' -> wmono rsegs m m' -> A + Z.of_nat (length bs) <= L ->
  u8arr rsegs m A bs -> u8arr rsegs m' A bs.
Proof.
  intros L H m m' A bs MU WM HA [HB HW]. split.
  - exact (lo_bytes L H m m' A bs MU HA HB).
  - exact (wr_at_transport rsegs m m' A _ HW WM).
Qed.

Lemma lo_cstr : forall L H m m' a s,
  munch [(L, H)] m m' -> a + Z.of_nat (length s) + 1 <= L ->
  cstr_at m a s -> cstr_at m' a s.
Proof.
  intros L H m m' a s MU HA [HB HN]. split; [|exact HN].
  apply (lo_bytes L H m m' a _ MU); [|exact HB].
  rewrite app_length. cbn [length]. lia.
Qed.

Lemma lo_u64 : forall L H m m' a v,
  munch [(L, H)] m m' -> a + 8 <= L -> u64_at m a v -> u64_at m' a v.
Proof.
  intros L H m m' a v MU HA HB. unfold u64_at in *.
  apply (lo_bytes L H m m' a _ MU); [|exact HB]. rewrite length_le8. change (Z.of_nat 8) with 8. lia.
Qed.

Lemma lo_u32 : forall L H m m' a v,
  munch [(L, H)] m m' -> a + 4 <= L -> u32_at m a v -> u32_at m' a v.
Proof.
  intros L H m m' a v MU HA HB. unfold u32_at in *.
  apply (lo_bytes L H m m' a _ MU); [|exact HB]. rewrite length_le4. change (Z.of_nat 4) with 4. lia.
Qed.

Lemma lo_odd : forall L H m m', 0x960e0 <= L -> munch [(L, H)] m m' -> odd_at m -> odd_at m'.
Proof.
  intros L H m m' HL MU HO i Hi. destruct (HO i Hi) as [HU HC]. split.
  - apply (lo_u64 L H m m' _ _ MU); [|exact HU]. unfold A_ODD. lia.
  - apply (lo_cstr L H m m' _ _ MU); [|exact HC].
    do 6 (destruct i as [|i]; [simpl; lia|]). lia.
Qed.

Lemma lo_texts : forall L H m m', 0x960e0 <= L -> munch [(L, H)] m m' -> texts_at m -> texts_at m'.
Proof.
  intros L H m m' HL MU HT i Hi. apply (lo_u64 L H m m' _ _ MU); [|exact (HT i Hi)].
  unfold A_TEXTS. lia.
Qed.

Lemma lo_policy : forall L H m m', 0x960e0 <= L -> munch [(L, H)] m m' -> policy_ro m -> policy_ro m'.
Proof.
  intros L H m m' HL MU (P1 & P2 & P3 & P4).
  split; [|split; [|split]]; (eapply lo_cstr; [exact MU| |eassumption]);
    unfold A_PREFIX, A_SERVED, A_VLAN, A_EMPTY, S_PREFIX, S_SERVED, S_VLAN; simpl; lia.
Qed.

Lemma lo_guard : forall L H m m', 0x960e0 <= L -> munch [(L, H)] m m' -> guard_m m -> guard_m m'.
Proof.
  intros L H m m' HL MU (G1 & c & G2). split.
  - apply (lo_bytes L H m m' _ _ MU); [|exact G1]. rewrite length_le8. unfold A_GOT_GUARD_S. simpl. lia.
  - exists c. apply (lo_bytes L H m m' _ _ MU); [|exact G2]. rewrite length_le8. unfold A_GUARD_S. simpl. lia.
Qed.

Lemma lo_la : forall L H m m', 0x960e0 <= L -> munch [(L, H)] m m' -> wmono rsegs m m' ->
  la_ok m -> la_ok m'.
Proof.
  intros L H m m' HL MU WM (la & sl & R1 & B1 & HLn). exists la, sl. split; [|split; [|exact HLn]].
  - apply (rw_cells_transport rsegs [(L, H)] m m' _ _ R1 MU WM).
    cbn [disjoint_from]. split; [|exact I]. left. unfold A_LONG_ALIAS. simpl. lia.
  - apply (lo_bytes L H m m' _ _ MU); [|exact B1]. rewrite HLn.
    unfold A_LONG_ALIAS, LONG_ALIAS_SIZE. simpl. lia.
Qed.

Lemma lo_gnames : forall L H m m', 0x960e0 <= L -> munch [(L, H)] m m' -> gnames_at m -> gnames_at m'.
Proof.
  intros L H m m' HL MU HG k Hk. destruct (HG k Hk) as (rest & HB & HLn). exists rest.
  split; [|exact HLn]. apply (lo_bytes L H m m' _ _ MU); [|exact HB]. rewrite HLn.
  change (Z.of_nat 8) with 8. unfold A_G_NAMES. lia.
Qed.

Lemma lo_ifptrs : forall L H m m', 0x960e0 <= L -> munch [(L, H)] m m' -> ifptrs_at m -> ifptrs_at m'.
Proof.
  intros L H m m' HL MU HP i Hi. apply (lo_u64 L H m m' _ _ MU); [|exact (HP i Hi)].
  unfold A_G_NL, NK_IF_NAME. lia.
Qed.

Lemma lo_nlk : forall L H m m' kbs, 0x960e0 <= L -> munch [(L, H)] m m' -> wmono rsegs m m' ->
  nlk_at m kbs -> nlk_at m' kbs.
Proof.
  intros L H m m' kbs HL MU WM [HU HLn]. split; [|exact HLn].
  apply (lo_u8arr L H m m' _ _ MU WM); [|exact HU]. rewrite HLn. unfold A_G_NL, NK_SIZE. lia.
Qed.

Lemma lo_iftab : forall L H m m' kbs, 0x960e0 <= L -> munch [(L, H)] m m' ->
  ifptrs_at m -> iftab_at m kbs link_tab -> iftab_at m' kbs link_tab.
Proof.
  intros L H m m' kbs HL MU HP (T1 & T2 & T3). split; [exact T1|]. split; [exact T2|].
  intros i nm ix Hn. destruct (T3 i nm ix Hn) as (Hix & p & U & Hp & C & U4).
  destruct (link_tab_names i nm ix Hn) as [Hnm Hi].
  pose proof (link_ptrs_lo i Hi) as Hq.
  assert (Rp : 0 <= p < 2 ^ 64).
  { pose proof C as ((Hp0 & Hp1 & _) & _). rewrite app_length in Hp1. cbn [length] in Hp1. lia. }
  assert (Ep : p = nth i link_ptrs 0) by exact (u64_at_det m _ p _ U (HP i Hi) Rp ltac:(lia)).
  split; [exact Hix|]. exists p. split; [|split; [exact Hp|split]].
  - apply (lo_u64 L H m m' _ _ MU); [|exact U]. unfold A_G_NL, NK_IF_NAME. lia.
  - apply (lo_cstr L H m m' _ _ MU); [|exact C]. lia.
  - apply (lo_u32 L H m m' _ _ MU); [|exact U4]. unfold A_G_NL, NK_IF_INDEX. lia.
Qed.

(* MemNorm.task_mem: TASK_SIZE = 2^47 and the window ends at S <= 2^47 *)
Lemma lo_task : forall L H m m', H <= 2 ^ 47 -> munch [(L, H)] m m' ->
  MemNorm.task_mem rsegs m -> MemNorm.task_mem rsegs m'.
Proof.
  intros L H m m' HH MU HT a b Ha.
  assert (TS : TASK_SIZE = 2 ^ 47) by (vm_compute; reflexivity).
  destruct (Z.lt_ge_cases (bv_unsigned a) H) as [H1|H1].
  - destruct (Z.lt_ge_cases (bv_unsigned a) L) as [H2|H2].
    + rewrite (MU a ltac:(cbn [outside]; split; [lia|exact I])) in Ha. exact (HT a b Ha).
    + right. lia.
  - rewrite (MU a ltac:(cbn [outside]; split; [lia|exact I])) in Ha. exact (HT a b Ha).
Qed.

(* ==========================================================================
   3. The frame at the loop head
   ========================================================================== *)

(* after the six stores the 376 bytes below the saved registers are LDefs' lh_cells; the in.n cell at
   +72 is still the bytes the frame had (lh_mem leaves its value open) *)
Lemma fr_to_lh : forall m S md mk P j0 j2,
  rw_cells rsegs m (S - 480)
    [CB 8 j0; C8 (wz A_ODD); C8 (wz (md + MD_MARK)); C8 (wz A_EMPTY); C8 (wz mk); C8 (wz A_G_NAMES);
     C8 (wz A_JT); C8 (wz GNL42); C8 (wz P); CB 304 j2] ->
  exists j0' j1 j2' nc, rw_cells rsegs m (S - SLOT_FRAME) (lh_cells md mk P nc j0' j1 j2').
Proof.
  intros m S md mk P j0 j2 [[Hwf Hb] Hw].
  cbn [cells_wf cell_wf] in Hwf. destruct Hwf as (L0 & _ & _ & _ & _ & _ & _ & _ & _ & L2 & _).
  exists j0, (firstn 40 (skipn 8 j2)), (skipn 48 j2), (bv_unsigned (le_bytes_to_word (firstn 8 j2))).
  unfold lh_cells, SLOT_FRAME. split; [split|].
  - cbn [cells_wf cell_wf]. rewrite firstn_length, !skipn_length. repeat split; try exact I; lia.
  - cbn [cells_bytes cbytes] in Hb |- *.
    assert (E : le8 (wz (bv_unsigned (le_bytes_to_word (firstn 8 j2)))) ++
                firstn 40 (skipn 8 j2) ++ skipn 48 j2 ++ [] = j2 ++ []).
    { unfold wz. rewrite Z_to_bv_bv_unsigned, le8_bytes8 by (rewrite firstn_length; lia).
      rewrite !app_nil_r.
      replace (skipn 48 j2) with (skipn 40 (skipn 8 j2)) by (rewrite skipn_skipn; reflexivity).
      rewrite firstn_skipn. rewrite firstn_skipn. reflexivity. }
    rewrite E. exact Hb.
  - cbn [cells_size csize Nat.add] in Hw |- *. exact Hw.
Qed.

(* ==========================================================================
   4. E1: 0x13998 -> the call calloc (1, 516)
   ========================================================================== *)

Lemma le_E1 : forall (G : lent) (md : Z) (ms : machine_state),
  le_cut1r G md ms ->
  evt rsegs (fun ms' => le_cut2 G md ms' /\
                        forall hp, seg_fp (n_S G) hp (ms_mem ms) (ms_mem ms')) ms.
Proof.
  intros G md ms HC.
  destruct HC as (ra & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m
    & EQ & FC & H26 & BS & KN & FRm & BZ & ST).
  subst ms. cbn [ms_mem].
  unfold L_CALLOC1_RA, wz. do 4 step.
  apply evt_done. split.
  - unfold le_cut2. do 13 eexists. exists F, fc, m.
    split; [reflexivity|]. split; [exact FC|]. split; [exact H26|]. split; [exact BS|].
    split; [exact KN|]. split; [exact FRm|]. split; [exact BZ|]. exact ST.
  - intros hp. apply seg_fp_nil.
Qed.

(* ==========================================================================
   5. E2: 0x139a8 -> the loop head 0x13a1c, or the exit 0x1413c when the input is empty
   ========================================================================== *)

Lemma le_E2 : forall (G : lent) (md mk : Z) (ms : machine_state),
  le_place G -> le_cut2r G md mk ms ->
  evt rsegs (fun ms' =>
      ((1 <= n_len G /\ lh_ms (le_env G md mk) 0 (n_gp G) ms') \/
       (n_len G = 0 /\ ex_ms (le_env G md mk) (n_gp G) ms')) /\
      seg_fp (n_S G) [(md, MD_SIZE); (mk, MK_SIZE)] (ms_mem ms) (ms_mem ms')) ms.
Proof.
  intros G md mk ms HPL HC.
  destruct HC as (ra & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m
    & EQ & FC & H26 & BS & KN & FRm & BZd & BZk & ST).
  subst ms. cbn [ms_mem].
  pose proof HPL as HPL2. destruct HPL2 as (HS1 & HS2 & HS3 & HPD & HP3).
  pose proof BZd as (Hmd0 & Hmd16 & (Hmd1 & Hmd2 & _) & _).
  pose proof BZk as (Hmk0 & Hmk16 & (Hmk1 & Hmk2 & _) & _).
  pose proof BS as (_ & _ & _ & _ & MI & _).
  destruct FRm as ((j0 & j1 & j2 & FR) & SB & SW).
  unfold fr_cells1 in FR.
  assert (HN0 : 0 <= n_len G) by (unfold n_len; lia).
  assert (HNL : n_len G = Z.of_nat (length (n_pl G))) by reflexivity.
  pose proof (munch_refl [(n_S G - SLOT_STACK_Z, n_S G)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold SLOT_FRAME, SLOT_STACK_Z, MD_SIZE, MK_SIZE in *.
  unfold L_CALLOC2_RA, wz in *. step.
  if_false_by (bv_eqb_lit_ne0 md ltac:(lia)).
  step. step.
  if_false_by (bv_eqb_lit_ne0 mk ltac:(lia)).
  step.
  destruct (Z.eq_dec (n_len G) 0) as [HZ|HNZ].
  - (* the input is empty: straight to the exit *)
    if_true_by (bv_eqb_lit_eq0 (n_len G) HZ).
    apply evt_done. cbn [ms_mem]. split; [|apply seg_fp_nil].
    right. split; [exact HZ|].
    destruct BS as ((OD & TX & PR & GD) & LA & PL & ER & _ & TM).
    destruct (rw_cells_forget rsegs m _ _ FR) as [jj FRj]. cbn [cells_size csize Nat.add] in FRj.
    unfold ex_ms. do 26 eexists. exists F, fc, m, jj.
    split; [reflexivity|]. split; [exact FC|]. split; [exact FRj|]. split; [exact SB|].
    split; [exact ER|]. split; [exact GD|]. split; [exact LA|].
    split; [exact MI|]. split; [exact TM|]. exact ST.
  - (* the loop's registers and the six frame cells *)
    if_false_by (bv_eqb_lit_ne0 (n_len G) ltac:(lia)).
    do 25 step.
    apply evt_done. cbn [ms_mem]. split.
    2: { exact (seg_fp_stk (n_S G) _ m _ MU WM). }
    left. split; [lia|].
    destruct BS as ((OD & TX & PR & GD) & LA & PL & ER & _ & TM).
    destruct KN as ((kbs & NK & NW & IT & K1 & K2 & K3 & K4) & GN & IP).
    destruct BZd as (_ & _ & _ & UZd). destruct BZk as (_ & _ & _ & UZk).
    assert (HL : 0x960e0 <= n_S G - 65536) by lia.
    unfold lh_ms. do 18 eexists. exists F, fc. eexists.
    exists (n_p0 G), (n_len G), kbs, (zeros MD_SIZE), (zeros MK_SIZE).
    split; [reflexivity|]. split; [exact FC|]. split; [lia|]. split; [lia|].
    split.
    { unfold lh_mem. cbn [e_S e_md e_mk e_p0 e_pl e_saved le_env].
      split; [exact (fr_to_lh _ (n_S G) md mk (n_p0 G) j0 j2 FR)|].
      split; [exact SB|].
      split; [exact (lo_nlk _ _ m _ kbs HL MU WM NK)|].
      split; [exact NW|].
      split; [exact (lo_iftab _ _ m _ kbs HL MU IP IT)|].
      split; [exact K1|]. split; [exact K2|]. split; [rewrite K3, K4; reflexivity|].
      split; [rewrite K3; lia|].
      split; [exact (lo_gnames _ _ m _ HL MU GN)|].
      split; [exact (lo_odd _ _ m _ HL MU OD)|].
      split; [exact (lo_policy _ _ m _ HL MU PR)|].
      split; [exact (lo_la _ _ m _ HL MU WM LA)|].
      split; [exact (lo_texts _ _ m _ HL MU TX)|].
      split; [exact (lo_ifptrs _ _ m _ HL MU IP)|].
      split.
      { split; [|rewrite zeros_length; unfold MD_SIZE; lia].
        apply (lo_u8arr _ _ m _ md _ MU WM); [|exact UZd].
        rewrite zeros_length by (unfold MD_SIZE; lia). unfold MD_SIZE. lia. }
      split; [exact model_wf_zeros|].
      split.
      { split; [|rewrite zeros_length; unfold MK_SIZE; lia].
        apply (lo_u8arr _ _ m _ mk _ MU WM); [|exact UZk].
        rewrite zeros_length by (unfold MK_SIZE; lia). unfold MK_SIZE. lia. }
      split; [exact marks_wf_zeros|].
      split; [exact marks_are_zeros|].
      split.
      { split.
        - apply (pay_keep G _ m _ HPL PL MU);
            (intros x Hx; unfold SLOT_STACK_Z in *; cbn [outside]; split; [lia | exact I]).
        - exists 0. lia. }
      split; [exact (wr_at_transport rsegs m _ _ _ ER WM)|].
      exact (lo_guard _ _ m _ HL MU GD). }
    split; [exact MI|].
    split; [exact (lo_task (n_S G - 65536) (n_S G) m _ HS2 MU TM)|].
    exact ST.
Qed.

(* ==========================================================================
   6. The loop head's environment is well placed
   ========================================================================== *)

Lemma le_env_ok : forall (G : lent) (md mk : Z) (m : word -> option byte),
  le_place G -> 1 <= n_len G < 2 ^ 26 ->
  blk_zero (n_S G) md MD_SIZE m -> blk_zero (n_S G) mk MK_SIZE m ->
  (md + MD_SIZE <= mk \/ mk + MK_SIZE <= md) ->
  (n_p0 G + n_len G <= md \/ md + MD_SIZE <= n_p0 G) ->
  (n_p0 G + n_len G <= mk \/ mk + MK_SIZE <= n_p0 G) ->
  length (lr_bytes (n_R G)) = 104%nat ->
  lenv_ok (le_env G md mk).
Proof.
  intros G md mk m HPL HN (_ & Hd16 & Hdo & _) (_ & Hk16 & Hko & _) Hdk Hpd Hpk HR.
  pose proof HPL as (HS1 & HS2 & HS3 & HPD & HP3).
  unfold lenv_ok, le_env. cbn [e_S e_md e_mk e_p0 e_pl e_saved].
  unfold n_len in *.
  split; [exact HS1|]. split; [exact HS2|]. split; [exact HS3|].
  split; [exact Hdo|]. split; [exact Hko|]. split; [exact Hd16|]. split; [exact Hk16|].
  split; [exact Hdk|]. split; [exact HN|].
  split.
  { apply HPD. unfold n_len in *. lia. }
  split; [exact Hpd|]. split; [exact Hpk|]. exact HR.
Qed.
