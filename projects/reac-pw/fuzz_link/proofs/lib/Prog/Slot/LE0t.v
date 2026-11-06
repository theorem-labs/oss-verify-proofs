(* The slot's entry, arm `en`: after interfaces() has run, the fake kernel and g_names in the form
   the entry's loops keep them (LEDefs' `le_nlk` and `le_gnames`) give the form the loop head asks
   for (LEDefs' `le_kern`).  Pure memory reasoning: every scalar field of the kernel block is read
   out of memory with `fld_u32_of_mem`, and the interface table is matched row by row against
   LDefs' `link_tab`. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import
  PropExec MState Mem Cells Exec Step Frame Tac Bytes Arr Image FP.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0 MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LEDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* ==========================================================================
   1. The names g_names holds carry no NUL
   ========================================================================== *)

Lemma dec2_digits : forall k c, 0 <= k < 100 -> In c (dec2 k) -> 48 <= c <= 57.
Proof.
  intros k c Hk. unfold dec2. destruct (Z.ltb_spec k 10) as [H|H]; cbn [In]; intros Hc.
  - destruct Hc as [<-|[]]; lia.
  - assert (H1 : 0 <= k / 10 < 10).
    { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    assert (H2 : 0 <= k mod 10 < 10) by (apply Z.mod_pos_bound; lia).
    destruct Hc as [<-|[<-|[]]]; lia.
Qed.

Lemma gname_nonul : forall k, 0 <= k < 100 -> ~ In (zb 0) (gname k).
Proof.
  intros k Hk IN. unfold gname, gname_z in IN. apply in_map_iff in IN.
  destruct IN as (c & E & Hc).
  assert (Hr : 48 <= c <= 110).
  { cbn [In] in Hc. destruct Hc as [<-|[<-|Hc]]; [lia | lia |].
    apply (dec2_digits k c Hk) in Hc. lia. }
  assert (E' : bv_unsigned (zb c) = bv_unsigned (zb 0)) by (rewrite E; reflexivity).
  unfold zb in E'. rewrite !Z_to_bv_unsigned in E'.
  change (bv_wrap 8 ?a) with (a mod 256) in E'.
  rewrite !Z.mod_small in E' by lia. lia.
Qed.

(* ==========================================================================
   2. The three lists of the interface table agree row by row
   ========================================================================== *)

Lemma gtab_eq : gtab = map (fun j => (gname (Z.of_nat j), Z.of_nat j + 2)) (kept 64).
Proof. unfold gtab. rewrite kept_64. reflexivity. Qed.

Lemma gtab_length : length gtab = 60%nat.
Proof. rewrite gtab_eq, length_map. exact kept_64_length. Qed.

Lemma g_ps_length : length (g_ps 64) = 60%nat.
Proof. unfold g_ps. rewrite length_map. exact kept_64_length. Qed.

Lemma g_ixs_length : length (g_ixs 64) = 60%nat.
Proof. unfold g_ixs. rewrite length_map. exact kept_64_length. Qed.

Lemma link_ptrs_length : length link_ptrs = 64%nat.
Proof. rewrite link_ptrs_eq, length_app, g_ps_length. reflexivity. Qed.

Lemma link_tab_length : length link_tab = 64%nat.
Proof. unfold link_tab. rewrite length_app, gtab_length. reflexivity. Qed.

(* rows 0..59: the kept names of g_names *)
Lemma row_g : forall i, (i < 60)%nat ->
  exists j, (j < 64)%nat /\
    nth_error link_tab i = Some (gname (Z.of_nat j), Z.of_nat j + 2) /\
    nth i link_ptrs 0 = A_G_NAMES + 8 * Z.of_nat j /\
    nth i (g_ixs 64 ++ o_ixs) 0 = Z.of_nat j + 2.
Proof.
  intros i Hi.
  pose proof gtab_length as LT. pose proof g_ps_length as LG. pose proof g_ixs_length as LI.
  destruct (nth_error (kept 64) i) as [j|] eqn:EJ.
  2: { apply nth_error_None in EJ. rewrite kept_64_length in EJ. lia. }
  exists j. split; [exact (kept_lt 64 j (nth_error_In _ _ EJ))|].
  split; [|split].
  - unfold link_tab. rewrite nth_error_app1 by lia.
    rewrite gtab_eq, nth_error_map, EJ. reflexivity.
  - apply nth_error_nth. rewrite link_ptrs_eq, nth_error_app1 by lia.
    unfold g_ps. rewrite nth_error_map, EJ. reflexivity.
  - apply nth_error_nth. rewrite nth_error_app1 by lia.
    unfold g_ixs. rewrite nth_error_map, EJ. reflexivity.
Qed.

(* rows 60..63: odd[1..4] *)
Lemma row_o : forall r, (r < 4)%nat ->
  nth_error link_tab (60 + r) = Some (nth (S r) odd_strs [], 101 + Z.of_nat r) /\
  nth (60 + r) link_ptrs 0 = nth (S r) odd_ptrs 0 /\
  nth (60 + r) (g_ixs 64 ++ o_ixs) 0 = 101 + Z.of_nat r /\
  nth (S r) odd_ptrs 0 <> 0.
Proof.
  intros r Hr.
  pose proof gtab_length as LT. pose proof g_ps_length as LG. pose proof g_ixs_length as LI.
  unfold link_tab. rewrite nth_error_app2 by lia. rewrite LT.
  rewrite link_ptrs_eq. rewrite app_nth2 by lia. rewrite app_nth2 by lia. rewrite LG, LI.
  replace (60 + r - 60)%nat with r by lia.
  destruct r as [|[|[|[|r]]]]; [| | | | lia].
  all: split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; cbn; lia.
Qed.

(* ==========================================================================
   3. From the entry's form to the loop head's
   ========================================================================== *)

Local Ltac nk_fld F H :=
  apply (F _ _ H);
  unfold NK_N_CHUNKS, NK_NEXT, NK_END_ERRNO, NK_SOCKET_ERRNO, NK_SEND_ERRNO, NK_OPEN, NK_OPENED,
    NK_CLOSED, NK_MISUSE, NK_N_SENT, NK_N_IF, NK_SIZE; lia.

Lemma le_kern_of : forall (m : word -> option byte),
  le_img m -> le_nlk m link_ptrs (g_ixs 64 ++ o_ixs) -> le_gnames m 64 -> le_kern m.
Proof.
  intros m IMG NLK GN.
  unfold le_img in IMG. destruct IMG as (ODD & _ & _ & _).
  unfold le_nlk, le_tabl, le_zfields in NLK.
  destruct NLK as ((kb & KL & KB) & KW & (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10) & _ & TN & TR).
  unfold le_gnames in GN. destruct GN as (GN & _).
  rewrite link_ptrs_length in TN, TR. change (Z.of_nat 64) with 64 in TN.
  assert (F : forall off v, u32_at m (A_G_NL + off) v -> 0 <= off -> off + 4 <= NK_SIZE ->
                0 <= v < 2 ^ 32 -> fld_u32 kb off = v).
  { intros off v H Ho Hn Hv. apply (fld_u32_of_mem m A_G_NL kb off v KB H Ho); [lia | exact Hv]. }
  assert (E1 : nk_n_chunks kb = 0) by nk_fld F Z1.
  assert (E2 : nk_next kb = 0) by nk_fld F Z2.
  assert (E3 : nk_end_errno kb = 0) by nk_fld F Z3.
  assert (E4 : nk_socket_errno kb = 0) by nk_fld F Z4.
  assert (E5 : nk_send_errno kb = 0) by nk_fld F Z5.
  assert (E6 : nk_open kb = 0) by nk_fld F Z6.
  assert (E7 : nk_opened kb = 0) by nk_fld F Z7.
  assert (E8 : nk_closed kb = 0) by nk_fld F Z8.
  assert (E9 : nk_misuse kb = 0) by nk_fld F Z9.
  assert (E10 : nk_n_sent kb = 0) by nk_fld F Z10.
  assert (EN : nk_n_if kb = 64) by nk_fld F TN.
  clear F Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 TN.
  split; [|split].
  - exists kb. split; [|split; [|split]].
    + unfold nlk_at, u8arr. split; [split; [exact KB | rewrite KL; exact KW] | exact KL].
    + unfold nlk_wf. rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, EN.
      unfold NL_CHUNKS, NL_SENT_MAX. repeat split; try lia; intros i Hi; lia.
    + unfold iftab_at. rewrite EN, link_tab_length. change (Z.of_nat 64) with 64.
      split; [reflexivity|]. split; [lia|].
      intros i nm ix HN.
      assert (Hi : (i < length link_tab)%nat) by (apply nth_error_Some; rewrite HN; discriminate).
      rewrite link_tab_length in Hi.
      destruct (TR i Hi) as (RP & RI).
      destruct (Nat.lt_ge_cases i 60) as [Hg|Ho].
      * destruct (row_g i Hg) as (j & Hj & ET & EP & EI).
        rewrite ET in HN. injection HN as E_nm E_ix. subst nm ix.
        rewrite EP in RP. rewrite EI in RI.
        split; [lia|]. exists (A_G_NAMES + 8 * Z.of_nat j).
        split; [exact RP|]. split; [unfold A_G_NAMES; lia|]. split; [|exact RI].
        destruct (GN j Hj) as (rest & RB & _).
        split; [|apply gname_nonul; lia].
        replace (gname (Z.of_nat j) ++ zb 0 :: rest) with ((gname (Z.of_nat j) ++ [zb 0]) ++ rest)
          in RB by (rewrite <- app_assoc; reflexivity).
        apply bytes_at_app in RB. exact (proj1 RB).
      * assert (Hr : exists r, i = (60 + r)%nat /\ (r < 4)%nat) by (exists (i - 60)%nat; lia).
        destruct Hr as (r & -> & Hr).
        destruct (row_o r Hr) as (ET & EP & EI & EZ).
        rewrite ET in HN. injection HN as E_nm E_ix. subst nm ix.
        rewrite EP in RP. rewrite EI in RI.
        destruct (ODD (S r) ltac:(lia)) as (_ & OC).
        split; [lia|]. exists (nth (S r) odd_ptrs 0).
        split; [exact RP|]. split; [exact EZ|]. split; [exact OC | exact RI].
    + split; [exact E6|]. split; [exact E9|]. split; [exact E7 | exact E8].
  - intros k Hk. destruct (GN (Z.to_nat k) ltac:(lia)) as (rest & RB & RL).
    rewrite Z2Nat.id in RB, RL by lia. exists rest. split; [exact RB | exact RL].
  - intros i Hi. exact (proj1 (TR i Hi)).
Qed.
