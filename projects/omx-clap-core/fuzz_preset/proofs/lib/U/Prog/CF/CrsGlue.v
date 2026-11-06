(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v; 64 of its 422 lines of code are new or changed and 670 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/TxGlue.v, with its module paths and module names changed; 647 of its 739 lines of code are new or changed and 330 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/U/Prog/WriterRet.v, with its module paths and module names changed; 702 of its 749 lines of code are new or changed and 692 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/pj_write.v, with its module paths and module names changed; 496 of its 536 lines of code are new or changed and 709 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/ReaderKB.v, with its module paths and module names changed; 101 of its 268 lines of code are new or changed and 369 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import check_reject_clean_starved_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Lemma cg_vm_self : forall md, md = with_vmmaps (m_vmmaps md) md.
Proof. intros md. destruct md as [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma cg_vm_twice : forall v1 v2 md, with_vmmaps v2 (with_vmmaps v1 md) = with_vmmaps v2 md.
Proof. intros v1 v2 md. destruct md as [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma cg_pairwise_in : forall {T : Type} (R : T -> T -> Prop) (l : list T) x y,
  pairwise R l -> In x l -> In y l -> x <> y -> R x y \/ R y x.
Proof.
  intros T R l. induction l as [|h l IH]; intros x y Hp Hx Hy Hne; cbn in *; [contradiction|].
  destruct Hp as [H1 H2]. destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
  - contradiction.
  - left. apply H1. exact Hy.
  - right. apply H1. exact Hx.
  - apply IH; assumption.
Qed.

Lemma cg_writable_munch : forall segs W m m' a, munch W m m' -> 0 <= a < 2 ^ 64 -> outside W a ->
  (writable_at segs m a <-> writable_at segs m' a).
Proof.
  intros segs W m m' a H Ha Ho. unfold writable_at, wview. rewrite (H (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit by lia. exact Ho.
Qed.

Lemma cg_fs_some : forall segs a n s, find_segment segs a n = Some s ->
  In s segs /\ Z.of_N (seg_base s) <= a /\ a + n <= Z.of_N (seg_base s) + Z.of_N (seg_size s).
Proof.
  induction segs as [|s0 segs IH]; intros a n s H; cbn in H; [discriminate|].
  destruct (Z.of_N (seg_base s0) <=? a) eqn:E1; destruct (a + n <=? Z.of_N (seg_base s0) + Z.of_N (seg_size s0)) eqn:E2;
    cbn in H;
    try (destruct (IH _ _ _ H) as (I1 & I2 & I3); split; [right; exact I1 | split; assumption]).
  inversion H; subst. apply Z.leb_le in E1. apply Z.leb_le in E2. split; [left; reflexivity | split; assumption].
Qed.

Lemma cg_rsegs_top : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 2 ^ 33) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cg_seg_top : forall s, In s rsegs -> Z.of_N (seg_base s) + Z.of_N (seg_size s) <= 2 ^ 33.
Proof. intros s H. pose proof cg_rsegs_top as T. rewrite forallb_forall in T. apply Z.leb_le. exact (T s H). Qed.

Lemma cg_high_nofs : forall a, 2 ^ 33 <= a -> find_segment rsegs a 1 = None.
Proof.
  intros a Ha. destruct (find_segment rsegs a 1) as [s|] eqn:E; [|reflexivity].
  destruct (cg_fs_some _ _ _ _ E) as (Hin & H1 & H2). pose proof (cg_seg_top s Hin). lia.
Qed.

Section KB.
Context {fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEG : ms_segs B = rsegs.

Lemma cg_ceil : 2 ^ 46 <= alloc_ceiling < 2 ^ 47.
Proof. pose proof (@OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_val rc) as H. lia. Qed.

Lemma cg_img_bound : forall a, in_img B a -> 0 <= a < 2 ^ 33.
Proof.
  intros a (_ & s & Hs & H1 & H2). rewrite SEG in Hs. unfold segments_reserved in Hs.
  apply in_map_iff in Hs as (s0 & <- & Hin). pose proof (cg_seg_top s0 Hin) as T.
  unfold segment_reservation in H1, H2. cbn [fst snd] in H1, H2.
  rewrite !Z_to_bv_unsigned in H1, H2. unfold bv_wrap in H1, H2. change (bv_modulus 64) with (2 ^ 64) in H1, H2.
  unfold page_round_down_Z, page_round_up_Z, page_size in H1, H2.
  assert (0 <= Z.of_N (seg_base s0)) by lia. assert (0 <= Z.of_N (seg_size s0)) by lia.
  split; [pose proof (Z.mod_pos_bound (Z.of_N (seg_base s0) / 4096 * 4096) (2 ^ 64)); lia|].
  rewrite Z_to_bv_unsigned in H2. unfold bv_wrap in H2. change (bv_modulus 64) with (2 ^ 64) in H2.
  Z.div_mod_to_equations. lia.
Qed.

Lemma cg_blk_of_user : forall L A p k, In (p, k) (user_blocks A) -> In (ptr_addr L p, k) (blocks L A).
Proof. intros L A p k H. unfold blocks. apply (in_map (fun b => (ptr_addr L (fst b), snd b))) in H. exact H. Qed.

Lemma cg_blk_user : forall L A a k, In (a, k) (blocks L A) -> exists p, In (p, k) (user_blocks A) /\ ptr_addr L p = a.
Proof.
  intros L A a k Hin. unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & E & Hp). cbn [fst snd] in E.
  injection E as E1 E2. subst k'. exists p. split; assumption.
Qed.

Lemma cg_blk_facts : forall L A mem md a k, aa_MR API L A mem md -> In (a, k) (blocks L A) ->
  4096 <= a /\ a + k <= alloc_ceiling /\
  (forall i, 0 <= i < k -> present mem (a + i) /\ ~ owned B L A (a + i)).
Proof.
  intros L A mem md a k HM Hin. destruct (cg_blk_user L A a k Hin) as (p & Hp & <-).
  destruct (mr_blocks_range B _ (aa_laws API) L A mem md p k HM Hp) as [H1 H2]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (mr_blocks B _ (aa_laws API) L A mem md p k i HM Hp Hi) as (P & _ & _ & N). split; assumption.
Qed.

Lemma cg_word_keep : forall m m' a v, word_mem (ms_segs B) m a v ->
  (forall k, 0 <= k < 8 -> mbyte (ms_segs B) m' (a + k) = mbyte (ms_segs B) m (a + k)) -> word_mem (ms_segs B) m' a v.
Proof. intros m m' a v H K k Hk. rewrite K by lia. apply H. exact Hk. Qed.

Lemma cg_ledger_keep : forall L A m m' Lam peak cnt fail, ledger B L A m Lam peak cnt fail ->
  (forall a, alloc_statics a -> mbyte (ms_segs B) m' a = mbyte (ms_segs B) m a) ->
  (forall a k i, In (a, k) Lam -> 0 <= i < 8 -> mbyte (ms_segs B) m' (a - 16 + i) = mbyte (ms_segs B) m (a - 16 + i)) ->
  ledger B L A m' Lam peak cnt fail.
Proof.
  intros L A m m' Lam peak cnt fail (AW & R1 & R2 & R3 & ND & FA) HS HH.
  destruct AW as (W1 & W2 & W3 & W4).
  split; [|split; [exact R1|split; [exact R2|split; [exact R3|split; [exact ND|]]]]].
  - split; [|split; [|split]]; eapply cg_word_keep; try eassumption; intros k Hk; apply HS;
      unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL; lia.
  - rewrite Forall_forall in FA |- *. intros [a k] Hin. specialize (FA _ Hin). destruct FA as (Hk & Hb & Hw & Hn).
    cbn [fst snd] in *. split; [exact Hk|]. split; [exact Hb|]. split; [|exact Hn].
    eapply cg_word_keep; [exact Hw|]. intros j Hj. apply (HH a k j Hin Hj).
Qed.

Lemma cg_ledger_fail : forall L A m m' Lam peak cnt fail fail', ledger B L A m Lam peak cnt fail ->
  (forall a, (G_LIVE <= a < G_LIVE + 8 \/ G_PEAK <= a < G_PEAK + 8 \/ G_COUNT <= a < G_COUNT + 8) ->
     mbyte (ms_segs B) m' a = mbyte (ms_segs B) m a) ->
  (forall a k i, In (a, k) Lam -> 0 <= i < 8 -> mbyte (ms_segs B) m' (a - 16 + i) = mbyte (ms_segs B) m (a - 16 + i)) ->
  word_mem (ms_segs B) m' G_FAIL fail' -> 0 <= fail' < 2 ^ 64 ->
  ledger B L A m' Lam peak cnt fail'.
Proof.
  intros L A m m' Lam peak cnt fail fail' (AW & R1 & R2 & R3 & ND & FA) HS HH HF HfR.
  destruct AW as (W1 & W2 & W3 & W4).
  split; [|split; [exact R1|split; [exact R2|split; [exact HfR|split; [exact ND|]]]]].
  - split; [|split; [|split]]; try exact HF; eapply cg_word_keep; try eassumption; intros k Hk; apply HS;
      unfold G_LIVE, G_PEAK, G_COUNT; lia.
  - rewrite Forall_forall in FA |- *. intros [a k] Hin. specialize (FA _ Hin). destruct FA as (Hk & Hb & Hw & Hn).
    cbn [fst snd] in *. split; [exact Hk|]. split; [exact Hb|]. split; [|exact Hn].
    eapply cg_word_keep; [exact Hw|]. intros j Hj. apply (HH a k j Hin Hj).
Qed.

Lemma cg_auxv_keep : forall sec lo mem mem', auxv_pre B sec lo mem ->
  (forall i, 0 <= i < 8 -> mbyte (ms_segs B) mem' (ms_libc B + 8 + i) = mbyte (ms_segs B) mem (ms_libc B + 8 + i)) ->
  (forall a, lo <= a < 2 ^ 63 -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a) ->
  auxv_pre B sec lo mem'.
Proof.
  intros sec lo mem mem' (av & ar & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10) KL KH.
  exists av, ar.
  split; [eapply cg_word_keep; [exact H1|]; intros k Hk; apply KL; exact Hk|].
  split; [intros k Hk; eapply cg_word_keep; [apply H2; exact Hk|]; intros j Hj; apply KH; lia|].
  split; [eapply cg_word_keep; [exact H3|]; intros j Hj; apply KH; lia|].
  split; [eapply cg_word_keep; [exact H4|]; intros j Hj; apply KH; lia|].
  repeat split; lia.
Qed.

Lemma cg_layout_trans : forall A L L1 A1 L2, layout_le A L L1 -> layout_le A1 L1 L2 ->
  (length (st_regions A) <= length (st_regions A1))%nat -> layout_le A L L2.
Proof.
  intros A L L1 A1 L2 (C1 & S1 & B1 & R1) (C2 & S2 & B2 & R2) HL.
  split; [congruence|]. split; [congruence|]. split; [congruence|].
  intros r Hr. rewrite R2 by lia. apply R1. exact Hr.
Qed.

Lemma rp_of_A : forall K L A regs mem md E mem1 W regsF,
  aa_MR API L A mem1 md -> WF A -> bounded A -> regs_preserved regs regsF ->
  munch W mem mem1 -> wmono (ms_segs B) mem mem1 ->
  (forall a, scratch_k B K regs a -> writable_at (ms_segs B) mem a) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ scratch_k B K regs x -> ~ E x -> outside W x) ->
  (forall i, 0 <= i < 8 -> outside W (ms_libc B + 8 + i)) -> 0 <= ms_libc B + 8 -> ms_libc B + 16 <= 2 ^ 64 ->
  (forall p n i, In (p, n) (user_blocks A) -> 0 <= i < n -> ~ E (ptr_addr L p + i) ->
     0 <= ptr_addr L p + i < 2 ^ 64 /\ outside W (ptr_addr L p + i)) ->
  rpost B API K L A regs mem md E (fun _ _ => False) L A regsF mem1 md.
Proof.
  intros K L A regs mem md E mem1 W regsF HM HWF HB RP MU WM HSW HE HL HL1 HL2 HP.
  pose proof cg_ceil as HC.
  split; [exact HM|]. split; [exact HWF|]. split; [exact HB|]. split; [apply layout_le_refl|].
  split; [tauto|].
  split; [intros _ i Hi; apply (MemNorm.mbyte_munch _ W); [exact MU | lia | apply HL; exact Hi]|].
  split; [lia|].
  split; [intros p n Hp _; exact Hp|].
  split; [reflexivity|].
  split; [exact RP|].
  split; [exists (m_vmmaps md); apply cg_vm_self|].
  split.
  { intros a Ha Hs He. assert (Ho : outside W a) by (apply HE; [lia | exact Hs | exact He]).
    split; [apply (MemNorm.mbyte_munch _ W); [exact MU | lia | exact Ho] | apply (cg_writable_munch _ W); [exact MU | lia | exact Ho]]. }
  split.
  { intros a Ha _ Hs He. pose proof (cg_img_bound a Ha) as Hr.
    assert (Ho : outside W a) by (apply HE; [lia | exact Hs | exact He]).
    split; [apply (MemNorm.mbyte_munch _ W); [exact MU | lia | exact Ho] | apply (cg_writable_munch _ W); [exact MU | lia | exact Ho]]. }
  split.
  { intros p n i Hp _ Hi He. destruct (HP p n i Hp Hi He) as [Hr Ho].
    apply (MemNorm.mbyte_munch _ W); [exact MU | exact Hr | exact Ho]. }
  intros a Ha. unfold writable_at. apply WM. exact (HSW a Ha).
Qed.

Lemma rp_seq : forall K L A regs mem md E L1 A1 regsX mem1 md1 K2 regs2 E2 gone2 L2 A2 regs3 mem2 md2 regsF,
  rpost B API K L A regs mem md E (fun _ _ => False) L1 A1 regsX mem1 md1 ->
  rpost B API K2 L1 A1 regs2 mem1 md1 E2 gone2 L2 A2 regs3 mem2 md2 ->
  regs_preserved regs regsF ->
  spZ regs - K <= spZ regs2 - K2 -> spZ regs2 <= spZ regs -> alloc_ceiling + K <= spZ regs -> 0 <= K2 ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ scratch_k B K regs a -> ~ E a -> ~ E2 a) ->
  (forall a, in_img B a -> ~ scratch_k B K regs a -> ~ E a -> ~ E2 a) ->
  (forall p n i, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A1) -> 0 <= i < n ->
     ~ E (ptr_addr L p + i) -> ~ E2 (ptr_addr L p + i)) ->
  (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A1) -> ~ gone2 (ptr_addr L p) n) ->
  (forall a, scratch_k B K regs a -> ~ scratch_k B K2 regs2 a -> ~ E2 a \/ writable_at (ms_segs B) mem2 a) ->
  rpost B API K L A regs mem md E (fun _ _ => False) L2 A2 regsF mem2 md2.
Proof.
  intros K L A regs mem md E L1 A1 regsX mem1 md1 K2 regs2 E2 gone2 L2 A2 regs3 mem2 md2 regsF R1 R2 RPF
    W1 W2 HC HK2 HE12 HI12 HB12 HG12 HW12.
  destruct R1 as (M1 & WF1 & B1 & Y1 & I1 & X1 & G1 & S1 & P1 & _ & D1 & H1 & IM1 & K1 & C1).
  destruct R2 as (M2 & WF2 & B2 & Y2 & I2 & X2 & G2 & S2 & P2 & _ & D2 & H2 & IM2 & K2' & C2).
  assert (NS : forall a, ~ scratch_k B K regs a -> ~ scratch_k B K2 regs2 a).
  { intros a Hn Hs. apply Hn. unfold scratch_k in *. destruct Hs as [Hs|Hs]; [left; lia | right; exact Hs]. }
  split; [exact M2|]. split; [exact WF2|]. split; [exact B2|].
  split; [exact (cg_layout_trans A L L1 A1 L2 Y1 Y2 G1)|].
  split; [intros H; apply I2, I1, H|].
  split.
  { intros HN i Hi. assert (HN1 : st_init_done A1 = false).
    { case_eq (st_init_done A1); intros E1; [rewrite (I2 E1) in HN; discriminate HN | reflexivity]. }
    rewrite (X2 HN i Hi). exact (X1 HN1 i Hi). }
  split; [lia|].
  split.
  { intros p n Hp _. assert (Hp1 : In (p, n) (user_blocks A1)) by (apply S1; [exact Hp | tauto]).
    apply S2; [exact Hp1|]. rewrite (P1 p n Hp Hp1). exact (HG12 p n Hp Hp1). }
  split.
  { intros p n Hp Hp2. assert (Hp1 : In (p, n) (user_blocks A1)) by (apply S1; [exact Hp | tauto]).
    rewrite (P2 p n Hp1 Hp2). exact (P1 p n Hp Hp1). }
  split; [exact RPF|].
  split.
  { destruct D1 as (v1 & E1). destruct D2 as (v2 & E2'). exists v2. rewrite E2', E1. apply cg_vm_twice. }
  split.
  { intros a Ha Hs He. destruct (H1 a Ha Hs He) as [Ea Wa].
    destruct (H2 a Ha (NS a Hs) (HE12 a Ha Hs He)) as [Eb Wb]. split; [congruence | tauto]. }
  split.
  { intros a Ha Hn Hs He. destruct (IM1 a Ha Hn Hs He) as [Ea Wa].
    destruct (IM2 a Ha Hn (NS a Hs) (HI12 a Ha Hs He)) as [Eb Wb]. split; [congruence | tauto]. }
  split.
  { intros p n i Hp Hp2 Hi He. assert (Hp1 : In (p, n) (user_blocks A1)) by (apply S1; [exact Hp | tauto]).
    pose proof (K2' p n i Hp1 Hp2 Hi) as Kb. rewrite (P1 p n Hp Hp1) in Kb.
    rewrite (Kb (HB12 p n i Hp Hp1 Hi He)). exact (K1 p n i Hp Hp1 Hi He). }
  intros a Ha.
  assert (Hd : scratch_k B K2 regs2 a \/ ~ scratch_k B K2 regs2 a) by (unfold scratch_k; lia).
  destruct Hd as [Hd|Hd]; [exact (C2 a Hd)|].
  destruct (HW12 a Ha Hd) as [He|Hw]; [|exact Hw].
  assert (Hst : spZ regs - K <= a < spZ regs).
  { unfold scratch_k in Ha, Hd. destruct Ha as [Ha|Ha]; [exact Ha | exfalso; apply Hd; right; exact Ha]. }
  pose proof (C1 a Ha) as Hw1.
  assert (Hr : alloc_ceiling <= a < 2 ^ 64).
  { pose proof (zr_word (getr regs 2)) as R. unfold inr64 in R. unfold spZ in Hst, HC. lia. }
  destruct (H2 a Hr Hd He) as [_ Wb]. apply Wb. exact Hw1.
Qed.

Lemma rp_regs : forall K L A regs mem md E gone L' A' regsX mem' md' regsF,
  rpost B API K L A regs mem md E gone L' A' regsX mem' md' -> regs_preserved regs regsF ->
  rpost B API K L A regs mem md E gone L' A' regsF mem' md'.
Proof.
  intros K L A regs mem md E gone L' A' regsX mem' md' regsF
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & _ & H11 & H12 & H13 & H14 & H15) RP.
  repeat (split; [eassumption|]). exact H15.
Qed.

Lemma rp_E : forall K L A regs mem md (E E' : Z -> Prop) gone L' A' regs' mem' md',
  rpost B API K L A regs mem md E gone L' A' regs' mem' md' -> (forall a, E a -> E' a) ->
  rpost B API K L A regs mem md E' gone L' A' regs' mem' md'.
Proof.
  intros K L A regs mem md E E' gone L' A' regs' mem' md'
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15) HE.
  repeat (split; [eassumption|]).
  split; [intros a Ha Hs He; apply H12; auto|].
  split; [intros a Ha Hn Hs He; apply H13; auto|].
  split; [intros p n i Hp Hp' Hi He; apply (H14 p n i); auto|].
  exact H15.
Qed.

Lemma rp_refl : forall K L A regs mem md E,
  call_pre_k B (aa_MR API) K L A regs mem md -> ms_libc B + 16 <= 2 ^ 64 -> 0 <= ms_libc B + 8 ->
  rpost B API K L A regs mem md E (fun _ _ => False) L A regs mem md.
Proof.
  intros K L A regs mem md E (HM & HWF & HB & _ & _ & _ & _ & HW & _ & HE & _) H1 H2.
  apply (rp_of_A K L A regs mem md E mem [] regs HM HWF HB).
  - intros r _. reflexivity.
  - apply munch_refl.
  - apply wmono_refl.
  - intros a [Ha|Ha]; [apply HW; exact Ha | apply HE; exact Ha].
  - intros. exact I.
  - intros. exact I.
  - exact H2.
  - exact H1.
  - intros p n i Hp Hi _. destruct (mr_blocks B _ (aa_laws API) L A mem md p n i HM Hp Hi) as (_ & R1 & R2 & _).
    pose proof cg_ceil. split; [lia | exact I].
Qed.

End KB.
