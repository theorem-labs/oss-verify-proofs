(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Rep ECH_LibState.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition boxed (P : Prop) : Prop := P.
Ltac box H := lazymatch type of H with ?T => change T with (boxed T) in H end.
Ltac unbox H := unfold boxed in H.
(* [comment removed for export] *)
Ltac blia1 H1 := let T1 := fresh "T_" in pose proof H1 as T1; unfold boxed in T1; cbn; lia.
Ltac blia2 H1 H2 := let T1 := fresh "T_" in let T2 := fresh "T_" in pose proof H1 as T1; pose proof H2 as T2; unfold boxed in T1, T2; cbn; lia.
Ltac blia3 H1 H2 H3 := let T1 := fresh "T_" in let T2 := fresh "T_" in let T3 := fresh "T_" in
  pose proof H1 as T1; pose proof H2 as T2; pose proof H3 as T3; unfold boxed in T1, T2, T3; cbn; lia.

(* [comment removed for export] *)
Lemma bytes_at_ext_addr : forall m A A' bs, bytes_at usegs m A bs -> A = A' -> bytes_at usegs m A' bs.
Proof. intros m A A' bs H E. subst A'. exact H. Qed.
Lemma rw_cells_ext_addr : forall m A A' cs, rw_cells usegs m A cs -> A = A' -> rw_cells usegs m A' cs.
Proof. intros m A A' cs H E. subst A'. exact H. Qed.

(* [comment removed for export] *)
Lemma nodup_ids_app_ne : forall (l1 l2 : list block) b1 b2,
  List.NoDup (map blk_id (l1 ++ l2)) -> In b1 l1 -> In b2 l2 -> blk_id b1 <> blk_id b2.
Proof.
  induction l1 as [|c l1 IH]; intros l2 b1 b2 ND H1 H2; [destruct H1|]. cbn in ND. inversion ND as [|x l NI ND']; subst.
  destruct H1 as [->|H1]; [| exact (IH _ _ _ ND' H1 H2)].
  intros E. apply NI. rewrite map_app. apply in_or_app. right. rewrite E. apply in_map. exact H2.
Qed.

Lemma nodup_ids_cons_ne : forall (b0 : block) (l : list block) b,
  List.NoDup (map blk_id (b0 :: l)) -> In b l -> blk_id b0 <> blk_id b.
Proof. intros b0 l b ND Hb. apply (nodup_ids_app_ne [b0] l); [exact ND| left; reflexivity| exact Hb]. Qed.

Lemma perm_in_rest : forall (Fr L' L : list block) b, Permutation (Fr ++ L') L -> In b L -> ~ In b Fr -> In b L'.
Proof.
  intros Fr L' L b P HI NF. apply Permutation_sym in P. pose proof (Permutation_in _ P HI) as K. apply in_app_or in K. destruct K as [K|K]; [contradiction| exact K].
Qed.

(* [comment removed for export] *)
Lemma img_find_segment_none : forall z n, 1 <= n -> (z + n <= 0x10000 \/ 0x358000 <= z) ->
  find_segment usegs z n = None.
Proof.
  intros z n Hn Hz. unfold usegs, RefMemImage.Ref.loaded_segments, Ubsan.M.loaded_segments, Ubsan.Ubsan_loaded_segments. cbn [find_segment].
  replace (Z.of_N (seg_base Ubsan.Ubsan_segment_000)) with 65536%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Ubsan.Ubsan_segment_000)) with 860160%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Ubsan.Ubsan_segment_001)) with 925696%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Ubsan.Ubsan_segment_001)) with 1978368%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Ubsan.Ubsan_segment_002)) with 2904064%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Ubsan.Ubsan_segment_002)) with 380928%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Ubsan.Ubsan_segment_003)) with 3284992%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Ubsan.Ubsan_segment_003)) with 221184%Z by (vm_compute; reflexivity).
  destruct (Z.leb_spec0 65536 z); destruct (Z.leb_spec0 (z + n) (65536 + 860160)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 925696 z); destruct (Z.leb_spec0 (z + n) (925696 + 1978368)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 2904064 z); destruct (Z.leb_spec0 (z + n) (2904064 + 380928)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 3284992 z); destruct (Z.leb_spec0 (z + n) (3284992 + 221184)); cbn [andb]; try lia.
  all: reflexivity.
Qed.

Lemma wr_at_bytes_off_image : forall m A n,
  wr_at usegs m A n -> 0 <= n -> (A + n <= 0x10000 \/ 0x358000 <= A) ->
  exists junk, Z.of_nat (length junk) = n /\ bytes_at usegs m A junk.
Proof.
  intros m A n (HA & HN & W) Hn OFF.
  exists (map (fun i => match m (wa (A + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 (Z.to_nat n))).
  rewrite length_map, length_seq. split; [lia|].
  split; [exact HA|]. split; [rewrite length_map, length_seq; lia|].
  intros i Hi. rewrite length_map, length_seq in Hi.
  rewrite nth_error_map, nth_error_seq. destruct (PeanoNat.Nat.ltb_spec0 i (Z.to_nat n)); [| lia]. cbn [option_map Nat.add].
  specialize (W (Z.of_nat i) ltac:(lia)). unfold wview in W. unfold mrd, wa in *.
  destruct (m (Z_to_bv 64 (A + Z.of_nat i))) as [b|] eqn:E; [reflexivity|].
  exfalso. apply W. rewrite unsigned_lit by lia. rewrite img_find_segment_none by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma img_mrd_overlay : forall m (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x358000 <= bv_unsigned x) -> mrd usegs m x = m x.
Proof.
  intros m x Hx. unfold mrd. destruct (m x); [reflexivity|]. unfold seg_rom, memory_read.
  rewrite img_find_segment_none; [reflexivity| cbn; lia| cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma rw_cells_same_raw : forall m m' A cs a,
  rw_cells usegs m A cs -> rw_cells usegs m' A cs -> (A + Z.of_nat (cells_size cs) <= 0x10000 \/ 0x358000 <= A) ->
  A <= a < A + Z.of_nat (cells_size cs) -> m' (wa a) = m (wa a).
Proof.
  intros m m' A cs a [[W1 B1] _] [[W2 B2] _] OFF Ha.
  pose proof (cells_bytes_length cs W1) as CL.
  destruct B1 as (HA & HL & R1). destruct B2 as (_ & _ & R2).
  specialize (R1 (Z.to_nat (a - A)) ltac:(rewrite CL; lia)). specialize (R2 (Z.to_nat (a - A)) ltac:(rewrite CL; lia)).
  rewrite Z2Nat.id in R1, R2 by lia. replace (A + (a - A)) with a in R1, R2 by lia.
  rewrite img_mrd_overlay in R1 by (unfold wa; rewrite unsigned_lit by lia; lia).
  rewrite img_mrd_overlay in R2 by (unfold wa; rewrite unsigned_lit by lia; lia).
  congruence.
Qed.

(* [comment removed for export] *)
Lemma xpres_of_munch_eq : forall LB SP X W m m',
  munch W m m' -> wmono usegs m m' ->
  (forall a, 0 <= a < 2^64 -> xclient LB SP X a -> outside W a \/ m' (wa a) = m (wa a)) ->
  xpres LB SP X m m'.
Proof.
  intros LB SP X W m m' MU WM HO a Ha HC. split.
  - destruct (HO a Ha HC) as [O|E]; [| exact E]. unfold wa. apply MU. rewrite unsigned_lit by lia. exact O.
  - intros Hw. apply WM. exact Hw.
Qed.

(* [comment removed for export] *)
Lemma relro_lib_munch : forall W m m',
  ECH_LibState.relro_lib m -> munch W m m' -> Forall (fun iv : Z * Z => snd iv <= RELRO_LO \/ RELRO_HI <= fst iv) W -> ECH_LibState.relro_lib m'.
Proof.
  intros W m m' RL MU FW a Ha Hs. unfold wa. rewrite MU; [apply RL; assumption|].
  rewrite unsigned_lit by (unfold RELRO_LO, RELRO_HI in Ha; lia).
  clear MU RL. induction W as [|[lo hi] W IH]; [exact I|]. cbn. split; [| apply IH; exact (Forall_inv_tail FW)].
  pose proof (Forall_inv FW) as K. cbn in K. lia.
Qed.

Section HCW.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HH : heap_sr_hyps H.

  (* [comment removed for export] *)
  Lemma perm_rest_id_ne : forall s m (Fr L' L : list block) b b',
    hs_RHEAP H s L m -> Permutation (Fr ++ L') L -> In b L' -> In b' Fr -> blk_id b <> blk_id b'.
  Proof.
    intros s m Fr L' L b b' HP P Hb Hb'. pose proof (HH_RHEAP_blocks_nodup H HH _ _ _ HP) as ND.
    assert (ND' : List.NoDup (map blk_id (Fr ++ L'))).
    { eapply Permutation_NoDup; [| exact ND]. apply Permutation_map. apply Permutation_sym. exact P. }
    intros E. eapply (nodup_ids_app_ne Fr L' b' b ND' Hb' Hb). symmetry. exact E.
  Qed.

  Lemma perm_rest_sub_remove : forall s m (Fr L' L : list block) q A n,
    hs_RHEAP H s L m -> Permutation (Fr ++ L') L -> In (q, A, n) Fr ->
    forall b, In b L' -> In b (hs_lb_remove H q L).
  Proof.
    intros s m Fr L' L q A n HP P Hq b Hb.
    assert (HIN : In (q, A, n) L) by (eapply Permutation_in; [exact P| apply in_or_app; left; exact Hq]).
    apply (proj2 (proj2 (proj2 (lb_remove_exact H HH q A n L (HH_RHEAP_blocks_nodup H HH _ _ _ HP) HIN)) b)).
    split; [eapply Permutation_in; [exact P| apply in_or_app; right; exact Hb]|].
    exact (perm_rest_id_ne s m Fr L' L b (q, A, n) HP P Hb Hq).
  Qed.

  (* [comment removed for export] *)
  Lemma xpres_of_munch_block : forall s LB m0 m m' SP X W hb,
    hs_RHEAP H s LB m0 -> In hb LB -> hceil <= SP ->
    munch W m m' -> wmono usegs m m' ->
    Forall (fun iv : Z * Z => (hceil <= fst iv /\ snd iv <= SP)
                              \/ (blk_addr hb <= fst iv /\ snd iv <= blk_addr hb + blk_size hb)
                              \/ (forall a, fst iv <= a < snd iv -> rin_ivs X a)) W ->
    xpres (hs_lb_remove H (blk_id hb) LB) SP X m m'.
  Proof.
    intros s LB m0 m m' SP X W hb HP HIN CE MU WM FW. hcb.
    destruct hb as [[q A] n]. cbn [blk_addr blk_size blk_id fst snd] in *.
    pose proof (lb_remove_exact H HH q A n LB (HH_RHEAP_blocks_nodup H HH _ _ _ HP) HIN) as (_ & _ & RM).
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP HIN) as BR. cbn [blk_addr blk_size fst snd] in BR. destruct BR as (B1 & B2 & B3 & B4 & B5).
    eapply xpres_of_munch_gen; [exact MU| exact WM|].
    intros a Ha [HC HX].
    assert (OUTB : forall b, In b (hs_lb_remove H q LB) -> blk_addr b <= a < blk_addr b + blk_size b -> a + 1 <= A \/ A + n <= a).
    { intros b Hb Hr. destruct (proj1 (RM b) Hb) as [HbL NE].
      pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ b (q, A, n) HP HbL HIN NE) as D. cbn [blk_addr blk_size fst snd] in D. lia. }
    clear MU WM. induction W as [|[lo hi] W IH]; [exact I|]. cbn.
    pose proof (Forall_inv FW) as K1. cbn in K1.
    split; [| apply IH; apply (Forall_inv_tail FW)].
    destruct K1 as [[K1 K2]|[[K1 K2]|K1]].
    - destruct HC as [HC|[[HC _]|(b & Hb & Hr)]]; [lia| lia|].
      destruct (proj1 (RM b) Hb) as [HbL _]. pose proof (HH_blocks_below H HH _ _ _ HP b HbL). lia.
    - destruct HC as [HC|[[[HC1 HC2] _]|(b & Hb & Hr)]]; [lia| lia|].
      pose proof (OUTB b Hb Hr). lia.
    - intros R. apply HX. apply K1. exact R.
  Qed.

  (* [comment removed for export] *)
  Lemma SKobj_frame : forall LB LB' SP m m' a K,
    SKobj LB m a K -> (forall b, In b (blocks_SK a K) -> In b LB') -> xpres LB' SP [] m m' -> SKobj LB' m' a K.
  Proof.
    intros LB LB' SP m m' a K SO KEEP XP.
    destruct SO as ((pad & PL & HDR) & POS & HIN & NC & CAP & SRT & EL & DAT).
    pose proof (rw_cells_bound _ _ _ _ HDR) as HB. unfold sk_hdr_cells in HB. cbn [cells_size csize Nat.add] in HB.
    assert (HIN' : In (sk_id K, a, SK_SIZE) LB') by (apply KEEP; left; reflexivity).
    unfold SKobj. split.
    { exists pad. split; [exact PL|]. eapply xpres_rw_cells'; [exact XP| exact HDR| | constructor].
      right; right. exists (sk_id K, a, SK_SIZE). split; [exact HIN'|]. unfold sk_hdr_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold SK_SIZE. lia. }
    split; [exact POS|]. split; [exact HIN'|]. split; [exact NC|]. split; [exact CAP|]. split; [exact SRT|]. split; [exact EL|].
    destruct DAT as [D0|(D1 & D2 & D3 & D4 & AR & junk & JK)]; [left; exact D0| right].
    assert (DIN' : In (sk_did K, sk_data K, 8 * sk_cap K) LB').
    { apply KEEP. unfold blocks_SK. replace (sk_cap K =? 0) with false by (symmetry; apply Z.eqb_neq; lia). right. left. reflexivity. }
    pose proof (u64arr_bound _ _ _ _ AR) as ARB. rewrite length_map in ARB. unfold sk_num, zlength in NC.
    split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [exact DIN'|]. split.
    - eapply xpres_u64arr; [exact XP| exact AR|]. split; [| constructor]. right; right. exists (sk_did K, sk_data K, 8 * sk_cap K). split; [exact DIN'|].
      cbn [blk_addr blk_size fst snd]. rewrite ?length_map. lia.
    - exists junk. eapply xpres_rw_cells'; [exact XP| exact JK| | constructor]. right; right. exists (sk_did K, sk_data K, 8 * sk_cap K). split; [exact DIN'|].
      cbn [blk_addr blk_size fst snd cells_size csize]. unfold sk_num, zlength. rewrite Nat.add_0_r, Z2Nat.id by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma SKobj_frameX : forall LB LB' SP X m m' a K,
    SKobj LB m a K -> (forall b, In b (blocks_SK a K) -> In b LB') -> xpres LB' SP X m m' ->
    (forall b, In b (blocks_SK a K) -> Forall (fun iv : Z * Z => blk_addr b + blk_size b <= fst iv \/ snd iv <= blk_addr b) X) ->
    SKobj LB' m' a K.
  Proof.
    intros LB LB' SP X m m' a K SO KEEP XP AVOID.
    destruct SO as ((pad & PL & HDR) & POS & HIN & NC & CAP & SRT & EL & DAT).
    pose proof (rw_cells_bound _ _ _ _ HDR) as HB. unfold sk_hdr_cells in HB. cbn [cells_size csize Nat.add] in HB.
    assert (HIN' : In (sk_id K, a, SK_SIZE) LB') by (apply KEEP; left; reflexivity).
    pose proof (AVOID _ ltac:(left; reflexivity)) as AVH. cbn [blk_addr blk_size fst snd] in AVH.
    assert (FX : forall A n, a <= A -> A + n <= a + SK_SIZE -> Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) X).
    { intros A n H1 H2. eapply Forall_impl; [| exact AVH]. intros [lo' hi'] K0. cbn in K0 |- *. lia. }
    unfold SKobj. split.
    { exists pad. split; [exact PL|]. eapply xpres_rw_cells'; [exact XP| exact HDR| |].
      - right; right. exists (sk_id K, a, SK_SIZE). split; [exact HIN'|]. unfold sk_hdr_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold SK_SIZE. lia.
      - apply FX; [lia|]. unfold sk_hdr_cells. cbn [cells_size csize Nat.add]. unfold SK_SIZE. lia. }
    split; [exact POS|]. split; [exact HIN'|]. split; [exact NC|]. split; [exact CAP|]. split; [exact SRT|]. split; [exact EL|].
    destruct DAT as [D0|(D1 & D2 & D3 & D4 & AR & junk & JK)]; [left; exact D0| right].
    assert (DINB : In (sk_did K, sk_data K, 8 * sk_cap K) (blocks_SK a K)).
    { unfold blocks_SK. replace (sk_cap K =? 0) with false by (symmetry; apply Z.eqb_neq; lia). right. left. reflexivity. }
    assert (DIN' : In (sk_did K, sk_data K, 8 * sk_cap K) LB') by (apply KEEP; exact DINB).
    pose proof (AVOID _ DINB) as AVD. cbn [blk_addr blk_size fst snd] in AVD.
    assert (FXD : forall A n, sk_data K <= A -> A + n <= sk_data K + 8 * sk_cap K -> Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) X).
    { intros A n H1 H2. eapply Forall_impl; [| exact AVD]. intros [lo' hi'] K0. cbn in K0 |- *. lia. }
    pose proof (u64arr_bound _ _ _ _ AR) as ARB. rewrite length_map in ARB. unfold sk_num, zlength in NC.
    split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [exact DIN'|]. split.
    - eapply xpres_u64arr; [exact XP| exact AR|]. split.
      + right; right. exists (sk_did K, sk_data K, 8 * sk_cap K). split; [exact DIN'|]. cbn [blk_addr blk_size fst snd]. rewrite ?length_map. lia.
      + rewrite ?length_map. apply FXD; lia.
    - exists junk. eapply xpres_rw_cells'; [exact XP| exact JK| |].
      + right; right. exists (sk_did K, sk_data K, 8 * sk_cap K). split; [exact DIN'|].
        cbn [blk_addr blk_size fst snd cells_size csize]. unfold sk_num, zlength. rewrite Nat.add_0_r, Z2Nat.id by lia. lia.
      + cbn [cells_size csize]. unfold sk_num, zlength. rewrite Nat.add_0_r, Z2Nat.id by lia. apply FXD; lia.
  Qed.

  Lemma SKobj_owned : forall LB m a K b, SKobj LB m a K -> In b (blocks_SK a K) -> In b LB.
  Proof.
    intros LB m a K b SO Hb. destruct SO as (_ & _ & HIN & NC & _ & _ & _ & DAT). unfold blocks_SK in Hb.
    destruct Hb as [<-|Hb]; [exact HIN|].
    destruct DAT as [[C0 _]|(D1 & _ & _ & DIN & _)].
    - rewrite C0 in Hb. cbn in Hb. destruct Hb.
    - replace (sk_cap K =? 0) with false in Hb by (symmetry; apply Z.eqb_neq; lia). destruct Hb as [<-|[]]. exact DIN.
  Qed.
End HCW.
