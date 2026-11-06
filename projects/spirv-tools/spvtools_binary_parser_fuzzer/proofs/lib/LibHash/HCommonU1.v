(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StoreOk MemSplit Hoare ShapeAlg SRealizes MmapSim
  RefMemcpyLib LibIface LibEff FPSteps SumMemsetLib SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib HRepFacts HStmts.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation SEGS := Ubsan.M.loaded_segments.

Lemma cellw_wb_other : forall M a (w : N) v (d : Z) bs,
  cellw SEGS M a w v -> 0 <= d < 2 ^ 64 -> d + Z.of_nat (length bs) <= 2 ^ 64 -> 0 <= a -> a + Z.of_N w <= 2 ^ 47 ->
  apart d (Z.of_nat (length bs)) a (Z.of_N w) ->
  cellw SEGS (wbytes M (Z_to_bv 64 d) bs) a w v.
Proof.
  intros M a w v d bs Hc Hd Hdl Ha Haw Hap.
  eapply cellw_agree; [exact Hc | | lia | lia].
  apply agree_on_wbytes_out; rewrite ?u64_of_Z; try lia; exact Hap.
Qed.

Lemma cellw_wb_other_c : forall M a (w : N) v (d : Z) bs,
  cellw SEGS M a w v ->
  (0 <= d < 2 ^ 64 /\ d + Z.of_nat (length bs) <= 2 ^ 64 /\ 0 <= a /\ a + Z.of_N w <= 2 ^ 47 /\
   apart d (Z.of_nat (length bs)) a (Z.of_N w)) ->
  cellw SEGS (wbytes M (Z_to_bv 64 d) bs) a w v.
Proof. intros M a w v d bs Hc (Hd & Hdl & Ha & Haw & Hap). exact (cellw_wb_other M a w v d bs Hc Hd Hdl Ha Haw Hap). Qed.

Lemma cellw_store_at : forall M a d (w : N) v v',
  d = a -> Z_to_bv 64 v' = Z_to_bv 64 v ->
  0 <= v < 2 ^ (8 * Z.of_N w) -> 0 <= a < 2 ^ 64 -> a + Z.of_N w <= 2 ^ 64 -> (w <= 8)%N ->
  cellw SEGS (wbytes M (Z_to_bv 64 d) (word_to_le_bytes (N.to_nat w) (Z_to_bv 64 v'))) a w v.
Proof. intros M a d w v v' -> -> Hv Ha Haw Hw. apply cellw_store; assumption. Qed.

Lemma defined_sub : forall M a n b k, defined M a n -> a <= b -> b + k <= a + n -> defined M b k.
Proof. intros M a n b k Hd Hab Hbk i Hi. replace (b + i) with (a + (b - a + i)) by lia. apply Hd. lia. Qed.
Lemma defined_pt : forall M a n x, defined M a n -> a <= x < a + n -> M (Z_to_bv 64 x) <> None.
Proof. intros M a n x Hd Hx. replace x with (a + (x - a)) by lia. apply Hd. lia. Qed.

Ltac cellpeel :=
  first
    [ apply cellw_store; [cbn; lia | lia | cbn; lia | cbn; lia]
    | apply cellw_store_at; [lia | first [reflexivity | f_equal; lia] | cbn; lia | lia | cbn; lia | cbn; lia]
    | tryif (apply cellw_wb_other_c;
            [ | rewrite ?length_N_to_le_bytes, ?repeat_length; unfold apart in *; try (change (Z.of_nat 8) with 8); try (change (Z.of_nat 4) with 4); cbn; lia ])
      then cellpeel
      else (apply cellw_wb_other;
      [ cellpeel | lia
      | rewrite ?length_N_to_le_bytes, ?repeat_length; try (change (Z.of_nat 8) with 8); try (change (Z.of_nat 4) with 4); lia
      | lia | cbn; lia
      | rewrite ?length_N_to_le_bytes, ?repeat_length; unfold apart in *; try (change (Z.of_nat 8) with 8); try (change (Z.of_nat 4) with 4); lia ])
    | assumption ].

Ltac postrun := evs; rewrite ?v_addi_Z by lia; rewrite ?Z.add_0_r, ?Z.add_opp_r.

Lemma land_1 : forall k, Z.land k 1 = k mod 2.
Proof. intros k. pose proof (Z.land_ones k 1 ltac:(lia)) as H. exact H. Qed.

Lemma bseq_pow2 : forall bc, In bc BSEQ -> bc <> 0 ->
  (bc = 2 /\ Z.land bc (bc - 1) = 0) \/ (3 <= bc < 2 ^ 31 /\ Z.land bc (bc - 1) <> 0).
Proof.
  intros bc Hin Hnz. unfold BSEQ in Hin.
  repeat (destruct Hin as [<-|Hin];
    [ first [ exfalso; lia | left; split; [reflexivity | reflexivity] | right; split; [lia | vm_compute; discriminate] ] |]).
  destruct Hin.
Qed.

Lemma ceiling_lt {AC : AllocCeiling} : alloc_ceiling < 2 ^ 47.
Proof. pose proof ac_bounds_lit. lia. Qed.

Lemma wview_high : forall M (x : word), 0x124000 <= bv_unsigned x -> wview SEGS M x = M x.
Proof.
  intros M x Hx. unfold wview. destruct (M x); [reflexivity|].
  unfold SEGS, Ubsan.M.loaded_segments, Ubsan.Ubsan_loaded_segments.
  cbn [find_segment seg_base seg_size Ubsan.Ubsan_segment_000 Ubsan.Ubsan_segment_001 Ubsan.Ubsan_segment_002 Ubsan.Ubsan_segment_003].
  repeat (match goal with |- context [if ?c then _ else _] =>
            replace c with false by (symmetry; apply Bool.andb_false_iff; right; apply Z.leb_gt; cbn; lia) end).
  reflexivity.
Qed.

Lemma testbit_mod_eq : forall a b k i, a mod 2 ^ k = b mod 2 ^ k -> 0 <= i < k -> Z.testbit a i = Z.testbit b i.
Proof.
  intros a b k i H Hi. rewrite <- (Z.mod_pow2_bits_low a k i), <- (Z.mod_pow2_bits_low b k i) by lia. rewrite H. reflexivity.
Qed.

Lemma Z_to_le_bytes_bits : forall n z z',
  (forall i, 0 <= i < 8 * Z.of_nat n -> Z.testbit z i = Z.testbit z' i) -> Z_to_le_bytes n z = Z_to_le_bytes n z'.
Proof.
  induction n as [|n IH]; intros z z' H; [reflexivity|]. cbn [Z_to_le_bytes]. f_equal.
  - apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap8_mod. apply Z.bits_inj'. intros i Hi.
    destruct (Z.lt_ge_cases i 8).
    + rewrite !Z.mod_pow2_bits_low by lia. apply H. lia.
    + rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
  - apply IH. intros i Hi. rewrite !Z.shiftr_spec by lia. apply H. lia.
Qed.

Lemma word_to_le_bytes_low : forall n v v', (n <= 8)%nat ->
  (forall i, 0 <= i < 8 * Z.of_nat n -> Z.testbit v i = Z.testbit v' i) ->
  word_to_le_bytes n (Z_to_bv 64 v) = word_to_le_bytes n (Z_to_bv 64 v').
Proof.
  intros n v v' Hn H. unfold word_to_le_bytes. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  apply Z_to_le_bytes_bits. intros i Hi. rewrite !Z.mod_pow2_bits_low by lia. apply H. lia.
Qed.

Lemma bv_swrap_mod : forall (n : N) z, bv_swrap n z mod 2 ^ Z.of_N n = z mod 2 ^ Z.of_N n.
Proof.
  intros n z. unfold bv_swrap, bv_wrap, bv_modulus.
  rewrite Zminus_mod, Z.mod_mod by lia. rewrite <- Zminus_mod.
  f_equal. lia.
Qed.

Lemma word_to_le_bytes_swrap : forall (w : N) v, (w <= 8)%N ->
  word_to_le_bytes (N.to_nat w) (Z_to_bv 64 (bv_swrap (8 * w) v)) = word_to_le_bytes (N.to_nat w) (Z_to_bv 64 v).
Proof.
  intros w v Hw. apply word_to_le_bytes_low; [lia|]. intros i Hi.
  apply (testbit_mod_eq _ _ (Z.of_N (8 * w))); [apply bv_swrap_mod | lia].
Qed.

Lemma sc_read_cellw_sx : forall E M (sa : saddr) (a : Z) (w : N) (v : Z) (e : expr),
  cellw SEGS M a w v -> (w <= 8)%N ->
  adenot E sa = Z_to_bv 64 a -> edenot E e = Z_to_bv 64 (bv_swrap (8 * w) v) ->
  sc_denot SEGS M E (SCReadBase sa (N.to_nat w) true e).
Proof.
  intros E M sa a w v e [Hv Hr] Hw Ha He. cbn [sc_denot].
  exists (word_to_le_bytes (N.to_nat w) (Z_to_bv 64 v)). rewrite Ha, He. split; [exact Hr|].
  unfold extz. rewrite bytes_le_N, N_nat_Z.
  assert (Hw64 : 2 ^ (8 * Z.of_N w) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  rewrite u64_of_Z by lia. rewrite Z.mod_small by lia.
  replace (8 * N.of_nat (N.to_nat w))%N with (8 * w)%N by lia. reflexivity.
Qed.

Lemma lapply_dels_keep : forall (ps : list Z) lv lv' q k,
  lapply lv (map LDel ps) lv' -> In (q, k) lv -> ~ In q ps -> In (q, k) lv'.
Proof.
  induction ps as [|p ps IH]; intros lv lv' q k HL Hin Hni; cbn in HL.
  - subst lv'. exact Hin.
  - destruct HL as (lv1 & Hd & HL). apply (IH lv1 lv' q k HL); [|intros H; apply Hni; right; exact H].
    apply (proj2 (Hd q k)). split; [exact Hin|]. intros ->. apply Hni. left. reflexivity.
Qed.

Lemma lapply_dels_keep' : forall {X : Type} (l : list (Z * X)) lv lv' q k,
  lapply lv (map (fun e => LDel (fst e)) l) lv' -> In (q, k) lv -> ~ In q (map fst l) -> In (q, k) lv'.
Proof.
  intros X l lv lv' q k HL Hin Hni. rewrite <- (map_map fst LDel) in HL.
  exact (lapply_dels_keep _ _ _ _ _ HL Hin Hni).
Qed.

Lemma lapply_dels_iff : forall (ps : list Z) lv lv' q k,
  lapply lv (map LDel ps) lv' -> (In (q, k) lv' <-> In (q, k) lv /\ ~ In q ps).
Proof.
  induction ps as [|p ps IH]; intros lv lv' q k HL; cbn in HL.
  - subst lv'. cbn. tauto.
  - destruct HL as (lv1 & Hd & HL). rewrite (IH lv1 lv' q k HL). unfold live_del in Hd. rewrite (Hd q k). cbn.
    split; [intros [[A B] C]; split; [exact A|]; intros [D|D]; [exact (B (eq_sym D)) | exact (C D)]
          | intros [A B]; split; [split; [exact A|]; intros D; apply B; left; symmetry; exact D | intros D; apply B; right; exact D]].
Qed.

Lemma lapply_dels_of_members : forall (ps : list Z) lv lv',
  ps <> [] -> (forall q k, In (q, k) lv' <-> In (q, k) lv /\ ~ In q ps) -> lapply lv (map LDel ps) lv'.
Proof.
  induction ps as [|p r IH]; intros lv lv' Hne HM; [exfalso; exact (Hne eq_refl)|]. cbn.
  destruct r as [|p2 r2].
  - exists lv'. split; [|reflexivity]. intros q k. rewrite (HM q k). cbn.
    split; [intros [A B]; split; [exact A|]; intros D; apply B; left; symmetry; exact D
          | intros [A B]; split; [exact A|]; intros [D|D]; [exact (B (eq_sym D)) | exact D]].
  - exists (List.filter (fun b => negb (fst b =? p)) lv). split.
    + intros q k. rewrite filter_In. cbn. rewrite Bool.negb_true_iff, Z.eqb_neq. tauto.
    + apply IH; [discriminate|]. intros q k. rewrite (HM q k), filter_In. cbn. rewrite Bool.negb_true_iff, Z.eqb_neq.
      split; [intros [A B]; split; [split; [exact A|]; intros D; apply B; left; symmetry; exact D | intros D; apply B; right; exact D]
            | intros [[A B] C]; split; [exact A|]; intros [D|D]; [exact (B (eq_sym D)) | exact (C D)]].
Qed.

Lemma lapply_dels_equiv : forall (ps ps' : list Z) lv lv',
  lapply lv (map LDel ps) lv' -> (forall q, In q ps <-> In q ps') -> lapply lv (map LDel ps') lv'.
Proof.
  intros ps ps' lv lv' HL Heq. destruct ps' as [|p' r'].
  - destruct ps as [|p0 r0]; [exact HL|]. exfalso. exact (proj1 (Heq p0) (or_introl eq_refl)).
  - apply lapply_dels_of_members; [discriminate|].
    intros q k. rewrite (lapply_dels_iff ps lv lv' q k HL), (Heq q). tauto.
Qed.

Section Common.
Context {AC : AllocCeiling}.
  Variable L : Layout.
  Variable MI : MallocIface SEGS L.
  Variable ST : StaticsIface SEGS L.

  Hypothesis HLimg_lo : forall a, in_ranges (ly_img L) a -> a < alloc_ceiling.
  Hypothesis HLrw_img : forall a, in_ranges (ly_rw L) a -> in_ranges (ly_img L) a.
  Hypothesis HLrelro_img : forall a, in_ranges (ly_relro L) a -> in_ranges (ly_img L) a.
  Hypothesis HLrw_relro : forall a, in_ranges (ly_rw L) a -> ~ in_ranges (ly_relro L) a.
  Hypothesis HLerr_rw : forall a, errno_win L a -> in_ranges (ly_rw L) a.

  Lemma live_facts : forall A M model p n, ainv MI A M model -> In (p, n) (live MI A) ->
    0 <= n /\ 0 < p /\ p + n <= alloc_ceiling /\ (forall a, p <= a < p + n -> ~ owned MI A a /\ M (Z_to_bv 64 a) <> None).
  Proof using AC L MI.
    intros A M model p n AI Hin. destruct (ai_live_block MI A M model p n AI Hin) as (Hn & _ & Hp & Hce & Hall).
    split; [exact Hn|]. split; [exact Hp|]. split; [exact Hce|].
    intros a Ha. destruct (Hall a Ha) as (Ho & _ & Hd). split; assumption.
  Qed.

  Lemma live_offimg : forall A M model p n a, ainv MI A M model -> In (p, n) (live MI A) ->
    p <= a < p + n -> ~ in_ranges (ly_img L) a.
  Proof using AC L MI.
    intros A M model p n a AI Hin Ha. destruct (ai_live_block MI A M model p n AI Hin) as (_ & _ & _ & _ & Hall).
    exact (proj1 (proj2 (Hall a Ha))).
  Qed.

  Lemma del_agree : forall A M M' p n lo hi a k,
    frame_eq (fun x => owned MI A x \/ (p <= x < p + n) \/ zwin lo hi x \/ errno_win L x) M M' ->
    (forall x, a <= x < a + k -> ~ owned MI A x) -> apart a k p n -> (a + k <= lo \/ hi <= a) ->
    0 <= a -> a + k < 2 ^ 64 ->
    (forall x, a <= x < a + k -> ~ in_ranges (ly_img L) x) ->
    agree_on M M' a k.
  Proof using AC L MI HLrw_img HLerr_rw.
    intros A M M' p n lo hi a k FR Hown Hap Hwin Ha Hak Hni i Hi. apply FR. rewrite u64_of_Z by lia.
    intros [Ho|[Hq|[Hw|He]]].
    - exact (Hown (a + i) ltac:(lia) Ho).
    - unfold apart in Hap. lia.
    - unfold zwin in Hw. lia.
    - exact (Hni (a + i) ltac:(lia) (HLrw_img _ (HLerr_rw _ He))).
  Qed.

  Lemma defined_of_stack_room : forall M sp S, 0x124000 <= sp - S -> 0 <= S -> sp <= 2 ^ 64 ->
    stack_room SEGS M sp S -> defined M (sp - S) S.
  Proof using.
    intros M sp S Hlo HS Hhi Hr i Hi. unfold stack_room in Hr.
    pose proof (store_ok_all SEGS M (Z.to_nat S) (Z_to_bv 64 (sp - S)) ltac:(rewrite u64_of_Z by lia; lia) Hr
                  (Z_to_bv 64 (sp - S + i)) ltac:(rewrite !u64_of_Z by lia; lia)) as Hw.
    rewrite wview_high in Hw by (rewrite u64_of_Z by lia; lia). exact Hw.
  Qed.

  Lemma stack_room_of_defined : forall M sp S, 0 <= sp - S -> sp < 2 ^ 64 -> 0 <= S ->
    defined M (sp - S) S -> stack_room SEGS M sp S.
  Proof using.
    intros M sp S H0 Hhi HS Hd. unfold stack_room. apply store_ok_of_defined; [lia | lia | exact Hd].
  Qed.

  Definition pres (l : list reg) (Rb R : bvmap 5 word) : Prop := forall r, In r l -> getr R r = getr Rb r.

  Lemma pres_trans : forall l R1 R2 R3, pres l R1 R2 -> pres l R2 R3 -> pres l R1 R3.
  Proof using. intros l R1 R2 R3 A B r Hr. rewrite (B r Hr). apply A, Hr. Qed.

  Lemma pres_kept : forall l Rb R R', (forall r, In r l -> In r callee_saved) -> pres l Rb R -> kept R R' -> pres l Rb R'.
  Proof using. intros l Rb R R' Hl HP HK r Hr. rewrite (HK r (Hl r Hr)). apply HP, Hr. Qed.

  Lemma sx_inv_via_eff : forall (s0 : LibIface.SX ST) (A A' : AS MI) M M' model (W : Z * Z) (F : Z -> Prop),
    sx_inv ST s0 M -> ainv MI A M model -> eff MI A A' M M' W F ->
    (forall a, owned MI A a -> ~ sx_region ST a) -> (forall a, errno_win L a -> ~ sx_region ST a) ->
    (forall a, F a -> ~ in_ranges (ly_img L) a) -> alloc_ceiling <= fst W ->
    sx_inv ST s0 M'.
  Proof using AC L MI ST HLimg_lo HLrw_img HLrelro_img HLrw_relro HLerr_rw.
    intros s0 A A' M M' model W F SX AI EF Hosx Hesx HF HW.
    pose proof ceiling_lt as Hcl.
    apply (sx_frame ST s0 M M' SX). intros a Ha.
    assert (Himg : in_ranges (ly_img L) (bv_unsigned a)).
    { destruct Ha as [Hs | Hr]; [exact (HLrw_img _ (sx_region_rw ST _ Hs)) | exact (HLrelro_img _ Hr)]. }
    pose proof (HLimg_lo _ Himg) as Hlt.
    apply (ef_frame _ _ _ _ _ _ _ _ _ EF). intros [Ho | [Ho' | [Hnm | [Hf | [Hw | He]]]]].
    - destruct Ha as [Hs | Hr]; [exact (Hosx _ Ho Hs)|].
      destruct (ai_owned_not_img_ro MI A M model _ AI Ho) as [Hrw | Hni]; [exact (HLrw_relro _ Hrw Hr) | exact (Hni Himg)].
    - destruct (ef_own _ _ _ _ _ _ _ _ _ EF _ Ho') as [Ho | [[Hni _] | Hf]].
      + destruct Ha as [Hs | Hr]; [exact (Hosx _ Ho Hs)|].
        destruct (ai_owned_not_img_ro MI A M model _ AI Ho) as [Hrw | Hni]; [exact (HLrw_relro _ Hrw Hr) | exact (Hni Himg)].
      + exact (Hni Himg).
      + exact (HF _ Hf Himg).
    - destruct Hnm as (Hni & _). exact (Hni Himg).
    - exact (HF _ Hf Himg).
    - unfold W_of in Hw. lia.
    - destruct Ha as [Hs | Hr]; [exact (Hesx _ He Hs)|]. exact (HLrw_relro _ (HLerr_rw _ He) Hr).
  Qed.

  Lemma img_ro_clear_via_eff : forall (A A' : AS MI) M M' model (W : Z * Z) (F : Z -> Prop),
    img_ro_clear L M -> ainv MI A M model -> eff MI A A' M M' W F ->
    (forall a, F a -> ~ in_ranges (ly_img L) a) -> alloc_ceiling <= fst W ->
    img_ro_clear L M'.
  Proof using AC L MI HLimg_lo HLerr_rw.
    intros A A' M M' model W F ROC AI EF HF HW.
    pose proof ceiling_lt as Hcl.
    eapply (img_ro_clear_frame L _ M M' ROC (ef_frame _ _ _ _ _ _ _ _ _ EF)).
    intros a Himg Hnrw. pose proof (HLimg_lo _ Himg) as Hlt.
    intros [Ho | [Ho' | [Hnm | [Hf | [Hw | He]]]]].
    - destruct (ai_owned_not_img_ro MI A M model _ AI Ho) as [Hrw | Hni]; [exact (Hnrw Hrw) | exact (Hni Himg)].
    - destruct (ef_own _ _ _ _ _ _ _ _ _ EF _ Ho') as [Ho | [[Hni _] | Hf]].
      + destruct (ai_owned_not_img_ro MI A M model _ AI Ho) as [Hrw | Hni]; [exact (Hnrw Hrw) | exact (Hni Himg)].
      + exact (Hni Himg).
      + exact (HF _ Hf Himg).
    - destruct Hnm as (Hni & _). exact (Hni Himg).
    - exact (HF _ Hf Himg).
    - unfold W_of in Hw. lia.
    - exact (Hnrw (HLerr_rw _ He)).
  Qed.

  Lemma img_ro_clear_store : forall M (d : Z) bs,
    img_ro_clear L M -> 0 <= d -> d + Z.of_nat (length bs) <= 2 ^ 64 ->
    (forall a, d <= a < d + Z.of_nat (length bs) -> ~ in_ranges (ly_img L) a) ->
    img_ro_clear L (wbytes M (Z_to_bv 64 d) bs).
  Proof using L.
    intros M d bs ROC Hd Hdl HF w Himg Hnrw. pose proof (u64_range w).
    destruct bs as [|b bs']; [exact (ROC w Himg Hnrw)|].
    assert (Hlen : 1 <= Z.of_nat (length (b :: bs'))) by (cbn [length]; lia).
    rewrite wbytes_outside; [exact (ROC w Himg Hnrw) | rewrite u64_of_Z by lia; lia |]. rewrite u64_of_Z by lia.
    destruct (Z.lt_ge_cases (bv_unsigned w) d); [left; lia|].
    destruct (Z.le_gt_cases (d + Z.of_nat (length (b :: bs'))) (bv_unsigned w)); [right; lia|].
    exfalso. exact (HF (bv_unsigned w) ltac:(lia) Himg).
  Qed.

  Section PerTable.
    Variables (NS : Z) (V : Type) (nval : mem -> Z -> V -> Prop).
    Hypothesis HNS : 24 <= NS.
    Hypothesis nval_agree : forall M M' p v, nval M p v -> agree_on M M' (p + 20) (NS - 20) -> 0 < p -> p + NS <= 2 ^ 47 -> nval M' p v.

  Lemma umapx_via_eff : forall (A A' : AS MI) M M' model obj bl bc ents (W : Z * Z) (F : Z -> Prop) top,
    umapx MI NS nval A M obj bl bc ents -> ainv MI A M model ->
    eff MI A A' M M' W F ->

    top <= obj -> snd W <= top -> alloc_ceiling <= top -> (forall i, 0 <= i < 40 -> ~ owned MI A (obj + i)) ->

    (forall a, umap_foot NS obj bl bc ents a -> ~ F a) ->

    alloc_ceiling <= fst W ->

    (forall p n, In (p, n) (umap_blocks NS bl bc ents) -> In (p, n) (live MI A) -> In (p, n) (live MI A')) ->
    umapx MI NS nval A' M' obj bl bc ents.
  Proof using AC L MI HLimg_lo HLrw_img HLerr_rw NS V nval HNS nval_agree.
    intros A A' M M' model obj bl bc ents W F top U AI EF Htop HW Hce Hown HF HWc Hlive.
    pose proof ceiling_lt as Hcl.
    eapply (umapx_agree SEGS L MI NS V nval nval_agree HNS A A' M M'); [exact U | | exact Hlive].
    intros a Ha. apply (ef_frame _ _ _ _ _ _ _ _ _ EF).
    assert (Hcases : (obj <= a < obj + 40 /\ M (Z_to_bv 64 a) <> None /\ ~ owned MI A a)
                     \/ (exists p n, In (p, n) (live MI A) /\ p <= a < p + n)).
    { destruct U as [HD Hoal Holo Hohi Hbseq Hload Hblive Hblal Hbllo Hblhi Hblobj Hbkt Hnd Hch Hnode Hapart].
      destruct Ha as [Hh | [[Hbc Hb] | (p & Hp & Hpa)]].
      - left. split; [exact Hh|]. split.
        + replace a with (obj + (a - obj)) by lia. apply (h_def HD). lia.
        + replace a with (obj + (a - obj)) by lia. apply Hown. lia.
      - right. destruct Hblive as [[Hbc0 _]|[_ Hin]]; [lia|]. exists bl, (8 * bc). split; [exact Hin | exact Hb].
      - right. apply in_map_iff in Hp. destruct Hp as ([p' [k v]] & Hpp & Hin). cbn in Hpp. subst p'.
        destruct (Hnode p k v Hin) as (Hlv & _). exists p, NS. split; [exact Hlv | exact Hpa]. }
    pose proof (u_obj_lo U) as Holo. pose proof (u_obj_hi U) as Hohi.
    rewrite u64_of_Z.
    2:{ destruct Hcases as [(Hh & _) | (p & n & Hin & Hpa)]; [lia|].
        destruct (live_facts A M model p n AI Hin) as (Hn & Hp0 & Hpc & _). lia. }
    intros [Ho | [Ho' | [Hnm | [Hf | [Hw | He]]]]].
    -   destruct Hcases as [(Hh & Hd & Hno) | (p & n & Hin & Hpa)]; [exact (Hno Ho)|].
      destruct (live_facts A M model p n AI Hin) as (_ & _ & _ & Hall). exact (proj1 (Hall a Hpa) Ho).
    -   destruct (ef_own _ _ _ _ _ _ _ _ _ EF a Ho') as [Ho | [[Hni [_ Hn]] | Hf]].
      + destruct Hcases as [(Hh & Hd & Hno) | (p & n & Hin & Hpa)]; [exact (Hno Ho)|].
        destruct (live_facts A M model p n AI Hin) as (_ & _ & _ & Hall). exact (proj1 (Hall a Hpa) Ho).
      + destruct Hcases as [(Hh & Hd & Hno) | (p & n & Hin & Hpa)]; [exact (Hd Hn)|].
        destruct (live_facts A M model p n AI Hin) as (_ & _ & _ & Hall). exact (proj2 (Hall a Hpa) Hn).
      + exact (HF a Ha Hf).
    - destruct Hnm as (Hni & _ & Hn).
      destruct Hcases as [(Hh & Hd & Hno) | (p & n & Hin & Hpa)]; [exact (Hd Hn)|].
      destruct (live_facts A M model p n AI Hin) as (_ & _ & _ & Hall). exact (proj2 (Hall a Hpa) Hn).
    - exact (HF a Ha Hf).
    - unfold W_of in Hw. destruct Hcases as [(Hh & _) | (p & n & Hin & Hpa)]; [lia|].
      destruct (live_facts A M model p n AI Hin) as (_ & _ & Hpc & _). lia.
    -
      pose proof (HLimg_lo a (HLrw_img a (HLerr_rw a He))) as Hlt.
      destruct Hcases as [(Hh & _) | (p & n & Hin & Hpa)]; [lia|].
      destruct (ai_live_block MI A M model p n AI Hin) as (_ & _ & _ & _ & Hall).
      destruct (Hall a Hpa) as (_ & Hni & _). exact (Hni (HLrw_img a (HLerr_rw a He))).
  Qed.

  Lemma agree_above_via_eff : forall (A A' : AS MI) M M' (W : Z * Z) (F : Z -> Prop) a n top,
    eff MI A A' M M' W F ->
    top <= a -> snd W <= top -> alloc_ceiling <= top -> 0 <= n -> a + n <= 2 ^ 47 ->
    (forall i, 0 <= i < n -> ~ owned MI A (a + i)) -> defined M a n ->
    (forall i, 0 <= i < n -> ~ F (a + i)) ->
    agree_on M M' a n.
  Proof using AC L MI HLimg_lo HLrw_img HLerr_rw.
    intros A A' M M' W F a n top EF Htop HW Hce Hn Han Hown Hdef HF i Hi.
    pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
    apply (ef_frame _ _ _ _ _ _ _ _ _ EF). rewrite u64_of_Z by lia.
    intros [Ho | [Ho' | [Hnm | [Hf | [Hw | He]]]]].
    - exact (Hown i Hi Ho).
    - destruct (ef_own _ _ _ _ _ _ _ _ _ EF _ Ho') as [Ho | [[_ [_ Hn0]] | Hf]];
        [exact (Hown i Hi Ho) | exact (Hdef i Hi Hn0) | exact (HF i Hi Hf)].
    - destruct Hnm as (_ & _ & Hn0). exact (Hdef i Hi Hn0).
    - exact (HF i Hi Hf).
    - unfold W_of in Hw. lia.
    - pose proof (HLimg_lo _ (HLrw_img _ (HLerr_rw _ He))). lia.
  Qed.

  Lemma defined_via_eff : forall (A A' : AS MI) M M' (W : Z * Z) (F : Z -> Prop) a n,
    eff MI A A' M M' W F -> alloc_ceiling <= a -> a + n <= 2 ^ 64 ->
    (forall i, 0 <= i < n -> ~ owned MI A (a + i)) -> (forall i, 0 <= i < n -> ~ F (a + i)) ->
    defined M a n -> defined M' a n.
  Proof using AC L MI HLimg_lo HLrw_img HLerr_rw.
    intros A A' M M' W F a n EF Ha Han Hown HF Hdef i Hi. pose proof ac_bounds_lit as Hcv.
    destruct (ef_def _ _ _ _ _ _ _ _ _ EF (a + i) ltac:(lia) (Hdef i Hi)) as [H|[H|[H|H]]];
      [exact H | exfalso; exact (Hown i Hi H) | exfalso; exact (HF i Hi H) |].
    exfalso. pose proof (HLimg_lo _ (HLrw_img _ (HLerr_rw _ H))). lia.
  Qed.

  Lemma umapx_rehost : forall (A A' : AS MI) M M' obj obj' bl bc (ents : list (Z * (Z * V))),
    umapx MI NS nval A M obj bl bc ents ->
    cell8 SEGS M' obj' bl -> cell8 SEGS M' (obj' + 8) bc -> cell8 SEGS M' (obj' + 16) (hdaddr ents) ->
    cell8 SEGS M' (obj' + 24) (Zlength ents) -> cell4 SEGS M' (obj' + 32) 0x3f800000 -> defined M' obj' 40 ->
    obj' mod 8 = 0 -> 0 < obj' -> obj' + 40 <= 2 ^ 47 ->
    (forall p k v, In (p, (k, v)) ents -> agree_on M M' p NS) ->
    (forall i, 0 <= i < bc -> (ents = [] \/ i <> hmod (hdkey ents) bc) -> agree_on M M' (bl + 8 * i) 8) ->
    (ents <> [] -> cell8 SEGS M' (bl + 8 * hmod (hdkey ents) bc) (obj' + 16)) ->
    (bc <> 0 -> apart bl (8 * bc) obj' 40) -> (forall p, In p (map fst ents) -> apart p NS obj' 40) ->
    (forall p n, In (p, n) (umap_blocks NS bl bc ents) -> In (p, n) (live MI A) -> In (p, n) (live MI A')) ->
    umapx MI NS nval A' M' obj' bl bc ents.
  Proof using AC L MI NS V nval HNS nval_agree.
    intros A A' M M' obj obj' bl bc ents U Cbl Cbc Cp1 Csz Cmlf Cdef Hal Hlo Hhi Hnd Hbk Hsent Hapb Hapn Hlive.
    destruct U as [HD Hoal Holo Hohi Hbseq Hload Hblive Hblal Hbllo Hblhi Hblobj Hbkt Hndup Hch Hnode Hapart].
    constructor; try assumption.
    - constructor; assumption.
    - destruct Hblive as [[Hbc0 Hbl0] | [Hbc1 Hin]]; [left; split; assumption | right].
      split; [exact Hbc1|]. apply Hlive; [|exact Hin]. unfold umap_blocks.
      destruct (Z.eqb_spec bc 0); [lia|]. apply in_app_iff. left. left. reflexivity.
    - intros i Hi. destruct (Hbkt i Hi) as (b & Hcell & Hok).
      assert (Hcase : ents = [] \/ i <> hmod (hdkey ents) bc \/ (ents <> [] /\ i = hmod (hdkey ents) bc)).
      { destruct ents; [left; reflexivity|]. destruct (Z.eq_dec i (hmod (hdkey (p :: ents)) bc)); [right; right; split; [discriminate| assumption] | right; left; assumption]. }
      destruct Hcase as [Hc | [Hc | [Hne Hc]]].
      + exists b. split; [| destruct Hok as [H|[H|(H1 & H2 & H3)]]; [left; exact H | right; left; exact H | exfalso; exact (H2 Hc)]].
        eapply cellw_agree; [exact Hcell | apply Hbk; [exact Hi | left; exact Hc] | lia | cbn; lia].
      + exists b. split; [| destruct Hok as [H|[H|(H1 & H2 & H3)]]; [left; exact H | right; left; exact H | exfalso; exact (Hc H3)]].
        eapply cellw_agree; [exact Hcell | apply Hbk; [exact Hi | right; exact Hc] | lia | cbn; lia].
      + exists (obj' + 16). subst i. split; [exact (Hsent Hne)|]. right; right. split; [reflexivity|]. split; [exact Hne | reflexivity].
    - eapply chain_agree; [exact Hch|]. intros p k v Hin. destruct (Hnode p k v Hin) as (_ & Hp0 & Hp1 & _).
      split; [|lia]. eapply agree_on_sub; [eapply Hnd; exact Hin | lia | lia].
    - intros p k v Hin. destruct (Hnode p k v Hin) as (Hlv & Hp0 & Hp1 & Hpal & Hh & Hk & Hkr & Hv & Hap1 & Hap2).
      pose proof (Hnd p k v Hin) as Hag.
      split; [|split; [exact Hp0|split; [exact Hp1|split; [exact Hpal|split; [|split; [|split; [exact Hkr|split; [|split; [|exact Hap2]]]]]]]]].
      + apply Hlive; [|exact Hlv]. unfold umap_blocks. apply in_app_iff. right.
        apply in_map_iff. exists (p, (k, v)). split; [reflexivity | exact Hin].
      + eapply cellw_agree; [exact Hh | eapply agree_on_sub; [exact Hag | lia | cbn; lia] | lia | cbn; lia].
      + eapply cellw_agree; [exact Hk | eapply agree_on_sub; [exact Hag | lia | cbn; lia] | lia | cbn; lia].
      + eapply nval_agree; [exact Hv | eapply agree_on_sub; [exact Hag | lia | lia] | lia | lia].
      + apply Hapn. apply in_map_iff. exists (p, (k, v)). split; [reflexivity | exact Hin].
  Qed.

  End PerTable.
End Common.
