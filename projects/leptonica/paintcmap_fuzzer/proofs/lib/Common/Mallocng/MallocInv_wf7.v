(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_sep MallocInv_tables MallocInv_wf MallocInv_wf2 MallocInv_wf3
  MallocInv_dll MallocInv_coh MallocInv_steps MallocInv_w32 MallocInv_actw MallocInv_vm MallocInv_ops MallocInv_usage.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Local Ltac pu_keep K := repeat match goal with H : ?T |- _ => lazymatch type of T with Prop => idtac | _ => fail end; lazymatch K with context [H] => fail | _ => idtac end;
                                                          tryif (match goal with X := _ |- _ => constr_eq X H end) then fail else clear H end.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma div_unique' : forall a b q r, 0 < b -> a = b * q + r -> 0 <= r < b -> a / b = q.
Proof using Type. pu_keep tt. intros a b q r Hb -> Hr. symmetry. apply (Z.div_unique _ _ _ r); lia. Qed.

Lemma mod_unique' : forall a b q r, 0 < b -> a = b * q + r -> 0 <= r < b -> a mod b = r.
Proof using Type. pu_keep tt. intros a b q r Hb -> Hr. symmetry. apply (Z.mod_unique _ _ q); lia. Qed.

Lemma L_pages : forall L, 0 < L -> L mod 4096 = 0 -> exists k, 1 <= k /\ L = 4096 * k.
Proof using Type. pu_keep tt. intros L HL HLm. exists (L / 4096). pose proof (Z.div_mod L 4096 ltac:(lia)). lia. Qed.

Lemma maplen_pages : forall L, 0 < L -> L mod 4096 = 0 -> 0 < L / 4096 /\ L / 4096 * 4096 = L.
Proof using Type. pu_keep tt. intros L HL HLm. destruct (L_pages L HL HLm) as (k & Hk & EL). rewrite EL. rewrite Z.mul_comm, Z.div_mul by lia. lia. Qed.

Lemma L_pages0 : forall L, 0 <= L -> L mod 4096 = 0 -> exists k, 0 <= k /\ L = 4096 * k.
Proof using Type. pu_keep tt. intros L HL HLm. exists (L / 4096). pose proof (Z.div_mod L 4096 ltac:(lia)). lia. Qed.

Section Word.
  Variables (L sc cnt : Z).
  Hypothesis HL : 0 <= L.
  Hypothesis HLm : L mod 4096 = 0.
  Hypothesis Hsc : 0 <= sc < 64.
  Hypothesis Hcnt : 1 <= cnt <= 32.

  Definition iw32 : Z := L + 64 * sc + 32 + (cnt - 1).
  Let L_pages := L_pages0 L HL HLm.

  Lemma iw32_last : w_last iw32 = cnt - 1.
  Proof using Hcnt Hsc L_pages. pu_keep (Hcnt, Hsc, L_pages).
    destruct L_pages as (k & Hk & EL). unfold w_last, iw32. apply (mod_unique' _ _ (128 * k + 2 * sc + 1)); lia.
  Qed.

  Lemma iw32_freeable : w_freeable iw32 = 1.
  Proof using Hcnt Hsc L_pages. pu_keep (Hcnt, Hsc, L_pages).
    destruct L_pages as (k & Hk & EL). unfold w_freeable, iw32.
    rewrite (div_unique' _ 32 (128 * k + 2 * sc + 1) (cnt - 1)) by lia. apply (mod_unique' _ _ (64 * k + sc)); lia.
  Qed.

  Lemma iw32_sc : w_sc iw32 = sc.
  Proof using Hcnt Hsc L_pages. pu_keep (Hcnt, Hsc, L_pages).
    destruct L_pages as (k & Hk & EL). unfold w_sc, iw32.
    rewrite (div_unique' _ 64 (64 * k + sc) (32 + (cnt - 1))) by lia. apply (mod_unique' _ _ k); lia.
  Qed.

  Lemma iw32_maplen : w_maplen iw32 = L / 4096.
  Proof using Hcnt Hsc L_pages. pu_keep (Hcnt, Hsc, L_pages).
    destruct L_pages as (k & Hk & EL). unfold w_maplen, iw32.
    rewrite (div_unique' _ 4096 k (64 * sc + 32 + (cnt - 1))) by lia. symmetry. apply (div_unique' _ 4096 k 0); lia.
  Qed.

  Lemma iw32_range : 0 <= iw32 < 2^64 <-> L < 2^64 - 4096 \/ iw32 < 2^64.
  Proof using HL Hcnt Hsc. pu_keep (HL, Hcnt, Hsc). unfold iw32. split; intros; lia. Qed.
End Word.

(* [comment removed for export] *)
Section Masks.
  Variables (cnt aidx : Z).
  Hypothesis Hcnt : 1 <= cnt <= 32.
  Hypothesis Haidx : 0 <= aidx <= cnt - 1.

  Definition itot : Z := 2 ^ cnt - 2.
  Definition iav : Z := itot mod 2 ^ (aidx + 1).
  Definition ifr : Z := itot - iav.

  Lemma pow_facts : 2 <= 2 ^ cnt <= 2^32 /\ 2 <= 2 ^ (aidx + 1) <= 2 ^ cnt.
  Proof using Haidx Hcnt. pu_keep (Haidx, Hcnt).
    split.
    - split; [replace 2 with (2^1) at 1 by reflexivity; apply Z.pow_le_mono_r; lia | apply Z.pow_le_mono_r; lia].
    - split; [replace 2 with (2^1) at 1 by reflexivity; apply Z.pow_le_mono_r; lia | apply Z.pow_le_mono_r; lia].
  Qed.

  Lemma itot_range : 0 <= itot < 2^32.
  Proof using Haidx Hcnt. pu_keep (Haidx, Hcnt). pose proof pow_facts. unfold itot. lia. Qed.

  Lemma itot_testbit : forall j, 0 <= j -> Z.testbit itot j = ((1 <=? j) && (j <? cnt))%bool.
  Proof using Hcnt. pu_keep (Hcnt).
    intros j Hj. unfold itot. replace (2 ^ cnt - 2) with (Z.ones (cnt - 1) * 2 ^ 1).
    2:{ unfold Z.ones. rewrite Z.shiftl_1_l. change (2^1) with 2. replace (2 ^ cnt) with (2 * 2 ^ (cnt - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia). unfold Z.pred. lia. }
    destruct (Z.lt_ge_cases j 1) as [Hlt | Hge].
    - rewrite Z.mul_pow2_bits_low by lia. replace (1 <=? j) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
    - rewrite Z.mul_pow2_bits by lia. replace (1 <=? j) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
      destruct (Z.lt_ge_cases j cnt) as [H | H].
      + rewrite Z.ones_spec_low by lia. symmetry. apply Z.ltb_lt. lia.
      + rewrite Z.ones_spec_high by lia. symmetry. apply Z.ltb_ge. lia.
  Qed.

  Lemma iav_eq : iav = 2 ^ (aidx + 1) - 2.
  Proof using Haidx Hcnt. pu_keep (Haidx, Hcnt).
    pose proof pow_facts as [P1 P2]. unfold iav, itot.
    replace (2 ^ cnt) with (2 ^ (aidx + 1) * 2 ^ (cnt - (aidx + 1))) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (1 <= 2 ^ (cnt - (aidx + 1))) by (replace 1 with (2^0) by reflexivity; apply Z.pow_le_mono_r; lia).
    apply (mod_unique' _ _ (2 ^ (cnt - (aidx + 1)) - 1)); [lia | nia | lia].
  Qed.

  Lemma ifr_eq : ifr = 2 ^ cnt - 2 ^ (aidx + 1).
  Proof using Haidx Hcnt. pu_keep (Haidx, Hcnt). unfold ifr. rewrite iav_eq. unfold itot. lia. Qed.

  Lemma masks_facts :
    0 <= iav < 2 ^ cnt /\ 0 <= ifr < 2 ^ cnt /\ Z.land iav ifr = 0 /\ Z.lor iav ifr = itot /\
    iav < 2 ^ (aidx + 1) /\
    (forall j, 0 <= j -> Z.testbit ifr j = ((1 <=? j) && (j <? cnt) && (aidx + 1 <=? j))%bool) /\
    (forall j, 0 <= j -> Z.testbit (Z.lor iav ifr) j = ((1 <=? j) && (j <? cnt))%bool).
  Proof using Haidx Hcnt. pu_keep (Haidx, Hcnt).
    pose proof pow_facts as [P1 P2]. pose proof itot_range as IR.
    destruct (mask_split itot aidx IR ltac:(lia)) as (_ & M1 & M2 & M3 & M4 & M5 & M6).
    fold iav in M1, M2, M3, M4, M5, M6. fold ifr in M3, M4, M5.
    assert (Hitot : itot < 2 ^ cnt) by (unfold itot; lia).
    split; [lia|]. split; [unfold ifr in *; lia|]. split; [exact M3|]. split; [exact M4|]. split; [exact M2|]. split.
    - intros j Hj. rewrite M5, itot_testbit by lia. reflexivity.
    - intros j Hj. rewrite M4, itot_testbit by lia. reflexivity.
  Qed.
End Masks.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ivl_disj : forall a b c d, (forall x, a <= x < b -> ~ (c <= x < d)) -> a < b -> c < d -> b <= c \/ d <= a.
Proof using Type. pu_keep tt.
  intros a b c d H Hab Hcd. destruct (Z.lt_ge_cases (Z.max a c) b) as [H1 | H1]; [| lia].
  destruct (Z.lt_ge_cases (Z.max a c) d) as [H2 | H2]; [| lia]. exfalso. apply (H (Z.max a c)); lia.
Qed.

Lemma nth_error_repeat' : forall {T} (x : T) n k y, nth_error (repeat x n) k = Some y -> y = x /\ (k < n)%nat.
Proof using Type. pu_keep tt.
  intros T x n. induction n as [|n IH]; intros k y H; [destruct k; discriminate|].
  destruct k as [|k]; cbn in H; [injection H as <-; split; [reflexivity | lia]|]. destruct (IH k y H) as [E Hk]. split; [exact E | lia].
Qed.

(* [comment removed for export] *)
Lemma slot_in_ext : forall mt j, 0 <= j -> j + 1 <= mt_cnt mt -> 0 <= mt_stride mt ->
  gext_lo mt + 16 <= slot_start mt j /\ slot_end mt j <= gext_hi mt.
Proof using Type. pu_keep tt.
  intros mt j Hj Hjc Hsd. unfold gext_lo, gext_hi, slot_start, slot_end, slot_start_g, slot_end_g.
  assert (0 <= j * mt_stride mt) by (apply Z.mul_nonneg_nonneg; lia).
  assert ((j + 1) * mt_stride mt <= mt_cnt mt * mt_stride mt) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma aib_lor_rng : forall ab aidx, 0 <= ab < 256 -> 0 <= aidx <= 31 ->
  0 <= Z.lor (Z.land ab 224) aidx < 256 /\ Z.lor (Z.land ab 224) aidx mod 32 = aidx.
Proof using Type. pu_keep tt.
  intros ab aidx Hab Haidx.
  assert (H224 : 0 <= Z.land ab 224 <= ab) by (split; [apply Z.land_nonneg; lia | apply land_le_left; lia]).
  assert (Hlo : Z.land (Z.land ab 224) aidx = 0).
  { apply Z.bits_inj'. intros j Hj. rewrite !Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases j 5) as [Hj5 | Hj5].
    - replace (Z.testbit 224 j) with false; [rewrite Bool.andb_false_r; reflexivity|].
      change 224 with (7 * 2^5). rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - replace (Z.testbit aidx j) with false; [rewrite Bool.andb_false_r; reflexivity|].
      symmetry. apply Z.bits_above_log2; [lia|]. apply (Z.le_lt_trans _ (Z.log2 31)); [apply Z.log2_le_mono; lia | cbn; lia]. }
  pose proof (Z.add_nocarry_lxor _ _ Hlo) as E. rewrite (Z.lxor_lor _ _ Hlo) in E.
  assert (Hmod : Z.land ab 224 mod 32 = 0).
  { change 32 with (2^5). rewrite <- (Z.land_ones _ 5) by lia. apply Z.bits_inj'. intros j Hj. rewrite !Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases j 5) as [Hj5 | Hj5].
    - replace (Z.testbit 224 j) with false; [rewrite Bool.andb_false_r; reflexivity|]. change 224 with (7 * 2^5). rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - rewrite Z.ones_spec_high by lia. apply Bool.andb_false_r. }
  assert (H224' : Z.land ab 224 <= 224) by (rewrite Z.land_comm; apply land_le_left; lia).
  rewrite <- E. split; [lia|].
  rewrite (Z_div_exact_full_2 (Z.land ab 224) 32) by lia.
  rewrite Z.add_comm, Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Section InstallRoot.
  Variables (A : astate) (m : Z) (md : meta_rec) (p L cnt aidx sc ab : Z) (xs : list (Z * Z)).
  Hypothesis HW : WF A.
  Hypothesis Hm : a_meta A m = Some md.
  Hypothesis Hr : mt_role md = RDead.
  Hypothesis Hprev : mt_f md FPrev = 0.
  Hypothesis Hnext : mt_f md FNext = 0.
  Hypothesis Hxm : a_xmaps A = (p, L) :: xs.
  (* [comment removed for export] *)
  Hypothesis Hsc : 0 <= sc < 48 \/ (sc = 63 /\ cnt = 1).
  Hypothesis Hcnt : 1 <= cnt <= 32.
  Hypothesis Haidx : 0 <= aidx <= cnt - 1.
  Hypothesis Hab : 0 <= ab < 256.
  Hypothesis Hpal : page_aligned p.
  Hypothesis Hhr : heap_range p (p + L).
  Hypothesis HL : 0 < L.
  Hypothesis HLm : L mod 4096 = 0.
  Hypothesis HL64 : L < 2^47.
  Hypothesis Hnodom : forall x, p <= x < p + L -> ~ dom A x.
  Hypothesis Hfit : 1 < cnt -> 16 * size_class sc * cnt + 16 <= L.
  Hypothesis Hsingle : cnt = 1 -> sc < 48 -> 256 <= size_class sc \/ L - 16 <= 16 * size_class sc.
  Hypothesis Hs20 : cnt = 1 -> sc < 48 -> L < 2^20 + 16.
  Hypothesis Hspan : 1 < cnt -> 16 * size_class sc * cnt < 2^20.
  Hypothesis Hpsc : aidx < cnt - 1 -> 7 <= sc.

  Let size := 16 * size_class sc.
  Definition ir_f (fl : mfield) : Z :=
    match fl with
    | FPrev => 0 | FNext => 0 | FMem => p
    | FAvail => iav cnt aidx | FFreed => ifr cnt aidx | FW32 => iw32 L sc cnt
    end.
  Definition ir_aib : Z := Z.lor (Z.land ab 224) aidx.
  Definition ir_slots : list slot_st := STaken :: repeat SIdle (Z.to_nat (cnt - 1)).
  Definition ir_mt : meta_rec := MT ir_f (RGroup ir_aib ir_slots).
  Definition instR : astate :=
    AST (a_ctx A) (a_areas A) (aupd (a_meta A) m ir_mt) (a_freelist A) (a_active A) (a_pages A) (a_brk_lo A)
        (a_live A) (a_mblocks A) xs.

  (* [comment removed for export] *)
  Lemma Hsc64 : 0 <= sc < 64. Proof using HL Hab Hcnt Hsc. pu_keep (HL, Hab, Hcnt, Hsc). lia. Qed.
  Lemma size_rng : sc < 48 -> 16 <= size <= 16 * 8191.
  Proof using HL HLm Hab Hcnt Hfit Hs20 Hsc Hsingle. pu_keep (HL, HLm, Hab, Hcnt, Hfit, Hs20, Hsc, Hsingle). intros H48. pose proof (size_class_range sc ltac:(lia)). unfold size. lia. Qed.
  Lemma ir_w32 : mt_w32 ir_mt = iw32 L sc cnt. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma ir_mem : mt_mem ir_mt = p. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma ir_avail : mt_avail ir_mt = iav cnt aidx. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma ir_freed : mt_freed ir_mt = ifr cnt aidx. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma ir_prev : mt_prev ir_mt = 0. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma ir_next : mt_next ir_mt = 0. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma HL0 : 0 <= L. Proof using HL Hab size. pu_keep (HL, Hab, size). lia. Qed.
  Lemma ir_last : mt_last ir_mt = cnt - 1. Proof using HL HLm Hab Hcnt Hsc. pu_keep (HL, HLm, Hab, Hcnt, Hsc). unfold mt_last. rewrite ir_w32. apply iw32_last; first [exact HL0 | exact Hsc64 | assumption]. Qed.
  Lemma ir_cnt : mt_cnt ir_mt = cnt. Proof using HL HLm Hab Hcnt Hsc. pu_keep (HL, HLm, Hab, Hcnt, Hsc). unfold mt_cnt. rewrite ir_last. lia. Qed.
  Lemma ir_sc : mt_sc ir_mt = sc. Proof using HL HLm Hab Hcnt Hsc. pu_keep (HL, HLm, Hab, Hcnt, Hsc). unfold mt_sc. rewrite ir_w32. apply iw32_sc; first [exact HL0 | exact Hsc64 | assumption]. Qed.
  Lemma ir_maplen : mt_maplen ir_mt = L / 4096. Proof using HL HLm Hab Hcnt Hsc. pu_keep (HL, HLm, Hab, Hcnt, Hsc). unfold mt_maplen. rewrite ir_w32. apply iw32_maplen; first [exact HL0 | exact Hsc64 | assumption]. Qed.
  Lemma ir_maplen_pos : 0 < mt_maplen ir_mt. Proof using HL HLm Hab Hcnt Hsc. pu_keep (HL, HLm, Hab, Hcnt, Hsc). rewrite ir_maplen. exact (proj1 (maplen_pages L HL HLm)). Qed.
  Lemma ir_map_len : grp_map_len ir_mt = L. Proof using HL HLm Hab Hcnt Hsc. pu_keep (HL, HLm, Hab, Hcnt, Hsc). unfold grp_map_len. rewrite ir_maplen. exact (proj2 (maplen_pages L HL HLm)). Qed.
  Lemma ir_stride : mt_stride ir_mt = (if cnt =? 1 then L - 16 else size).
  Proof using HL HLm Hab Hcnt Hs20 Hsc Hsingle. pu_keep (HL, HLm, Hab, Hcnt, Hs20, Hsc, Hsingle).
    unfold mt_stride. rewrite ir_last, ir_sc, ir_maplen. fold size. pose proof (maplen_pages L HL HLm) as [P1 P2].
    replace (L / 4096 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [orb].
    destruct (Z.eqb_spec (cnt - 1) 0), (Z.eqb_spec cnt 1); cbn [negb]; lia.
  Qed.
  Lemma ir_stride_ge : 16 <= mt_stride ir_mt /\ 16 + cnt * mt_stride ir_mt <= L.
  Proof using HL HLm Hab Hcnt Hfit Hs20 Hsc Hsingle. pu_keep (HL, HLm, Hab, Hcnt, Hfit, Hs20, Hsc, Hsingle).
    rewrite ir_stride. destruct (maplen_pages L HL HLm) as [P1 P2].
    destruct (Z.eqb_spec cnt 1) as [E | NE]; [rewrite E; lia | pose proof (size_rng ltac:(lia)); split; [lia | pose proof (Hfit ltac:(lia)); unfold size in *; nia]].
  Qed.
  Lemma ir_w32_range : 0 <= mt_w32 ir_mt < 2^64.
  Proof using HL HL64 HLm Hab Hcnt Hfit Hs20 Hsc Hsingle Hspan. pu_keep (HL, HL64, HLm, Hab, Hcnt, Hfit, Hs20, Hsc, Hsingle, Hspan). rewrite ir_w32. unfold iw32. lia. Qed.
  Lemma ir_gext : gext_lo ir_mt = p /\ gext_hi ir_mt + 4 <= p + L /\ p + 16 <= gext_hi ir_mt.
  Proof using HL HLm Hab Hcnt Hfit Hs20 Hsc Hsingle. pu_keep (HL, HLm, Hab, Hcnt, Hfit, Hs20, Hsc, Hsingle). unfold gext_lo, gext_hi. rewrite ir_mem, ir_cnt. pose proof ir_stride_ge. split; [reflexivity | nia]. Qed.
  Lemma ir_aib_rng : 0 <= ir_aib < 256 /\ ir_aib mod 32 = aidx.
  Proof using HL Hab Haidx Hcnt Hsc size. pu_keep (HL, Hab, Haidx, Hcnt, Hsc, size). unfold ir_aib. apply aib_lor_rng; lia. Qed.

  (* [comment removed for export] *)
  Lemma ir_meta : forall x, a_meta instR x = if Z.eq_dec x m then Some ir_mt else a_meta A x.
  Proof using Type. pu_keep tt. intros x. reflexivity. Qed.
  Lemma ir_meta_m : a_meta instR m = Some ir_mt.
  Proof using Type. pu_keep tt. rewrite ir_meta. destruct (Z.eq_dec m m); [reflexivity | contradiction]. Qed.
  Lemma ir_meta_other : forall x, x <> m -> a_meta instR x = a_meta A x.
  Proof using Type. pu_keep tt. intros x Hx. rewrite ir_meta. destruct (Z.eq_dec x m); [contradiction | reflexivity]. Qed.
  Lemma ir_meta_inv : forall x mtx, a_meta instR x = Some mtx -> (x = m /\ mtx = ir_mt) \/ (x <> m /\ a_meta A x = Some mtx).
  Proof using Type. pu_keep tt.
    intros x mtx Hx. rewrite ir_meta in Hx. destruct (Z.eq_dec x m) as [-> | Hne]; [left; injection Hx as <-; auto | right; auto].
  Qed.
  Lemma ir_group_inv : forall x mtx aibx slx, a_meta instR x = Some mtx -> mt_role mtx = RGroup aibx slx ->
    (x = m /\ mtx = ir_mt /\ aibx = ir_aib /\ slx = ir_slots) \/ (x <> m /\ a_meta A x = Some mtx).
  Proof using Type. pu_keep tt.
    intros x mtx aibx slx Hx Hrx. destruct (ir_meta_inv x mtx Hx) as [(-> & ->) | H]; [left | right; exact H].
    cbn in Hrx. injection Hrx as <- <-. auto.
  Qed.
  (* [comment removed for export] *)
  Lemma ir_old : forall x mtx, a_meta A x = Some mtx -> mt_role mtx <> RDead -> a_meta instR x = Some mtx.
  Proof using Hm Hr. pu_keep (Hm, Hr).
    intros x mtx Hx Hrx. destruct (Z.eq_dec x m) as [-> | Hne]; [rewrite Hm in Hx; injection Hx as <-; contradiction|].
    rewrite (ir_meta_other x Hne). exact Hx.
  Qed.
  Lemma ir_old_grp : forall x mtx aibx slx, a_meta A x = Some mtx -> mt_role mtx = RGroup aibx slx -> a_meta instR x = Some mtx /\ x <> m.
  Proof using Hm Hr. pu_keep (Hm, Hr).
    intros x mtx aibx slx Hx Hrx. split; [apply (ir_old x mtx Hx); rewrite Hrx; discriminate|].
    intros ->. rewrite Hm in Hx. injection Hx as <-. rewrite Hr in Hrx. discriminate.
  Qed.
  Lemma ir_not_in_fl : ~ In m (a_freelist A).
  Proof using HW Hm Hr. pu_keep (HW, Hm, Hr).
    intros Hin. destruct (proj1 (wf_fl_mem A HW m) Hin) as (mt0 & H0 & Hr0). rewrite Hm in H0. injection H0 as <-. rewrite Hr in Hr0. discriminate Hr0.
  Qed.
  Lemma ir_not_in_act : forall sc', ~ In m (a_active A sc').
  Proof using HW Hm Hr. pu_keep (HW, Hm, Hr).
    intros sc' Hin. destruct (wf_act_mem A HW sc' m Hin) as (mt0 & aib0 & sl0 & H0 & Hr0 & _). rewrite Hm in H0. injection H0 as <-.
    rewrite Hr in Hr0. discriminate Hr0.
  Qed.
  Lemma ir_dll : forall l, ~ In m l -> dll A l -> dll instR l.
  Proof using Type. pu_keep tt.
    intros l Hn Hd k x Hk. destruct (Hd k x Hk) as (mtx & Hx & R). exists mtx. split; [| exact R].
    rewrite ir_meta_other; [exact Hx|]. intros ->. apply Hn. eapply nth_error_In. exact Hk.
  Qed.

  (* [comment removed for export] *)
  Lemma ir_slots_len : length ir_slots = Z.to_nat cnt.
  Proof using HL Hab Hcnt Hsc size. pu_keep (HL, Hab, Hcnt, Hsc, size). unfold ir_slots. cbn [length]. rewrite repeat_length. lia. Qed.
  Lemma ir_slots_inv : forall j st, nth_error ir_slots j = Some st -> (j = 0%nat /\ st = STaken) \/ ((0 < j < Z.to_nat cnt)%nat /\ st = SIdle).
  Proof using HL Hab Haidx Hcnt Hsc size. pu_keep (HL, Hab, Haidx, Hcnt, Hsc, size).
    intros j st Hj. unfold ir_slots in Hj. destruct j as [|j]; cbn in Hj; [left; injection Hj as <-; auto|].
    destruct (nth_error_repeat' SIdle _ _ _ Hj) as [-> Hlt]. right. split; [lia | reflexivity].
  Qed.
  Lemma ir_no_nested : forall j ch, nth_error ir_slots j <> Some (SNested ch).
  Proof using HL Hab Haidx Hcnt Hsc size. pu_keep (HL, Hab, Haidx, Hcnt, Hsc, size). intros j ch E. destruct (ir_slots_inv _ _ E) as [(_ & H) | (_ & H)]; discriminate H. Qed.
  Lemma ir_no_live : forall j off n, nth_error ir_slots j <> Some (SLive off n).
  Proof using HL Hab Haidx Hcnt Hsc size. pu_keep (HL, Hab, Haidx, Hcnt, Hsc, size). intros j off n E. destruct (ir_slots_inv _ _ E) as [(_ & H) | (_ & H)]; discriminate H. Qed.

  (* [comment removed for export] *)
  Lemma ir_ext_nodom : forall x, gext_lo ir_mt <= x < gext_hi ir_mt + 4 -> ~ dom A x.
  Proof using HL HLm Hab Hcnt Hfit Hnodom Hs20 Hsc Hsingle. pu_keep (HL, HLm, Hab, Hcnt, Hfit, Hnodom, Hs20, Hsc, Hsingle). intros x Hx. pose proof ir_gext as (G1 & G2 & G3). apply Hnodom. lia. Qed.

  Lemma old_grp_ext : forall x mtx aibx slx, a_meta A x = Some mtx -> mt_role mtx = RGroup aibx slx ->
    gext_hi mtx + 4 <= p \/ p + L <= gext_lo mtx.
  Proof using HL HW Hab Hcnt Hnodom Hsc size. pu_keep (HL, HW, Hab, Hcnt, Hnodom, Hsc, size).
    intros x mtx aibx slx Hx Hrx.
    pose proof (wf_grp A HW x mtx aibx slx Hx Hrx) as (Hw & _ & Hscx & _). pose proof (stride_ge16 mtx ltac:(lia) Hscx).
    apply (ivl_disj (gext_lo mtx) (gext_hi mtx + 4) p (p + L)); [| unfold gext_lo, gext_hi, mt_cnt; pose proof (w_last_range (mt_w32 mtx)); unfold mt_last; nia | lia].
    intros y Hy Hy'. exact (Hnodom y Hy' (grp_dom A x mtx aibx slx y HW Hx Hrx Hy)).
  Qed.

  Lemma old_root_map : forall x mtx aibx slx, a_meta A x = Some mtx -> mt_role mtx = RGroup aibx slx -> 0 < mt_maplen mtx ->
    mt_mem mtx + grp_map_len mtx <= p \/ p + L <= mt_mem mtx.
  Proof using HL Hab Hcnt Hnodom Hsc size. pu_keep (HL, Hab, Hcnt, Hnodom, Hsc, size).
    intros x mtx aibx slx Hx Hrx Hml. unfold grp_map_len.
    apply (ivl_disj (mt_mem mtx) (mt_mem mtx + mt_maplen mtx * 4096) p (p + L)); [| lia | lia].
    intros y Hy Hy'. apply (Hnodom y Hy'). right; left. exists x, mtx, aibx, slx. unfold grp_map_len. auto.
  Qed.

  Lemma old_area : forall pg, In pg (a_areas A) -> pg + 4096 <= p \/ p + L <= pg.
  Proof using HL Hab Hnodom size. pu_keep (HL, Hab, Hnodom, size).
    intros pg Hpg. apply (ivl_disj pg (pg + 4096) p (p + L)); [| lia | lia].
    intros y Hy Hy'. apply (Hnodom y Hy'). left. exists pg. auto.
  Qed.

  Lemma old_page : forall pg, In pg (a_pages A) -> pg + 4096 <= p \/ p + L <= pg.
  Proof using HL Hab Hnodom size. pu_keep (HL, Hab, Hnodom, size).
    intros pg Hpg. apply (ivl_disj pg (pg + 4096) p (p + L)); [| lia | lia].
    intros y Hy Hy'. apply (Hnodom y Hy'). right; right. exists pg. auto.
  Qed.

  (* [comment removed for export] *)
  Lemma ir_wf_grp :
     0 <= mt_w32 ir_mt < 2^64 /\ w_freeable (mt_w32 ir_mt) = 1 /\
     (mt_sc ir_mt < 48 \/ (mt_sc ir_mt = 63 /\ mt_last ir_mt = 0 /\ 0 < mt_maplen ir_mt)) /\
     Z.of_nat (length ir_slots) = mt_cnt ir_mt /\
     0 <= mt_avail ir_mt < 2 ^ (mt_cnt ir_mt) /\ 0 <= mt_freed ir_mt < 2 ^ (mt_cnt ir_mt) /\
     Z.land (mt_avail ir_mt) (mt_freed ir_mt) = 0 /\
     0 <= ir_aib < 256 /\ mt_avail ir_mt < 2 ^ (ir_aib mod 32 + 1) /\ ir_aib mod 32 <= mt_last ir_mt /\
     (forall i st, nth_error ir_slots (Z.to_nat i) = Some st -> 0 <= i ->
        (Z.testbit (Z.lor (mt_avail ir_mt) (mt_freed ir_mt)) i = true <-> st = SIdle)) /\
     mt_mem ir_mt mod 16 = 0 /\ 0x1000 <= mt_mem ir_mt /\
     16 + mt_cnt ir_mt * mt_stride ir_mt <= (if mt_maplen ir_mt =? 0 then 2^64 else grp_map_len ir_mt) /\
     mt_mem ir_mt + 16 + mt_cnt ir_mt * mt_stride ir_mt <= alloc_ceiling /\
     (0 < mt_maplen ir_mt -> page_aligned (mt_mem ir_mt) /\ heap_range (mt_mem ir_mt) (mt_mem ir_mt + grp_map_len ir_mt)).
  Proof using HL HL64 HLm Hab Haidx Hcnt Hfit Hhr Hpal Hs20 Hsc Hsingle Hspan. pu_keep (HL, HL64, HLm, Hab, Haidx, Hcnt, Hfit, Hhr, Hpal, Hs20, Hsc, Hsingle, Hspan).
    pose proof (masks_facts cnt aidx Hcnt Haidx) as (M1 & M2 & M3 & M4 & M5 & M6 & M7). pose proof ir_aib_rng as [B1 B2].
    rewrite ir_avail, ir_freed, ir_cnt, ir_last, ir_sc, ir_mem, ir_map_len, ir_w32. rewrite B2.
    pose proof ir_stride_ge as [S1 S2]. pose proof ir_maplen_pos as MP. unfold heap_range in Hhr. pose proof (maplen_pages L HL HLm) as [P1 P2].
    split; [unfold iw32; lia|]. split; [apply iw32_freeable; first [exact HL0 | exact Hsc64 | assumption]|].
    split; [destruct Hsc as [H48 | [E63 E1]]; [left; lia | right; rewrite E63, E1; split; [reflexivity | split; [lia | exact MP]]]|]. split; [rewrite ir_slots_len; lia|].
    split; [lia|]. split; [lia|]. split; [exact M3|]. split; [exact B1|]. split; [exact M5|]. split; [lia|].
    split.
    { intros i st Hi Hi0. rewrite M7 by lia. destruct (ir_slots_inv _ _ Hi) as [(E & ->) | (E & ->)].
      - split; [intros H | intros H; discriminate H]. assert (i = 0) by lia. subst i. cbn in H. discriminate H.
      - split; [reflexivity | intros _]. apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]. }
    split. { unfold page_aligned in Hpal. rewrite (Z_div_exact_full_2 p 4096) by lia. replace (4096 * (p / 4096)) with ((256 * (p / 4096)) * 16) by lia. apply Z_mod_mult. }
    split; [lia|]. split; [replace (mt_maplen ir_mt =? 0) with false by (symmetry; apply Z.eqb_neq; lia); lia|].
    split; [lia|]. intros _. split; [exact Hpal | unfold heap_range; lia].
  Qed.
  (* [comment removed for export] *)
  Lemma ir_masks : 0 <= mt_avail ir_mt < 2^32 /\ 0 <= mt_freed ir_mt < 2^32 /\
    Z.lor (mt_avail ir_mt) (mt_freed ir_mt) = itot cnt /\ (1 < cnt -> Z.lor (mt_avail ir_mt) (mt_freed ir_mt) <> 0) /\
    (cnt = 1 -> Z.lor (mt_avail ir_mt) (mt_freed ir_mt) = 0).
  Proof using HL Hab Haidx Hcnt Hfit Hpsc Hs20 Hsc Hsingle Hspan. pu_keep (HL, Hab, Haidx, Hcnt, Hfit, Hpsc, Hs20, Hsc, Hsingle, Hspan).
    pose proof (masks_facts cnt aidx Hcnt Haidx) as (M1 & M2 & M3 & M4 & M5 & M6 & M7). pose proof (pow_facts cnt aidx Hcnt Haidx) as [P1 P2].
    rewrite ir_avail, ir_freed, M4. assert (2 ^ cnt <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia). unfold itot.
    split; [lia|]. split; [lia|]. split; [reflexivity|]. split.
    - intros Hc E. assert (2 ^ 2 <= 2 ^ cnt) by (apply Z.pow_le_mono_r; lia). change (2^2) with 4 in *. lia.
    - intros ->. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma old_ext_len : forall x mtx aibx slx, a_meta A x = Some mtx -> mt_role mtx = RGroup aibx slx ->
    gext_lo mtx + 28 <= gext_hi mtx.
  Proof using HL HW Hab Hcnt Hsc size. pu_keep (HL, HW, Hab, Hcnt, Hsc, size).
    intros x mtx aibx slx Hx Hrx. pose proof (wf_grp A HW x mtx aibx slx Hx Hrx) as (Hw & _ & Hscx & _).
    pose proof (stride_ge16 mtx ltac:(lia) Hscx) as S16. pose proof (w_last_range (mt_w32 mtx)) as WL.
    unfold gext_lo, gext_hi, mt_cnt, mt_last in *.
    assert (16 <= (w_last (mt_w32 mtx) + 1) * mt_stride mtx) by nia. lia.
  Qed.

  Lemma lam_cases : forall mtx, gext_hi mtx + 4 <= p \/ p + L <= gext_lo mtx ->
    gext_hi ir_mt + 4 <= gext_lo mtx \/ gext_hi mtx + 4 <= gext_lo ir_mt.
  Proof using HL HLm Hab Hcnt Hfit Hs20 Hsc Hsingle. pu_keep (HL, HLm, Hab, Hcnt, Hfit, Hs20, Hsc, Hsingle). intros mtx D. pose proof ir_gext as (G1 & G2 & G3). destruct D; [right | left]; lia. Qed.

  Lemma mem_new_old : forall x mtx aibx slx, a_meta A x = Some mtx -> mt_role mtx = RGroup aibx slx -> mt_mem mtx <> p.
  Proof using HL HLm HW Hab Hcnt Hfit Hnodom Hsc size. pu_keep (HL, HLm, HW, Hab, Hcnt, Hfit, Hnodom, Hsc, size).
    intros x mtx aibx slx Hx Hrx E. pose proof (old_grp_ext _ _ _ _ Hx Hrx) as D. pose proof (old_ext_len _ _ _ _ Hx Hrx) as LEN.
    unfold gext_lo in *. lia.
  Qed.

  Lemma cover_new : forall pa pm paib psl j ch, a_meta A pa = Some pm -> mt_role pm = RGroup paib psl -> 0 <= j ->
    nth_error psl (Z.to_nat j) = Some (SNested ch) -> slot_start pm j <= gext_lo ir_mt -> gext_hi ir_mt <= slot_end pm j -> False.
  Proof using HL HLm HW Hab Hcnt Hfit Hnodom Hs20 Hsc Hsingle. pu_keep (HL, HLm, HW, Hab, Hcnt, Hfit, Hnodom, Hs20, Hsc, Hsingle).
    intros pa pm paib psl j ch Hpa Hpr Hj0 Hj Hlo Hhi. pose proof ir_gext as (G1 & G2 & G3).
    pose proof (wf_grp A HW _ _ _ _ Hpa Hpr) as (Hw' & _ & Hsc' & Hlen' & _). pose proof (stride_ge16 pm ltac:(lia) Hsc') as S16.
    assert (Hjlt : j + 1 <= mt_cnt pm).
    { pose proof (proj1 (nth_error_Some psl (Z.to_nat j)) ltac:(rewrite Hj; discriminate)). lia. }
    destruct (slot_in_ext pm j Hj0 Hjlt ltac:(lia)) as [E1 E2].
    apply (ir_ext_nodom p ltac:(lia)). apply (grp_dom A pa pm paib psl p HW Hpa Hpr). lia.
  Qed.

  Lemma span_new : 0 < mt_last ir_mt -> mt_cnt ir_mt * mt_stride ir_mt < 2^20.
  Proof using HL HLm Hab Hcnt Hs20 Hsc Hsingle Hspan. pu_keep (HL, HLm, Hab, Hcnt, Hs20, Hsc, Hsingle, Hspan).
    rewrite ir_cnt, ir_stride, ir_last. intros Hlast. replace (cnt =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
    pose proof (Hspan ltac:(lia)). unfold size. nia.
  Qed.

  Theorem WF_instR : WF instR.
  Proof using HL HL64 HLm HW Hab Haidx Hcnt Hfit Hhr Hm Hnodom Hpal Hpsc Hr Hs20 Hsc Hsingle Hspan. pu_keep (HL, HL64, HLm, HW, Hab, Haidx, Hcnt, Hfit, Hhr, Hm, Hnodom, Hpal, Hpsc, Hr, Hs20, Hsc, Hsingle, Hspan).
    pose proof HW as W. pose proof ir_wf_grp as GRP. pose proof ir_gext as (G1 & G2 & G3).
    pose proof ir_maplen_pos as MP. pose proof ir_masks as (K1 & K2 & K3 & K4 & K5). pose proof ir_aib_rng as [B1 B2].
    pose proof (masks_facts cnt aidx Hcnt Haidx) as (M1 & M2 & M3 & M4 & M5 & M6 & M7).
    constructor; cbn [a_ctx a_areas a_meta a_freelist a_active a_pages a_brk_lo a_live a_mblocks a_xmaps instR].
    - exact (wf_areas_nodup A W).
    - exact (wf_areas_al A W).
    - (* [comment removed for export] *) intros x. rewrite <- (wf_meta_dom A W). unfold aupd.
      destruct (Z.eq_dec x m) as [-> | Hne]; [rewrite Hm; split; intros _; discriminate | tauto].
    - exact (wf_init A W).
    - exact (wf_uninit A W).
    - exact (wf_amc A W).
    - (* [comment removed for export] *) intros Hc. destruct (wf_am A W Hc) as (pg & H1 & H2 & H3 & H4). exists pg. repeat split; auto.
      intros k Hk. destruct (H4 k Hk) as (mtk & Hmk & Hrk). exists mtk. split; [| exact Hrk].
      apply (ir_old _ _ Hmk). rewrite Hrk. discriminate.
    - exact (wf_atail A W).
    - exact (wf_ahead A W).
    - (* [comment removed for export] *) intros x mtx Hx Hrx. destruct (ir_meta_inv x mtx Hx) as [(-> & ->) | (Hne & H)]; [cbn in Hrx; discriminate Hrx | exact (wf_avail_zero A W x mtx H Hrx)].
    - (* [comment removed for export] *) intros x mtx Hx Hrx. destruct (ir_meta_inv x mtx Hx) as [(-> & ->) | (Hne & H)]; [cbn in Hrx; discriminate Hrx | exact (wf_free_zero A W x mtx H Hrx)].
    - exact (wf_fl_nodup A W).
    - exact (wf_fl_head A W).
    - (* [comment removed for export] *) intros x. rewrite (wf_fl_mem A W x). split.
      + intros (mtx & Hx & Hrx). exists mtx. split; [| exact Hrx]. apply (ir_old _ _ Hx). rewrite Hrx. discriminate.
      + intros (mtx & Hx & Hrx). destruct (ir_meta_inv x mtx Hx) as [(-> & ->) | (Hne & H)]; [cbn in Hrx; discriminate Hrx | eauto].
    - (* [comment removed for export] *) apply ir_dll; [apply ir_not_in_fl | exact (wf_fl_dll A W)].
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx. destruct (ir_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & H)]; [exact GRP | exact (wf_grp A W x mtx aibx slx H Hrx)].
    - (* [comment removed for export] *) intros x mtx aibx slx i off n Hx Hrx Hi. destruct (ir_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & H)]; [exfalso; exact (ir_no_live _ _ _ Hi) | exact (wf_live A W x mtx aibx slx i off n H Hrx Hi)].
    - (* [comment removed for export] *) intros x mtx aibx slx i ch Hx Hrx Hi Hi0. destruct (ir_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & H)]; [exfalso; exact (ir_no_nested _ _ Hi)|].
      destruct (wf_nested A W x mtx aibx slx i ch H Hrx Hi Hi0) as (mc & aibc & slc & Hmc & Hrc & R).
      exists mc, aibc, slc. split; [exact (proj1 (ir_old_grp _ _ _ _ Hmc Hrc)) | split; [exact Hrc | exact R]].
    - (* [comment removed for export] *) intros ch mc aibc slc Hch Hrc Hmlc. destruct (ir_group_inv ch mc aibc slc Hch Hrc) as [(-> & -> & -> & ->) | (Hne & H)]; [exfalso; lia|].
      destruct (wf_nested_parent A W ch mc aibc slc H Hrc Hmlc) as (x & mtx & aibx & slx & j & Hx & Hrx & Hj0 & Hj).
      exists x, mtx, aibx, slx, j. split; [exact (proj1 (ir_old_grp _ _ _ _ Hx Hrx)) | split; [exact Hrx | split; [exact Hj0 | exact Hj]]].
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx. destruct (ir_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & H)].
      + exists m, ir_mt, ir_aib, ir_slots. split; [exact ir_meta_m|]. split; [reflexivity|]. split; [exact MP|]. rewrite ir_mem, ir_map_len. split; [lia|]. split; [lia | auto].
      + destruct (wf_grp_root A W x mtx aibx slx H Hrx) as (mr & mtr & aibr & slr & Hmr & Hrr & R).
        exists mr, mtr, aibr, slr. split; [exact (proj1 (ir_old_grp _ _ _ _ Hmr Hrr)) | split; [exact Hrr | exact R]].
    - (* [comment removed for export] *) intros x mtx aibx slx x' mtx' aibx' slx' Hx Hrx Hx' Hrx' Hne.
      destruct (ir_group_inv _ _ _ _ Hx Hrx) as [(-> & -> & -> & ->) | (Hn & H)]; destruct (ir_group_inv _ _ _ _ Hx' Hrx') as [(-> & -> & -> & ->) | (Hn' & H')].
      + exfalso. exact (Hne eq_refl).
      + destruct (lam_cases _ (old_grp_ext _ _ _ _ H' Hrx')) as [D|D]; [left; exact D | right; left; exact D].
      + destruct (lam_cases _ (old_grp_ext _ _ _ _ H Hrx)) as [D|D]; [right; left; exact D | left; exact D].
      + exact (wf_laminar A W x mtx aibx slx x' mtx' aibx' slx' H Hrx H' Hrx' Hne).
    - exact (wf_act_head A W).
    - exact (wf_act_nodup A W).
    - (* [comment removed for export] *) intros c Hc. apply ir_dll; [apply ir_not_in_act | exact (wf_act_dll A W c Hc)].
    - (* [comment removed for export] *) intros c x Hin. destruct (wf_act_mem A W c x Hin) as (mtx & aibx & slx & Hx & Hrx & R).
      exists mtx, aibx, slx. split; [exact (proj1 (ir_old_grp _ _ _ _ Hx Hrx)) | auto].
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx Hnin. destruct (ir_group_inv _ _ _ _ Hx Hrx) as [(-> & -> & -> & ->) | (Hn & H)]; [rewrite ir_prev, ir_next; auto | exact (wf_unlinked A W x mtx aibx slx H Hrx Hnin)].
    - (* [comment removed for export] *) intros c x mtx Hin Hne Hx. destruct (ir_meta_inv x mtx Hx) as [(-> & ->) | (_ & Hx')]; [exfalso; exact (ir_not_in_act c Hin) | exact (wf_act_nonhead A W c x mtx Hin Hne Hx')].
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx H63. destruct (ir_group_inv _ _ _ _ Hx Hrx) as [(-> & -> & -> & ->) | (Hn & H)]; [rewrite ir_prev, ir_next; split; reflexivity | exact (wf_act63 A W x mtx aibx slx H Hrx H63)].
    - (* [comment removed for export] *) intros pg x mtx aibx slx Hpg Hx Hrx Hml. destruct (ir_group_inv _ _ _ _ Hx Hrx) as [(-> & -> & -> & ->) | (Hn & H)]; [| exact (wf_disj_area_grp A W pg x mtx aibx slx Hpg H Hrx Hml)].
      rewrite ir_mem, ir_map_len. destruct (old_area pg Hpg); lia.
    - (* [comment removed for export] *) intros x mtx aibx slx x' mtx' aibx' slx' Hx Hrx Hmlx Hx' Hrx' Hmlx' Hne.
      destruct (ir_group_inv _ _ _ _ Hx Hrx) as [(-> & -> & -> & ->) | (Hn & H)]; destruct (ir_group_inv _ _ _ _ Hx' Hrx') as [(-> & -> & -> & ->) | (Hn' & H')].
      + exfalso. exact (Hne eq_refl).
      + rewrite ir_mem, ir_map_len. destruct (old_root_map _ _ _ _ H' Hrx' Hmlx'); lia.
      + rewrite ir_mem, ir_map_len. destruct (old_root_map _ _ _ _ H Hrx Hmlx); lia.
      + exact (wf_disj_grp_grp A W x mtx aibx slx x' mtx' aibx' slx' H Hrx Hmlx H' Hrx' Hmlx' Hne).
    - (* [comment removed for export] *) intros x mtx aibx slx x' mtx' aibx' slx' Hx Hrx Hx' Hrx' E.
      destruct (ir_group_inv _ _ _ _ Hx Hrx) as [(-> & -> & -> & ->) | (Hn & H)]; destruct (ir_group_inv _ _ _ _ Hx' Hrx') as [(-> & -> & -> & ->) | (Hn' & H')].
      + reflexivity.
      + exfalso. rewrite ir_mem in E. exact (mem_new_old _ _ _ _ H' Hrx' (eq_sym E)).
      + exfalso. rewrite ir_mem in E. exact (mem_new_old _ _ _ _ H Hrx E).
      + exact (wf_grp_mem_inj A W x mtx aibx slx x' mtx' aibx' slx' H Hrx H' Hrx' E).
    - (* [comment removed for export] *) intros q n. rewrite (wf_live_map A W q n). unfold is_live. cbn [a_meta instR]. split.
      + intros (x & mtx & aibx & slx & i & off & Hx & Hrx & R). exists x, mtx, aibx, slx, i, off.
        split; [exact (proj1 (ir_old_grp _ _ _ _ Hx Hrx)) | auto].
      + intros (x & mtx & aibx & slx & i & off & Hx & Hrx & Hi0 & Hi & E). destruct (ir_group_inv _ _ _ _ Hx Hrx) as [(-> & -> & -> & ->) | (Hn & H)]; [exfalso; exact (ir_no_live _ _ _ Hi)|].
        exists x, mtx, aibx, slx, i, off. auto 10.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx Hlast. destruct (ir_group_inv _ _ _ _ Hx Hrx) as [(-> & -> & -> & ->) | (Hn & H)]; [exact (span_new Hlast) | exact (wf_span A W x mtx aibx slx H Hrx Hlast)].
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx Hlast Hml Hsc48. destruct (ir_group_inv _ _ _ _ Hx Hrx) as [(-> & -> & -> & ->) | (Hn & H)]; [| exact (wf_single A W x mtx aibx slx H Hrx Hlast Hml Hsc48)].
      rewrite ir_sc, ir_stride. rewrite ir_last in Hlast. rewrite ir_sc in Hsc48. replace (cnt =? 1) with true by (symmetry; apply Z.eqb_eq; lia). exact (Hsingle ltac:(lia) Hsc48).
    - (* [comment removed for export] *) intros x mtx aibx slx j Hx Hrx Hj. destruct (ir_group_inv _ _ _ _ Hx Hrx) as [(-> & -> & -> & ->) | (Hn & H)]; [| exact (wf_inactive A W x mtx aibx slx j H Hrx Hj)].
      rewrite B2, ir_last in Hj. rewrite ir_freed, M6 by lia.
      apply andb_true_intro; split; [apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt] | apply Z.leb_le]; lia.
    - (* [comment removed for export] *) intros c x mtx aibx slx x' mtx' aibx' slx' Hin Hin' Hx Hrx Hx' Hrx'.
      destruct (ir_group_inv _ _ _ _ Hx Hrx) as [(-> & -> & -> & ->) | (Hn & H)]; [exfalso; exact (ir_not_in_act c Hin)|].
      destruct (ir_group_inv _ _ _ _ Hx' Hrx') as [(-> & -> & -> & ->) | (Hn' & H')]; [exfalso; exact (ir_not_in_act c Hin')|].
      exact (wf_partial A W c x mtx aibx slx x' mtx' aibx' slx' Hin Hin' H Hrx H' Hrx').
    - exact (wf_ctx_nonneg A W).
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx Hml. destruct (ir_group_inv _ _ _ _ Hx Hrx) as [(-> & -> & -> & ->) | (Hn & H)]; [exfalso; lia | exact (wf_nested_small A W x mtx aibx slx H Hrx Hml)].
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx Hsc48 Hmask. destruct (ir_group_inv _ _ _ _ Hx Hrx) as [(-> & -> & -> & ->) | (Hn & H)]; [| exact (wf_reusable A W x mtx aibx slx H Hrx Hsc48 Hmask)].
      rewrite ir_sc, ir_stride. rewrite ir_sc in Hsc48. destruct (Z.eqb_spec cnt 1) as [E | NE]; [exfalso; exact (Hmask (K5 E)) | unfold size; lia].
    - (* [comment removed for export] *) intros pa pm paib psl j ch x mtx aibx slx Hpa Hpr Hj0 Hj Hx Hrx Hlo Hhi.
      destruct (ir_group_inv _ _ _ _ Hpa Hpr) as [(-> & -> & -> & ->) | (Hn & Hpa0)]; [exfalso; exact (ir_no_nested _ _ Hj)|].
      destruct (ir_group_inv _ _ _ _ Hx Hrx) as [(-> & -> & -> & ->) | (Hn' & Hx0)].
      + exfalso. exact (cover_new pa pm paib psl j ch Hpa0 Hpr Hj0 Hj Hlo Hhi).
      + destruct (wf_cover A W pa pm paib psl j ch x mtx aibx slx Hpa0 Hpr Hj0 Hj Hx0 Hrx Hlo Hhi) as (mtc & aibc & slc & Hch & Hrc & R).
        exists mtc, aibc, slc. split; [exact (proj1 (ir_old_grp _ _ _ _ Hch Hrc)) | split; [exact Hrc | exact R]].
    - exact (wf_shift A W).
    - exact (wf_noarea_shift A W).
    - exact (wf_brk0 A W).
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx Hsc48. destruct (ir_group_inv _ _ _ _ Hx Hrx) as [(-> & -> & -> & ->) | (Hn & H)]; [| exact (wf_stride20 A W x mtx aibx slx H Hrx Hsc48)].
      rewrite ir_stride. rewrite ir_sc in Hsc48. pose proof (size_rng Hsc48). destruct (Z.eqb_spec cnt 1) as [E | NE]; [pose proof (Hs20 E Hsc48); lia | unfold size in *; lia].
    - exact (wf_pages_al A W).
    - exact (wf_disj_page_area A W).
    - (* [comment removed for export] *) intros pg x mtx aibx slx Hpg Hx Hrx Hml. destruct (ir_group_inv _ _ _ _ Hx Hrx) as [(-> & -> & -> & ->) | (Hn & H)]; [| exact (wf_disj_page_grp A W pg x mtx aibx slx Hpg H Hrx Hml)].
      rewrite ir_mem, ir_map_len. destruct (old_page pg Hpg); lia.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx Hp'. destruct (ir_group_inv _ _ _ _ Hx Hrx) as [(-> & -> & -> & ->) | (Hn & H)]; [| exact (wf_partial_sc A W x mtx aibx slx H Hrx Hp')].
      rewrite ir_sc. rewrite B2, ir_last in Hp'. exact (Hpsc Hp').
    - exact (wf_mblocks_len A W).
    - exact (wf_mblocks_sz A W).
    - exact (wf_shift_mblocks A W).
    - exact (wf_shift_acct A W).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis Hfields : forall fl, mt_f md fl = ir_f fl.

  Lemma ir_mt_fields : forall fl, mt_f ir_mt fl = mt_f md fl.
  Proof using Hfields. pu_keep (Hfields). intros fl. rewrite Hfields. reflexivity. Qed.

  Lemma ir_slot_facts : forall i st f, nth_error ir_slots i = Some st -> In f (slot_fields ir_mt (Z.of_nat i) st) ->
    f = FCT (slot_start ir_mt (Z.of_nat i) - 4) 1 0 \/ f = FCT (slot_end ir_mt (Z.of_nat i)) 1 0.
  Proof using HL Hab Haidx Hcnt Hsc. pu_keep (HL, Hab, Haidx, Hcnt, Hsc).
    intros i st f Hi Hf. destruct (ir_slots_inv _ _ Hi) as [(_ & ->) | (_ & ->)]; cbn in Hf; unfold slot_start, slot_end;
      (destruct Hf as [<- | [<- | []]]; [left | right]; reflexivity).
  Qed.

  Lemma has_instR : forall f, has instR f ->
    has A f \/ f = FCT p 8 m \/ f = FCT (p + 8) 1 ir_aib \/
    (exists i, (i < Z.to_nat cnt)%nat /\ (f = FCT (slot_start ir_mt (Z.of_nat i) - 4) 1 0 \/ f = FCT (slot_end ir_mt (Z.of_nat i)) 1 0)).
  Proof using HL Hab Haidx Hcnt Hfields Hm Hsc. pu_keep (HL, Hab, Haidx, Hcnt, Hfields, Hm, Hsc).
    intros f [Hc | [Har | [Hmf | Hg]]].
    - left. left. exact Hc.
    - left. right; left. exact Har.
    - left. right; right; left. destruct Hmf as (x & mtx & fl & Hx & ->). destruct (ir_meta_inv x mtx Hx) as [(-> & ->) | (Hne & H)].
      + exists m, md, fl. rewrite ir_mt_fields. auto.
      + exists x, mtx, fl. auto.
    - destruct Hg as (x & mtx & aibx & slx & Hx & Hrx & R). destruct (ir_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & H)].
      + right. destruct R as [Hh | (i & st & Hi & Hf)].
        * cbn in Hh. destruct Hh as [<- | [<- | []]]; [left; reflexivity | right; left; reflexivity].
        * right; right. exists i. split; [| exact (ir_slot_facts i st f Hi Hf)].
          pose proof (proj1 (nth_error_Some ir_slots i) ltac:(rewrite Hi; discriminate)) as LL. rewrite ir_slots_len in LL. exact LL.
      + left. right; right; right. exists x, mtx, aibx, slx. auto.
  Qed.

  Lemma has_instR_intro : forall f, has A f -> has instR f.
  Proof using Hfields Hm Hr. pu_keep (Hfields, Hm, Hr).
    intros f [Hc | [Har | [Hmf | Hg]]].
    - left. exact Hc.
    - right; left. exact Har.
    - right; right; left. destruct Hmf as (x & mtx & fl & Hx & ->). destruct (Z.eq_dec x m) as [-> | Hne].
      + rewrite Hm in Hx. injection Hx as <-. exists m, ir_mt, fl. rewrite ir_mt_fields. split; [exact ir_meta_m | reflexivity].
      + exists x, mtx, fl. rewrite (ir_meta_other x Hne). auto.
    - right; right; right. destruct Hg as (x & mtx & aibx & slx & Hx & Hrx & R).
      exists x, mtx, aibx, slx. split; [exact (proj1 (ir_old_grp _ _ _ _ Hx Hrx)) | auto].
  Qed.

  Lemma has_instR_hdr : has instR (FCT p 8 m) /\ has instR (FCT (p + 8) 1 ir_aib).
  Proof using Type. pu_keep tt.
    split; (right; right; right; exists m, ir_mt, ir_aib, ir_slots; split; [exact ir_meta_m|]; split; [reflexivity|]; left; cbn; auto).
  Qed.

  Lemma has_instR_slot : forall i, (i < Z.to_nat cnt)%nat ->
    has instR (FCT (slot_start ir_mt (Z.of_nat i) - 4) 1 0) /\ has instR (FCT (slot_end ir_mt (Z.of_nat i)) 1 0).
  Proof using HL Hab Haidx Hcnt Hsc. pu_keep (HL, Hab, Haidx, Hcnt, Hsc).
    intros i Hi.
    assert (E : exists st, nth_error ir_slots i = Some st).
    { destruct (nth_error ir_slots i) as [st|] eqn:E; [exists st; reflexivity|].
      exfalso. apply nth_error_None in E. rewrite ir_slots_len in E. lia. }
    destruct E as [st Hst].
    assert (Hin : forall f, In f (slot_fields ir_mt (Z.of_nat i) st) -> has instR f).
    { intros f Hf. right; right; right. exists m, ir_mt, ir_aib, ir_slots. split; [exact ir_meta_m|]. split; [reflexivity|]. right. exists i, st. auto. }
    destruct (ir_slots_inv _ _ Hst) as [(_ & ->) | (_ & ->)]; (split; apply Hin; cbn; auto).
  Qed.

  Lemma dom_instR : forall x, dom instR x <-> dom A x \/ p <= x < p + L.
  Proof using HL HLm Hab Hcnt Hm Hr Hsc. pu_keep (HL, HLm, Hab, Hcnt, Hm, Hr, Hsc).
    intros x. unfold dom. cbn [a_areas a_meta a_pages instR]. split.
    - intros [Ha | [(y & mty & aiby & sly & Hy & Hry & Hml & R) | Hp]]; [left; left; exact Ha | | left; right; right; exact Hp].
      destruct (ir_group_inv y mty aiby sly Hy Hry) as [(-> & -> & -> & ->) | (Hne & H)].
      + right. rewrite ir_mem, ir_map_len in R. exact R.
      + left. right; left. exists y, mty, aiby, sly. auto.
    - intros [[Ha | [(y & mty & aiby & sly & Hy & Hry & Hml & R) | Hp]] | Hn]; [left; exact Ha | | right; right; exact Hp |].
      + right; left. exists y, mty, aiby, sly. split; [exact (proj1 (ir_old_grp _ _ _ _ Hy Hry)) | auto].
      + right; left. exists m, ir_mt, ir_aib, ir_slots. split; [exact ir_meta_m|]. split; [reflexivity|]. split; [exact ir_maplen_pos|].
        rewrite ir_mem, ir_map_len. exact Hn.
  Qed.

  Lemma VMok_instR : forall h, VMok A h ->
    In (Z_to_bv 64 p, Z_to_bv 64 L) (vm_maps h) ->
    region_free (vm_noaccess h) (Z_to_bv 64 p) (Z_to_bv 64 L) = true ->
    VMok instR h.
  Proof using HL HL64 HLm Hab Hcnt Hhr Hm Hr Hsc Hxm. pu_keep (HL, HL64, HLm, Hab, Hcnt, Hhr, Hm, Hr, Hsc, Hxm).
    intros h [Vg Vb Va Vres Vbv Vpw Vmw Vna Vac Vpc Vall Vspan Vtop] Hin Hrf.
    constructor; cbn [a_ctx a_areas a_meta a_freelist a_active a_pages a_brk_lo a_live a_mblocks a_xmaps instR]; try assumption.
    - intros x mtx aibx slx Hx Hrx Hml. destruct (ir_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & H)]; [| exact (Vg x mtx aibx slx H Hrx Hml)].
      rewrite ir_mem, ir_map_len. split; [exact Hin | exact Hrf].
    - intros b sz Hb. destruct (Vall b sz Hb) as [(x & mtx & aibx & slx & Hx & Hrx & R) | [Ho | (c & l & Hcl & R)]].
      + left. exists x, mtx, aibx, slx. split; [exact (proj1 (ir_old_grp _ _ _ _ Hx Hrx)) | auto].
      + right; left. exact Ho.
      + rewrite Hxm in Hcl. apply in_app_iff in Hcl. destruct Hcl as [Hcl | [E | Hcl]].
        * right; right. exists c, l. split; [apply in_app_iff; left; exact Hcl | exact R].
        * injection E as <- <-.
          (* [comment removed for export] *)
          pose proof (Vmw b sz Hb) as (S1 & S2 & S3 & S4). unfold heap_range in Hhr. ceil.
          left. exists m, ir_mt, ir_aib, ir_slots. split; [exact ir_meta_m|]. split; [reflexivity|]. split; [exact ir_maplen_pos|].
          rewrite ir_mem, ir_map_len.
          destruct (maps_pw_in2 _ _ _ _ _ Vpw Hb Hin) as [E | [D | D]].
          -- injection E as -> ->. rewrite !uZ by lia. auto.
          -- exfalso. rewrite uZ in D by lia. lia.
          -- exfalso. rewrite !uZ in D by lia. lia.
        * right; right. exists c, l. split; [apply in_app_iff; right; exact Hcl | exact R].
  Qed.

  (* [comment removed for export] *)
  Lemma meta_usage_instR : forall c x, meta_usage instR c x = meta_usage A c x + (if Z.eq_dec x m then (if sc =? c then cnt else 0) else 0).
  Proof using HL HLm Hab Hcnt Hm Hr Hsc. pu_keep (HL, HLm, Hab, Hcnt, Hm, Hr, Hsc).
    intros c x. unfold meta_usage. rewrite ir_meta. destruct (Z.eq_dec x m) as [-> | Hne]; [| lia].
    rewrite Hm, Hr. unfold ir_mt. rewrite mt_role_MT. fold ir_mt. rewrite ir_sc, ir_cnt. lia.
  Qed.

  Lemma usage_of_instR : forall c, 0 <= c < 48 -> usage_of instR c = usage_of A c + (if sc =? c then cnt else 0).
  Proof using HL HLm HW Hab Hcnt Hm Hr Hsc. pu_keep (HL, HLm, HW, Hab, Hcnt, Hm, Hr, Hsc).
    intros c Hc.
    destruct (proj1 (wf_meta_dom A HW m) ltac:(rewrite Hm; discriminate)) as (pg & k & Hpg & Hk & Em).
    rewrite (usage_of_point A instR c m pg k (- (if sc =? c then cnt else 0)) HW eq_refl Hpg Hk Em); [lia | |].
    - intros x Hx. rewrite meta_usage_instR. destruct (Z.eq_dec x m); [contradiction | lia].
    - rewrite meta_usage_instR. destruct (Z.eq_dec m m); [lia | contradiction].
  Qed.

  Lemma AvOK_instR : AvOK A -> AvOK instR.
  Proof using Type. pu_keep tt.
    intros Hav x mtx Hx Hrx. cbn [a_ctx a_areas instR].
    destruct (ir_meta_inv x mtx Hx) as [(-> & ->) | (Hne & H)]; [cbn in Hrx; discriminate Hrx | exact (Hav x mtx H Hrx)].
  Qed.

  Lemma deads_instR : forall D, deads A (m :: D) -> ~ In m D -> deads instR D.
  Proof using Hm. pu_keep (Hm).
    intros D Hd Hnin x. split.
    - intros (mtx & Hx & Hrx). destruct (ir_meta_inv x mtx Hx) as [(-> & ->) | (Hne & H)]; [cbn in Hrx; discriminate Hrx|].
      destruct (proj1 (Hd x) (ex_intro _ mtx (conj H Hrx))) as [-> | Hin]; [contradiction | exact Hin].
    - intros Hin. assert (Hne : x <> m) by (intros ->; exact (Hnin Hin)).
      destruct (proj2 (Hd x) (or_intror Hin)) as (mtx & Hx & Hrx). exists mtx. rewrite (ir_meta_other x Hne). auto.
  Qed.
End InstallRoot.

End WithLayout.
