(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_sep MallocInv_tables MallocInv_wf MallocInv_wf2 MallocInv_wf3
  MallocInv_dll MallocInv_coh MallocInv_steps MallocInv_w32 MallocInv_actw MallocInv_vm MallocInv_ops MallocInv_usage MallocInv_wf7.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Local Ltac pu_keep K := repeat match goal with H : ?T |- _ => lazymatch type of T with Prop => idtac | _ => fail end; lazymatch K with context [H] => fail | _ => idtac end;
                                                          tryif (match goal with X := _ |- _ => constr_eq X H end) then fail else clear H end.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

Section InstallNested.
  Variables (A : astate) (m : Z) (md : meta_rec) (pa : Z) (pm : meta_rec) (paib : Z) (psl : list slot_st) (i cnt sc ab : Z).
  Hypothesis HW : WF A.
  Hypothesis Hm : a_meta A m = Some md.
  Hypothesis Hr : mt_role md = RDead.
  Hypothesis Hpa : a_meta A pa = Some pm.
  Hypothesis Hpr : mt_role pm = RGroup paib psl.
  Hypothesis Hi0 : 0 <= i.
  Hypothesis Hi : nth_error psl (Z.to_nat i) = Some STaken.
  Hypothesis Hsc : 0 <= sc < 48.
  Hypothesis Hcnt : 2 <= cnt <= 32.
  Hypothesis Hab : 0 <= ab < 256.
  Hypothesis Hfit : 16 + cnt * (16 * size_class sc) <= mt_stride pm.
  Hypothesis Hsmall : 16 + cnt * (16 * size_class sc) <= 2048.

  Let size := 16 * size_class sc.
  Definition in_p : Z := slot_start pm i.
  Let p := in_p.

  Definition in_f (fl : mfield) : Z :=
    match fl with
    | FPrev => 0 | FNext => 0 | FMem => p
    | FAvail => iav cnt (cnt - 1) | FFreed => ifr cnt (cnt - 1) | FW32 => iw32 0 sc cnt
    end.
  Definition in_aib : Z := Z.lor (Z.land ab 224) (cnt - 1).
  Definition in_slots : list slot_st := STaken :: repeat SIdle (Z.to_nat (cnt - 1)).
  Definition in_mt : meta_rec := MT in_f (RGroup in_aib in_slots).
  Definition psl' : list slot_st := list_set psl (Z.to_nat i) (SNested m).
  Definition pm' : meta_rec := MT (mt_f pm) (RGroup paib psl').
  Definition instN : astate :=
    AST (a_ctx A) (a_areas A) (aupd (aupd (a_meta A) pa pm') m in_mt) (a_freelist A) (a_active A) (a_pages A) (a_brk_lo A)
        (a_live A) (a_mblocks A) (a_xmaps A).

  (* [comment removed for export] *)
  Lemma pa_ne_m : pa <> m.
  Proof using Hm Hpa Hpr Hr. pu_keep (Hm, Hpa, Hpr, Hr). intros ->. rewrite Hm in Hpa. injection Hpa as ->. rewrite Hr in Hpr. discriminate Hpr. Qed.
  Lemma size_rng : 16 <= size <= 16 * 8191.
  Proof using Hab Hcnt Hsc Hsmall p. pu_keep (Hab, Hcnt, Hsc, Hsmall, p). pose proof (size_class_range sc Hsc). unfold size. lia. Qed.
  Lemma Hcnt1 : 1 <= cnt <= 32. Proof using Hab Hcnt Hsc p size. pu_keep (Hab, Hcnt, Hsc, p, size). lia. Qed.
  Lemma Haidx : 0 <= cnt - 1 <= cnt - 1. Proof using Hab Hcnt Hsc p size. pu_keep (Hab, Hcnt, Hsc, p, size). lia. Qed.

  (* [comment removed for export] *)
  Lemma pa_grp : 0 <= mt_w32 pm < 2^64 /\ (mt_sc pm < 48 \/ (mt_sc pm = 63 /\ mt_last pm = 0 /\ 0 < mt_maplen pm)) /\
    Z.of_nat (length psl) = mt_cnt pm /\ 16 <= mt_stride pm /\ mt_mem pm mod 16 = 0 /\ 0x1000 <= mt_mem pm /\
    mt_mem pm + 16 + mt_cnt pm * mt_stride pm <= alloc_ceiling.
  Proof using HW Hab Hpa Hpr Hsc p size. pu_keep (HW, Hab, Hpa, Hpr, Hsc, p, size).
    pose proof (wf_grp A HW pa pm paib psl Hpa Hpr) as (Hw & _ & Hscx & Hlen & _ & _ & _ & _ & _ & _ & _ & Hal & Hmem & _ & Hce & _).
    pose proof (stride_ge16 pm ltac:(lia) Hscx). repeat split; try assumption; lia.
  Qed.
  Lemma Hilt : (Z.to_nat i < length psl)%nat.
  Proof using Hi. pu_keep (Hi). apply (proj1 (nth_error_Some psl (Z.to_nat i))). rewrite Hi. discriminate. Qed.
  Lemma Hic : i + 1 <= mt_cnt pm.
  Proof using HW Hab Hi Hpa Hpr Hsc size. pu_keep (HW, Hab, Hi, Hpa, Hpr, Hsc, size). pose proof pa_grp as (_ & _ & Hlen & _). pose proof Hilt. lia. Qed.
  Lemma slot_i_in : gext_lo pm + 16 <= slot_start pm i /\ slot_end pm i <= gext_hi pm.
  Proof using HW Hab Hi Hi0 Hpa Hpr Hsc size. pu_keep (HW, Hab, Hi, Hi0, Hpa, Hpr, Hsc, size). pose proof pa_grp as (_ & _ & _ & S16 & _). apply (slot_in_ext pm i Hi0 Hic). lia. Qed.
  Lemma slot_i_len : slot_end pm i = slot_start pm i + mt_stride pm - 4.
  Proof using Hab Hsc size. pu_keep (Hab, Hsc, size). unfold slot_end, slot_start, slot_end_g, slot_start_g. lia. Qed.
  Lemma slots_apart : forall mt j j', 0 <= j -> 0 <= j' -> j <> j' -> 0 <= mt_stride mt ->
    slot_end mt j + 4 <= slot_start mt j' \/ slot_end mt j' + 4 <= slot_start mt j.
  Proof using Hab Hsc p size. pu_keep (Hab, Hsc, p, size).
    intros mt j j' Hj Hj' Hne Hsd. unfold slot_end, slot_start, slot_end_g, slot_start_g.
    destruct (Z.lt_ge_cases j j') as [Hlt | Hge].
    - left. assert ((j + 1) * mt_stride mt <= j' * mt_stride mt) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
    - right. assert ((j' + 1) * mt_stride mt <= j * mt_stride mt) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma in_w32 : mt_w32 in_mt = iw32 0 sc cnt. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma in_mem : mt_mem in_mt = p. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma in_avail : mt_avail in_mt = iav cnt (cnt - 1). Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma in_freed : mt_freed in_mt = ifr cnt (cnt - 1). Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma in_prev : mt_prev in_mt = 0. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma in_next : mt_next in_mt = 0. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma in_last : mt_last in_mt = cnt - 1. Proof using Hab Hcnt Hsc. pu_keep (Hab, Hcnt, Hsc). unfold mt_last. rewrite in_w32. apply iw32_last; [lia | reflexivity | lia | exact Hcnt1]. Qed.
  Lemma in_cnt : mt_cnt in_mt = cnt. Proof using Hab Hcnt Hsc. pu_keep (Hab, Hcnt, Hsc). unfold mt_cnt. rewrite in_last. lia. Qed.
  Lemma in_sc : mt_sc in_mt = sc. Proof using Hab Hcnt Hsc. pu_keep (Hab, Hcnt, Hsc). unfold mt_sc. rewrite in_w32. apply iw32_sc; [lia | reflexivity | lia | exact Hcnt1]. Qed.
  Lemma in_maplen : mt_maplen in_mt = 0. Proof using Hab Hcnt Hsc. pu_keep (Hab, Hcnt, Hsc). unfold mt_maplen. rewrite in_w32. rewrite iw32_maplen; [reflexivity | lia | reflexivity | lia | exact Hcnt1]. Qed.
  Lemma in_stride : mt_stride in_mt = size.
  Proof using Hab Hcnt Hsc. pu_keep (Hab, Hcnt, Hsc). unfold mt_stride. rewrite in_maplen, in_sc. reflexivity. Qed.
  Lemma in_w32_range : 0 <= mt_w32 in_mt < 2^64.
  Proof using Hab Hcnt Hsc. pu_keep (Hab, Hcnt, Hsc). rewrite in_w32. unfold iw32. lia. Qed.
  Lemma in_gext : gext_lo in_mt = p /\ gext_hi in_mt = p + 12 + cnt * size /\ gext_hi in_mt <= slot_end pm i /\ p + 16 <= gext_hi in_mt.
  Proof using Hab Hcnt Hfit Hsc Hsmall. pu_keep (Hab, Hcnt, Hfit, Hsc, Hsmall).
    unfold gext_lo, gext_hi. rewrite in_mem, in_cnt, in_stride. pose proof size_rng. pose proof slot_i_len.
    assert (32 <= cnt * size) by nia. unfold p, in_p in *. repeat split; lia.
  Qed.
  Lemma in_aib_rng : 0 <= in_aib < 256 /\ in_aib mod 32 = cnt - 1.
  Proof using Hab Hcnt Hsc p size. pu_keep (Hab, Hcnt, Hsc, p, size). unfold in_aib. apply aib_lor_rng; lia. Qed.
  Lemma p_al16 : p mod 16 = 0.
  Proof using HW Hab Hpa Hpr Hsc i size. pu_keep (HW, Hab, Hpa, Hpr, Hsc, i, size).
    pose proof pa_grp as (_ & _ & _ & _ & Hal & _). destruct (stride_16 pm) as [q Hq].
    unfold p, in_p, slot_start, slot_start_g. rewrite Hq.
    rewrite (Z_div_exact_full_2 (mt_mem pm) 16) by lia.
    replace (16 * (mt_mem pm / 16) + 16 + i * (16 * q)) with ((mt_mem pm / 16 + 1 + i * q) * 16) by lia. apply Z_mod_mult.
  Qed.

  (* [comment removed for export] *)
  Lemma in_meta : forall x, a_meta instN x = if Z.eq_dec x m then Some in_mt else if Z.eq_dec x pa then Some pm' else a_meta A x.
  Proof using Type. pu_keep tt. intros x. reflexivity. Qed.
  Lemma in_meta_m : a_meta instN m = Some in_mt.
  Proof using Type. pu_keep tt. rewrite in_meta. destruct (Z.eq_dec m m); [reflexivity | contradiction]. Qed.
  Lemma in_meta_pa : a_meta instN pa = Some pm'.
  Proof using Hm Hpa Hpr Hr. pu_keep (Hm, Hpa, Hpr, Hr). rewrite in_meta. pose proof pa_ne_m. destruct (Z.eq_dec pa m); [contradiction|]. destruct (Z.eq_dec pa pa); [reflexivity | contradiction]. Qed.
  Lemma in_meta_other : forall x, x <> m -> x <> pa -> a_meta instN x = a_meta A x.
  Proof using Type. pu_keep tt. intros x Hx Hx'. rewrite in_meta. destruct (Z.eq_dec x m); [contradiction|]. destruct (Z.eq_dec x pa); [contradiction | reflexivity]. Qed.
  Lemma in_meta_inv : forall x mtx, a_meta instN x = Some mtx ->
    (x = m /\ mtx = in_mt) \/ (x = pa /\ mtx = pm') \/ (x <> m /\ x <> pa /\ a_meta A x = Some mtx).
  Proof using Type. pu_keep tt.
    intros x mtx Hx. rewrite in_meta in Hx. destruct (Z.eq_dec x m) as [-> | Hne]; [left; injection Hx as <-; auto|].
    destruct (Z.eq_dec x pa) as [-> | Hne']; [right; left; injection Hx as <-; auto | right; right; auto].
  Qed.

  (* [comment removed for export] *)
  Lemma pm'_f : forall fl, mt_f pm' fl = mt_f pm fl. Proof using Type. pu_keep tt. intros fl. unfold pm'. apply mt_f_MT. Qed.
  Lemma pm'_w32 : mt_w32 pm' = mt_w32 pm. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma pm'_mem : mt_mem pm' = mt_mem pm. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma pm'_prev : mt_prev pm' = mt_prev pm. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma pm'_next : mt_next pm' = mt_next pm. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma pm'_avail : mt_avail pm' = mt_avail pm. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma pm'_freed : mt_freed pm' = mt_freed pm. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma pm'_last : mt_last pm' = mt_last pm. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma pm'_maplen : mt_maplen pm' = mt_maplen pm. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma pm'_sc : mt_sc pm' = mt_sc pm. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma pm'_stride : mt_stride pm' = mt_stride pm. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma pm'_cnt : mt_cnt pm' = mt_cnt pm. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma pm'_gext_lo : gext_lo pm' = gext_lo pm. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma pm'_gext_hi : gext_hi pm' = gext_hi pm. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma pm'_slot_start : forall j, slot_start pm' j = slot_start pm j. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma pm'_slot_end : forall j, slot_end pm' j = slot_end pm j. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma pm'_grp_map_len : grp_map_len pm' = grp_map_len pm. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma pm'_slot_fields : forall j st, slot_fields pm' j st = slot_fields pm j st. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma psl'_length : length psl' = length psl.
  Proof using Type. pu_keep tt. unfold psl'. apply list_set_length. Qed.
  Lemma psl'_i : nth_error psl' (Z.to_nat i) = Some (SNested m).
  Proof using Hi. pu_keep (Hi). unfold psl'. apply list_set_nth_same. exact Hilt. Qed.
  Lemma psl'_other : forall j, j <> Z.to_nat i -> nth_error psl' j = nth_error psl j.
  Proof using Type. pu_keep tt. intros j Hj. unfold psl'. apply list_set_nth_other. intros E. apply Hj. symmetry. exact E. Qed.
  Lemma psl'_inv : forall j st, nth_error psl' (Z.to_nat j) = Some st -> 0 <= j ->
    (j = i /\ st = SNested m) \/ (j <> i /\ nth_error psl (Z.to_nat j) = Some st).
  Proof using Hab Hi Hi0 Hsc p size. pu_keep (Hab, Hi, Hi0, Hsc, p, size).
    intros j st Hj Hj0. destruct (Z.eq_dec j i) as [-> | Hne].
    - left. rewrite psl'_i in Hj. injection Hj as <-. auto.
    - right. rewrite psl'_other in Hj by lia. auto.
  Qed.
  Lemma psl'_inv_nat : forall j st, nth_error psl' j = Some st ->
    (j = Z.to_nat i /\ st = SNested m) \/ (j <> Z.to_nat i /\ nth_error psl j = Some st).
  Proof using Hi. pu_keep (Hi).
    intros j st Hj. destruct (Nat.eq_dec j (Z.to_nat i)) as [-> | Hne].
    - left. rewrite psl'_i in Hj. injection Hj as <-. auto.
    - right. rewrite psl'_other in Hj by exact Hne. auto.
  Qed.
  Lemma psl_nested_kept : forall j ch, nth_error psl j = Some (SNested ch) -> nth_error psl' j = Some (SNested ch) /\ j <> Z.to_nat i.
  Proof using Hi. pu_keep (Hi).
    intros j ch Hj. assert (Hne : j <> Z.to_nat i) by (intros ->; rewrite Hi in Hj; discriminate Hj).
    rewrite psl'_other by exact Hne. auto.
  Qed.

  (* [comment removed for export] *)
  Lemma in_group_inv : forall x mtx aibx slx, a_meta instN x = Some mtx -> mt_role mtx = RGroup aibx slx ->
    (x = m /\ mtx = in_mt /\ aibx = in_aib /\ slx = in_slots) \/
    (x = pa /\ mtx = pm' /\ aibx = paib /\ slx = psl') \/
    (x <> m /\ x <> pa /\ a_meta A x = Some mtx).
  Proof using Type. pu_keep tt.
    intros x mtx aibx slx Hx Hrx. destruct (in_meta_inv x mtx Hx) as [(-> & ->) | [(-> & ->) | H]]; [left | right; left | right; right; exact H].
    - cbn in Hrx. injection Hrx as <- <-. auto.
    - cbn in Hrx. injection Hrx as <- <-. auto.
  Qed.
  (* [comment removed for export] *)
  Lemma in_fwd : forall y my aiby sly, a_meta A y = Some my -> mt_role my = RGroup aiby sly ->
    exists my' sly', a_meta instN y = Some my' /\ mt_role my' = RGroup aiby sly' /\ y <> m /\
      (forall fl, mt_f my' fl = mt_f my fl) /\ mt_w32 my' = mt_w32 my /\ mt_mem my' = mt_mem my /\
      mt_stride my' = mt_stride my /\ mt_cnt my' = mt_cnt my /\ mt_maplen my' = mt_maplen my /\ mt_sc my' = mt_sc my /\
      mt_last my' = mt_last my /\ gext_lo my' = gext_lo my /\ gext_hi my' = gext_hi my /\
      mt_avail my' = mt_avail my /\ mt_freed my' = mt_freed my /\ mt_prev my' = mt_prev my /\ mt_next my' = mt_next my /\
      grp_map_len my' = grp_map_len my /\ (forall j, slot_start my' j = slot_start my j) /\ (forall j, slot_end my' j = slot_end my j) /\
      (forall j ch, nth_error sly j = Some (SNested ch) -> nth_error sly' j = Some (SNested ch)) /\
      (forall j off n, nth_error sly' j = Some (SLive off n) <-> nth_error sly j = Some (SLive off n)) /\
      (forall j st, nth_error sly' j = Some st -> nth_error sly j = Some st \/ (y = pa /\ j = Z.to_nat i /\ st = SNested m)) /\
      ((y <> pa /\ my' = my /\ sly' = sly) \/ (y = pa /\ my' = pm' /\ sly' = psl')).
  Proof using Hab Hcnt Hi Hm Hpa Hpr Hr Hsc. pu_keep (Hab, Hcnt, Hi, Hm, Hpa, Hpr, Hr, Hsc).
    intros y my aiby sly Hy Hry.
    assert (Hym : y <> m) by (intros ->; rewrite Hm in Hy; injection Hy as ->; rewrite Hr in Hry; discriminate Hry).
    destruct (Z.eq_dec y pa) as [-> | Hnp].
    - rewrite Hpa in Hy. injection Hy as <-. rewrite Hpr in Hry. injection Hry as <- <-.
      exists pm', psl'. split; [exact in_meta_pa|]. split; [reflexivity|]. split; [exact Hym|]. split; [exact pm'_f|].
      repeat (split; [reflexivity|]). split.
      + intros j ch Hj. exact (proj1 (psl_nested_kept j ch Hj)).
      + split.
        * intros j off n. split; intros Hj.
          -- destruct (psl'_inv_nat j _ Hj) as [(_ & E) | (_ & E)]; [discriminate E | exact E].
          -- rewrite psl'_other; [exact Hj|]. intros ->. rewrite Hi in Hj. discriminate Hj.
        * split; [| right; auto]. intros j st Hj. destruct (psl'_inv_nat j st Hj) as [(-> & ->) | (_ & E)]; [right; auto | left; exact E].
    - exists my, sly. split; [rewrite (in_meta_other y Hym Hnp); exact Hy|]. split; [exact Hry|]. split; [exact Hym|].
      repeat (split; [reflexivity|]).
      split; [intros j ch Hj; exact Hj|]. split; [intros j off n; tauto|]. split; [intros j st Hj; left; exact Hj|]. left. auto.
  Qed.
  (* [comment removed for export] *)
  Lemma in_old_grp : forall y my aiby sly, a_meta A y = Some my -> mt_role my = RGroup aiby sly ->
    exists my' sly', a_meta instN y = Some my' /\ mt_role my' = RGroup aiby sly' /\ (forall fl, mt_f my' fl = mt_f my fl) /\
      gext_lo my' = gext_lo my /\ gext_hi my' = gext_hi my /\ mt_maplen my' = mt_maplen my /\ mt_mem my' = mt_mem my /\ grp_map_len my' = grp_map_len my.
  Proof using Hab Hcnt Hi Hm Hpa Hpr Hr Hsc. pu_keep (Hab, Hcnt, Hi, Hm, Hpa, Hpr, Hr, Hsc).
    intros y my aiby sly Hy Hry. destruct (in_fwd y my aiby sly Hy Hry) as (my' & sly' & H1 & H2 & _ & H3 & _ & H5 & _ & _ & H8 & _ & _ & H10 & H11 & _ & _ & _ & _ & H12 & _).
    exists my', sly'. auto 10.
  Qed.
  Lemma in_old : forall x mtx, a_meta A x = Some mtx -> (forall aib sl, mt_role mtx <> RGroup aib sl) -> mt_role mtx <> RDead -> a_meta instN x = Some mtx.
  Proof using Hm Hpa Hpr Hr. pu_keep (Hm, Hpa, Hpr, Hr).
    intros x mtx Hx Hng Hnd. rewrite in_meta_other; [exact Hx | |].
    - intros ->. rewrite Hm in Hx. injection Hx as <-. exact (Hnd Hr).
    - intros ->. rewrite Hpa in Hx. injection Hx as <-. exact (Hng _ _ Hpr).
  Qed.
  Lemma in_not_in_fl : ~ In m (a_freelist A).
  Proof using HW Hm Hr. pu_keep (HW, Hm, Hr).
    intros Hin. destruct (proj1 (wf_fl_mem A HW m) Hin) as (mt0 & H0 & Hr0). rewrite Hm in H0. injection H0 as <-. rewrite Hr in Hr0. discriminate Hr0.
  Qed.
  Lemma in_not_in_act : forall sc', ~ In m (a_active A sc').
  Proof using HW Hm Hr. pu_keep (HW, Hm, Hr).
    intros sc' Hin. destruct (wf_act_mem A HW sc' m Hin) as (mt0 & aib0 & sl0 & H0 & Hr0 & _). rewrite Hm in H0. injection H0 as <-.
    rewrite Hr in Hr0. discriminate Hr0.
  Qed.
  Lemma pa_not_in_fl : ~ In pa (a_freelist A).
  Proof using HW Hpa Hpr. pu_keep (HW, Hpa, Hpr).
    intros Hin. destruct (proj1 (wf_fl_mem A HW pa) Hin) as (mt0 & H0 & Hr0). rewrite Hpa in H0. injection H0 as <-. rewrite Hpr in Hr0. discriminate Hr0.
  Qed.
  Lemma in_dll : forall l, ~ In m l -> dll A l -> dll instN l.
  Proof using Hm Hpa Hpr Hr. pu_keep (Hm, Hpa, Hpr, Hr).
    intros l Hn Hd k x Hk. destruct (Hd k x Hk) as (mtx & Hx & R).
    assert (Hxm : x <> m) by (intros ->; apply Hn; eapply nth_error_In; exact Hk).
    destruct (Z.eq_dec x pa) as [-> | Hne].
    - exists pm'. split; [exact in_meta_pa|]. rewrite pm'_next, pm'_prev. rewrite Hpa in Hx. injection Hx as <-. exact R.
    - exists mtx. rewrite (in_meta_other x Hxm Hne). auto.
  Qed.

  (* [comment removed for export] *)
  Lemma in_slots_len : length in_slots = Z.to_nat cnt.
  Proof using Hab Hcnt Hsc p size. pu_keep (Hab, Hcnt, Hsc, p, size). unfold in_slots. cbn [length]. rewrite repeat_length. lia. Qed.
  Lemma in_slots_inv : forall j st, nth_error in_slots j = Some st -> (j = 0%nat /\ st = STaken) \/ ((0 < j < Z.to_nat cnt)%nat /\ st = SIdle).
  Proof using Hab Hcnt Hsc p size. pu_keep (Hab, Hcnt, Hsc, p, size).
    intros j st Hj. unfold in_slots in Hj. destruct j as [|j]; cbn in Hj; [left; injection Hj as <-; auto|].
    destruct (nth_error_repeat' SIdle _ _ _ Hj) as [-> Hlt]. right. split; [lia | reflexivity].
  Qed.
  Lemma in_no_nested : forall j ch, nth_error in_slots j <> Some (SNested ch).
  Proof using Hab Hcnt Hsc p size. pu_keep (Hab, Hcnt, Hsc, p, size). intros j ch E. destruct (in_slots_inv _ _ E) as [(_ & H) | (_ & H)]; discriminate H. Qed.
  Lemma in_no_live : forall j off n, nth_error in_slots j <> Some (SLive off n).
  Proof using Hab Hcnt Hsc p size. pu_keep (Hab, Hcnt, Hsc, p, size). intros j off n E. destruct (in_slots_inv _ _ E) as [(_ & H) | (_ & H)]; discriminate H. Qed.

  (* [comment removed for export] *)
  Lemma old_ext_len : forall x mtx aibx slx, a_meta A x = Some mtx -> mt_role mtx = RGroup aibx slx ->
    gext_lo mtx + 28 <= gext_hi mtx /\ 16 <= mt_stride mtx /\ Z.of_nat (length slx) = mt_cnt mtx.
  Proof using HW Hab Hsc p size. pu_keep (HW, Hab, Hsc, p, size).
    intros x mtx aibx slx Hx Hrx. pose proof (wf_grp A HW x mtx aibx slx Hx Hrx) as (Hw & _ & Hscx & Hlen & _).
    pose proof (stride_ge16 mtx ltac:(lia) Hscx) as S16. pose proof (w_last_range (mt_w32 mtx)) as WL.
    unfold gext_lo, gext_hi, mt_cnt, mt_last in *.
    assert (16 <= (w_last (mt_w32 mtx) + 1) * mt_stride mtx) by nia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma in_slot_unique : forall j, 0 <= j -> slot_start pm j <= p -> gext_hi in_mt <= slot_end pm j -> j = i.
  Proof using HW Hab Hcnt Hfit Hi0 Hpa Hpr Hsc Hsmall. pu_keep (HW, Hab, Hcnt, Hfit, Hi0, Hpa, Hpr, Hsc, Hsmall).
    intros j Hj Hlo Hhi. pose proof in_gext as (G1 & G2 & G3 & G4). pose proof pa_grp as (_ & _ & _ & S16 & _).
    destruct (Z.eq_dec j i) as [E | Hne]; [exact E|]. exfalso.
    destruct (slots_apart pm j i Hj Hi0 Hne ltac:(lia)) as [D | D]; unfold p, in_p in *; [| pose proof slot_i_len]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma slot_i_clear : forall x mtx aibx slx, a_meta A x = Some mtx -> mt_role mtx = RGroup aibx slx ->
    ~ (slot_start pm i <= gext_lo mtx /\ gext_hi mtx <= slot_end pm i).
  Proof using HW Hab Hi Hi0 Hpa Hpr Hsc size. pu_keep (HW, Hab, Hi, Hi0, Hpa, Hpr, Hsc, size).
    intros x mtx aibx slx Hx Hrx [Hlo Hhi]. pose proof slot_i_in as [S1 S2]. pose proof pa_grp as (_ & _ & _ & S16 & _).
    destruct (old_ext_len x mtx aibx slx Hx Hrx) as (LEN & S16x & Hlenx).
    assert (Hne : pa <> x).
    { intros <-. rewrite Hpa in Hx. injection Hx as <-. unfold gext_lo in *. lia. }
    destruct (wf_laminar A HW pa pm paib psl x mtx aibx slx Hpa Hpr Hx Hrx Hne) as [D | [D | [D | D]]].
    - lia.
    - unfold gext_lo in *. lia.
    - destruct D as (j & ch & Hj0 & Hj & Dlo & Dhi).
      assert (Hji : j <> i) by (intros ->; rewrite Hi in Hj; discriminate Hj).
      destruct (slots_apart pm j i Hj0 Hi0 Hji ltac:(lia)); lia.
    - destruct D as (j & ch & Hj0 & Hj & Dlo & Dhi).
      assert (Hjc : j + 1 <= mt_cnt mtx).
      { pose proof (proj1 (nth_error_Some slx (Z.to_nat j)) ltac:(rewrite Hj; discriminate)). lia. }
      destruct (slot_in_ext mtx j Hj0 Hjc ltac:(lia)) as [E1 E2]. unfold gext_lo in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma lam_new_old : forall x mtx aibx slx, a_meta A x = Some mtx -> mt_role mtx = RGroup aibx slx -> x <> pa ->
    gext_hi in_mt + 4 <= gext_lo mtx \/ gext_hi mtx + 4 <= gext_lo in_mt \/
    (exists j ch, 0 <= j /\ nth_error slx (Z.to_nat j) = Some (SNested ch) /\ slot_start mtx j <= gext_lo in_mt /\ gext_hi in_mt <= slot_end mtx j).
  Proof using HW Hab Hcnt Hfit Hi Hi0 Hpa Hpr Hsc Hsmall. pu_keep (HW, Hab, Hcnt, Hfit, Hi, Hi0, Hpa, Hpr, Hsc, Hsmall).
    intros x mtx aibx slx Hx Hrx Hne. pose proof in_gext as (G1 & G2 & G3 & G4). pose proof slot_i_in as [S1 S2].
    pose proof pa_grp as (_ & _ & _ & S16 & _).
    destruct (wf_laminar A HW pa pm paib psl x mtx aibx slx Hpa Hpr Hx Hrx (not_eq_sym Hne)) as [D | [D | [D | D]]].
    - left. lia.
    - right; left. unfold p, in_p in *. lia.
    - destruct D as (j & ch & Hj0 & Hj & Dlo & Dhi).
      assert (Hji : j <> i) by (intros ->; rewrite Hi in Hj; discriminate Hj).
      destruct (slots_apart pm j i Hj0 Hi0 Hji ltac:(lia)); unfold p, in_p in *; [right; left | left]; lia.
    - destruct D as (j & ch & Hj0 & Hj & Dlo & Dhi). right; right. exists j, ch. unfold p, in_p in *. repeat split; auto; lia.
  Qed.

  Lemma mem_new_old : forall x mtx aibx slx, a_meta A x = Some mtx -> mt_role mtx = RGroup aibx slx -> mt_mem mtx <> p.
  Proof using HW Hab Hi Hi0 Hpa Hpr Hsc size. pu_keep (HW, Hab, Hi, Hi0, Hpa, Hpr, Hsc, size).
    intros x mtx aibx slx Hx Hrx E. pose proof slot_i_in as [S1 S2]. pose proof pa_grp as (_ & _ & _ & S16 & _). pose proof slot_i_len as SL.
    destruct (old_ext_len x mtx aibx slx Hx Hrx) as (LEN & S16x & Hlenx).
    destruct (Z.eq_dec x pa) as [-> | Hne].
    { rewrite Hpa in Hx. injection Hx as <-. unfold gext_lo, p, in_p in *. lia. }
    destruct (wf_laminar A HW pa pm paib psl x mtx aibx slx Hpa Hpr Hx Hrx ltac:(intros ->; exact (Hne eq_refl))) as [D | [D | [D | D]]];
      unfold gext_lo, p, in_p in *.
    - lia.
    - lia.
    - destruct D as (j & ch & Hj0 & Hj & Dlo & Dhi).
      assert (Hji : j <> i) by (intros ->; rewrite Hi in Hj; discriminate Hj).
      destruct (slots_apart pm j i Hj0 Hi0 Hji ltac:(lia)); lia.
    - destruct D as (j & ch & Hj0 & Hj & Dlo & Dhi).
      assert (Hjc : j + 1 <= mt_cnt mtx).
      { pose proof (proj1 (nth_error_Some slx (Z.to_nat j)) ltac:(rewrite Hj; discriminate)). lia. }
      destruct (slot_in_ext mtx j Hj0 Hjc ltac:(lia)) as [E1 E2]. unfold gext_lo in E1. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma nested_child_ne : forall x mtx aibx slx j ch, a_meta A x = Some mtx -> mt_role mtx = RGroup aibx slx -> 0 <= j ->
    nth_error slx (Z.to_nat j) = Some (SNested ch) -> ch <> x /\ ch <> m.
  Proof using HW Hab Hm Hr Hsc p size. pu_keep (HW, Hab, Hm, Hr, Hsc, p, size).
    intros x mtx aibx slx j ch Hx Hrx Hj0 Hj.
    destruct (wf_nested A HW x mtx aibx slx j ch Hx Hrx Hj Hj0) as (mc & aibc & slc & Hmc & Hrc & Hml & Hmem & _).
    split.
    - intros ->. rewrite Hx in Hmc. injection Hmc as <-.
      destruct (old_ext_len x mtx aibx slx Hx Hrx) as (_ & S16 & Hlen).
      assert (Hjc : j + 1 <= mt_cnt mtx) by (pose proof (proj1 (nth_error_Some slx (Z.to_nat j)) ltac:(rewrite Hj; discriminate)); lia).
      destruct (slot_in_ext mtx j Hj0 Hjc ltac:(lia)) as [E1 E2]. unfold gext_lo in E1. lia.
    - intros ->. rewrite Hm in Hmc. injection Hmc as <-. rewrite Hr in Hrc. discriminate Hrc.
  Qed.

  (* [comment removed for export] *)
  Lemma in_wf_grp :
     0 <= mt_w32 in_mt < 2^64 /\ w_freeable (mt_w32 in_mt) = 1 /\
     (mt_sc in_mt < 48 \/ (mt_sc in_mt = 63 /\ mt_last in_mt = 0 /\ 0 < mt_maplen in_mt)) /\
     Z.of_nat (length in_slots) = mt_cnt in_mt /\
     0 <= mt_avail in_mt < 2 ^ (mt_cnt in_mt) /\ 0 <= mt_freed in_mt < 2 ^ (mt_cnt in_mt) /\
     Z.land (mt_avail in_mt) (mt_freed in_mt) = 0 /\
     0 <= in_aib < 256 /\ mt_avail in_mt < 2 ^ (in_aib mod 32 + 1) /\ in_aib mod 32 <= mt_last in_mt /\
     (forall j st, nth_error in_slots (Z.to_nat j) = Some st -> 0 <= j ->
        (Z.testbit (Z.lor (mt_avail in_mt) (mt_freed in_mt)) j = true <-> st = SIdle)) /\
     mt_mem in_mt mod 16 = 0 /\ 0x1000 <= mt_mem in_mt /\
     16 + mt_cnt in_mt * mt_stride in_mt <= (if mt_maplen in_mt =? 0 then 2^64 else grp_map_len in_mt) /\
     mt_mem in_mt + 16 + mt_cnt in_mt * mt_stride in_mt <= alloc_ceiling /\
     (0 < mt_maplen in_mt -> page_aligned (mt_mem in_mt) /\ heap_range (mt_mem in_mt) (mt_mem in_mt + grp_map_len in_mt)).
  Proof using HW Hab Hcnt Hfit Hi Hi0 Hpa Hpr Hsc Hsmall. pu_keep (HW, Hab, Hcnt, Hfit, Hi, Hi0, Hpa, Hpr, Hsc, Hsmall).
    pose proof (masks_facts cnt (cnt - 1) Hcnt1 Haidx) as (M1 & M2 & M3 & M4 & M5 & M6 & M7). pose proof in_aib_rng as [B1 B2].
    rewrite in_avail, in_freed, in_cnt, in_last, in_sc, in_mem, in_maplen, in_w32, in_stride. rewrite B2.
    pose proof slot_i_in as [S1 S2]. pose proof pa_grp as (_ & _ & _ & S16 & _ & Hmem & Hce). pose proof size_rng as SZ. pose proof slot_i_len as SL.
    split; [unfold iw32; lia|]. split; [apply iw32_freeable; [lia | reflexivity | lia | exact Hcnt1]|]. split; [left; lia|]. split; [rewrite in_slots_len; lia|].
    split; [lia|]. split; [lia|]. split; [exact M3|]. split; [exact B1|]. split; [exact M5|]. split; [lia|].
    split.
    { intros j st Hj Hj0. rewrite M7 by lia. destruct (in_slots_inv _ _ Hj) as [(E & ->) | (E & ->)].
      - split; [intros H | intros H; discriminate H]. assert (j = 0) by lia. subst j. cbn in H. discriminate H.
      - split; [reflexivity | intros _]. apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]. }
    split; [exact p_al16|]. split; [unfold gext_lo, p, in_p in *; lia|]. cbn [Z.eqb]. split; [nia|].
    split; [| intros H; lia]. unfold gext_lo, gext_hi, p, in_p in *. lia.
  Qed.

  Lemma pa_wf_grp :
     0 <= mt_w32 pm' < 2^64 /\ w_freeable (mt_w32 pm') = 1 /\
     (mt_sc pm' < 48 \/ (mt_sc pm' = 63 /\ mt_last pm' = 0 /\ 0 < mt_maplen pm')) /\
     Z.of_nat (length psl') = mt_cnt pm' /\
     0 <= mt_avail pm' < 2 ^ (mt_cnt pm') /\ 0 <= mt_freed pm' < 2 ^ (mt_cnt pm') /\
     Z.land (mt_avail pm') (mt_freed pm') = 0 /\
     0 <= paib < 256 /\ mt_avail pm' < 2 ^ (paib mod 32 + 1) /\ paib mod 32 <= mt_last pm' /\
     (forall j st, nth_error psl' (Z.to_nat j) = Some st -> 0 <= j ->
        (Z.testbit (Z.lor (mt_avail pm') (mt_freed pm')) j = true <-> st = SIdle)) /\
     mt_mem pm' mod 16 = 0 /\ 0x1000 <= mt_mem pm' /\
     16 + mt_cnt pm' * mt_stride pm' <= (if mt_maplen pm' =? 0 then 2^64 else grp_map_len pm') /\
     mt_mem pm' + 16 + mt_cnt pm' * mt_stride pm' <= alloc_ceiling /\
     (0 < mt_maplen pm' -> page_aligned (mt_mem pm') /\ heap_range (mt_mem pm') (mt_mem pm' + grp_map_len pm')).
  Proof using HW Hab Hi Hi0 Hpa Hpr Hsc size. pu_keep (HW, Hab, Hi, Hi0, Hpa, Hpr, Hsc, size).
    pose proof (wf_grp A HW pa pm paib psl Hpa Hpr) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
    rewrite pm'_w32, pm'_sc, pm'_last, pm'_maplen, pm'_cnt, pm'_avail, pm'_freed, pm'_mem, pm'_stride, pm'_grp_map_len, psl'_length.
    repeat (split; [assumption|]). split; [| exact G12].
    intros j st Hj Hj0. destruct (psl'_inv j st Hj Hj0) as [(-> & ->) | (Hne & H)].
    - rewrite (G11 i STaken Hi Hi0). split; intros E; discriminate E.
    - exact (G11 j st H Hj0).
  Qed.

  Theorem WF_instN : WF instN.
  Proof using HW Hab Hcnt Hfit Hi Hi0 Hm Hpa Hpr Hr Hsc Hsmall. pu_keep (HW, Hab, Hcnt, Hfit, Hi, Hi0, Hm, Hpa, Hpr, Hr, Hsc, Hsmall).
    pose proof HW as W. pose proof in_wf_grp as GRP. pose proof pa_wf_grp as GRPA. pose proof in_gext as (G1 & G2 & G3 & G4).
    pose proof in_aib_rng as [B1 B2]. pose proof slot_i_in as [S1 S2]. pose proof pa_ne_m as PM.
    pose proof (masks_facts cnt (cnt - 1) Hcnt1 Haidx) as (M1 & M2 & M3 & M4 & M5 & M6 & M7).
    constructor; cbn [a_ctx a_areas a_meta a_freelist a_active a_pages a_brk_lo a_live a_mblocks a_xmaps instN].
    - exact (wf_areas_nodup A W).
    - exact (wf_areas_al A W).
    - (* [comment removed for export] *) intros x. rewrite <- (wf_meta_dom A W). unfold aupd.
      destruct (Z.eq_dec x m) as [-> | Hne]; [rewrite Hm; split; intros _; discriminate |].
      destruct (Z.eq_dec x pa) as [-> | Hne']; [rewrite Hpa; split; intros _; discriminate | tauto].
    - exact (wf_init A W).
    - exact (wf_uninit A W).
    - exact (wf_amc A W).
    - (* [comment removed for export] *) intros Hc. destruct (wf_am A W Hc) as (pg & H1 & H2 & H3 & H4). exists pg. repeat split; auto.
      intros k Hk. destruct (H4 k Hk) as (mtk & Hmk & Hrk). exists mtk. split; [| exact Hrk].
      apply (in_old _ _ Hmk); rewrite Hrk; [discriminate | discriminate].
    - exact (wf_atail A W).
    - exact (wf_ahead A W).
    - (* [comment removed for export] *) intros x mtx Hx Hrx. destruct (in_meta_inv x mtx Hx) as [(-> & ->) | [(-> & ->) | (Hn1 & Hn2 & H)]]; [cbn in Hrx; discriminate Hrx | cbn in Hrx; discriminate Hrx | exact (wf_avail_zero A W x mtx H Hrx)].
    - (* [comment removed for export] *) intros x mtx Hx Hrx. destruct (in_meta_inv x mtx Hx) as [(-> & ->) | [(-> & ->) | (Hn1 & Hn2 & H)]]; [cbn in Hrx; discriminate Hrx | cbn in Hrx; discriminate Hrx | exact (wf_free_zero A W x mtx H Hrx)].
    - exact (wf_fl_nodup A W).
    - exact (wf_fl_head A W).
    - (* [comment removed for export] *) intros x. rewrite (wf_fl_mem A W x). split.
      + intros (mtx & Hx & Hrx). exists mtx. split; [| exact Hrx]. apply (in_old _ _ Hx); rewrite Hrx; [discriminate | discriminate].
      + intros (mtx & Hx & Hrx). destruct (in_meta_inv x mtx Hx) as [(-> & ->) | [(-> & ->) | (Hn1 & Hn2 & H)]]; [cbn in Hrx; discriminate Hrx | cbn in Hrx; discriminate Hrx | eauto].
    - (* [comment removed for export] *) apply in_dll; [apply in_not_in_fl | exact (wf_fl_dll A W)].
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx. destruct (in_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | [(-> & -> & -> & ->) | (Hn1 & Hn2 & H)]]; [exact GRP | exact GRPA | exact (wf_grp A W x mtx aibx slx H Hrx)].
    - (* [comment removed for export] *) intros x mtx aibx slx j off n Hx Hrx Hj. destruct (in_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | [(-> & -> & -> & ->) | (Hn1 & Hn2 & H)]]; [exfalso; exact (in_no_live _ _ _ Hj) | | exact (wf_live A W x mtx aibx slx j off n H Hrx Hj)].
      intros Hj0. rewrite pm'_stride. destruct (psl'_inv j _ Hj Hj0) as [(_ & E) | (Hne & Hj')]; [discriminate E|]. exact (wf_live A W pa pm paib psl j off n Hpa Hpr Hj' Hj0).
    - (* [comment removed for export] *) intros x mtx aibx slx j ch Hx Hrx Hj Hj0. destruct (in_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | [(-> & -> & -> & ->) | (Hn1 & Hn2 & H)]]; [exfalso; exact (in_no_nested _ _ Hj) | |].
      + rewrite pm'_stride, pm'_slot_start. destruct (psl'_inv j _ Hj Hj0) as [(-> & E) | (Hne & Hj')].
        * injection E as Ech. subst ch. exists in_mt, in_aib, in_slots. split; [exact in_meta_m|]. split; [reflexivity|]. split; [exact in_maplen|].
          rewrite in_mem, in_cnt, in_stride. split; [reflexivity | exact Hfit].
        * destruct (wf_nested A W pa pm paib psl j ch Hpa Hpr Hj' Hj0) as (mc & aibc & slc & Hmc & Hrc & R1 & R2 & R3).
          destruct (in_fwd ch mc aibc slc Hmc Hrc) as (mc' & slc' & F1 & F2 & _ & _ & _ & F5 & F6 & F7 & F8 & _).
          exists mc', aibc, slc'. rewrite F5, F6, F7, F8. auto 10.
      + destruct (wf_nested A W x mtx aibx slx j ch H Hrx Hj Hj0) as (mc & aibc & slc & Hmc & Hrc & R1 & R2 & R3).
        destruct (in_fwd ch mc aibc slc Hmc Hrc) as (mc' & slc' & F1 & F2 & _ & _ & _ & F5 & F6 & F7 & F8 & _).
        exists mc', aibc, slc'. rewrite F5, F6, F7, F8. auto 10.
    - (* [comment removed for export] *) intros ch mc aibc slc Hch Hrc Hmlc. destruct (in_group_inv ch mc aibc slc Hch Hrc) as [(-> & -> & -> & ->) | [(-> & -> & -> & ->) | (Hn1 & Hn2 & H)]].
      + exists pa, pm', paib, psl', i. split; [exact in_meta_pa|]. split; [reflexivity|]. split; [exact Hi0 | exact psl'_i].
      + rewrite pm'_maplen in Hmlc. destruct (wf_nested_parent A W pa pm paib psl Hpa Hpr Hmlc) as (x & mtx & aibx & slx & j & Hx & Hrx & Hj0 & Hj).
        destruct (in_fwd x mtx aibx slx Hx Hrx) as (mtx' & slx' & F1 & F2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FN & _).
        exists x, mtx', aibx, slx', j. split; [exact F1|]. split; [exact F2|]. split; [exact Hj0|]. apply FN. exact Hj.
      + destruct (wf_nested_parent A W ch mc aibc slc H Hrc Hmlc) as (x & mtx & aibx & slx & j & Hx & Hrx & Hj0 & Hj).
        destruct (in_fwd x mtx aibx slx Hx Hrx) as (mtx' & slx' & F1 & F2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FN & _).
        exists x, mtx', aibx, slx', j. split; [exact F1|]. split; [exact F2|]. split; [exact Hj0|]. apply FN. exact Hj.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx.
      assert (ROOT : forall y my aiby sly, a_meta A y = Some my -> mt_role my = RGroup aiby sly ->
        gext_lo my <= gext_lo mtx -> gext_hi mtx + 4 <= gext_hi my + 4 -> mt_maplen mtx = 0 ->
        exists mr mtr aibr slr, a_meta instN mr = Some mtr /\ mt_role mtr = RGroup aibr slr /\ 0 < mt_maplen mtr /\
          mt_mem mtr <= gext_lo mtx /\ gext_hi mtx + 4 <= mt_mem mtr + grp_map_len mtr /\ (0 < mt_maplen mtx -> mr = x)).
      { intros y my aiby sly Hy Hry Hlo Hhi Hml0.
        destruct (wf_grp_root A W y my aiby sly Hy Hry) as (mr & mtr & aibr & slr & Hmr & Hrr & Hmlr & Rlo & Rhi & _).
        destruct (in_old_grp mr mtr aibr slr Hmr Hrr) as (mtr' & slr' & F1 & F2 & _ & _ & _ & F6 & F7 & F8).
        exists mr, mtr', aibr, slr'. rewrite F6, F7, F8. repeat split; auto; lia. }
      destruct (in_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | [(-> & -> & -> & ->) | (Hn1 & Hn2 & H)]].
      + apply (ROOT pa pm paib psl Hpa Hpr); [unfold p, in_p in *; lia | lia | exact in_maplen].
      + destruct (wf_grp_root A W pa pm paib psl Hpa Hpr) as (mr & mtr & aibr & slr & Hmr & Hrr & Hmlr & Rlo & Rhi & Rself).
        destruct (in_old_grp mr mtr aibr slr Hmr Hrr) as (mtr' & slr' & F1 & F2 & _ & _ & _ & F6 & F7 & F8).
        exists mr, mtr', aibr, slr'. rewrite F6, F7, F8, pm'_gext_lo, pm'_gext_hi, pm'_maplen. repeat split; auto.
      + destruct (wf_grp_root A W x mtx aibx slx H Hrx) as (mr & mtr & aibr & slr & Hmr & Hrr & Hmlr & Rlo & Rhi & Rself).
        destruct (in_old_grp mr mtr aibr slr Hmr Hrr) as (mtr' & slr' & F1 & F2 & _ & _ & _ & F6 & F7 & F8).
        exists mr, mtr', aibr, slr'. rewrite F6, F7, F8. repeat split; auto.
    - (* [comment removed for export] *) intros x mtx aibx slx x' mtx' aibx' slx' Hx Hrx Hx' Hrx' Hne.
      destruct (in_group_inv _ _ _ _ Hx Hrx) as [(-> & -> & -> & ->) | [(-> & -> & -> & ->) | (Hn1 & Hn2 & H)]];
      destruct (in_group_inv _ _ _ _ Hx' Hrx') as [(-> & -> & -> & ->) | [(-> & -> & -> & ->) | (Hn1' & Hn2' & H')]].
      + exfalso. exact (Hne eq_refl).
      + (* [comment removed for export] *) right; right; right. exists i, m. rewrite pm'_slot_start, pm'_slot_end. split; [exact Hi0|]. split; [exact psl'_i|]. unfold p, in_p in *. lia.
      + destruct (lam_new_old x' mtx' aibx' slx' H' Hrx' Hn2') as [D | [D | D]]; [left; exact D | right; left; exact D | right; right; right; exact D].
      + right; right; left. exists i, m. rewrite pm'_slot_start, pm'_slot_end. split; [exact Hi0|]. split; [exact psl'_i|]. unfold p, in_p in *. lia.
      + exfalso. exact (Hne eq_refl).
      + destruct (wf_laminar A W pa pm paib psl x' mtx' aibx' slx' Hpa Hpr H' Hrx' Hne) as [D | [D | [D | D]]]; [left; exact D | right; left; exact D | | right; right; right; exact D].
        right; right; left. destruct D as (j & ch & Hj0 & Hj & R). exists j, ch. split; [exact Hj0|]. split; [exact (proj1 (psl_nested_kept _ _ Hj)) | exact R].
      + destruct (lam_new_old x mtx aibx slx H Hrx Hn2) as [D | [D | D]]; [right; left; exact D | left; exact D | right; right; left; exact D].
      + destruct (wf_laminar A W x mtx aibx slx pa pm paib psl H Hrx Hpa Hpr Hne) as [D | [D | [D | D]]]; [left; exact D | right; left; exact D | right; right; left; exact D |].
        right; right; right. destruct D as (j & ch & Hj0 & Hj & R). exists j, ch. split; [exact Hj0|]. split; [exact (proj1 (psl_nested_kept _ _ Hj)) | exact R].
      + exact (wf_laminar A W x mtx aibx slx x' mtx' aibx' slx' H Hrx H' Hrx' Hne).
    - exact (wf_act_head A W).
    - exact (wf_act_nodup A W).
    - (* [comment removed for export] *) intros c Hc. apply in_dll; [apply in_not_in_act | exact (wf_act_dll A W c Hc)].
    - (* [comment removed for export] *) intros c x Hin. destruct (wf_act_mem A W c x Hin) as (mtx & aibx & slx & Hx & Hrx & R).
      destruct (in_fwd x mtx aibx slx Hx Hrx) as (mtx' & slx' & F1 & F2 & _ & _ & _ & _ & _ & _ & _ & F9 & _).
      exists mtx', aibx, slx'. rewrite F9. auto.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx Hnin. destruct (in_group_inv _ _ _ _ Hx Hrx) as [(-> & -> & -> & ->) | [(-> & -> & -> & ->) | (Hn1 & Hn2 & H)]]; [rewrite in_prev, in_next; auto | | exact (wf_unlinked A W x mtx aibx slx H Hrx Hnin)].
      rewrite pm'_prev, pm'_next. rewrite pm'_sc in Hnin. exact (wf_unlinked A W pa pm paib psl Hpa Hpr Hnin).
    - (* [comment removed for export] *) intros c x mtx Hin Hne Hx. destruct (in_meta_inv x mtx Hx) as [(-> & ->) | [(-> & ->) | (Hn1 & Hn2 & Hx')]]; [exfalso; exact (in_not_in_act c Hin) | | exact (wf_act_nonhead A W c x mtx Hin Hne Hx')].
      rewrite pm'_avail, pm'_freed. exact (wf_act_nonhead A W c pa pm Hin Hne Hpa).
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx H63. destruct (in_group_inv _ _ _ _ Hx Hrx) as [(-> & -> & -> & ->) | [(-> & -> & -> & ->) | (Hn1 & Hn2 & H)]]; [rewrite in_sc in H63; lia | | exact (wf_act63 A W x mtx aibx slx H Hrx H63)].
      rewrite pm'_prev, pm'_next. rewrite pm'_sc in H63. exact (wf_act63 A W pa pm paib psl Hpa Hpr H63).
    - (* [comment removed for export] *) intros pg x mtx aibx slx Hpg Hx Hrx Hml. destruct (in_group_inv _ _ _ _ Hx Hrx) as [(-> & -> & -> & ->) | [(-> & -> & -> & ->) | (Hn1 & Hn2 & H)]]; [rewrite in_maplen in Hml; lia | | exact (wf_disj_area_grp A W pg x mtx aibx slx Hpg H Hrx Hml)].
      rewrite pm'_mem, pm'_grp_map_len. rewrite pm'_maplen in Hml. exact (wf_disj_area_grp A W pg pa pm paib psl Hpg Hpa Hpr Hml).
    - (* [comment removed for export] *) intros x mtx aibx slx x' mtx' aibx' slx' Hx Hrx Hmlx Hx' Hrx' Hmlx' Hne.
      assert (OLD : forall y my aiby sly, a_meta instN y = Some my -> mt_role my = RGroup aiby sly -> 0 < mt_maplen my ->
        exists my0 sly0, a_meta A y = Some my0 /\ mt_role my0 = RGroup aiby sly0 /\ mt_maplen my0 = mt_maplen my /\ mt_mem my0 = mt_mem my /\ grp_map_len my0 = grp_map_len my).
      { intros y my aiby sly Hy Hry Hmly. destruct (in_group_inv _ _ _ _ Hy Hry) as [(-> & -> & -> & ->) | [(-> & -> & -> & ->) | (Hn1 & Hn2 & Hy0)]]; [rewrite in_maplen in Hmly; lia | |].
        - exists pm, psl. auto.
        - exists my, sly. auto. }
      destruct (OLD _ _ _ _ Hx Hrx Hmlx) as (m0 & s0 & A0x & R0 & ML0 & MM0 & GL0). destruct (OLD _ _ _ _ Hx' Hrx' Hmlx') as (m1 & s1 & A1x & R1 & ML1 & MM1 & GL1).
      rewrite <- MM0, <- MM1, <- GL0, <- GL1. rewrite <- ML0 in Hmlx. rewrite <- ML1 in Hmlx'.
      exact (wf_disj_grp_grp A W x m0 aibx s0 x' m1 aibx' s1 A0x R0 Hmlx A1x R1 Hmlx' Hne).
    - (* [comment removed for export] *) intros x mtx aibx slx x' mtx' aibx' slx' Hx Hrx Hx' Hrx' E.
      assert (OLD : forall y my aiby sly, a_meta instN y = Some my -> mt_role my = RGroup aiby sly -> y <> m ->
        exists my0 sly0, a_meta A y = Some my0 /\ mt_role my0 = RGroup aiby sly0 /\ mt_mem my0 = mt_mem my).
      { intros y my aiby sly Hy Hry Hym. destruct (in_group_inv _ _ _ _ Hy Hry) as [(-> & -> & -> & ->) | [(-> & -> & -> & ->) | (Hn1 & Hn2 & Hy0)]]; [contradiction | exists pm, psl; auto | exists my, sly; auto]. }
      destruct (Z.eq_dec x m) as [-> | Hxm]; destruct (Z.eq_dec x' m) as [-> | Hxm'].
      + reflexivity.
      + exfalso. destruct (in_meta_inv m mtx Hx) as [(_ & ->) | [(Epa & _) | (Hmm & _ & _)]]; [| exact (PM (eq_sym Epa)) | exact (Hmm eq_refl)]. rewrite in_mem in E.
        destruct (OLD _ _ _ _ Hx' Hrx' Hxm') as (m1 & s1 & A1x & R1 & MM1). rewrite <- MM1 in E. exact (mem_new_old _ _ _ _ A1x R1 (eq_sym E)).
      + exfalso. destruct (in_meta_inv m mtx' Hx') as [(_ & ->) | [(Epa & _) | (Hmm & _ & _)]]; [| exact (PM (eq_sym Epa)) | exact (Hmm eq_refl)]. rewrite in_mem in E.
        destruct (OLD _ _ _ _ Hx Hrx Hxm) as (m0 & s0 & A0x & R0 & MM0). rewrite <- MM0 in E. exact (mem_new_old _ _ _ _ A0x R0 E).
      + destruct (OLD _ _ _ _ Hx Hrx Hxm) as (m0 & s0 & A0x & R0 & MM0). destruct (OLD _ _ _ _ Hx' Hrx' Hxm') as (m1 & s1 & A1x & R1 & MM1).
        rewrite <- MM0, <- MM1 in E. exact (wf_grp_mem_inj A W x m0 aibx s0 x' m1 aibx' s1 A0x R0 A1x R1 E).
    - (* [comment removed for export] *) intros q n. rewrite (wf_live_map A W q n). unfold is_live. cbn [a_meta instN]. split.
      + intros (x & mtx & aibx & slx & j & off & Hx & Hrx & Hj0 & Hj & Eq).
        destruct (in_fwd x mtx aibx slx Hx Hrx) as (mtx' & slx' & F1 & F2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FS & _ & _ & FL & _).
        exists x, mtx', aibx, slx', j, off. rewrite FS. split; [exact F1|]. split; [exact F2|]. split; [exact Hj0|]. split; [apply (proj2 (FL _ _ _)); exact Hj | exact Eq].
      + intros (x & mtx & aibx & slx & j & off & Hx & Hrx & Hj0 & Hj & Eq).
        destruct (in_group_inv _ _ _ _ Hx Hrx) as [(-> & -> & -> & ->) | [(-> & -> & -> & ->) | (Hn1 & Hn2 & H)]]; [exfalso; exact (in_no_live _ _ _ Hj) | |].
        * exists pa, pm, paib, psl, j, off. rewrite pm'_slot_start in Eq. destruct (psl'_inv j _ Hj Hj0) as [(_ & E') | (Hne & Hj')]; [discriminate E'|]. auto 10.
        * exists x, mtx, aibx, slx, j, off. auto 10.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx Hlast. destruct (in_group_inv _ _ _ _ Hx Hrx) as [(-> & -> & -> & ->) | [(-> & -> & -> & ->) | (Hn1 & Hn2 & H)]]; [| exact (wf_span A W pa pm paib psl Hpa Hpr Hlast) | exact (wf_span A W x mtx aibx slx H Hrx Hlast)].
      rewrite in_cnt, in_stride. unfold size in *. lia.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx Hlast Hml Hsc48. destruct (in_group_inv _ _ _ _ Hx Hrx) as [(-> & -> & -> & ->) | [(-> & -> & -> & ->) | (Hn1 & Hn2 & H)]]; [rewrite in_maplen in Hml; lia | exact (wf_single A W pa pm paib psl Hpa Hpr Hlast Hml Hsc48) | exact (wf_single A W x mtx aibx slx H Hrx Hlast Hml Hsc48)].
    - (* [comment removed for export] *) intros x mtx aibx slx j Hx Hrx Hj. destruct (in_group_inv _ _ _ _ Hx Hrx) as [(-> & -> & -> & ->) | [(-> & -> & -> & ->) | (Hn1 & Hn2 & H)]]; [rewrite B2, in_last in Hj; lia | exact (wf_inactive A W pa pm paib psl j Hpa Hpr Hj) | exact (wf_inactive A W x mtx aibx slx j H Hrx Hj)].
    - (* [comment removed for export] *) intros c x mtx aibx slx x' mtx' aibx' slx' Hin Hin' Hx Hrx Hx' Hrx'.
      assert (OLD : forall y my aiby sly, a_meta instN y = Some my -> mt_role my = RGroup aiby sly -> In y (a_active A c) ->
        exists my0 sly0, a_meta A y = Some my0 /\ mt_role my0 = RGroup aiby sly0 /\ mt_last my0 = mt_last my).
      { intros y my aiby sly Hy Hry Hyin. destruct (in_group_inv _ _ _ _ Hy Hry) as [(-> & -> & -> & ->) | [(-> & -> & -> & ->) | (Hn1 & Hn2 & Hy0)]]; [exfalso; exact (in_not_in_act c Hyin) | exists pm, psl; auto | exists my, sly; auto]. }
      destruct (OLD _ _ _ _ Hx Hrx Hin) as (m0 & s0 & A0x & R0 & L0). destruct (OLD _ _ _ _ Hx' Hrx' Hin') as (m1 & s1 & A1x & R1 & L1).
      rewrite <- L0, <- L1. exact (wf_partial A W c x m0 aibx s0 x' m1 aibx' s1 Hin Hin' A0x R0 A1x R1).
    - exact (wf_ctx_nonneg A W).
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx Hml. destruct (in_group_inv _ _ _ _ Hx Hrx) as [(-> & -> & -> & ->) | [(-> & -> & -> & ->) | (Hn1 & Hn2 & H)]]; [| exact (wf_nested_small A W pa pm paib psl Hpa Hpr Hml) | exact (wf_nested_small A W x mtx aibx slx H Hrx Hml)].
      rewrite in_last, in_cnt, in_stride. unfold size in *. lia.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx Hsc48 Hmask. destruct (in_group_inv _ _ _ _ Hx Hrx) as [(-> & -> & -> & ->) | [(-> & -> & -> & ->) | (Hn1 & Hn2 & H)]]; [rewrite in_sc, in_stride; unfold size; lia | exact (wf_reusable A W pa pm paib psl Hpa Hpr Hsc48 Hmask) | exact (wf_reusable A W x mtx aibx slx H Hrx Hsc48 Hmask)].
    - (* [comment removed for export] *) intros pa0 pm0 paib0 psl0 j ch x mtx aibx slx Hpa0 Hpr0 Hj0 Hj Hx Hrx Hlo Hhi.
      (* [comment removed for export] *)
      assert (FIN : forall mtc aibc slc, a_meta A ch = Some mtc -> mt_role mtc = RGroup aibc slc ->
        gext_lo mtc <= gext_lo mtx -> gext_hi mtx <= gext_hi mtc ->
        exists mtc' aibc' slc', a_meta instN ch = Some mtc' /\ mt_role mtc' = RGroup aibc' slc' /\ gext_lo mtc' <= gext_lo mtx /\ gext_hi mtx <= gext_hi mtc').
      { intros mtc aibc slc Hmc Hrc Clo Chi. destruct (in_old_grp ch mtc aibc slc Hmc Hrc) as (mtc' & slc' & F1 & F2 & _ & F4 & F5 & _).
        exists mtc', aibc, slc'. rewrite F4, F5. auto. }
      destruct (in_group_inv _ _ _ _ Hpa0 Hpr0) as [(-> & -> & -> & ->) | [(-> & -> & -> & ->) | (Pn1 & Pn2 & HP)]]; [exfalso; exact (in_no_nested _ _ Hj) | |].
      + (* [comment removed for export] *)
        rewrite pm'_slot_start in Hlo. rewrite pm'_slot_end in Hhi.
        destruct (psl'_inv j _ Hj Hj0) as [(-> & E) | (Hji & Hj')].
        * injection E as ->. (* [comment removed for export] *)
          destruct (in_group_inv _ _ _ _ Hx Hrx) as [(-> & -> & -> & ->) | [(-> & -> & -> & ->) | (Xn1 & Xn2 & HX)]].
          -- exists in_mt, in_aib, in_slots. split; [exact in_meta_m|]. split; [reflexivity|]. lia.
          -- exfalso. rewrite pm'_gext_lo in Hlo. unfold gext_lo in *. lia.
          -- exfalso. exact (slot_i_clear x mtx aibx slx HX Hrx (conj Hlo Hhi)).
        * destruct (in_group_inv _ _ _ _ Hx Hrx) as [(-> & -> & -> & ->) | [(-> & -> & -> & ->) | (Xn1 & Xn2 & HX)]].
          -- exfalso. rewrite G1 in Hlo. exact (Hji (in_slot_unique j Hj0 Hlo Hhi)).
          -- exfalso. rewrite pm'_gext_lo in Hlo. unfold gext_lo in Hlo.
             assert (Hjc : j + 1 <= mt_cnt pm) by (pose proof (proj1 (nth_error_Some psl (Z.to_nat j)) ltac:(rewrite Hj'; discriminate)); pose proof pa_grp as (_ & _ & Hlen & _); lia).
             pose proof pa_grp as (_ & _ & _ & S16 & _). destruct (slot_in_ext pm j Hj0 Hjc ltac:(lia)) as [E1 E2]. unfold gext_lo in E1. lia.
          -- destruct (wf_cover A W pa pm paib psl j ch x mtx aibx slx Hpa Hpr Hj0 Hj' HX Hrx Hlo Hhi) as (mtc & aibc & slc & Hmc & Hrc & Clo & Chi).
             exact (FIN mtc aibc slc Hmc Hrc Clo Chi).
      + (* [comment removed for export] *)
        destruct (in_group_inv _ _ _ _ Hx Hrx) as [(-> & -> & -> & ->) | [(-> & -> & -> & ->) | (Xn1 & Xn2 & HX)]].
        * (* [comment removed for export] *)
          pose proof pa_grp as (_ & _ & _ & S16 & _).
          destruct (old_ext_len pa0 pm0 paib0 psl0 HP Hpr0) as (LEN0 & S160 & Hlen0).
          assert (Hjc : j + 1 <= mt_cnt pm0) by (pose proof (proj1 (nth_error_Some psl0 (Z.to_nat j)) ltac:(rewrite Hj; discriminate)); lia).
          destruct (slot_in_ext pm0 j Hj0 Hjc ltac:(lia)) as [E1 E2].
          destruct (wf_laminar A W pa pm paib psl pa0 pm0 paib0 psl0 Hpa Hpr HP Hpr0 ltac:(intros ->; exact (Pn2 eq_refl))) as [D | [D | [D | D]]].
          -- exfalso. lia.
          -- exfalso. unfold p, in_p in *. lia.
          -- exfalso. destruct D as (j1 & ch1 & Hj10 & Hj1 & Dlo & Dhi).
             assert (Hji : j1 <> i) by (intros ->; rewrite Hi in Hj1; discriminate Hj1).
             destruct (slots_apart pm j1 i Hj10 Hi0 Hji ltac:(lia)); unfold p, in_p in *; lia.
          -- destruct D as (j1 & ch1 & Hj10 & Hj1 & Dlo & Dhi).
             assert (Ej : j1 = j).
             { destruct (Z.eq_dec j1 j) as [E | Hne]; [exact E|]. exfalso.
               destruct (slots_apart pm0 j1 j Hj10 Hj0 Hne ltac:(lia)); unfold p, in_p in *; lia. }
             subst j1. rewrite Hj in Hj1. injection Hj1 as Ech1. subst ch1.
             destruct (wf_cover A W pa0 pm0 paib0 psl0 j ch pa pm paib psl HP Hpr0 Hj0 Hj Hpa Hpr Dlo Dhi) as (mtc & aibc & slc & Hmc & Hrc & Clo & Chi).
             apply (FIN mtc aibc slc Hmc Hrc); unfold p, in_p in *; lia.
        * rewrite pm'_gext_lo in Hlo. rewrite pm'_gext_hi in Hhi. rewrite pm'_gext_lo, pm'_gext_hi.
          destruct (wf_cover A W pa0 pm0 paib0 psl0 j ch pa pm paib psl HP Hpr0 Hj0 Hj Hpa Hpr Hlo Hhi) as (mtc & aibc & slc & Hmc & Hrc & Clo & Chi).
          exact (FIN mtc aibc slc Hmc Hrc Clo Chi).
        * destruct (wf_cover A W pa0 pm0 paib0 psl0 j ch x mtx aibx slx HP Hpr0 Hj0 Hj HX Hrx Hlo Hhi) as (mtc & aibc & slc & Hmc & Hrc & Clo & Chi).
          exact (FIN mtc aibc slc Hmc Hrc Clo Chi).
    - exact (wf_shift A W).
    - exact (wf_noarea_shift A W).
    - exact (wf_brk0 A W).
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx Hsc48. destruct (in_group_inv _ _ _ _ Hx Hrx) as [(-> & -> & -> & ->) | [(-> & -> & -> & ->) | (Hn1 & Hn2 & H)]]; [rewrite in_stride; pose proof size_rng; lia | exact (wf_stride20 A W pa pm paib psl Hpa Hpr Hsc48) | exact (wf_stride20 A W x mtx aibx slx H Hrx Hsc48)].
    - exact (wf_pages_al A W).
    - exact (wf_disj_page_area A W).
    - (* [comment removed for export] *) intros pg x mtx aibx slx Hpg Hx Hrx Hml. destruct (in_group_inv _ _ _ _ Hx Hrx) as [(-> & -> & -> & ->) | [(-> & -> & -> & ->) | (Hn1 & Hn2 & H)]]; [rewrite in_maplen in Hml; lia | | exact (wf_disj_page_grp A W pg x mtx aibx slx Hpg H Hrx Hml)].
      rewrite pm'_mem, pm'_grp_map_len. rewrite pm'_maplen in Hml. exact (wf_disj_page_grp A W pg pa pm paib psl Hpg Hpa Hpr Hml).
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx Hp'. destruct (in_group_inv _ _ _ _ Hx Hrx) as [(-> & -> & -> & ->) | [(-> & -> & -> & ->) | (Hn1 & Hn2 & H)]]; [rewrite B2, in_last in Hp'; lia | exact (wf_partial_sc A W pa pm paib psl Hpa Hpr Hp') | exact (wf_partial_sc A W x mtx aibx slx H Hrx Hp')].
    - exact (wf_mblocks_len A W).
    - exact (wf_mblocks_sz A W).
    - exact (wf_shift_mblocks A W).
    - exact (wf_shift_acct A W).
  Qed.

  (* [comment removed for export] *)
  Hypothesis Hfields : forall fl, mt_f md fl = in_f fl.

  Lemma in_mt_fields : forall fl, mt_f in_mt fl = mt_f md fl.
  Proof using Hfields. pu_keep (Hfields). intros fl. rewrite Hfields. reflexivity. Qed.

  Lemma in_slot_facts : forall j st f, nth_error in_slots j = Some st -> In f (slot_fields in_mt (Z.of_nat j) st) ->
    f = FCT (slot_start in_mt (Z.of_nat j) - 4) 1 0 \/ f = FCT (slot_end in_mt (Z.of_nat j)) 1 0.
  Proof using Hab Hcnt Hsc. pu_keep (Hab, Hcnt, Hsc).
    intros j st f Hj Hf. destruct (in_slots_inv _ _ Hj) as [(_ & ->) | (_ & ->)]; cbn in Hf; unfold slot_start, slot_end;
      (destruct Hf as [<- | [<- | []]]; [left | right]; reflexivity).
  Qed.

  (* [comment removed for export] *)
  Lemma slot_i_new_facts : forall f, In f (slot_fields pm i (SNested m)) ->
    In f (slot_fields pm i STaken) \/ f = FCT (p - 3) 1 (i + 32 * 6) \/ f = FCT (p - 2) 2 ((p - mt_mem pm - 16) / 16).
  Proof using Type. pu_keep tt.
    intros f Hf. unfold slot_fields, slot_fields_g in *. apply in_app_iff in Hf. destruct Hf as [Hf | Hf]; [left; apply in_app_iff; left; exact Hf|].
    right. unfold p, in_p, slot_start. destruct Hf as [<- | [<- | []]]; [left | right]; reflexivity.
  Qed.

  Lemma has_instN : forall f, has instN f ->
    has A f \/ f = FCT p 8 m \/ f = FCT (p + 8) 1 in_aib \/
    (exists j, (j < Z.to_nat cnt)%nat /\ (f = FCT (slot_start in_mt (Z.of_nat j) - 4) 1 0 \/ f = FCT (slot_end in_mt (Z.of_nat j)) 1 0)) \/
    f = FCT (p - 3) 1 (i + 32 * 6) \/ f = FCT (p - 2) 2 ((p - mt_mem pm - 16) / 16).
  Proof using Hab Hcnt Hfields Hi Hi0 Hm Hpa Hpr Hsc. pu_keep (Hab, Hcnt, Hfields, Hi, Hi0, Hm, Hpa, Hpr, Hsc).
    intros f [Hc | [Har | [Hmf | Hg]]].
    - left. left. exact Hc.
    - left. right; left. exact Har.
    - left. right; right; left. destruct Hmf as (x & mtx & fl & Hx & ->). destruct (in_meta_inv x mtx Hx) as [(-> & ->) | [(-> & ->) | (Hn1 & Hn2 & H)]].
      + exists m, md, fl. rewrite in_mt_fields. auto.
      + exists pa, pm, fl. rewrite pm'_f. auto.
      + exists x, mtx, fl. auto.
    - destruct Hg as (x & mtx & aibx & slx & Hx & Hrx & R). destruct (in_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | [(-> & -> & -> & ->) | (Hn1 & Hn2 & H)]].
      + right. destruct R as [Hh | (j & st & Hj & Hf)].
        * cbn in Hh. destruct Hh as [<- | [<- | []]]; [left; reflexivity | right; left; reflexivity].
        * right; right; left. exists j. split; [| exact (in_slot_facts j st f Hj Hf)].
          pose proof (proj1 (nth_error_Some in_slots j) ltac:(rewrite Hj; discriminate)) as LL. rewrite in_slots_len in LL. exact LL.
      + destruct R as [Hh | (j & st & Hj & Hf)].
        * left. right; right; right. exists pa, pm, paib, psl. unfold grp_hdr_fields in *. rewrite pm'_mem in Hh. auto.
        * rewrite pm'_slot_fields in Hf. destruct (psl'_inv_nat j st Hj) as [(-> & ->) | (Hne & Hj')].
          -- rewrite Z2Nat.id in Hf by exact Hi0. destruct (slot_i_new_facts f Hf) as [Ho | [Ho | Ho]]; [| right; right; right; right; left; exact Ho | right; right; right; right; right; exact Ho].
             left. right; right; right. exists pa, pm, paib, psl. split; [exact Hpa|]. split; [exact Hpr|]. right. exists (Z.to_nat i), STaken. rewrite Z2Nat.id by exact Hi0. auto.
          -- left. right; right; right. exists pa, pm, paib, psl. split; [exact Hpa|]. split; [exact Hpr|]. right. exists j, st. auto.
      + left. right; right; right. exists x, mtx, aibx, slx. auto.
  Qed.

  Lemma has_instN_intro : forall f, has A f -> has instN f.
  Proof using Hab Hcnt Hfields Hi Hm Hpa Hpr Hr Hsc. pu_keep (Hab, Hcnt, Hfields, Hi, Hm, Hpa, Hpr, Hr, Hsc).
    intros f [Hc | [Har | [Hmf | Hg]]].
    - left. exact Hc.
    - right; left. exact Har.
    - right; right; left. destruct Hmf as (x & mtx & fl & Hx & ->). destruct (Z.eq_dec x m) as [-> | Hne].
      + rewrite Hm in Hx. injection Hx as <-. exists m, in_mt, fl. rewrite in_mt_fields. split; [exact in_meta_m | reflexivity].
      + destruct (Z.eq_dec x pa) as [-> | Hne'].
        * rewrite Hpa in Hx. injection Hx as <-. exists pa, pm', fl. rewrite pm'_f. split; [exact in_meta_pa | reflexivity].
        * exists x, mtx, fl. rewrite (in_meta_other x Hne Hne'). auto.
    - right; right; right. destruct Hg as (x & mtx & aibx & slx & Hx & Hrx & R).
      destruct (in_fwd x mtx aibx slx Hx Hrx) as (mtx' & slx' & F1 & F2 & _ & F3 & _ & FM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FC).
      destruct FC as [(Hxp & E1 & E2) | (E0 & E1 & E2)].
      + subst mtx' slx'. exists x, mtx, aibx, slx. auto.
      + subst x mtx' slx'. rewrite Hpa in Hx. injection Hx as E. subst mtx. rewrite Hpr in Hrx. injection Hrx as Ea Es. subst aibx slx.
        exists pa, pm', paib, psl'. split; [exact in_meta_pa|]. split; [reflexivity|].
        destruct R as [Hh | (j & st & Hj & Hf)]; [left; exact Hh | right].
        destruct (Nat.eq_dec j (Z.to_nat i)) as [-> | Hne].
        * exists (Z.to_nat i), (SNested m). split; [exact psl'_i|]. rewrite Hi in Hj. injection Hj as <-.
          unfold slot_fields, slot_fields_g in *. apply in_app_iff in Hf. apply in_app_iff. destruct Hf as [Hf | []]. left. exact Hf.
        * exists j, st. rewrite psl'_other by exact Hne. auto.
  Qed.

  Lemma has_instN_hdr : has instN (FCT p 8 m) /\ has instN (FCT (p + 8) 1 in_aib).
  Proof using Type. pu_keep tt.
    split; (right; right; right; exists m, in_mt, in_aib, in_slots; split; [exact in_meta_m|]; split; [reflexivity|]; left; cbn; auto).
  Qed.

  Lemma has_instN_slot : forall j, (j < Z.to_nat cnt)%nat ->
    has instN (FCT (slot_start in_mt (Z.of_nat j) - 4) 1 0) /\ has instN (FCT (slot_end in_mt (Z.of_nat j)) 1 0).
  Proof using Hab Hcnt Hsc. pu_keep (Hab, Hcnt, Hsc).
    intros j Hj.
    assert (E : exists st, nth_error in_slots j = Some st).
    { destruct (nth_error in_slots j) as [st|] eqn:E; [exists st; reflexivity|].
      exfalso. apply nth_error_None in E. rewrite in_slots_len in E. lia. }
    destruct E as [st Hst].
    assert (Hin : forall f, In f (slot_fields in_mt (Z.of_nat j) st) -> has instN f).
    { intros f Hf. right; right; right. exists m, in_mt, in_aib, in_slots. split; [exact in_meta_m|]. split; [reflexivity|]. right. exists j, st. auto. }
    destruct (in_slots_inv _ _ Hst) as [(_ & ->) | (_ & ->)]; (split; apply Hin; cbn; auto).
  Qed.

  Lemma has_instN_pslot : has instN (FCT (p - 3) 1 (i + 32 * 6)) /\ has instN (FCT (p - 2) 2 ((p - mt_mem pm - 16) / 16)).
  Proof using Hi Hi0 Hm Hpa Hpr Hr. pu_keep (Hi, Hi0, Hm, Hpa, Hpr, Hr).
    assert (Hin : forall f, In f (slot_fields pm' i (SNested m)) -> has instN f).
    { intros f Hf. right; right; right. exists pa, pm', paib, psl'. split; [exact in_meta_pa|]. split; [reflexivity|]. right.
      exists (Z.to_nat i), (SNested m). rewrite Z2Nat.id by exact Hi0. split; [exact psl'_i | exact Hf]. }
    split; apply Hin; rewrite pm'_slot_fields; unfold slot_fields, slot_fields_g; apply in_app_iff; right; cbn; unfold p, in_p, slot_start; auto.
  Qed.

  Lemma dom_instN : forall x, dom instN x <-> dom A x.
  Proof using Hab Hcnt Hi Hm Hpa Hpr Hr Hsc. pu_keep (Hab, Hcnt, Hi, Hm, Hpa, Hpr, Hr, Hsc).
    intros x. unfold dom. cbn [a_areas a_meta a_pages instN]. split.
    - intros [Ha | [(y & mty & aiby & sly & Hy & Hry & Hml & R) | Hp]]; [left; exact Ha | | right; right; exact Hp].
      destruct (in_group_inv y mty aiby sly Hy Hry) as [(-> & -> & -> & ->) | [(-> & -> & -> & ->) | (Hn1 & Hn2 & H)]]; [rewrite in_maplen in Hml; lia | |].
      + right; left. exists pa, pm, paib, psl. auto.
      + right; left. exists y, mty, aiby, sly. auto.
    - intros [Ha | [(y & mty & aiby & sly & Hy & Hry & Hml & R) | Hp]]; [left; exact Ha | | right; right; exact Hp].
      right; left. destruct (in_old_grp y mty aiby sly Hy Hry) as (mty' & sly' & F1 & F2 & _ & _ & _ & F6 & F7 & F8).
      exists y, mty', aiby, sly'. rewrite F6, F7, F8. auto.
  Qed.

  Lemma VMok_instN : forall h, VMok A h -> VMok instN h.
  Proof using Hab Hcnt Hi Hm Hpa Hpr Hr Hsc. pu_keep (Hab, Hcnt, Hi, Hm, Hpa, Hpr, Hr, Hsc).
    intros h [Vg Vb Va Vres Vbv Vpw Vmw Vna Vac Vpc Vall Vspan Vtop].
    constructor; cbn [a_ctx a_areas a_meta a_freelist a_active a_pages a_brk_lo a_live a_mblocks a_xmaps instN]; try assumption.
    - intros x mtx aibx slx Hx Hrx Hml. destruct (in_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | [(-> & -> & -> & ->) | (Hn1 & Hn2 & H)]]; [rewrite in_maplen in Hml; lia | | exact (Vg x mtx aibx slx H Hrx Hml)].
      rewrite pm'_mem, pm'_grp_map_len. rewrite pm'_maplen in Hml. exact (Vg pa pm paib psl Hpa Hpr Hml).
    - intros b sz Hb. destruct (Vall b sz Hb) as [(x & mtx & aibx & slx & Hx & Hrx & Hml & R) | Ho]; [left | right; exact Ho].
      destruct (in_old_grp x mtx aibx slx Hx Hrx) as (mtx' & slx' & F1 & F2 & _ & _ & _ & F6 & F7 & F8).
      exists x, mtx', aibx, slx'. rewrite F6, F7, F8. auto.
  Qed.

  Lemma meta_usage_instN : forall c x, meta_usage instN c x = meta_usage A c x + (if Z.eq_dec x m then (if sc =? c then cnt else 0) else 0).
  Proof using Hab Hcnt Hm Hpa Hpr Hr Hsc. pu_keep (Hab, Hcnt, Hm, Hpa, Hpr, Hr, Hsc).
    intros c x. unfold meta_usage. rewrite in_meta. destruct (Z.eq_dec x m) as [-> | Hne].
    - rewrite Hm, Hr. unfold in_mt. rewrite mt_role_MT. fold in_mt. rewrite in_sc, in_cnt. lia.
    - destruct (Z.eq_dec x pa) as [-> | Hne']; [| lia]. rewrite Hpa, Hpr. unfold pm'. rewrite mt_role_MT. fold pm'. rewrite pm'_sc, pm'_cnt. lia.
  Qed.

  Lemma usage_of_instN : forall c, 0 <= c < 48 -> usage_of instN c = usage_of A c + (if sc =? c then cnt else 0).
  Proof using HW Hab Hcnt Hm Hpa Hpr Hr Hsc. pu_keep (HW, Hab, Hcnt, Hm, Hpa, Hpr, Hr, Hsc).
    intros c Hc.
    destruct (proj1 (wf_meta_dom A HW m) ltac:(rewrite Hm; discriminate)) as (pg & k & Hpg & Hk & Em).
    rewrite (usage_of_point A instN c m pg k (- (if sc =? c then cnt else 0)) HW eq_refl Hpg Hk Em); [lia | |].
    - intros x Hx. rewrite meta_usage_instN. destruct (Z.eq_dec x m); [contradiction | lia].
    - rewrite meta_usage_instN. destruct (Z.eq_dec m m); [lia | contradiction].
  Qed.

  Lemma AvOK_instN : AvOK A -> AvOK instN.
  Proof using Type. pu_keep tt.
    intros Hav x mtx Hx Hrx. cbn [a_ctx a_areas instN].
    destruct (in_meta_inv x mtx Hx) as [(-> & ->) | [(-> & ->) | (Hn1 & Hn2 & H)]]; [cbn in Hrx; discriminate Hrx | cbn in Hrx; discriminate Hrx | exact (Hav x mtx H Hrx)].
  Qed.

  Lemma deads_instN : forall D, deads A (m :: D) -> ~ In m D -> deads instN D.
  Proof using Hm Hpa Hpr. pu_keep (Hm, Hpa, Hpr).
    intros D Hd Hnin x. split.
    - intros (mtx & Hx & Hrx). destruct (in_meta_inv x mtx Hx) as [(-> & ->) | [(-> & ->) | (Hn1 & Hn2 & H)]]; [cbn in Hrx; discriminate Hrx | cbn in Hrx; discriminate Hrx |].
      destruct (proj1 (Hd x) (ex_intro _ mtx (conj H Hrx))) as [-> | Hin]; [contradiction | exact Hin].
    - intros Hin. assert (Hne : x <> m) by (intros ->; exact (Hnin Hin)).
      destruct (proj2 (Hd x) (or_intror Hin)) as (mtx & Hx & Hrx).
      assert (Hne' : x <> pa) by (intros ->; rewrite Hpa in Hx; injection Hx as <-; rewrite Hpr in Hrx; discriminate Hrx).
      exists mtx. rewrite (in_meta_other x Hne Hne'). auto.
  Qed.
End InstallNested.

End WithLayout.
