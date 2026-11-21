(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/echconfiglist_parser/lib/LazyRestrictRun.v; 369 of its 418 lines of code are new or changed and 69 lines of the source are left out. *)
(* Theorem Labs, 2026-11 (LPS 20f40762): the lifts from a binary's own segment list [segs] to the
   run's list [segs ++ tail] for a configuration with lazy reservations ([LazySR.lzok]), the lazy
   counterpart of [RunTail] (Common/Cfg/RunTail.v) and of the transfer lemmas of Ref/F_timeRun.v
   (its [tr_*] lemmas, F_timeRun.v:276-359).  The tail is the vDSO pair ([Run.vdso_segments],
   theories/LinuxProcessSem/Run.v:290-306, both "r--"): neither executable nor writable, every
   byte of it inside a window [vlo, vhi) that holds no byte of [segs].

   - [lzok_app_tail] / [lzok_of_app_tail]: [lzok] over [segs ++ tail] is [lzok] over [segs] plus
     [lazy_ranges_okb tail L] (the form LazyRestrict.v:550 states); [lzok_app_tail_window] gives
     it from lazy ranges that miss the window ([VdsoClean.range_off]).
   - [evt_sreach_lazy_tail]: LazySR.v's [evt_sreach_lazy_at] (LazySR.v:245-255) over
     [segs ++ tail], with [lzok] over [segs] going in and coming out; [_post] is its form with a
     target set, [_segs] takes a walk over [segs], [_wrom] a walk over [segs] from the binary's
     backing.  This is the lazy counterpart of [RunTail.exec_evt_sreach_tail], which asks
     [m_vm_lazy = []].
   - [lzt_mem_inv_keep] / [lzt_vclean_of_inv]: [mem_inv] over the larger list from [mem_inv] over
     [segs] and a clean window ([VdsoClean.vclean]), and the clean window back from [mem_inv] over
     the larger list.
   - [lzt_*_keep] / [lzt_*_back]: [mrd], [bytes_at], [cells_at], [ro_cells], [rw_cells], [wr_at],
     [stk], [wmono], [mem_inv] from [segs] to [segs ++ tail], and back away from the window.
   - [lzt_hid_avoids], [lzt_L_off_window], [evt_sreach_lazy_av]: a walk over [segs ++ tail] keeps
     the lazy view over [segs] when no hidden byte is a byte of the window, which lazy ranges
     inside the mapped table and maps that miss the window give; no [lazy_ranges_okb tail L]
     is needed (a zero-size lazy entry inside the window hides nothing but falsifies it).

   [RunTail.sreach_app_tail], [sreach_wrom] and [sreach_lift_tail] carry no [m_vm_lazy] premise,
   so they already lift an [sreach] over [segs] from a lazy configuration; nothing here repeats
   them.  This file names nothing of a binary: copy it whole into a unit with the same
   LazySR / Lib layer. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import
  Scfg SReach LazyRestrict LazySR VdsoClean.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import RomBase RomStable RunTail.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Exec.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require CatSim LazyRestrictRun.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Mem Cells Step Frame.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(** * Lazy ranges over two segment lists *)

Lemma lzt_lazy_range_okb_app : forall (sa sb : list Segment) r,
  lazy_range_okb (sa ++ sb) r = lazy_range_okb sa r && lazy_range_okb sb r.
Proof.
  intros sa sb r. unfold lazy_range_okb. rewrite forallb_app.
  destruct (range_nowrapb r); reflexivity.
Qed.

Lemma lzt_lazy_ranges_okb_app : forall (sa sb : list Segment) L,
  lazy_ranges_okb (sa ++ sb) L = true <->
  lazy_ranges_okb sa L = true /\ lazy_ranges_okb sb L = true.
Proof.
  intros sa sb L.
  assert (E : forallb (lazy_range_okb (sa ++ sb)) L
              = forallb (lazy_range_okb sa) L && forallb (lazy_range_okb sb) L).
  { induction L as [|r L IH]; [reflexivity|].
    cbn [forallb]. rewrite IH, lzt_lazy_range_okb_app.
    destruct (lazy_range_okb sa r), (lazy_range_okb sb r),
             (forallb (lazy_range_okb sa) L), (forallb (lazy_range_okb sb) L); reflexivity. }
  unfold lazy_ranges_okb, segs_nowrapb. rewrite forallb_app, E, !andb_true_iff. tauto.
Qed.

(* a byte a segment of the list covers is found by [find_segment]
   (theories/LinuxProcessSem/RiscvSemantics.v:332-342) *)
Lemma lzt_find_segment_cover : forall (sl : list Segment) (s : Segment) (x : Z),
  In s sl -> Z.of_N (seg_base s) <= x -> x + 1 <= Z.of_N (seg_base s) + Z.of_N (seg_size s) ->
  find_segment sl x 1 <> None.
Proof.
  induction sl as [|s0 rest IH]; intros s x Hin H1 H2; [destruct Hin|].
  cbn [find_segment].
  destruct (Z.leb (Z.of_N (seg_base s0)) x
            && Z.leb (x + 1) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)))%bool eqn:E.
  - discriminate.
  - destruct Hin as [<- | Hin].
    + rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.leb_le _ _) H2) in E.
      cbn [andb] in E. discriminate E.
    + exact (IH s x Hin H1 H2).
Qed.

Section LazyTail.
  Variables segs tail : list Segment.
  Hypothesis Hnx : forall s, In s tail -> seg_executable s = false.
  Hypothesis Hnw : forall s, In s tail -> seg_writable s = false.
  (* the window: every tail byte is inside it, every byte of it is a tail byte, and [segs]
     holds none of it *)
  Variables vlo vhi : Z.
  Hypothesis Htw : forall (x : Z) s, find_segment tail x 1 = Some s -> vlo <= x < vhi.
  Hypothesis Hcov : forall (x : Z), vlo <= x < vhi -> find_segment tail x 1 <> None.
  Hypothesis Hsoff : forall (x : Z), vlo <= x < vhi -> find_segment segs x 1 = None.
  Context {SC : StepCfg}.

  (** ** 1. [lzok] over the larger list *)

  Lemma lzok_app_tail : forall L S Zr c,
    lzok segs L S Zr c -> lazy_ranges_okb tail L = true -> lzok (segs ++ tail) L S Zr c.
  Proof.
    intros L S Zr c Hok HT. destruct Hok as [HL Hinv Hh HZ HSZ HZL HLM].
    constructor; [| exact Hinv | exact Hh | exact HZ | exact HSZ | exact HZL | exact HLM].
    apply (proj2 (lzt_lazy_ranges_okb_app segs tail L)). split; [exact HL | exact HT].
  Qed.

  Lemma lzok_of_app_tail : forall L S Zr c, lzok (segs ++ tail) L S Zr c -> lzok segs L S Zr c.
  Proof.
    intros L S Zr c Hok. destruct Hok as [HL Hinv Hh HZ HSZ HZL HLM].
    constructor; [| exact Hinv | exact Hh | exact HZ | exact HSZ | exact HZL | exact HLM].
    exact (proj1 (proj1 (lzt_lazy_ranges_okb_app segs tail L) HL)).
  Qed.

  Lemma lzok_tail_ranges : forall L S Zr c, lzok (segs ++ tail) L S Zr c -> lazy_ranges_okb tail L = true.
  Proof.
    intros L S Zr c Hok. exact (proj2 (proj1 (lzt_lazy_ranges_okb_app segs tail L) (lzok_ranges Hok))).
  Qed.

  (* a tail segment with at least one byte lies inside the window *)
  Lemma lzt_seg_in_window : forall s, In s tail -> (0 < seg_size s)%N ->
    vlo <= Z.of_N (seg_base s) /\ Z.of_N (seg_base s) + Z.of_N (seg_size s) <= vhi.
  Proof.
    intros s Hin Hsz.
    assert (Hpos : 0 < Z.of_N (seg_size s)) by lia.
    split.
    - destruct (find_segment tail (Z.of_N (seg_base s)) 1) as [s1|] eqn:E.
      + exact (proj1 (Htw _ s1 E)).
      + exfalso. refine (lzt_find_segment_cover tail s (Z.of_N (seg_base s)) Hin _ _ E); lia.
    - destruct (find_segment tail (Z.of_N (seg_base s) + Z.of_N (seg_size s) - 1) 1) as [s1|] eqn:E.
      + pose proof (Htw _ s1 E) as H. lia.
      + exfalso.
        refine (lzt_find_segment_cover tail s (Z.of_N (seg_base s) + Z.of_N (seg_size s) - 1) Hin _ _ E); lia.
  Qed.

  (* lazy ranges that miss the window miss every tail segment *)
  Lemma lzt_lazy_ranges_okb : forall L,
    (forall s, In s tail -> (0 < seg_size s)%N) ->
    vhi <= 2 ^ 64 ->
    (forall r, In r L -> range_nowrapb r = true) ->
    Forall (range_off vlo vhi) L ->
    lazy_ranges_okb tail L = true.
  Proof.
    intros L Hne Hvhi HLn HLo. unfold lazy_ranges_okb. apply andb_true_iff. split.
    - unfold segs_nowrapb. apply forallb_forall. intros s Hin.
      destruct (lzt_seg_in_window s Hin (Hne s Hin)) as [_ H2].
      cbv beta. apply Z.leb_le. lia.
    - apply forallb_forall. intros [lo sz] Hr.
      unfold lazy_range_okb. apply andb_true_iff. split; [exact (HLn (lo, sz) Hr)|].
      apply forallb_forall. intros s Hin.
      destruct (lzt_seg_in_window s Hin (Hne s Hin)) as [H1 H2].
      pose proof HLo as Ho. rewrite Forall_forall in Ho. specialize (Ho (lo, sz) Hr).
      unfold range_off in Ho. cbn [fst snd] in Ho.
      unfold seg_disjoint_rangeb. cbn [fst snd]. apply orb_true_iff.
      destruct Ho as [Ho | Ho]; [right | left]; apply Z.leb_le; lia.
  Qed.

  Lemma lzok_app_tail_window : forall L S Zr c,
    lzok segs L S Zr c ->
    (forall s, In s tail -> (0 < seg_size s)%N) ->
    vhi <= 2 ^ 64 ->
    Forall (range_off vlo vhi) L ->
    lzok (segs ++ tail) L S Zr c.
  Proof.
    intros L S Zr c Hok Hne Hvhi HLo. apply (lzok_app_tail L S Zr c Hok).
    apply (lzt_lazy_ranges_okb L Hne Hvhi); [| exact HLo].
    intros r Hr. pose proof (lazy_ranges_okb_In segs L r (lzok_ranges Hok) Hr) as H.
    unfold lazy_range_okb in H. apply andb_true_iff in H. exact (proj1 H).
  Qed.

  (** ** 3. The straight-line law over the larger list *)

  (* LazySR.v:245-255 at [segs ++ tail]; the caller's [lzok] is over [segs] on both sides *)
  Theorem evt_sreach_lazy_tail : forall L S Zr (P : machine_state -> Prop) msF ms mo (Q : config -> Prop),
    lazy_ranges_okb tail L = true ->
    lzok segs L S Zr (mkCfg msF mo) ->
    restrict L S msF = ms ->
    Exec.evt (segs ++ tail) P ms ->
    (forall msF' mo', lzok segs L S Zr (mkCfg msF' mo') ->
                      same_but_materialized mo mo' ->
                      hid_same L S msF msF' ->
                      P (restrict L S msF') ->
                      sreach (segs ++ tail) Q (mkCfg msF' mo')) ->
    sreach (segs ++ tail) Q (mkCfg msF mo).
  Proof.
    intros L S Zr P msF ms mo Q HT Hok Hr Hevt Hk.
    apply (@evt_sreach_lazy_at (segs ++ tail) SC L S Zr P msF ms mo Q
             (lzok_app_tail L S Zr (mkCfg msF mo) Hok HT) Hr Hevt).
    intros msF' mo' Hok' Hsame Hs HP.
    exact (Hk msF' mo' (lzok_of_app_tail L S Zr (mkCfg msF' mo') Hok') Hsame Hs HP).
  Qed.

  Theorem evt_sreach_lazy_tail_post : forall L S Zr (P : machine_state -> Prop) msF ms mo,
    lazy_ranges_okb tail L = true ->
    lzok segs L S Zr (mkCfg msF mo) ->
    restrict L S msF = ms ->
    Exec.evt (segs ++ tail) P ms ->
    sreach (segs ++ tail)
      (fun c => P (restrict L S (cfg_ms c))
                /\ lzok segs L S Zr c
                /\ same_but_materialized mo (cfg_model c)
                /\ hid_same L S msF (cfg_ms c))
      (mkCfg msF mo).
  Proof.
    intros L S Zr P msF ms mo HT Hok Hr Hevt.
    apply (evt_sreach_lazy_tail L S Zr P msF ms mo _ HT Hok Hr Hevt).
    intros msF' mo' Hok' Hsame Hs HP. apply sr_done. cbn [cfg_ms cfg_model].
    split; [exact HP|]. split; [exact Hok'|]. split; [exact Hsame | exact Hs].
  Qed.

  (* the walk over [segs] alone: its machine steps are steps over the larger list
     ([RunTail.exec_msteps_app_tail], RunTail.v:75) *)
  Theorem evt_sreach_lazy_tail_segs : forall L S Zr (P : machine_state -> Prop) msF ms mo (Q : config -> Prop),
    lazy_ranges_okb tail L = true ->
    lzok segs L S Zr (mkCfg msF mo) ->
    restrict L S msF = ms ->
    Exec.evt segs P ms ->
    (forall msF' mo', lzok segs L S Zr (mkCfg msF' mo') ->
                      same_but_materialized mo mo' ->
                      hid_same L S msF msF' ->
                      P (restrict L S msF') ->
                      sreach (segs ++ tail) Q (mkCfg msF' mo')) ->
    sreach (segs ++ tail) Q (mkCfg msF mo).
  Proof.
    intros L S Zr P msF ms mo Q HT Hok Hr (ms' & Hms & HP) Hk.
    apply (evt_sreach_lazy_tail L S Zr P msF ms mo Q HT Hok Hr); [| exact Hk].
    exists ms'. split; [| exact HP].
    eapply exec_msteps_app_tail; first [exact Hnx | exact Hnw | exact Hms].
  Qed.

  (* the walk over [segs] stated from the binary's backing, run from the state with backing [r]
     ([RunTail.exec_msteps_wrom], RunTail.v:47): the counterpart of [exec_evt_sreach_tail] *)
  Theorem evt_sreach_lazy_tail_wrom : forall L S Zr (P : machine_state -> Prop) msF ms0 mo r (Q : config -> Prop),
    lazy_ranges_okb tail L = true ->
    lzok segs L S Zr (mkCfg msF mo) ->
    restrict L S msF = wrom ms0 r ->
    Exec.evt segs P ms0 ->
    (forall msF' mo', lzok segs L S Zr (mkCfg msF' mo') ->
                      same_but_materialized mo mo' ->
                      hid_same L S msF msF' ->
                      (exists ms1, restrict L S msF' = wrom ms1 r /\ P ms1) ->
                      sreach (segs ++ tail) Q (mkCfg msF' mo')) ->
    sreach (segs ++ tail) Q (mkCfg msF mo).
  Proof.
    intros L S Zr P msF ms0 mo r Q HT Hok Hr (ms1 & Hms & HP) Hk.
    apply (evt_sreach_lazy_tail L S Zr (fun x => exists x0, x = wrom x0 r /\ P x0)
             msF (wrom ms0 r) mo Q HT Hok Hr).
    - exists (wrom ms1 r). split.
      + eapply exec_msteps_app_tail;
          first [exact Hnx | exact Hnw | exact (exec_msteps_wrom segs ms0 ms1 r Hms)].
      + exists ms1. split; [reflexivity | exact HP].
    - intros msF' mo' Hok' Hsame Hs (x0 & Ex & HPx).
      apply (Hk msF' mo' Hok' Hsame Hs). exists x0. split; [exact Ex | exact HPx].
  Qed.

  (** ** 2. [mem_inv] and the clean window *)

  (* an overlay byte is never at a tail address: those are inside the window, which is clean
     (Ref/F_timeRun.v:301, [tr_mem_inv_keep]) *)
  Lemma lzt_mem_inv_keep : forall m, mem_inv segs m -> vclean vlo vhi m -> mem_inv (segs ++ tail) m.
  Proof.
    intros m MI VC a b Ha. pose proof (MI a b Ha) as R. revert R.
    unfold ro_addr. rewrite find_segment_app.
    destruct (find_segment segs (bv_unsigned a) 1) as [sg|]; intros R; [exact R|].
    destruct (find_segment tail (bv_unsigned a) 1) as [sg|] eqn:E2; [|reflexivity].
    exfalso. rewrite (VC a (Htw _ _ E2)) in Ha. discriminate Ha.
  Qed.

  Lemma lzt_mem_inv_back : forall m, mem_inv (segs ++ tail) m -> mem_inv segs m.
  Proof.
    intros m MI a b Ha. pose proof (MI a b Ha) as R. revert R.
    unfold ro_addr. rewrite find_segment_app.
    destruct (find_segment segs (bv_unsigned a) 1) as [sg|]; intros R; [exact R | reflexivity].
  Qed.

  (* every window byte is a read-only tail byte, so [mem_inv] keeps the overlay off it
     (Ref/F_timeRun.v:311, [tr_vclean_of_inv]) *)
  Lemma lzt_vclean_of_inv : forall m, mem_inv (segs ++ tail) m -> vclean vlo vhi m.
  Proof.
    intros m MI x Hx. destruct (m x) as [b|] eqn:E; [exfalso | reflexivity].
    pose proof (MI x b E) as R. revert R.
    unfold ro_addr. rewrite find_segment_app.
    rewrite (Hsoff (bv_unsigned x) Hx).
    destruct (find_segment tail (bv_unsigned x) 1) as [sg|] eqn:E2; [| exfalso; exact (Hcov _ Hx E2)].
    cbv beta iota. rewrite (Hnw sg (find_segment_in _ _ _ _ E2)). cbn [negb].
    intros R. discriminate R.
  Qed.

  (* the restriction only hides bytes; with lazy ranges off the window it hides none of it *)
  Lemma lzt_vclean_restrict : forall L S m, vclean vlo vhi m -> vclean vlo vhi (restrict_mem L S m).
  Proof.
    intros L S m C x Hx. unfold restrict_mem, restrict_mem_by. cbv beta.
    destruct (hiddenb L S x); [reflexivity | exact (C x Hx)].
  Qed.

  Lemma lzt_vclean_of_restrict : forall L S m,
    Forall (range_off vlo vhi) L -> vclean vlo vhi (restrict_mem L S m) -> vclean vlo vhi m.
  Proof.
    intros L S m HL C x Hx. rewrite <- (restrict_mem_outside_lazy L S m x); [exact (C x Hx)|].
    apply in_rangesb_false. intros lo sz Hin Hr.
    pose proof HL as Ho. rewrite Forall_forall in Ho. specialize (Ho (lo, sz) Hin).
    unfold range_off in Ho. cbn [fst snd] in Ho. lia.
  Qed.

  (** ** 5. Memory predicates between the two lists *)

  (* the writable view is the same over both lists (RomStable.v:349) *)
  Lemma lzt_wview : forall m x, wview (segs ++ tail) m x = wview segs m x.
  Proof. intros m x. apply wview_app_nw; first [exact Hnw | exact Hnx]. Qed.

  (* a read the binary's list serves is served the same by the larger list (RomStable.v:327) *)
  Lemma lzt_mrd_keep : forall m a b, mrd segs m a = Some b -> mrd (segs ++ tail) m a = Some b.
  Proof.
    intros m a b H. unfold mrd in *.
    destruct (m a) as [b0|] eqn:EM; [exact H|].
    unfold OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib.PropExec.seg_rom in *.
    destruct (memory_read segs a 1) as [bs|] eqn:E; [|discriminate H].
    rewrite (memory_read_app_nx segs tail a 1 bs E). exact H.
  Qed.

  (* off the window the two lists read the same (Ref/F_timeRun.v:323, [tr_mrd_off]) *)
  Lemma lzt_mrd_off : forall m x, ~ (vlo <= bv_unsigned x < vhi) -> mrd (segs ++ tail) m x = mrd segs m x.
  Proof.
    intros m x Hx. unfold mrd. destruct (m x) as [b|]; [reflexivity|].
    unfold OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib.PropExec.seg_rom, memory_read.
    rewrite find_segment_app.
    destruct (find_segment segs _ _) as [sg|]; [reflexivity|].
    destruct (find_segment tail _ _) as [sg|] eqn:E; [|reflexivity].
    exfalso. apply Hx. exact (Htw _ sg E).
  Qed.

  Lemma lzt_bytes_at_keep : forall m A bs, bytes_at segs m A bs -> bytes_at (segs ++ tail) m A bs.
  Proof.
    intros m A bs (H0 & H1 & H2). split; [exact H0|]. split; [exact H1|].
    intros i Hi. destruct (nth_error bs i) as [b|] eqn:EN.
    - apply lzt_mrd_keep. rewrite (H2 i Hi), EN. reflexivity.
    - apply nth_error_None in EN. lia.
  Qed.

  Lemma lzt_bytes_at_back : forall m A bs, (A + Z.of_nat (length bs) <= vlo \/ vhi <= A) ->
    bytes_at (segs ++ tail) m A bs -> bytes_at segs m A bs.
  Proof.
    intros m A bs Hout (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
    intros i Hi. rewrite <- lzt_mrd_off; [exact (H i Hi)|].
    rewrite wa_unsigned by lia. lia.
  Qed.

  Lemma lzt_cells_at_keep : forall m A cs, cells_at segs m A cs -> cells_at (segs ++ tail) m A cs.
  Proof. intros m A cs [Hwf Hb]. split; [exact Hwf | exact (lzt_bytes_at_keep m A _ Hb)]. Qed.

  Lemma lzt_cells_at_back : forall m A cs, (A + Z.of_nat (cells_size cs) <= vlo \/ vhi <= A) ->
    cells_at (segs ++ tail) m A cs -> cells_at segs m A cs.
  Proof.
    intros m A cs Hout [Hwf Hb]. split; [exact Hwf|].
    apply lzt_bytes_at_back; [rewrite (cells_bytes_length cs Hwf); exact Hout | exact Hb].
  Qed.

  Lemma lzt_ro_cells_keep : forall m A cs, ro_cells segs m A cs -> ro_cells (segs ++ tail) m A cs.
  Proof. intros m A cs H. exact (lzt_cells_at_keep m A cs H). Qed.

  Lemma lzt_ro_cells_back : forall m A cs, (A + Z.of_nat (cells_size cs) <= vlo \/ vhi <= A) ->
    ro_cells (segs ++ tail) m A cs -> ro_cells segs m A cs.
  Proof. intros m A cs Hout H. exact (lzt_cells_at_back m A cs Hout H). Qed.

  Lemma lzt_wr_at_keep : forall m A n, wr_at segs m A n -> wr_at (segs ++ tail) m A n.
  Proof.
    intros m A n (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
    intros i Hi. rewrite lzt_wview. exact (H i Hi).
  Qed.

  Lemma lzt_wr_at_back : forall m A n, wr_at (segs ++ tail) m A n -> wr_at segs m A n.
  Proof.
    intros m A n (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
    intros i Hi. rewrite <- lzt_wview. exact (H i Hi).
  Qed.

  Lemma lzt_rw_cells_keep : forall m A cs, rw_cells segs m A cs -> rw_cells (segs ++ tail) m A cs.
  Proof.
    intros m A cs [Hc Hw]. split; [exact (lzt_cells_at_keep m A cs Hc) | exact (lzt_wr_at_keep m A _ Hw)].
  Qed.

  Lemma lzt_rw_cells_back : forall m A cs, (A + Z.of_nat (cells_size cs) <= vlo \/ vhi <= A) ->
    rw_cells (segs ++ tail) m A cs -> rw_cells segs m A cs.
  Proof.
    intros m A cs Hout [Hc Hw].
    split; [exact (lzt_cells_at_back m A cs Hout Hc) | exact (lzt_wr_at_back m A _ Hw)].
  Qed.

  Lemma lzt_stk_keep : forall m lo hi, stk segs m lo hi -> stk (segs ++ tail) m lo hi.
  Proof.
    intros m lo hi (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
    intros a Ha. destruct (H a Ha) as [Hw (b & Hb)].
    split; [rewrite lzt_wview; exact Hw | exists b; exact (lzt_mrd_keep m _ _ Hb)].
  Qed.

  Lemma lzt_stk_back : forall m lo hi, (hi <= vlo \/ vhi <= lo) ->
    stk (segs ++ tail) m lo hi -> stk segs m lo hi.
  Proof.
    intros m lo hi Hout (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
    intros a Ha. destruct (H a Ha) as [Hw Hb]. split; [rewrite <- lzt_wview; exact Hw|].
    rewrite <- lzt_mrd_off; [exact Hb|]. rewrite wa_unsigned by lia. lia.
  Qed.

  Lemma lzt_wmono_keep : forall m m', wmono segs m m' -> wmono (segs ++ tail) m m'.
  Proof.
    intros m m' W x Hx. rewrite lzt_wview in Hx. rewrite lzt_wview. exact (W x Hx).
  Qed.

  Lemma lzt_wmono_back : forall m m', wmono (segs ++ tail) m m' -> wmono segs m m'.
  Proof.
    intros m m' W x Hx. rewrite <- lzt_wview in Hx. rewrite <- lzt_wview. exact (W x Hx).
  Qed.

  (** ** 6. The hidden bytes avoid the larger list *)

  (* [LazyRestrict.lazy_ranges_ok_avoids] over [segs ++ tail]: over [segs] from
     [lazy_ranges_okb segs L]; over the tail because every tail byte is in the window and no
     lazy address is *)
  Lemma lzt_hid_avoids : forall L S,
    (forall s, In s tail -> (0 < seg_size s)%N) ->
    vhi <= 2 ^ 64 ->
    lazy_ranges_okb segs L = true ->
    (forall x : word, vlo <= bv_unsigned x < vhi -> in_rangesb x L = false) ->
    hid_avoids_segs (segs ++ tail) (hiddenb L S).
  Proof.
    intros L S Hne Hvhi HL Hw.
    destruct (lazy_ranges_ok_avoids segs L S HL) as [HA1 HA2].
    split.
    - intros a seg Hin Hcv. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      + exact (HA1 a seg Hin Hcv).
      + destruct (lzt_seg_in_window seg Hin (Hne seg Hin)) as [W1 W2].
        unfold seg_covers in Hcv.
        apply hiddenb_outside_L. apply Hw. lia.
    - intros seg Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      + exact (HA2 seg Hin).
      + destruct (lzt_seg_in_window seg Hin (Hne seg Hin)) as [W1 W2]. lia.
  Qed.
End LazyTail.

(* no lazy address is in the window when the mapped table misses it ([lzok_LM]: every lazy
   address is mapped) *)
Lemma lzt_L_off_window : forall segs L S Zr c vlo vhi,
  lzok segs L S Zr c ->
  Forall (range_off vlo vhi) (vm_maps (m_vmmaps (cfg_model c))) ->
  forall x : word, vlo <= bv_unsigned x < vhi -> in_rangesb x L = false.
Proof.
  intros segs L S Zr c vlo vhi Hok HM x Hx.
  destruct (in_rangesb x L) eqn:E; [exfalso | reflexivity].
  pose proof (lzok_LM Hok x E) as HMx.
  apply in_rangesb_true in HMx. destruct HMx as (lo & sz & Hin & Hr).
  rewrite Forall_forall in HM. specialize (HM (lo, sz) Hin).
  unfold range_off in HM. cbn [fst snd] in HM. lia.
Qed.

(** ** 7. The straight-line law over a list whose hidden bytes avoid it

    LazyRestrictRun.v:79-125 ([account_step_restrict], [msteps_restrict_gen]) with
    [hid_avoids_segs] in place of [lazy_ranges_okb], the one fact of it their proofs read
    ([LazyRestrict.step_restrict], LazyRestrict.v:685-697); and LazySR.v:194-255 with the lazy
    view over a list [segs0] of its own. *)
Section Avoid.
  Variable wl : list Segment.
  Variables L S : list (word * word).
  Hypothesis HA : hid_avoids_segs wl (hiddenb L S).

  Lemma lzt_account_step_av : forall msF ms1 model,
    lazy_inv L S model ->
    RiscvSemantics.step wl (restrict L S msF) = MachineOk ms1 ->
    exists model',
      mi_account_step wl msF model = MachineOk (unrestrict_to L S msF ms1, model')
      /\ lazy_inv L S model'
      /\ same_but_materialized model model'
      /\ (forall a, hiddenb L S a = true -> ms_mem ms1 a = None).
  Proof.
    intros msF ms1 model Hinv Hstep.
    destruct (step_restrict_by wl (hiddenb L S) HA msF ms1 Hstep) as (rep & Hsa & Hval & Hvis & Hnone & _).
    destruct (materialize_restrict L S model (accessed_ranges _ rep) Hinv Hvis) as (pages & Hmat & Hinv').
    exists (with_vm_backing (m_vm_lazy model) pages model).
    unfold mi_account_step. rewrite Hsa, Hmat, Hval.
    split; [reflexivity|]. split; [exact Hinv'|]. split; [|exact Hnone].
    apply same_but_materialized_with_vm_backing.
  Qed.

  Lemma lzt_msteps_restrict_av : forall ms0 ms1,
    CatSim.msteps wl ms0 ms1 ->
    forall msF model,
      ms0 = restrict L S msF ->
      lazy_inv L S model ->
      m_halted model = None ->
      exists model',
        LazyRestrictRun.dsteps wl (mkCfg msF model) (mkCfg (unrestrict_to L S msF ms1) model')
        /\ lazy_inv L S model'
        /\ same_but_materialized model model'
        /\ restrict L S (unrestrict_to L S msF ms1) = ms1.
  Proof.
    intros ms0 ms1 Hms; induction Hms as [ms | ms ms' ms'' Hsvc Hstep Hms IH];
      intros msF model -> Hinv Hh.
    - exists model. rewrite unrestrict_restrict_self.
      split; [apply LazyRestrictRun.ds_refl|]. split; [exact Hinv|].
      split; [apply same_but_materialized_refl | reflexivity].
    - destruct (lzt_account_step_av msF ms' model Hinv Hstep) as (model1 & Hacc & Hinv1 & Hsame1 & Hnone).
      specialize (IH (unrestrict_to L S msF ms') model1).
      rewrite (restrict_unrestrict_to L S msF ms' Hnone) in IH.
      assert (Hh1 : m_halted model1 = None)
        by (rewrite (same_but_materialized_halted _ _ Hsame1); exact Hh).
      destruct (IH eq_refl Hinv1 Hh1) as (model' & Hd & Hinv' & Hsame' & Hr).
      rewrite unrestrict_to_idem in Hd, Hr.
      exists model'. split; [|split; [exact Hinv'|split; [|exact Hr]]].
      + eapply LazyRestrictRun.dsteps_account; [exact Hh | exact Hsvc | exact Hacc | exact Hd].
      + eapply same_but_materialized_trans; eassumption.
  Qed.
End Avoid.

(* LazySR.v:245-255 ([evt_sreach_lazy_at]) over the walked list [wl], the lazy view over [segs0]
   going in and coming out *)
Theorem evt_sreach_lazy_av {SC : StepCfg} : forall (segs0 wl : list Segment) L S Zr
    (P : machine_state -> Prop) msF ms mo (Q : config -> Prop),
  hid_avoids_segs wl (hiddenb L S) ->
  lzok segs0 L S Zr (mkCfg msF mo) ->
  restrict L S msF = ms ->
  Exec.evt wl P ms ->
  (forall msF' mo', lzok segs0 L S Zr (mkCfg msF' mo') ->
                    same_but_materialized mo mo' ->
                    hid_same L S msF msF' ->
                    P (restrict L S msF') ->
                    sreach wl Q (mkCfg msF' mo')) ->
  sreach wl Q (mkCfg msF mo).
Proof.
  intros segs0 wl L S Zr P msF ms mo Q HA Hok Hr Hevt Hk. subst ms.
  destruct (proj1 (evt_cj_iff wl P (restrict L S msF)) Hevt) as (ms1 & Hms & HP).
  destruct (lzt_msteps_restrict_av wl L S HA _ _ Hms msF mo eq_refl (lzok_inv Hok) (lzok_halted Hok))
    as (mo' & Hd & Hinv' & Hsame & Hr).
  eapply (sreach_dsteps wl); [exact Hd|].
  apply Hk; [| exact Hsame | apply hid_same_unrestrict | rewrite Hr; exact HP].
  eapply lzok_lifted; [exact Hok | exact Hinv' | exact Hsame | apply hid_same_unrestrict].
Qed.
