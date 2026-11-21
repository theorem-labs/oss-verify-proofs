(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require Import RunCtx.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require PropExec ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import MState Frame Cells Mem Step Tac Image ZBridge SysStep Walk Arr ITree Nodes.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import PState. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import KInv. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import KLink. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import KEv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM15. Import MM15. Import MM15.ProgDeps. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM13. Import MM13. Import MM13.MallocBlocks. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM12. Import MM12. Import MM12.Malloc_iface.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require Import PImg RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Mr Require Import MrFeasNull MrFeasNull44 MrFeasSome1 MrFeasLift MrFeasLift2 MrRoom MrRulesU7 MrTall MrShape MrAcc MrAccNodes MrAccPath
  MrDrv MrDrvAcc MrRules2U7 MrUcb MrGen MrFirst MrFeasFirst MrRules3U7.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.MrP7 Require Import U7HeapPre U7HBase U7RdRules.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section AIINST.
Context {RCa1 : RunCtx}.
Context {rc : runConstT}.

Definition LIM : Z := 2 ^ 34.
Definition UB (j : nat) : Z := Z.of_nat j * (2 ^ 27 + 2 ^ 14).
Definition lim_ok (mo : Model) : Prop := LIM <= vm_limit (m_vmmaps mo).
Lemma LIMMM : mm_inv lim_ok.
Proof.
  intros n mo rsp mo' evs Hn Hst H. unfold lim_ok in *. rewrite (lim_mm n mo rsp mo' evs); [exact H | | exact Hst].
  destruct n; try contradiction; exact I.
Qed.

Definition link (X : list bptr) (bl : list (aptr * aptr)) : Prop :=
  forall p, In p X -> exists g b, In (g, b) bl /\ fst p = aadd b UNIT.

Definition AIgen (flnone : bool) (j : nat) (X : list bptr) (s : PState) (mo : Model) : Prop :=
  exists a44 fl bl C U,
    KST (Z.of_nat FUEL + Z.of_nat j) (ps_m s) a44 fl bl /\ (flnone = true -> fl = None) /\ link X bl /\
    acc C U mo /\ C + 2 * Z.of_nat j + 2 <= 40000 /\ U + UB j + 2 ^ 27 + 2 ^ 14 <= LIM /\ lim_ok mo.
Definition AI := AIgen false.
Definition AIm := AIgen true.

Lemma AIm_perm : forall j X X' s mo, Permutation X X' -> AIm j X s mo -> AIm j X' s mo.
Proof.
  intros j X X' s mo HP (a44 & fl & bl & C & U & K & HF & LK & REST). exists a44, fl, bl, C, U.
  split; [exact K|]. split; [exact HF|]. split; [|exact REST].
  intros p Hp. apply LK. eapply Permutation_in; [apply Permutation_sym; exact HP | exact Hp].
Qed.

Lemma AI_vm : forall j X s mo mo', AI j X s mo -> m_vmmaps mo' = m_vmmaps mo -> m_vm_materialized mo' = m_vm_materialized mo -> AI j X s mo'.
Proof.
  intros j X s mo mo' (a44 & fl & bl & C & U & K & HF & LK & ACC & HC & HU & HL) EV EM. exists a44, fl, bl, C, U.
  repeat (split; [assumption|]). split; [eapply acc_same_vm; eassumption|]. repeat (split; [assumption|]).
  unfold lim_ok in *. rewrite EV. exact HL.
Qed.

Lemma AI_end : forall j pb s mo, AI j [pb] s mo -> drv_state s /\ room (2 ^ 27) mo.
Proof.
  intros j pb s mo (a44 & fl & bl & C & U & K & HF & LK & ACC & HC & HU & HL). split.
  - split; [eapply KST_drv; exact K|]. unfold metaok_ps. eapply metaok_le; [|eapply KST_metaok; exact K]. lia.
  - eapply acc_room; [exact ACC | lia|]. unfold lim_ok, LIM, UB in *. lia.
Qed.

Theorem rule_malloc_grow_proof : rule_malloc_grow AI AIm.
Proof.
  intros j R M mo s LB X G n lo B errv A Bs (HH & HOWN & HG & HAUX & HspB & HSTK & Hlo1 & Hlo2 & HERR & HMI & Htp) Ha0 Hn
         (a44 & fl & bl & C & U & K & _ & LK & ACC & HC & HU & HL) HA0 HB0 HK.
  assert (Hn32 : 0 <= n < 2 ^ 32) by lia.
  assert (Hbig : MMAP_THRESHOLD <= n) by (unfold MMAP_THRESHOLD; lia).
  assert (Hd : 1 <= Z.of_nat FUEL + Z.of_nat (S j)) by lia.
  eapply (malloc_rz_2xa R M mo s LB X G n lo B errv HH HOWN HG HAUX HspB HSTK Hlo1 Hlo2 HERR HMI Htp Ha0 Hn32
            (fun r s' => match r with
                         | Some q => exists g b, fst q = aadd b UNIT /\ KST (Z.of_nat FUEL + Z.of_nat (S j) - 1) (ps_m s') a44 None ((g, b) :: bl)
                         | None => True end)
            _ C U (fun c u => c <= C + 2 /\ u <= U + (n + IB + UNIT + 4096)) _ ACC lim_ok LIMMM HL A Bs); try assumption.
  -
    eapply raw_malloc_null_feasible_gen; eauto; [lia|]. apply cmalloc_rnull_big. exact Hbig.
  -
    eapply (raw_malloc_some_feasible X G (2 ^ 27 + 20)); eauto; try lia.
    + unfold metaok_ps. eapply metaok_le; [|eapply KST_metaok; exact K]. lia.
    + apply room_grantable; [lia | lia|]. eapply acc_room; [exact ACC | lia|]. unfold lim_ok, LIM, UB in *. lia.
  -
    intros R' M' mo' s' r C' U' MR OR HF [HC' HU'] HACC' HL'. eapply HK; [exact MR | exact OR|].
    destruct r as [q|]; [|exact I]. destruct HF as (g & b & Hq & K').
    exists a44, None, ((g, b) :: bl), C', U'.
    split; [replace (Z.of_nat FUEL + Z.of_nat j) with (Z.of_nat FUEL + Z.of_nat (S j) - 1) by lia; exact K'|].
    split; [reflexivity|]. split.
    { intros p [<-|Hp]; [exists g, b; split; [left; reflexivity | exact Hq]|].
      destruct (LK p Hp) as (g' & b' & Hin & E). exists g', b'. split; [right; exact Hin | exact E]. }
    split; [exact HACC'|]. unfold UB, IB, UNIT in *. rewrite Nat2Z.inj_succ in *. repeat split; try lia. exact HL'.
  Unshelve.
  +
    eapply tall_mono; [| apply (tall_raw_malloc n s (fun st' c => match c with
                                  | Some c0 => exists g b, c0 = aadd b UNIT /\ KST (Z.of_nat FUEL + Z.of_nat (S j) - 1) st' a44 None ((g, b) :: bl)
                                  | None => True end))].
    * intros [|[[q|] s']]; cbn; auto.
    * eapply uall_mono; [| apply (cmalloc_big_KST _ _ _ _ _ n K Hd Hbig); lia]. intros [st' [c|]]; cbn; auto.
  +
    apply tacc_raw_malloc. eapply (cmalloc_big_cost _ _ _ _ _ n C U K Hd Hbig). unfold IB, UNIT. lia.
Qed.

Theorem rule_free_grow_proof : rule_free_grow AI AIm.
Proof.
  intros j R M mo s LB X G p A n lo B errv T (HH & HOWN & HG & HAUX & HspB & HSTK & Hlo1 & Hlo2 & HERR & HMI & Htp) Hin Ha0
         (a44 & fl & bl & C & U & K & HFL & LK & ACC & HC & HU & HL) HK.
  specialize (HFL eq_refl). subst fl.
  destruct (LK p ltac:(left; reflexivity)) as (g & b & Hgb & Hp).
  eapply (free_rz_anyxa R M mo s LB X G p A n lo B errv T
            (fun s' => exists a44', KST (Z.of_nat FUEL + Z.of_nat j) (ps_m s') a44' (Some g) (bl_remove g bl))
            C U (fun c u => c <= C /\ u <= U) lim_ok LIMMM HL HH Hin HOWN HG HAUX HspB HSTK Hlo1 Hlo2 HERR HMI Htp Ha0).
  - eapply tall_mono; [| apply (tall_raw_free p s (fun st' => exists a44', KST (Z.of_nat FUEL + Z.of_nat j) st' a44' (Some g) (bl_remove g bl)))].
    + intros [|[[] s']]; cbn; auto.
    + rewrite Hp. eapply uall_mono; [| apply (cfree_KST _ _ _ _ g b K Hgb)]. intros st' (a' & K' & _). exists a'. exact K'.
  - apply tacc_raw_free. rewrite Hp. apply (cfree_cost _ _ _ _ g b C U K Hgb).
  - exact ACC.
  - intros R' M' mo' s' C' U' KEPT MI' ST' ERR' AUX' HP _ _ HH' HOWN' (a' & K') [HC' HU'] HACC' HL'.
    eapply HK; try eassumption.
    exists a', (Some g), (bl_remove g bl), C', U'. split; [exact K'|]. split; [discriminate|]. split.
    { intros p' Hp'. destruct (LK p' ltac:(right; exact Hp')) as (g' & b' & Hin' & E'). exists g', b'. split; [|exact E'].
      apply bl_remove_In. split; [exact Hin'|]. cbn [fst]. intros ->.
      assert (b' = b).
      { pose proof (ks_ndm _ _ _ _ _ K) as ND. cbn [fl_list] in ND. rewrite app_nil_r in ND.
        pose proof (NoDup_map_In_inj fst bl (g, b') (g, b) ND Hin' Hgb eq_refl) as E. injection E as ->. reflexivity. }
      subst b'. destruct HOWN as [_ [ND _]]. cbn [map] in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI _].
      apply NI. rewrite Hp, <- E'. apply in_map. exact Hp'. }
    split; [exact HACC'|]. repeat split; try lia. exact HL'.
Qed.

(* an entry of a list is no larger than the list's live_bytes. *)
Lemma live_bytes_nonneg_ai : forall l : list (word * word), 0 <= live_bytes l.
Proof. induction l as [|[a n] l IH]; cbn [live_bytes]; [lia|]. pose proof (bv_unsigned_in_range 64 n). lia. Qed.
Lemma live_bytes_each_ai : forall (l : list (word * word)) (K : Z),
  live_bytes l <= K -> Forall (fun p => bv_unsigned (snd p) <= K) l.
Proof.
  induction l as [|[a n] l IH]; intros K H; [constructor|]. cbn [live_bytes] in H.
  pose proof (live_bytes_nonneg_ai l). pose proof (bv_unsigned_in_range 64 n).
  constructor; [cbn [snd]; lia | apply IH; lia].
Qed.

Theorem rule_malloc_first_proof : rule_malloc_first AI 10.
Proof.
  intros R M mo G lo B errv brk0 lim A Bs s (HH & HOWN & HG & HAUX & HspB & HSTK & Hlo1 & Hlo2 & HERR & HMI & Htp) Ha0 Evm0 Ek Hlim
         HA0 HB0 HK.
  (* the launch triple is the RunCtx's *)
  set (inp := rc_inp) in *. set (sp := rc_sp) in *. set (mbase := rc_mb) in *.
  (* the launch's VmMaps written out: init_model's reserved list is the image's
     segments ++ the vDSO pair (State.init_reserved). The lines below read Evm as before. *)
  assert (Evm : m_vmmaps mo = mkVmMapsFull (init_reserved (segments_reserved psegs) mbase sp (in_kernel inp)) [] [] brk0 brk0 lim mbase sp)
    by (rewrite Evm0; reflexivity).
  pose proof HOWN as [(L & Hcr & HKL & _) _].
  pose proof (kl_minv _ _ _ HKL) as (_ & _ & _ & _ & _ & _ & _ & _ & Hmat & Hsp).
  pose proof (kl_start _ _ _ HKL) as (S1 & S2 & S3 & S4).
  pose proof (KL_atop_lt _ _ _ HKL) as Hat.
  assert (HACC : acc 6 0 mo).   (* four image segments + at most two vDSO entries *)
  { apply acc_of_empty.
    - unfold AsanCeil.init_sp_ok. lia.
    - rewrite Evm. reflexivity.
    - exact Hmat.
    - rewrite Evm. cbn [vm_reserved]. unfold init_reserved. apply Forall_app. split.
      + rewrite segments_reserved_plain. repeat constructor; cbn [snd]; rewrite unsigned_lit by lia; lia.
      + eapply Forall_impl; [|exact (live_bytes_each_ai _ _ (proj2 (vdso_reserved_size _ _)))].
        intros p Hp. cbn beta in Hp |- *. lia.
    - rewrite Evm. cbn [vm_reserved]. unfold init_reserved. rewrite length_app, segments_reserved_plain.
      match goal with |- context [length (vdso_reserved ?k ?t)] => pose proof (proj1 (vdso_reserved_size k t)) as VN end.
      cbn [length]. lia. }
  set (b := bv_unsigned brk0).
  assert (HJ : J (limok LIM) (Some b) 6 0 mo).
  { split; [exact HACC|]. split.
    - unfold limok, LIM. rewrite Evm. cbn [vm_limit]. exact Hlim.
    - cbn [KB]. rewrite Evm in S1, S4 |- *. cbn [vm_brk vm_start_brk] in *. split; [reflexivity|]. unfold PGSZ in *. subst b. lia. }
  assert (HUG : ucbg (budget LIM) (cmalloc (ps_m s) 65536) (Some b) 6 0 (first_post 6 0)).
  { apply (cmalloc_first_KST_g (budget LIM) (budget_down LIM)); try reflexivity.
    - intros sc. reflexivity.
    - unfold budget, LIM. lia. }
  assert (Hn32 : 0 <= 65536 < 2 ^ 32) by lia.
  eapply (malloc_rz_2xg R M mo s [] [] G 65536 lo B errv HH HOWN HG HAUX HspB HSTK Hlo1 Hlo2 HERR HMI Htp Ha0 Hn32
            _ (J (limok LIM) (Some b) 6 0)
            (tgenM_raw_malloc (limok LIM) (limok_mm LIM) 65536 s (Some b) 6 0 _ (ucbg_ucb _ _ _ _ _ _ HUG)) HJ A Bs); try assumption.
  -
    eapply raw_malloc_null_feasible; eauto; [intros sc; reflexivity | lia].
  -
    eapply (raw_malloc_gsome_feasible [] G LIM 65536 s mo (Some b) 6 0 _ HG HOWN); [lia | reflexivity | exact HUG | exact HJ].
  -
    intros R' M' mo' s' r MR OR (p & C' & U' & [HP [HC' HU']] & Er & HACC' & HL'). eapply HK; [exact MR | exact OR|].
    destruct r as [q|]; [|exact I].
    destruct p as [slot|]; [|discriminate]. injection Er as ->. cbn [snd fst] in HP. destruct HP as (g & b1 & Hslot & K').
    exists (Some g), None, [(g, b1)], C', U'.
    split; [exact K'|]. split; [intros _; reflexivity|]. split.
    { intros p' [<-|[]]. exists g, b1. split; [left; reflexivity | exact Hslot]. }
    split; [exact HACC'|]. unfold UB, LIM in *. change (Z.of_nat 10) with 10. repeat split; try lia. exact HL'.
Qed.

End AIINST.
