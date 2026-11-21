(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.Prelim. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require SM01. Import SM01. Import SM01.MSafe. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require Import KInv. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require Import KLink. Import SM01.KStep. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require Import KEv. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require SM06. Import SM06. Import SM06.MI_Contracts.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require SM01. Import SM01.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Malloc Require MM15. Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Mr Require Import MrBridge MrFeasNull MrFeasSome1 MrFeasNull44 MrKRefuse.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section Lift.
Context {rc : runConstT}.

Definition refusable (e : ev) : Prop :=
  match e with
  | EBrk _ | EMprotect _ _ _ => True
  | EMmap _ _ _ flags => (Z.land flags MAP_FIXED =? 0) = true
  | _ => False
  end.

Definition refuses (e : ev) (z : Z) : Prop :=
  match e with
  | EBrk req => req = 0 \/ z <> req
  | EMmap _ _ _ _ => is_err z = true
  | EMprotect _ _ _ => ((z =? 0) || (z =? TWO64 - ENOSYS)) = false
  | _ => False
  end.

Lemma tpath_msys_ok : forall {A} n (dec : resp -> option A) (s : PState) mo rsp mo' a,
  nstep n mo rsp mo' [] -> dec rsp = Some a ->
  tpath nstep (Monad.msys n dec s) mo [] (Ok (a, s)) mo'.
Proof.
  intros A n dec s mo rsp mo' a Hst Hd. unfold Monad.msys. apply tpath_enode. exists rsp. split; [exact Hst|]. rewrite Hd. reflexivity.
Qed.

Lemma tpath_mbind_ok : forall {A C} (m : Monad.M PState A) (f : A -> Monad.M PState C) s mo a s1 mo1 r mo',
  tpath nstep (m s) mo [] (Ok (a, s1)) mo1 -> tpath nstep (f a s1) mo1 [] r mo' ->
  tpath nstep (Monad.mbind m f s) mo [] r mo'.
Proof.
  intros A C m f s mo a s1 mo1 r mo' H1 H2. unfold Monad.mbind. apply tpath_ebind. right.
  exists [], (a, s1), mo1, []. split; [exact H1|]. split; [exact H2 | reflexivity].
Qed.

Lemma tpath_ret_ok : forall {A} (a : A) (s : PState) mo, tpath nstep (Monad.mret a s) mo [] (Ok (a, s)) mo.
Proof. intros. cbn. repeat split. Qed.

Lemma ev_refuse_path : forall L e (G : PState -> Model -> Prop) s0 mo,
  event_pre L e -> KL L (ps_brk s0) mo -> refusable e ->
  exists z s' mo', tpath nstep (ev_step (ld_atop L) e s0) mo [] (Ok (z, s')) mo' /\ refuses e z.
Proof.
  intros L e G s0 mo Hpre HK Href.
  destruct e as [req|addr len prot flags|addr len|addr len prot|? ? ?|?]; cbn [refusable] in Href; try contradiction.
  -
    cbn [event_pre] in Hpre. pose proof (kl_phase _ _ _ HK) as Kph.
    set (b := vm_brk (m_vmmaps mo)).
    destruct Hpre as [[-> Hph]|[(cur & Hph & ->)|(b0 & l0 & Hph & Hreg & ->)]].
    + exists (bv_unsigned b), (set_brk_ps (bv_unsigned b) s0), (with_brk_next mo (Z_to_bv 64 0) b). split; [|left; reflexivity].
      unfold ev_step. cbn [Z.eqb].
      eapply tpath_mbind_ok; [apply (tpath_msys_ok (NBrk 0) dec_brk0 s0 mo (eff0 b) _ (bv_unsigned b) (nstep_brk_same 0 mo)); reflexivity|].
      eapply tpath_mbind_ok; [cbn; repeat split|]. apply tpath_ret_ok.
    + rewrite Hph in Kph. destruct Kph as (Ecur & Ebrk & Epb & _).
      pose proof (round_up_pg_ge cur) as Hge.
      assert (NE : round_up_pg cur + 2 * PGSZ <> 0).
      { pose proof (kl_start _ _ _ HK) as (S1 & _). unfold PGSZ in *. lia. }
      exists (ps_brk s0), s0, (with_brk_next mo (Z_to_bv 64 (round_up_pg cur + 2 * PGSZ)) b). split.
      * unfold ev_step. rewrite (proj2 (Z.eqb_neq _ _) NE).
        eapply tpath_mbind_ok; [cbn; repeat split|].
        eapply tpath_mbind_ok.
        { apply (tpath_msys_ok (NBrk _) (dec_brk (ps_brk s0) _) s0 mo (eff0 b) _ BrkSame (nstep_brk_same _ mo)).
          unfold dec_brk, eff0. fold b in Ebrk. rewrite Ebrk, Epb, Z.eqb_refl. reflexivity. }
        apply tpath_ret_ok.
      * right. rewrite Epb. unfold PGSZ in *. lia.
    + rewrite Hph in Kph. destruct Kph as (b1 & l1 & Hreg1 & Ebrk & Epb). rewrite Hreg in Hreg1. injection Hreg1 as <- <-.
      pose proof (kl_brkreg _ _ _ HK b0 l0 Hreg) as (R1 & R2 & R3 & _).
      assert (NE : b0 + l0 + PGSZ <> 0) by (unfold PGSZ in *; lia).
      exists (ps_brk s0), s0, (with_brk_next mo (Z_to_bv 64 (b0 + l0 + PGSZ)) b). split.
      * unfold ev_step. rewrite (proj2 (Z.eqb_neq _ _) NE).
        eapply tpath_mbind_ok; [cbn; repeat split|].
        eapply tpath_mbind_ok.
        { apply (tpath_msys_ok (NBrk _) (dec_brk (ps_brk s0) _) s0 mo (eff0 b) _ BrkSame (nstep_brk_same _ mo)).
          unfold dec_brk, eff0. fold b in Ebrk. rewrite Ebrk, Epb, Z.eqb_refl. reflexivity. }
        apply tpath_ret_ok.
      * right. rewrite Epb. unfold PGSZ in *. lia.
  -
    cbn [event_pre] in Hpre. destruct Hpre as [(Hq & -> & -> & Hprot & Hlen)|(cur & _ & _ & _ & _ & ->)].
    2:{ exfalso. revert Href. vm_compute. discriminate. }
    exists (neg_errno ENOMEM), s0, mo. split; [|apply is_err_neg; unfold ENOMEM; lia].
    unfold ev_step. change (negb (Z.land MAPF MAP_FIXED_Z =? 0)) with false. cbv iota.
    assert (Hst : nstep (NMmap 0 len prot MAPF) mo (efferr ENOMEM) mo []).
    { apply nstep_mmap_refuse; [unfold LEN_MAX in Hlen; lia | exact Hprot]. }
    destruct (prot =? 0).
    + eapply tpath_mbind_ok; [apply (tpath_msys_ok _ _ s0 mo (efferr ENOMEM) mo (MmErr ENOMEM) Hst); reflexivity|]. apply tpath_ret_ok.
    + eapply tpath_mbind_ok; [apply (tpath_msys_ok _ _ s0 mo (efferr ENOMEM) mo (MmErr ENOMEM) Hst); reflexivity|]. apply tpath_ret_ok.
  -
    cbn [event_pre] in Hpre. destruct Hpre as (Hq & -> & -> & b & l & k & Hin & -> & Hk2).
    pose proof (KL_atop_lt _ _ _ HK) as HKat.
    rewrite round_up_pg_eq in Hk2. fold (mmap_len l) in Hk2.
    pose proof (kl_metas _ _ _ HK b l k Hin) as (A1 & A2 & A3 & A4 & Ak & Ak1 & A5 & A6 & Ana).
    pose proof (went_In_bounds _ _ _ b l HK (or_intror (ex_intro _ k Hin))) as (_ & B2 & _ & _ & B5 & B6).
    set (a := b + (1 + k) * PGSZ). set (nb := mmap_len l) in *. set (h := m_vmmaps mo) in *.
    set (aw := Z_to_bv 64 a). set (nw := Z_to_bv 64 PGSZ).
    assert (Hab : b + PGSZ <= a /\ a + PGSZ <= b + nb) by (subst a; unfold PGSZ in *; nia).
    assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; unfold PGSZ in *; lia).
    assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply unsigned_lit; unfold PGSZ; lia).
    assert (Hamod : a mod 4096 = 0). { subst a. unfold PGSZ in *. rewrite Z.add_mod, A3, Z.mod_mul by lia. reflexivity. }
    assert (Hcn : map_contains (vm_noaccess h) aw nw = true).
    { destruct (Ana (1 + k) ltac:(lia) ltac:(lia)) as (e & He & Hel & Heh). unfold map_contains. apply existsb_exists. exists e. split; [exact He|].
      rewrite Ua, Un. unfold elo, ehi in Hel, Heh. subst a. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
    assert (Hcm : map_contains (vm_maps h) aw nw = true).
    { unfold map_contains. apply existsb_exists. exists (went b nb). split; [exact A5|]. rewrite Ua, Un. unfold elo, ehi in B5, B6. rewrite B5.
      replace (bv_unsigned (fst (went b nb)) + bv_unsigned (snd (went b nb))) with (b + nb) by (symmetry; exact B6).
      rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
    (* the range misses the vDSO pair: it lies in a mapped entry, every mapped entry is
       free of the reserved ledger (kl_mres), and the pair is in that ledger (kl_vin). *)
    assert (Hvd : region_free (vdso_reserved (m_kernel mo) (vdso_top h)) aw nw = true).
    { apply region_free_sep. intros y Hy.
      pose proof (region_free_disj _ _ _ y (kl_mres _ _ _ HK _ A5) (kl_vin _ _ _ HK _ Hy)) as D.
      unfold elo, ehi in B5, B6, D |- *. rewrite Ua, Un. lia. }
    exists (neg_errno ENOMEM), s0, mo. split; [|reflexivity].
    unfold ev_step.
    assert (Hst : nstep (NMprotect a PGSZ PROT_RW) mo (efferr ENOMEM) mo []).
    { apply nstep_mprotect_refuse;
        [unfold PGSZ in *; lia | unfold PGSZ in *; lia | exact Hamod | exact Hcn | exact Hcm | exact Hvd]. }
    eapply tpath_mbind_ok; [apply (tpath_msys_ok _ _ s0 mo (efferr ENOMEM) mo (RgErr ENOMEM) Hst); reflexivity|]. apply tpath_ret_ok.
Qed.

Lemma membed_refuse_path : forall {R} (t : stree ev Z R) (Post : mled -> R -> Prop) (P : R -> Prop)
    (G : PState -> Model -> Prop) L s0 mo,
  frame_ok G -> ctree_ok L t Post -> KL L (ps_brk s0) mo -> G s0 mo -> rnull P t ->
  exists r s' mo', tpath nstep (membed (ld_atop L) t s0) mo [] (Ok (r, s')) mo' /\ P r.
Proof.
  intros R t. induction t as [r|e k IH]; intros Post P G L s0 mo HG Hok HK HGs Hrn.
  - exists r, s0, mo. split; [apply tpath_ret_ok | exact Hrn].
  - cbn [ctree_ok] in Hok. destruct Hok as [Hpre Hk].
    assert (Href : refusable e /\ forall z, refuses e z -> rnull P (k z)).
    { destruct e as [req|addr len prot flags|addr len|addr len prot|? ? ?|?]; cbn [rnull refusable refuses] in *;
        try contradiction.
      - split; [exact I | exact Hrn].
      - destruct Hrn as [Hf Hz]. split; [exact Hf | exact Hz].
      - split; [exact I | exact Hrn]. }
    destruct Href as [Href Hkz].
    destruct (ev_refuse_path L e G s0 mo Hpre HK Href) as (z & s1 & mo1 & Hp & Hz).
    pose proof (ev_step_spec L e G s0 HG Hpre s0 mo (conj eq_refl (conj HK HGs))) as Hspec.
    unfold etwf in Hspec. pose proof (twf_tpath _ _ _ _ _ _ Hspec Hp) as Hpost. cbn [fst snd] in Hpost.
    destruct Hpost as (Hans & HK1 & HG1 & _).
    destruct (IH z Post P G (event_post L e z) s1 mo1 HG (Hk z Hans) HK1 HG1 (Hkz z Hz)) as (r & s' & mo' & Hp' & HP).
    rewrite event_post_atop in Hp'.
    exists r, s', mo'. split; [|exact HP].
    cbn [membed]. eapply tpath_mbind_ok; [exact Hp | exact Hp'].
Qed.

Lemma tfeas_of_tpath : forall {R} (t : itree node R) mo tr r mo' (S : R -> Prop),
  tpath nstep t mo tr r mo' -> S r -> B.tfeas node nstep t mo S.
Proof.
  intros R t. induction t as [r0|n k IH]; intros mo tr r mo' S Hp HS; cbn in *.
  - destruct Hp as (-> & _ & _). exact HS.
  - destruct Hp as (rsp & mo1 & evs & tr' & Hst & Hp & _). exists rsp, mo1, evs. split; [exact Hst|]. eapply IH; eauto.
Qed.

Definition is_null (r : exc (option bptr * PState)) : bool :=
  match r with Ok (None, _) => true | _ => false end.

Theorem raw_malloc_null_feasible_gen : forall X (G : PState -> Model -> Prop) n s mo,
  frame_ok G -> OWN X G s mo -> 0 <= n ->
  rnull (fun r => snd r = None) (cmalloc (ps_m s) n) ->
  B.tfeas node nstep (raw_malloc n s) mo (fun r => is_null r = true).
Proof.
  intros X G n s mo HG [(L & Hcr & HK & _) [_ HGs]] Hn Hrn.
  pose proof (cmalloc_contract_proof _ _ n Hcr Hn) as Hok.
  destruct (membed_refuse_path (cmalloc (ps_m s) n) _ (fun r => snd r = None) G L s mo HG Hok HK HGs Hrn)
    as ([st' p] & s' & mo' & Hp & HP).
  cbn in HP. subst p. rewrite <- (creach_atop _ _ Hcr) in Hp.
  eapply (tfeas_of_tpath _ mo [] (Ok (None, set_m st' s')) mo'); [|reflexivity].
  unfold raw_malloc.
  eapply tpath_mbind_ok; [cbn; repeat split|].
  eapply tpath_mbind_ok; [exact Hp|]. cbv beta iota.
  eapply tpath_mbind_ok; [cbn; repeat split|]. apply tpath_ret_ok.
Qed.

Theorem raw_malloc_null_feasible : forall X (G : PState -> Model -> Prop) n s mo,
  frame_ok G -> OWN X G s mo -> allnone (ps_m s) -> 0 <= n ->
  B.tfeas node nstep (raw_malloc n s) mo (fun r => is_null r = true).
Proof. intros X G n s mo HG HO Hall Hn. eapply raw_malloc_null_feasible_gen; eauto. apply cmalloc_rnull. exact Hall. Qed.

Theorem raw_malloc_null_feasible44 : forall X (G : PState -> Model -> Prop) n s mo,
  frame_ok G -> OWN X G s mo -> none44 (ps_m s) -> full44 (ps_m s) -> 0 <= n ->
  B.tfeas node nstep (raw_malloc n s) mo (fun r => is_null r = true).
Proof. intros X G n s mo HG HO H1 H2 Hn. eapply raw_malloc_null_feasible_gen; eauto. apply cmalloc_rnull44; assumption. Qed.

End Lift.
