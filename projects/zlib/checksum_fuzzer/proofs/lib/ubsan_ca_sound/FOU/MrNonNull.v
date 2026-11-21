(** * FOU.MrNonNull — under memory forced-only, malloc never returns NULL where the model has room

    The bundle's malloc rules realize an alternative: [t_alt2 A Bs], the NULL continuation [A] (out of
    memory) beside the block continuation [Bs], with both made feasible by one path each ([MrFeasLift]:
    refuse every allocation; [MrFeasLift2] / [MrFeasFirst]: grant them).  Under [FOCore.alloc_forced_cfg]
    an allocation that the model can grant is never refused (the refusal is spurious), so where the
    budget leaves room EVERY filtered path through [raw_malloc] returns a block.  This file proves that
    ([raw_malloc_nonnull_gone] for the metadata-ready case of [MrFeasSome1.cmalloc_gone],
    [raw_malloc_nonnull_gall] for the general case of [FOU.MrGall.cmalloc_gall] under the [ucbg] budget),
    stated over [tpath]: every path, not one.  [twf_tpaths] then adds it to the rules' well-formedness. *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require MmapSim RefNodes AllocSim.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM09. Import SM09. Import SM09.Prelim. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM01. Import SM01. Import SM01.MSafe. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import KInv. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import KLink. Import SM01.KStep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import KEv. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM06. Import SM06. Import SM06.MI_Contracts.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM01. Import SM01.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM15. Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Mr Require Import MrBridge MrNodes MrFeasSome1 MrKGrant MrFeasLift MrFeasLift2 MrRoom
  MrAccSpec MrAcc MrAccNodes MrAccPath MrKGrant2 MrUcb MrGen MrFeasFirst.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.FO Require Import FOCore.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.FOU Require Import MrGall.
Import ListNotations.
Import ITree.Exc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* -------------------------------------------------------------------------
   Every path of an itree, and the rules' well-formedness with it
   ------------------------------------------------------------------------- *)

Definition tpaths {R} (t : itree node R) (mo : Model) (Phi : R -> Prop) : Prop :=
  forall tr r mo', tpath nstep t mo tr r mo' -> Phi r.

Lemma twf_tpaths : forall {R} (t : itree node R) mo (P : R -> Model -> Prop) (Phi : R -> Prop),
  B.twf node nstep nsafe t mo P -> tpaths t mo Phi ->
  B.twf node nstep nsafe t mo (fun r mo' => P r mo' /\ Phi r).
Proof.
  intros R t. induction t as [r | n k IH]; intros mo P Phi H Hp; cbn in *.
  - split; [exact H|]. apply (Hp [] r mo). cbn. repeat split.
  - destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. apply IH; [eapply Hk; exact Hst|].
    intros tr r mo'' Hp'. apply (Hp (evs ++ tr) r mo''). exists rsp, mo', evs, tr. auto.
Qed.

(* -------------------------------------------------------------------------
   Beside a grant, a filtered allocation step is not a refusal
   ------------------------------------------------------------------------- *)

Lemma nstep_mmap_nonrefusal : forall addr len prot flags mo rsp mo1 evs rsp2 mo2 evs2,
  nstep (NMmap addr len prot flags) mo rsp mo1 evs ->
  nstep (NMmap addr len prot flags) mo rsp2 mo2 evs2 ->
  errno_ret_in mmap_errnos (eff_ret rsp2) = false ->
  errno_ret_in mmap_errnos (eff_ret rsp) = false.
Proof.
  intros addr len prot flags mo rsp mo1 evs rsp2 mo2 evs2 H1 H2 Hnr.
  destruct (errno_ret_in mmap_errnos (eff_ret rsp)) eqn:Er; [|reflexivity]. exfalso.
  cbn [nstep node_input] in H1, H2. destruct H1 as (_ & _ & _ & Hns). destruct H2 as (_ & _ & Hs2 & _).
  apply Hns. split; [reflexivity|]. split; [rewrite refusal_b_pure_mmap; exact Er|].
  exists rsp2, mo2, evs2. split; [exact Hs2 | rewrite refusal_b_pure_mmap; exact Hnr].
Qed.

Lemma nstep_mprotect_nonrefusal : forall addr len prot mo rsp mo1 evs rsp2 mo2 evs2,
  nstep (NMprotect addr len prot) mo rsp mo1 evs ->
  nstep (NMprotect addr len prot) mo rsp2 mo2 evs2 ->
  errno_ret_in mprotect_errnos (eff_ret rsp2) = false ->
  errno_ret_in mprotect_errnos (eff_ret rsp) = false.
Proof.
  intros addr len prot mo rsp mo1 evs rsp2 mo2 evs2 H1 H2 Hnr.
  destruct (errno_ret_in mprotect_errnos (eff_ret rsp)) eqn:Er; [|reflexivity]. exfalso.
  cbn [nstep node_input] in H1, H2. destruct H1 as (_ & _ & Hns). destruct H2 as (_ & Hs2 & _).
  apply Hns. split; [reflexivity|]. split; [rewrite refusal_b_pure_mprotect; exact Er|].
  exists rsp2, mo2, evs2. split; [exact Hs2 | rewrite refusal_b_pure_mprotect; exact Hnr].
Qed.

(** A decoded mmap error carries an errno return. *)
Lemma dec_mmap_err_ret : forall atop len avoid rsp e,
  dec_mmap atop len avoid rsp = Some (MmErr e) -> eff_ret rsp = errno_ret e.
Proof.
  intros atop len avoid [r ws zs us cs ci] e H. unfold dec_mmap in H.
  destruct ws; [|discriminate]. destruct zs as [|z1 zs].
  - destruct us; [|discriminate]. destruct cs; [|discriminate].
    destruct (errno_of r) eqn:Ee; [|discriminate]. injection H as <-. cbn [eff_ret].
    exact (proj1 (errno_of_Some _ _ Ee)).
  - destruct z1 as [a n]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate].
    destruct (_ && _ && _); discriminate.
Qed.

Lemma dec_mmap_none_err_ret : forall atop len avoid rsp e,
  dec_mmap_none atop len avoid rsp = Some (MmErr e) -> eff_ret rsp = errno_ret e.
Proof.
  intros atop len avoid [r ws zs us cs ci] e H. unfold dec_mmap_none in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us as [|u1 us].
  - destruct cs; [|discriminate].
    destruct (errno_of r) eqn:Ee; [|discriminate]. injection H as <-. cbn [eff_ret].
    exact (proj1 (errno_of_Some _ _ Ee)).
  - destruct u1 as [a n]. destruct us; [|discriminate]. destruct cs; [|discriminate].
    destruct (_ && _ && _); discriminate.
Qed.

Lemma errno_ret_ENOMEM_mmap : errno_ret_in mmap_errnos (errno_ret ENOMEM) = true.
Proof. apply errno_ret_in_intro. left. reflexivity. Qed.

Section NN.
Context {rc : runConstT}.

Lemma tpath_mbind_inv : forall {A C} (m : Monad.M PState A) (f : A -> Monad.M PState C) s mo tr r mo',
  tpath nstep (Monad.mbind m f s) mo tr r mo' ->
  (tpath nstep (m s) mo tr Unr mo' /\ r = Unr)
  \/ exists tr1 a s1 mo1 tr2, tpath nstep (m s) mo tr1 (Ok (a, s1)) mo1 /\ tpath nstep (f a s1) mo1 tr2 r mo'
                              /\ tr = tr1 ++ tr2.
Proof.
  intros A C m f s mo tr r mo' H. unfold Monad.mbind in H. apply tpath_ebind in H.
  destruct H as [H | (tr1 & [a s1] & mo1 & tr2 & H1 & H2 & ->)]; [left; exact H|].
  right. exists tr1, a, s1, mo1, tr2. auto.
Qed.

Lemma tpath_mret_inv : forall {A} (a : A) (s : PState) mo tr r mo',
  tpath nstep (Monad.mret a s) mo tr r mo' -> r = Ok (a, s) /\ mo' = mo /\ tr = [].
Proof. intros A a s mo tr r mo' H. cbn in H. destruct H as (H1 & H2 & H3). subst. auto. Qed.

Lemma tpath_msys_inv : forall {A} n (dec : resp -> option A) (s : PState) mo tr r mo',
  tpath nstep (Monad.msys n dec s) mo tr r mo' ->
  exists rsp, nstep n mo rsp mo' tr /\ r = match dec rsp with Some a => Ok (a, s) | None => Unr end.
Proof.
  intros A n dec s mo tr r mo' H. unfold Monad.msys in H. apply tpath_enode in H as (rsp & Hst & ->).
  exists rsp. split; [exact Hst|]. destruct (dec rsp); reflexivity.
Qed.

(** The anonymous read-write mmap event: beside a grant every filtered answer is an address. *)
Lemma ev_mmap_rw_nonerr : forall L s0 mo len tr z s1 mo1,
  KL L (ps_brk s0) mo -> 0 < len < 2^63 ->
  (exists a : word, MmapSim.grant_ok (Z_to_bv 64 0) mo a (page_round_up_Z len) = true) ->
  tpath nstep (ev_step (ld_atop L) (EMmap 0 len PROT_RW MAPF) s0) mo tr (Ok (z, s1)) mo1 ->
  is_err z = false.
Proof.
  intros L s0 mo len tr z s1 mo1 HK Hlen [a Hg] Hp.
  unfold ev_step in Hp. change (negb (Z.land MAPF MAP_FIXED_Z =? 0)) with false in Hp.
  change (PROT_RW =? 0) with false in Hp. cbv iota in Hp.
  apply tpath_mbind_inv in Hp as [[_ Hu] | (tr1 & x & s2 & mo2 & tr2 & H1 & H2 & _)]; [discriminate|].
  apply tpath_msys_inv in H1 as (rsp & Hst & Hr).
  destruct (dec_mmap (ld_atop L) len [] rsp) as [x'|] eqn:Ed; [|discriminate]. injection Hr as <- <-.
  apply tpath_mret_inv in H2 as (Hz & _ & _). inversion Hz; subst.
  destruct (nstep_mmap_grant len mo a Hlen Hg) as [mo' Hgs].
  assert (Hne : errno_ret_in mmap_errnos (eff_ret rsp) = false).
  { apply (nstep_mmap_nonrefusal _ _ _ _ _ _ _ _ _ _ _ Hst Hgs). cbn [eff_ret].
    apply (MmapSim.grant_not_errno (Z_to_bv 64 0) mo a (page_round_up_Z len)); [|exact Hg].
    apply page_round_up_Z_nonneg; lia. }
  pose proof (kl_atop _ _ _ HK) as Hat. pose proof (alloc_top_lt64 (m_vmmaps mo)) as Hcl.
  destruct (nstep_dec_mmap (ld_atop L) len [] mo rsp _ _ ltac:(lia) ltac:(unfold mmap_len; pose proof (AllocSim.page_round_up_Z_bounds len ltac:(lia)); unfold page_size in *; lia)
              (Forall_nil _) ltac:(cbv zeta; rewrite Hat; lia) Hst) as (_ & _ & x'' & Ed' & Hx).
  rewrite Ed in Ed'. injection Ed' as <-.
  destruct x as [e|xa].
  - exfalso. destruct Hx as [-> _]. rewrite (dec_mmap_err_ret _ _ _ _ _ Ed), errno_ret_ENOMEM_mmap in Hne. discriminate.
  - destruct Hx as (Hok & _). unfold mmap_addr_ok in Hok.
    apply andb_prop in Hok as [Hok _]. apply andb_prop in Hok as [_ Htop]. apply Z.leb_le in Htop.
    pose proof (page_round_up_Z_nonneg len ltac:(lia)) as Hn0. unfold mmap_len in Htop.
    unfold is_err, TWO64. apply Z.ltb_ge. lia.
Qed.

(** The anonymous PROT_NONE mmap event (metadata areas). *)
Lemma ev_mmap_none_nonerr : forall L s0 mo len tr z s1 mo1,
  KL L (ps_brk s0) mo -> 0 < len < 2^63 ->
  (exists a : word, RefNodes.grant_ok_na (Z_to_bv 64 0) mo a (page_round_up_Z len) = true) ->
  tpath nstep (ev_step (ld_atop L) (EMmap 0 len PROT_NONE MAPF) s0) mo tr (Ok (z, s1)) mo1 ->
  is_err z = false.
Proof.
  intros L s0 mo len tr z s1 mo1 HK Hlen [a Hg] Hp.
  unfold ev_step in Hp. change (negb (Z.land MAPF MAP_FIXED_Z =? 0)) with false in Hp.
  change (PROT_NONE =? 0) with true in Hp. cbv iota in Hp.
  apply tpath_mbind_inv in Hp as [[_ Hu] | (tr1 & x & s2 & mo2 & tr2 & H1 & H2 & _)]; [discriminate|].
  apply tpath_msys_inv in H1 as (rsp & Hst & Hr).
  destruct (dec_mmap_none (ld_atop L) len [] rsp) as [x'|] eqn:Ed; [|discriminate]. injection Hr as <- <-.
  apply tpath_mret_inv in H2 as (Hz & _ & _). inversion Hz; subst.
  pose proof (nstep_mmap_none_grant len mo a Hlen Hg) as Hgs. cbv zeta in Hgs.
  assert (Hne : errno_ret_in mmap_errnos (eff_ret rsp) = false).
  { apply (nstep_mmap_nonrefusal _ _ _ _ _ _ _ _ _ _ _ Hst Hgs). cbn [eff_ret].
    apply (RefNodes.grant_na_not_errno (Z_to_bv 64 0) mo a (page_round_up_Z len)); [|exact Hg].
    apply page_round_up_Z_nonneg; lia. }
  pose proof (kl_atop _ _ _ HK) as Hat. pose proof (alloc_top_lt64 (m_vmmaps mo)) as Hcl.
  destruct (nstep_dec_mmap_none (ld_atop L) len [] mo rsp _ _ ltac:(lia)
              ltac:(unfold mmap_len; pose proof (AllocSim.page_round_up_Z_bounds len ltac:(lia)); unfold page_size in *; lia)
              (Forall_nil _) ltac:(cbv zeta; rewrite Hat; lia) Hst) as (_ & _ & x'' & Ed' & Hx).
  rewrite Ed in Ed'. injection Ed' as <-.
  destruct x as [e|xa].
  - exfalso. destruct Hx as [-> _]. rewrite (dec_mmap_none_err_ret _ _ _ _ _ Ed), errno_ret_ENOMEM_mmap in Hne. discriminate.
  - destruct Hx as (Hok & _). unfold mmap_addr_ok in Hok.
    apply andb_prop in Hok as [Hok _]. apply andb_prop in Hok as [_ Htop]. apply Z.leb_le in Htop.
    pose proof (page_round_up_Z_nonneg len ltac:(lia)) as Hn0. unfold mmap_len in Htop.
    unfold is_err, TWO64. apply Z.ltb_ge. lia.
Qed.

(** The metadata-page mprotect: page-aligned, so its only errno is the refusal ENOMEM. *)
Lemma nstep_mprotect_rgerr_refusal : forall addr mo rsp mo' evs e,
  0 < addr -> addr + PGSZ < 2^64 -> addr mod 4096 = 0 ->
  nstep (NMprotect addr PGSZ PROT_RW) mo rsp mo' evs ->
  dec_mprotect addr PGSZ rsp = Some (RgErr e) ->
  errno_ret_in mprotect_errnos (eff_ret rsp) = true.
Proof.
  intros addr mo rsp mo' evs e Ha Hhi Hal H Hd.
  apply nstep_mprotect_iff in H as [H _]. destruct rsp as [r ws zs us cs ci]. cbn [eff_ret].
  destruct (errno_ret_in mprotect_errnos r) eqn:Herr; [reflexivity|]. exfalso.
  unfold check_mprotect in H.
  change (mprotect_grows_conflict_b (Z_to_bv 64 PROT_RW)) with false in H. cbv iota in H.
  rewrite (unsigned_lit addr) in H by (unfold PGSZ in *; lia). rewrite page_size_eq, Hal in H. cbn [Z.eqb negb] in H.
  change (w_is0 (Z_to_bv 64 PGSZ)) with false in H. cbv iota in H.
  rewrite (unsigned_lit PGSZ) in H by (unfold PGSZ; lia). change (page_round_up_Z PGSZ) with PGSZ in H.
  replace (two_pow_64 <=? addr + PGSZ) with false in H by (symmetry; apply Z.leb_gt; unfold two_pow_64; lia).
  change (mprotect_modeled_b (Z_to_bv 64 PROT_RW)) with true in H. cbn [negb] in H. cbv iota zeta in H.
  (* port727 (): check_mprotect first answers unmodeled for a request meeting the vDSO pair *)
  match type of H with (if negb ?c then _ else _) = _ => destruct c; cbn [negb] in H; [|discriminate] end.
  match type of H with (if ?c then _ else _) = _ => destruct c end.
  - destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
    rewrite Herr in H.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:E end; [|discriminate].
    apply andb_prop in E as [E E2]. apply andb_prop in E as [_ E1]. apply listNN_eqb_eq in E2. subst zs.
    unfold w_is0 in E1. apply bv_eqb_eq in E1. subst r.
    unfold dec_mprotect in Hd. destruct (_ && _ && _); discriminate.
  - match type of H with (if ?c then _ else _) = _ => destruct c end; [|discriminate].
    destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (w_is0 r) eqn:E0; [|discriminate]. unfold w_is0 in E0. apply bv_eqb_eq in E0. subst r.
    unfold dec_mprotect in Hd. cbn in Hd. discriminate.
Qed.

(** The metadata-page mprotect event: beside the success every filtered answer is 0. *)
Lemma ev_mprotect_zero : forall L s0 mo a C U tr z s1 mo1,
  KL L (ps_brk s0) mo -> event_pre L (EMprotect a PGSZ PROT_RW) -> acc C U mo -> U <= vm_limit (m_vmmaps mo) ->
  tpath nstep (ev_step (ld_atop L) (EMprotect a PGSZ PROT_RW) s0) mo tr (Ok (z, s1)) mo1 ->
  z = 0.
Proof.
  intros L s0 mo a0 C U tr z s1 mo1 HK Hpre HA HU Hp.
  cbn [event_pre] in Hpre. destruct Hpre as (Hq & _ & _ & b & l & k & Hin & -> & Hk2).
  pose proof (KL_atop_lt _ _ _ HK) as HKat.
  rewrite round_up_pg_eq in Hk2. fold (mmap_len l) in Hk2.
  pose proof (kl_metas _ _ _ HK b l k Hin) as (A1 & A2 & A3 & A4 & Ak & Ak1 & A5 & A6 & Ana).
  pose proof (went_In_bounds _ _ _ b l HK (or_intror (ex_intro _ k Hin))) as (_ & B2 & _ & _ & B5 & B6).
  set (a := b + (1 + k) * PGSZ) in *. set (nb := mmap_len l) in *. set (h := m_vmmaps mo) in *.
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
  assert (Hrng : 0 < a < 2 ^ 63) by (unfold PGSZ in *; lia).
  (* port727 (): nstep_mprotect_rw_grant's vDSO premise, proved as Mr/MrFeasFirst's
     ev_grant_mprotect_path (its twin here) proves it: the page lies in a mapped entry, every mapped entry is free of
     the reserved ledger (kl_mres), and the pair is in that ledger (kl_vin). *)
  assert (Hvd : region_free (vdso_reserved (m_kernel mo) (vdso_top h)) aw nw = true).
  { apply region_free_sep. intros y Hy.
    pose proof (region_free_disj _ _ _ y (kl_mres _ _ _ HK _ A5) (kl_vin _ _ _ HK _ Hy)) as D.
    unfold elo, ehi in B5, B6, D |- *. rewrite Ua, Un. lia. }
  pose proof (nstep_mprotect_rw_grant a mo Hrng Hamod Hcn Hcm (mapped_le_of_acc C U mo HA HU) Hvd) as Hgs.
  unfold ev_step in Hp.
  apply tpath_mbind_inv in Hp as [[_ Hu] | (tr1 & x & s2 & mo2 & tr2 & H1 & H2 & _)]; [discriminate|].
  apply tpath_msys_inv in H1 as (rsp & Hst & Hr).
  destruct (dec_mprotect_rw a PGSZ rsp) as [x'|] eqn:Ed; [|discriminate]. injection Hr as <- <-.
  apply tpath_mret_inv in H2 as (Hz & _ & _). inversion Hz; subst.
  assert (Hne : errno_ret_in mprotect_errnos (eff_ret rsp) = false).
  { apply (nstep_mprotect_nonrefusal _ _ _ _ _ _ _ _ _ _ Hst Hgs). reflexivity. }
  unfold dec_mprotect_rw in Ed. revert Ed.
  destruct (dec_mprotect a PGSZ rsp) as [[e|[|]]|] eqn:Ed2; intros Ed; try discriminate.
  - exfalso.
    rewrite (nstep_mprotect_rgerr_refusal a mo rsp _ _ e ltac:(lia) ltac:(unfold PGSZ in *; lia) Hamod Hst Ed2) in Hne.
    discriminate.
  - injection Ed as <-. reflexivity.
Qed.

(* -------------------------------------------------------------------------
   The tree walks: every filtered path through the embedded malloc tree
   ------------------------------------------------------------------------- *)

Definition okres {R} (P : R -> Prop) (r : exc (R * PState)) : Prop :=
  match r with Ok (x, _) => P x | Unr => True end.

(** Metadata ready ([gone]): one anonymous read-write mmap, granted where [grantable] holds. *)
Lemma membed_gone_tpaths : forall {R} (t : stree ev Z R) (Post : mled -> R -> Prop) (P : R -> Prop)
    (G : PState -> Model -> Prop) B al L s0 mo,
  frame_ok G -> ctree_ok L t Post -> KL L (ps_brk s0) mo -> G s0 mo -> gone B al P t ->
  (al = true -> grantable B mo) -> B < 2^63 ->
  tpaths (membed (ld_atop L) t s0) mo (okres P).
Proof.
  intros R t. induction t as [r|e k IH]; intros Post P G B al L s0 mo HG Hok HK HGs Hgo Hgr HB tr r' mo' Hp.
  - cbn [membed] in Hp. apply tpath_mret_inv in Hp as (-> & _ & _). exact Hgo.
  - cbn [membed] in Hp. apply tpath_mbind_inv in Hp as [[_ ->] | (tr1 & z & s1 & mo1 & tr2 & H1 & H2 & _)]; [exact I|].
    cbn [ctree_ok] in Hok. destruct Hok as [Hpre Hk].
    destruct e as [req|addr len prot flags|addr len|addr len prot|? ? ?|?]; cbn [gone] in Hgo; try contradiction.
    + destruct Hgo as (-> & -> & -> & -> & Hlen & Hkz).
      pose proof (ev_mmap_rw_nonerr L s0 mo len tr1 z s1 mo1 HK ltac:(lia) (Hgr eq_refl len Hlen) H1) as Hz.
      pose proof (ev_step_spec L _ G s0 HG Hpre s0 mo (conj eq_refl (conj HK HGs))) as Hspec.
      unfold etwf in Hspec. pose proof (twf_tpath _ _ _ _ _ _ Hspec H1) as Hpost. cbn [fst snd] in Hpost.
      destruct Hpost as (Hans & HK1 & HG1 & _).
      rewrite <- (event_post_atop L (EMmap 0 len PROT_RW (MAP_PRIVATE + MAP_ANON)) z) in H2.
      exact (IH z Post P G B false (event_post L _ z) s1 mo1 HG (Hk z Hans) HK1 HG1 (Hkz z Hz) ltac:(discriminate) HB
               tr2 r' mo' H2).
Qed.

(** General ([gall]): every allocation granted where the [ucbg] budget leaves room. *)
Lemma membed_gall_tpaths : forall {R} (t : stree ev Z R) (Post : mled -> R -> Prop) (P : R -> Prop)
    (Q : R -> Z -> Z -> Prop) (G : PState -> Model -> Prop) lim L s0 mo kb C U,
  frame_ok G -> ctree_ok L t Post -> KL L (ps_brk s0) mo -> G s0 mo -> gall P t ->
  ucbg (budget lim) t kb C U Q -> J (limok lim) kb C U mo ->
  tpaths (membed (ld_atop L) t s0) mo (okres P).
Proof.
  intros R t. induction t as [r|e k IH]; intros Post P Q G lim L s0 mo kb C U HG Hok HK HGs Hga Hu HJ tr r' mo' Hp.
  - cbn [membed] in Hp. apply tpath_mret_inv in Hp as (-> & _ & _). exact Hga.
  - cbn [membed] in Hp. apply tpath_mbind_inv in Hp as [[_ ->] | (tr1 & z & s1 & mo1 & tr2 & H1 & H2 & _)]; [exact I|].
    cbn [ctree_ok] in Hok. destruct Hok as [Hpre Hk].
    assert (HX : ev_ok e kb /\ budget lim (C + ev_dc e) (U + ev_du e kb) /\
                 (forall z, ev_ans e kb z -> ucbg (budget lim) (k z) (ev_kb e kb) (C + ev_dc e) (U + ev_du e kb) Q)).
    { destruct e; cbn [event_pre] in Hpre; try contradiction; cbn [ucbg] in Hu; exact Hu. }
    destruct HX as (Hevok & HBud & Huz).
    pose proof HJ as (HA & HL & HKB).
    pose proof (ev_step_spec L e G s0 HG Hpre s0 mo (conj eq_refl (conj HK HGs))) as Hspec.
    unfold etwf in Hspec. pose proof (twf_tpath _ _ _ _ _ _ Hspec H1) as Hpost. cbn [fst snd] in Hpost.
    destruct Hpost as (Hans & HK1 & HG1 & _).
    pose proof (ev_step_J (limok lim) (limok_mm lim) (ld_atop L) e s0 kb C U Hevok) as HT. unfold tgenM in HT.
    pose proof (tgen_tpath _ _ _ _ _ _ _ HT HJ H1) as HJ1. cbv beta iota in HJ1. destruct HJ1 as [Hez HJ1].
    assert (Hgk : gall P (k z)).
    { destruct e as [req|addr len prot flags|addr len|addr len prot|? ? ?|?]; cbn [gall] in Hga.
      - exact (Hga z).
      - pose proof Hpre as Hpre0. cbn [event_pre] in Hpre0.
        destruct Hpre0 as [(Hq & -> & -> & Hprot & Hlen)|(cur & Hph & -> & -> & -> & ->)].
        + change (Z.land MAPF MAP_FIXED =? 0) with true in Hga. apply Hga.
          cbn [ev_ok ev_dc ev_du budget] in Hevok, HBud. destruct HBud as [HBc HBu]. unfold limok in HL. unfold LEN_MAX in Hlen.
          assert (HR : room len mo) by (eapply acc_room; [exact HA | lia | lia]).
          assert (Hr : 0 <= page_round_up_Z len <= len + 4095).
          { pose proof (AllocSim.page_round_up_Z_bounds len ltac:(lia)). unfold page_size in *. lia. }
          destruct Hprot as [-> | ->].
          * eapply ev_mmap_none_nonerr; [exact HK | | | exact H1]; [lia |].
            apply (mmap_none_grant_exists len len mo HR); lia.
          * eapply ev_mmap_rw_nonerr; [exact HK | | | exact H1]; [lia |].
            exact (room_grantable len mo ltac:(lia) ltac:(lia) HR len ltac:(lia)).
        + change (Z.land MAPFX MAP_FIXED =? 0) with false in Hga. exact (Hga z).
      - destruct Hga.
      - cbn [ev_dc ev_du budget] in HBud. destruct HBud as [HBc HBu]. unfold limok in HL.
        pose proof Hpre as Hpre0. cbn [event_pre] in Hpre0. destruct Hpre0 as (_ & -> & -> & _).
        rewrite (ev_mprotect_zero L s0 mo addr C U tr1 z s1 mo1 HK Hpre HA ltac:(lia) H1). exact Hga.
      - cbn [event_pre] in Hpre. contradiction.
      - cbn [event_pre] in Hpre. contradiction. }
    rewrite <- (event_post_atop L e z) in H2.
    exact (IH z Post P Q G lim (event_post L e z) s1 mo1 (ev_kb e kb) _ _ HG (Hk z Hans) HK1 HG1 Hgk (Huz z Hez) HJ1
             tr2 r' mo' H2).
Qed.

(* -------------------------------------------------------------------------
   raw_malloc: every filtered path returns a block
   ------------------------------------------------------------------------- *)

Lemma raw_malloc_tpaths : forall n s mo (Pm : mstate * option cptr -> Prop),
  (forall r, Pm r -> snd r <> None) ->
  tpaths (membed (s_atop (ps_m s)) (cmalloc (ps_m s) n) s) mo (okres Pm) ->
  tpaths (raw_malloc n s) mo (fun r => is_null r = false).
Proof.
  intros n s mo Pm HPm Hall tr r mo' Hp. unfold raw_malloc in Hp.
  apply tpath_mbind_inv in Hp as [[_ ->] | (tr1 & s0 & s1 & mo1 & tr2 & H1 & H2 & _)]; [reflexivity|].
  destruct (tpath_mret_inv s s mo _ _ _ H1) as (Hr & -> & ->). injection Hr as -> ->.
  cbv beta in H2.
  apply tpath_mbind_inv in H2 as [[_ ->] | (tr3 & [st' p] & s2 & mo2 & tr4 & H3 & H4 & _)]; [reflexivity|].
  pose proof (HPm _ (Hall tr3 (Ok ((st', p), s2)) mo2 H3)) as Hp3. cbn [snd] in Hp3.
  cbv beta iota in H4.
  apply tpath_mbind_inv in H4 as [[_ ->] | (tr5 & u & s3 & mo3 & tr6 & H5 & H6 & _)]; [reflexivity|].
  cbv beta in H6.
  apply tpath_mret_inv in H6 as (-> & _ & _). cbn. destruct p; [reflexivity | contradiction].
Qed.

Theorem raw_malloc_nonnull_gone : forall X (G : PState -> Model -> Prop) B n s mo,
  frame_ok G -> OWN X G s mo -> metaok_ps s -> grantable B mo ->
  0 <= n -> n + 20 <= B -> 2^24 <= B -> B < 2^62 ->
  tpaths (raw_malloc n s) mo (fun r => is_null r = false).
Proof.
  intros X G B n s mo HG [(L & Hcr & HK & _) [_ HGs]] Hmeta Hgr Hn HnB HB HB2.
  pose proof (cmalloc_contract_proof _ _ n Hcr Hn) as Hok.
  assert (Hov : size_overflows n = false) by (unfold size_overflows; apply Z.leb_gt; lia).
  apply (raw_malloc_tpaths n s mo (fun r => snd r <> None) (fun r H => H)).
  rewrite (creach_atop _ _ Hcr).
  exact (membed_gone_tpaths (cmalloc (ps_m s) n) _ (fun r => snd r <> None) G B true L s mo HG Hok HK HGs
           (cmalloc_gone B (ps_m s) n (Z.of_nat FUEL) Hmeta ltac:(lia) Hov Hn HnB HB) (fun _ => Hgr) ltac:(lia)).
Qed.

Theorem raw_malloc_nonnull_gall : forall X (G : PState -> Model -> Prop) lim n s mo kb C U
    (Q : mstate * option cptr -> Z -> Z -> Prop),
  frame_ok G -> OWN X G s mo -> 0 <= n -> size_overflows n = false ->
  ucbg (budget lim) (cmalloc (ps_m s) n) kb C U Q -> J (limok lim) kb C U mo ->
  tpaths (raw_malloc n s) mo (fun r => is_null r = false).
Proof.
  intros X G lim n s mo kb C U Q HG [(L & Hcr & HK & _) [_ HGs]] Hn Hov Hu HJ.
  pose proof (cmalloc_contract_proof _ _ n Hcr Hn) as Hok.
  apply (raw_malloc_tpaths n s mo (fun r => snd r <> None) (fun r H => H)).
  rewrite (creach_atop _ _ Hcr).
  exact (membed_gall_tpaths (cmalloc (ps_m s) n) _ (fun r => snd r <> None) Q G lim L s mo kb C U HG Hok HK HGs
           (cmalloc_gall (ps_m s) n Hov) Hu HJ).
Qed.

End NN.
