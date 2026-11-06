(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes Decode RelSpec RelSpecMm.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KStep__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Logic. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require FreeRange NoRefuse. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require ProgFullQ. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KStep__Spec.KStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Progress OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Logic OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KStep__Spec.LB_Kernel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KStep__Spec.LB_Embed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.FreeRange OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.NoRefuse OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.ProgFullQ.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require Import SimW.
(* [comment removed for export] *) Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.zify_cheap_cleanup ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.zify_split_ranges; OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.zify_spec_trivial.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CE : CEIL}.
Fixpoint small_reqs {R} (RQ : Z) (t : Malloc.M R) {struct t} : Prop :=
  match t with
  | SRet _ => True
  | SVis (EUndef _) _ => True
  | SVis (EMmap _ len _ flags) k => (Z.land flags MAP_FIXED =? 0 = true -> mmap_len len <= RQ) /\ forall z, small_reqs RQ (k z)
  | SVis _ k => forall z, small_reqs RQ (k z)
  end.

(* [comment removed for export] *)
#[using="Type"] Lemma fit_arith : forall nZ B, 0 < nZ <= RMAX -> 0 <= B <= BLIVE ->
  nZ + B + (B / page_size) * (page_size + nZ) <= band_ceiling - bottomup_floor.     (* [comment removed for export] *)
Proof.
  intros nZ B HnZ HB. rewrite band_width. rewrite page_size_eq.
  assert (HQ : B / 4096 <= 2^18). { unfold BLIVE in HB. apply Z.div_le_upper_bound; lia. }
  assert (HQ0 : 0 <= B / 4096) by (apply Z.div_pos; lia).
  unfold RMAX, BLIVE in *. nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma nstep_mmap_rw_grant : forall len mo rsp mo' evs,
  0 < len -> mmap_len len < 2^64 ->
  band_ceiling <= alloc_top (m_vmmaps mo) ->
  (forall fl, mmap_grant_refusable fl mo (mmap_len len) = false) ->
  nstep (NMmap 0 len PROT_RW MAPF) mo rsp mo' evs ->
  exists a, rsp = mkEffect a [] [(a, Z_to_bv 64 (mmap_len len))] /\ 0 < bv_unsigned a /\ bv_unsigned a + mmap_len len <= alloc_top (m_vmmaps mo).
Proof.
  intros len mo rsp mo' evs Hlen Hlen2 Hband Hnr H. pose proof (mmap_len_bound len Hlen) as Hb.
  apply nstep_mmap_rw_outcome in H; [|reflexivity|reflexivity|rewrite w_is0_lit by lia; apply Z.eqb_neq; lia|reflexivity|exact Hband].
  cbv zeta in H. rewrite unsigned_lit in H by lia. fold (mmap_len len) in H.
  destruct H as [(e & HIn & Heq) | (a & (A1 & A2 & A3 & A4 & A5) & Heq)]; apply Ok_inj in Heq as (-> & -> & _).
  - rewrite Hnr in HIn. destruct HIn.
  - exists a. split; [reflexivity|]. split; [exact A2| exact A3].
Qed.

#[using="Type"] Lemma nstep_mmap_none_grant : forall len mo rsp mo' evs,
  0 < len -> mmap_len len < 2^64 ->
  band_ceiling <= alloc_top (m_vmmaps mo) ->
  mmap_reserve_refusable mo (mmap_len len) = false ->
  nstep (NMmap 0 len PROT_NONE MAPF) mo rsp mo' evs ->
  exists a, rsp = mkEffectU a [] [] [(a, Z_to_bv 64 (mmap_len len))] [] [] /\ 0 < bv_unsigned a /\ bv_unsigned a + mmap_len len <= alloc_top (m_vmmaps mo).
Proof.
  intros len mo rsp mo' evs Hlen Hlen2 Hband Hnr H. pose proof (mmap_len_bound len Hlen) as Hb.
  apply nstep_mmap_noaccess_outcome in H; [|reflexivity|reflexivity|rewrite w_is0_lit by lia; apply Z.eqb_neq; lia|reflexivity|reflexivity|exact Hband].
  cbv zeta in H. rewrite unsigned_lit in H by lia. fold (mmap_len len) in H.
  destruct H as [(e & HIn & Heq) | (a & (A1 & A2 & A3 & A4) & Heq)]; apply Ok_inj in Heq as (-> & -> & _).
  - rewrite Hnr in HIn. destruct HIn.
  - exists a. split; [reflexivity|]. split; [exact A2| exact A3].
Qed.

#[using="Type"] Lemma nstep_mprotect_grant : forall addr len mo rsp mo' evs,
  let h := m_vmmaps mo in
  let a := Z_to_bv 64 addr in let n := Z_to_bv 64 (mmap_len len) in
  0 <= addr < 2^64 -> 0 < len < 2^64 -> addr mod page_size = 0 ->
  addr + mmap_len len < 2^64 ->
  map_contains (vm_noaccess h) a n = true -> map_contains (vm_maps h) a n = true ->
  mprotect_refusable mo a n = false ->
  nstep (NMprotect addr len PROT_RW) mo rsp mo' evs ->
  rsp = mkEffect (Z_to_bv 64 0) [] [(a, n)].
Proof.
  intros addr len mo rsp mo' evs h a n Ha Hlen Hal Hnw Hna Hmc Hnr H.
  pose proof (mmap_len_bound len (proj1 Hlen)) as Hb.
  apply nstep_mprotect_expose_outcome in H;
    [| reflexivity
     | rewrite unsigned_lit by lia; exact Hal
     | rewrite w_is0_lit by lia; apply Z.eqb_neq; lia
     | rewrite !unsigned_lit by lia; unfold two_pow_64, mmap_len in *; lia
     | reflexivity
     | rewrite unsigned_lit by lia; exact Hna
     | rewrite unsigned_lit by lia; exact Hmc ].
  fold a in H. rewrite (unsigned_lit len) in H by lia. fold (mmap_len len) n h in H.
  destruct H as [(e & HIn & Heq) | (Hbud & Heq)]; apply Ok_inj in Heq as (-> & -> & _).
  - rewrite Hnr in HIn. destruct HIn.
  - reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma tpath_vis_flat {A} n (k : resp -> itree node (exc A)) mo tr r mo' :
  tpath nstep (Vis n k) mo tr r mo' -> (forall rsp, match k rsp with Ret _ => True | Vis _ _ => False end) ->
  exists rsp, nstep n mo rsp mo' tr /\ k rsp = Ret r.
Proof.
  cbn. intros (rsp & mo1 & evs & tr' & Hst & Hp & ->) Hf. specialize (Hf rsp).
  destruct (k rsp) as [r0|n' k'] eqn:Ek; [| destruct Hf]. cbn in Hp. destruct Hp as (-> & -> & ->).
  exists rsp. rewrite app_nil_r. auto.
Qed.

Section Drive.
Context {St : Type} {AS : AllocSt St}.
Local Notation MP := (Monad.M St).

Ltac flat_shape W :=
  unfold mbind, msys, mret, mget, mupd, enode, ebind in W; cbn [ITree.bind fst snd] in W.

(* [comment removed for export] *)
Definition DCTX (B : Z) (L : mled) (G : St -> Model -> Prop) (s : St) (mo : Model) : Prop :=
  KL L (ps_brk s) mo /\ LI L mo /\ G s mo /\ gm L + BB L <= B.

(* [comment removed for export] *)
Definition req_ok (e : ev) : Prop :=
  match e with EMmap _ len _ flags => Z.land flags MAP_FIXED =? 0 = true -> mmap_len len <= RMAX | _ => True end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma ev_step_tpath_shape : forall L e s mo tr z s1 mo1,
  event_pre L e ->
  tpath nstep (ev_step e s) mo tr (Ok (z, s1)) mo1 ->
  tr = [] /\ vm_only mo mo1.
Proof.
  intros L e s mo tr z s1 mo1 Hpre Hp.
  destruct e as [req|addr len prot flags|addr len|addr len prot|? ? ?|?|ma mol mnl]; cbn [event_pre] in Hpre; try contradiction; try (destruct Hpre as [[] ?]); unfold ev_step in Hp.
  - destruct (req =? 0).
    + flat_shape Hp. apply tpath_vis_flat in Hp as (rsp & Hst & _); [| intros rsp; destruct (dec_brk0 rsp); exact I].
      pose proof (nstep_mm_vm_only (NBrk 0) _ _ _ _ I Hst) as (Hv & -> & _). auto.
    + flat_shape Hp. apply tpath_vis_flat in Hp as (rsp & Hst & _); [| intros rsp; destruct (dec_brk (ps_brk s) req rsp) as [[|]|]; exact I].
      pose proof (nstep_mm_vm_only (NBrk req) _ _ _ _ I Hst) as (Hv & -> & _). auto.
  - assert (Hfl : Z.testbit flags 14 = false).
    { destruct Hpre as [(_ & _ & -> & _)|(cur & _ & _ & _ & _ & ->)]; reflexivity. }
    destruct (negb (Z.land flags MAP_FIXED_Z =? 0)); [| destruct (prot =? 0)]; flat_shape Hp.
    + apply tpath_vis_flat in Hp as (rsp & Hst & _); [| intros rsp; destruct (dec_mmap_fixed addr len rsp); exact I].
      pose proof (nstep_mm_vm_only (NMmap addr len prot flags) _ _ _ _ Hfl Hst) as (Hv & -> & _). auto.
    + apply tpath_vis_flat in Hp as (rsp & Hst & _); [| intros rsp; destruct (dec_mmap_none len [] rsp); exact I].
      pose proof (nstep_mm_vm_only (NMmap addr len prot flags) _ _ _ _ Hfl Hst) as (Hv & -> & _). auto.
    + apply tpath_vis_flat in Hp as (rsp & Hst & _); [| intros rsp; destruct (dec_mmap len [] rsp); exact I].
      pose proof (nstep_mm_vm_only (NMmap addr len prot flags) _ _ _ _ Hfl Hst) as (Hv & -> & _). auto.
  - flat_shape Hp. apply tpath_vis_flat in Hp as (rsp & Hst & _); [| intros rsp; destruct (dec_munmap addr len rsp); exact I].
    pose proof (nstep_mm_vm_only (NMunmap addr len) _ _ _ _ I Hst) as (Hv & -> & _). auto.
  - flat_shape Hp. apply tpath_vis_flat in Hp as (rsp & Hst & _); [| intros rsp; destruct (dec_mprotect_rw addr len rsp); exact I].
    pose proof (nstep_mm_vm_only (NMprotect addr len prot) _ _ _ _ I Hst) as (Hv & -> & _). auto.
  - flat_shape Hp. apply tpath_vis_flat in Hp as (rsp & Hst & _); [| intros rsp; destruct (dec_mremap ma mol mnl [] [] rsp); exact I].
    pose proof (nstep_mm_vm_only (NMremap ma mol mnl) _ _ _ _ I Hst) as (Hv & -> & _). auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ev_step_tpath_good : forall L e s mo tr z s1 mo1 B,
  event_pre L e -> KL L (ps_brk s) mo -> LI L mo -> gm L + BB L <= B -> 0 <= B /\ B + PINB <= BLIVE -> req_ok e ->
  tpath nstep (ev_step e s) mo tr (Ok (z, s1)) mo1 ->
  good e z.
Proof.
  intros L e s mo tr z s1 mo1 B Hpre HK HLI HB HBB Hrq Hp. pose proof alloc_ceiling_lt as Hcl.
  pose proof (kl_static _ _ _ HK) as [KS1 KS2].
  destruct e as [req|addr len prot flags|addr len|addr len prot|? ? ?|?|? ? ?]; cbn [event_pre] in Hpre; try contradiction; try (destruct Hpre as [[] ?]); cbn [good]; try exact I.
  - (* [comment removed for export] *)
    intros Hnf. cbn [req_ok] in Hrq. specialize (Hrq ltac:(rewrite Hnf; reflexivity)).
    destruct Hpre as [(Hq & -> & -> & Hprot & Hlen)|(cur & Hph & -> & -> & -> & ->)]; [| cbv in Hnf; discriminate].
    pose proof (mmap_len_ge len ltac:(lia)) as ML.
    pose proof PINB_nonneg as HP0. pose proof (gm_nonneg L (ps_brk s) mo HK) as HG0. pose proof (BB_ge_brkreg L (ps_brk s) mo HK) as [_ HB0].
    assert (Hnr : forall fl, mmap_grant_refusable fl mo (mmap_len len) = false /\ mmap_reserve_refusable mo (mmap_len len) = false).
    { intros fl. apply (mmap_not_refusable L (ps_brk s) mo (B + PINB) HK HLI ltac:(lia)); [unfold BLIVE, PGSZ in *; lia| lia| unfold RMAX, BLIVE in *; lia|].
      apply fit_arith; [unfold RMAX in *; lia| lia]. }
    unfold ev_step in Hp. change (negb (Z.land MAPF MAP_FIXED_Z =? 0)) with false in Hp. cbn iota in Hp.
    destruct Hprot as [-> | ->].
    + change (PROT_NONE =? 0) with true in Hp. cbn iota in Hp. flat_shape Hp.
      apply tpath_vis_flat in Hp as (rsp & Hst & Ek); [| intros rsp; destruct (dec_mmap_none len [] rsp); exact I].
      destruct (nstep_mmap_none_grant len mo rsp mo1 tr ltac:(lia) ltac:(unfold LEN_MAX in Hlen; lia) (band_le_top _ (kl_top _ _ _ HK)) (proj2 (Hnr (Z_to_bv 64 0))) Hst) as (a & -> & A2 & A3).
      pose proof (alloc_top_room (m_vmmaps mo)) as ATR. unfold stack_max_size, two_pow_64 in ATR.
      unfold dec_mmap_none in Ek. cbn [core] in Ek.
      destruct (bv_eqb a a && bv_eqb (Z_to_bv 64 (mmap_len len)) (Z_to_bv 64 (mmap_len len)) && mmap_addr_ok len [] (bv_unsigned a)); [| discriminate].
      cbn in Ek. injection Ek as <- _. unfold is_err, TWO64. apply Z.ltb_ge. lia.
    + change (PROT_RW =? 0) with false in Hp. cbn iota in Hp. flat_shape Hp.
      apply tpath_vis_flat in Hp as (rsp & Hst & Ek); [| intros rsp; destruct (dec_mmap len [] rsp); exact I].
      destruct (nstep_mmap_rw_grant len mo rsp mo1 tr ltac:(lia) ltac:(unfold LEN_MAX in Hlen; lia) (band_le_top _ (kl_top _ _ _ HK)) (fun fl => proj1 (Hnr fl)) Hst) as (a & -> & A2 & A3).
      pose proof (alloc_top_room (m_vmmaps mo)) as ATR. unfold stack_max_size, two_pow_64 in ATR.
      unfold dec_mmap in Ek. cbn [core] in Ek.
      destruct (bv_eqb a a && bv_eqb (Z_to_bv 64 (mmap_len len)) (Z_to_bv 64 (mmap_len len)) && mmap_addr_ok len [] (bv_unsigned a)); [| discriminate].
      cbn in Ek. injection Ek as <- _. unfold is_err, TWO64. apply Z.ltb_ge. lia.
  - (* [comment removed for export] *)
    destruct Hpre as (Hq & -> & -> & b & l & k & Hin & -> & Hk).
    pose proof (kl_metas _ _ _ HK b l k Hin) as (A1 & A2 & A3 & A4 & Ak & Ak1 & A5 & A6 & Ana).
    pose proof (went_In_bounds _ _ _ b l HK (or_intror (ex_intro _ k Hin))) as (_ & B2 & _ & _ & B5 & B6).
    set (a := b + (1 + k) * PGSZ) in *. set (nb := mmap_len l) in *. set (h := m_vmmaps mo) in *.
    rewrite round_up_pg_eq in Hk. fold (mmap_len l) nb in Hk.
    assert (Hab : b + PGSZ <= a /\ a + PGSZ <= b + nb) by (subst a; unfold PGSZ in *; nia).
    assert (Hamod : a mod 4096 = 0). { subst a. unfold PGSZ in *. rewrite Z.add_mod, A3, Z.mod_mul by lia. reflexivity. }
    assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; unfold PGSZ in *; lia).
    assert (Un : bv_unsigned (Z_to_bv 64 (mmap_len PGSZ)) = PGSZ) by (change (mmap_len PGSZ) with PGSZ; apply unsigned_lit; unfold PGSZ; lia).
    assert (Hcn : map_contains (vm_noaccess h) (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len PGSZ)) = true).
    { destruct (Ana (1 + k) ltac:(lia) ltac:(lia)) as (e & He & Hel & Heh). unfold map_contains. apply existsb_exists. exists e. split; [exact He|].
      rewrite Ua, Un. unfold elo, ehi in Hel, Heh. subst a. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
    assert (Hcm : map_contains (vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len PGSZ)) = true).
    { unfold map_contains. apply existsb_exists. exists (went b nb). split; [exact A5|]. rewrite Ua, Un. unfold elo, ehi in B5, B6. rewrite B5.
      replace (bv_unsigned (fst (went b nb)) + bv_unsigned (snd (went b nb))) with (b + nb) by (symmetry; exact B6).
      rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
    pose proof PINB_nonneg as HP0.
    assert (Hnr : mprotect_refusable mo (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len PGSZ)) = false).
    { apply (mprotect_not_refusable L (ps_brk s) mo (B + PINB) HK HLI ltac:(lia)). subst h. unfold RMAX, BLIVE in *. lia. }
    unfold ev_step in Hp. flat_shape Hp.
    apply tpath_vis_flat in Hp as (rsp & Hst & Ek); [| intros rsp; destruct (dec_mprotect_rw a PGSZ rsp); exact I].
    pose proof (nstep_mprotect_grant a PGSZ mo rsp mo1 tr ltac:(unfold PGSZ in *; lia) ltac:(unfold PGSZ; lia) ltac:(rewrite page_size_eq; exact Hamod)
                  ltac:(change (mmap_len PGSZ) with PGSZ; unfold PGSZ in *; lia) Hcn Hcm Hnr Hst) as ->.
    unfold dec_mprotect_rw, dec_mprotect in Ek. cbn [core] in Ek. rewrite unsigned_lit in Ek by lia. cbn [Z.eqb andb] in Ek.
    rewrite !bv_eqb_refl in Ek. cbn in Ek. injection Ek as <- _. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma req_of_BOUND L e B : BOUND L e B -> B + PINB <= BLIVE -> req_ok e.
Proof.
  intros [_ HR] HB. destruct e; cbn in HR |- *; auto; intros Hf; specialize (HR Hf); unfold QMAX, RMAX in *; lia.
Qed.

#[using="Type"] Lemma ev_step_G : forall L e G s mo tr z s1 mo1 B,
  frame_ok G -> event_pre L e -> DCTX B L G s mo -> 0 <= B /\ B + PINB <= BLIVE -> BOUND L e B ->
  tpath nstep (ev_step e s) mo tr (Ok (z, s1)) mo1 ->
  tr = [] /\ good e z /\ answer_ok L e z = true /\ DCTX B (event_post L e z) G s1 mo1
  /\ ps_m s1 = ps_m s /\ ps_rest s1 = ps_rest s /\ vm_only mo mo1.
Proof.
  intros L e G s mo tr z s1 mo1 B HG Hpre (HK & HLI & HGs & HB) HBB HBD Hp.
  pose proof (req_of_BOUND L e B HBD (proj2 HBB)) as Hrq.
  pose proof (ev_step_LI L e G s HG Hpre s mo (conj eq_refl (conj HK (conj HLI HGs)))) as W.
  pose proof (twf_tpath _ _ _ _ _ _ W Hp) as Q. cbn [fst snd] in Q. destruct Q as [(Hans & HK1 & HG1 & Hm & Hx) HL1].
  destruct (ev_step_tpath_shape L e s mo tr z s1 mo1 Hpre Hp) as [-> Hvo].
  pose proof (ev_step_tpath_good L e s mo [] z s1 mo1 B Hpre HK HLI HB HBB Hrq Hp) as Hgood.
  split; [reflexivity|]. split; [exact Hgood|]. split; [exact Hans|]. split; [| auto].
  split; [exact HK1|]. split; [exact HL1|]. split; [exact HG1|]. pose proof (BOUND_post _ _ _ HBD z Hans). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Theorem membedF_tpath_G {R} : forall (t : Malloc.M R) L Post G s mo tr r s' mo' B,
  frame_ok G -> ftree L t Post -> fbnd8 B L t -> 0 <= B /\ B + PINB <= BLIVE ->
  DCTX B L G s mo ->
  tpath nstep (membedF peekG t s) mo tr (Ok (r, s')) mo' ->
  tr = [] /\ gpath t r /\ exists L', fpath L t L' r /\ Post L' r /\ DCTX B L' G s' mo'
  /\ ps_m s' = ps_m s /\ ps_rest s' = ps_rest s /\ vm_only mo mo'.
Proof.
  induction t as [r0|e k IH]; intros L Post G s mo tr r s' mo' B HG Hok Hbd HBB HD Hp.
  - cbn in Hp. destruct Hp as (E & -> & ->). injection E as -> ->. cbn in Hok.
    split; [reflexivity|]. split; [constructor|]. exists L. split; [constructor|]. split; [exact Hok|]. split; [exact HD|]. split; [reflexivity|]. split; [reflexivity| apply vm_only_refl].
  - cbn [membedF] in Hp. unfold mbind in Hp. apply tpath_ebind in Hp. destruct Hp as [[_ E]|(tr1 & [z s1] & mo1 & tr2 & Hp1 & Hp2 & ->)]; [discriminate|].
    cbn [fst snd] in Hp2.
    destruct (is_peek e) eqn:Ep.
    + destruct e as [| | | |p c h| |]; cbn in Ep; try discriminate. cbn [ev_stepF] in Hp1.
      unfold peekG, msys in Hp1. apply tpath_enode in Hp1 as (rsp & Hst & E).
      destruct (nstep_dec_peek _ _ _ _ _ Hst) as (-> & -> & Hv & _). cbn in E. injection E as Ez Es. subst z s1.
      cbn [ftree] in Hok. cbn [fbnd8] in Hbd.
      destruct (IH (dec_peek rsp) L Post G s mo tr2 r s' mo' B HG (Hok _ Hv) (Hbd _ Hv) HBB HD Hp2) as (-> & GP & L' & FP & HP & HD' & Hm & Hx & Hvo).
      split; [reflexivity|]. split; [apply (gpath_peek _ _ _ _ (dec_peek rsp)); exact GP|]. exists L'. split; [apply (fpath_peek _ _ _ _ _ (dec_peek rsp)); [exact Hv| exact FP]|]. auto 10.
    + assert (Hev : event_pre L e /\ (forall a, if answer_ok L e a then ftree (event_post L e a) (k a) Post else rejects (k a))
                    /\ BOUND L e B /\ (forall a, answer_ok L e a = true -> fbnd8 B (event_post L e a) (k a))
                    /\ is_undef e = false /\ ev_stepF peekG e = ev_step e).
      { destruct e; cbn in Ep; try discriminate; cbn [ftree] in Hok; cbn [fbnd8] in Hbd; try (destruct Hok; fail);
          destruct Hok as [H1 H2]; destruct Hbd as [H3 H4]; try contradiction;
          exact (conj H1 (conj H2 (conj H3 (conj H4 (conj eq_refl eq_refl))))). }
      destruct Hev as (Hpre & Hk & HBD & Hbk & Hu & Estep). rewrite Estep in Hp1.
      destruct (ev_step_G L e G s mo tr1 z s1 mo1 B HG Hpre HD HBB HBD Hp1) as (-> & Hgood & Hans & HD1 & Hm1 & Hx1 & Hvo1).
      specialize (Hk z). rewrite Hans in Hk.
      destruct (IH z (event_post L e z) Post G s1 mo1 tr2 r s' mo' B HG Hk (Hbk z Hans) HBB HD1 Hp2) as (-> & GP & L' & FP & HP & HD' & Hm & Hx & Hvo).
      split; [reflexivity|]. split; [apply (gpath_vis _ _ z); [exact Ep| exact Hu| exact Hgood| exact GP]|].
      exists L'. split; [eapply fpath_vis; eauto|]. split; [exact HP|]. split; [exact HD'|].
      split; [congruence|]. split; [congruence| eapply vm_only_trans; eauto].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition okn (n : node) : Prop :=
  match n with
  | NBrk _ | NMunmap _ _ | NMprotect _ _ _ | NPeek _ | NMremap _ _ _ => True
  | NMmap _ _ _ flags => Z.land (bv_unsigned (Z_to_bv 64 flags)) MAP_NORESERVE = 0
  | _ => False
  end.

(* [comment removed for export] *)
Fixpoint oknodes {R} (t : itree node R) (mo : Model) : Prop :=
  match t with
  | Ret _ => True
  | Vis n k => okn n /\ forall rsp mo' evs, nstep n mo rsp mo' evs -> oknodes (k rsp) mo'
  end.

(* [comment removed for export] *)
#[using="Type"] Lemma mm_answer_exists : forall n mo,
  okn n -> match n with NPeek _ => False | _ => True end -> nsafe n mo -> exists rsp mo', nstep n mo rsp mo' [].
Proof.
  (* [comment removed for export] *)
  intros n mo Hn Hnp Hs. destruct n; try contradiction; cbn [nsafe node_input] in Hs; destruct Hs as [[Hnu [o Ho]] Hdec];
    (destruct o as [eff0 mo0 evs0|]; [| exfalso; exact (Hnu Ho)]);
    destruct (admissible_exists _ _ _ _ _ Hdec Ho) as (eff & mo' & evs & Ho1 & Hns); pose proof Ho1 as H'.
  - rewrite syscall_spec_214 in H' by reflexivity. apply brk_shape in H' as (_ & -> & _).
    exists eff, mo'. cbn [nstep node_input]. split; [reflexivity| split; [exact Ho1| exact Hns]].
  - rewrite syscall_spec_222 in H' by reflexivity. cbn [in_arg in_args pure_input nth] in H'. apply mmap_shape in H' as (_ & -> & _); [| exact Hn].
    exists eff, mo'. cbn [nstep node_input]. split; [reflexivity| split; [exact Ho1| exact Hns]].
  - rewrite syscall_spec_215 in H' by reflexivity. apply munmap_shape in H' as (_ & -> & _).
    exists eff, mo'. cbn [nstep node_input]. split; [reflexivity| split; [exact Ho1| exact Hns]].
  - rewrite syscall_spec_226 in H' by reflexivity. apply mprotect_shape in H' as (_ & -> & _).
    exists eff, mo'. cbn [nstep node_input]. split; [reflexivity| split; [exact Ho1| exact Hns]].
  - rewrite syscall_spec_216 in H' by reflexivity. apply mremap_shape in H' as (_ & -> & _).
    exists eff, mo'. cbn [nstep node_input]. split; [reflexivity| split; [exact Ho1| exact Hns]].
Qed.

Variable segs : list Segment.   (* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma twf_drive {R} : forall (t : itree node R) mo (P : R -> Model -> Prop),
  twf t mo P -> oknodes t mo ->
  wreach (npeek segs) nstep t mo (fun tr r mo' => tpath nstep t mo tr r mo' /\ P r mo').
Proof.
  induction t as [r|n k IH]; intros mo P Hw Ha.
  - apply wreach_ret. cbn. auto.
  - cbn in Hw. destruct Hw as [Hs Hk]. destruct Ha as [Hn Hak].
    assert (PK : match n with NPeek _ => True | _ => npeek segs n = None end) by (destruct n; try reflexivity; exact I).
    destruct n; try (exfalso; exact Hn);
      first
        [ match goal with |- wreach _ _ (Vis (NPeek _) _) _ _ => idtac end;
          eapply wreach_peek; [reflexivity|]; intros rsp mo1 evs Hst;
          pose proof (nstep_dec_peek _ _ _ _ _ Hst) as (-> & -> & _);
          eapply wreach_mono; [apply IH; [eapply Hk; exact Hst| eapply Hak; exact Hst]|];
          intros tr r mo' [Hp HP]; cbn [app]; split; [| exact HP]; exists rsp, mo, [], tr; auto
        | destruct (mm_answer_exists _ mo Hn I Hs) as (rsp & mo1 & Hst);
          eapply wreach_vis; [exact PK| exact Hst|];
          eapply wreach_mono; [apply IH; [eapply Hk; exact Hst| eapply Hak; exact Hst]|];
          intros tr r mo' [Hp HP]; cbn [app]; split; [| exact HP]; exists rsp, mo1, [], tr; auto ].
Qed.

#[using="Type"] Lemma oknodes_bind {A B'} (t : itree node A) (f : A -> itree node B') : forall mo,
  oknodes t mo -> (forall r mo' tr, tpath nstep t mo tr r mo' -> oknodes (f r) mo') -> oknodes (ITree.bind _ t f) mo.
Proof.
  induction t as [r|n k IH]; intros mo Ht Hf; cbn.
  - apply (Hf r mo []). cbn. auto.
  - destruct Ht as [Hn Hk]. split; [exact Hn|]. intros rsp mo' evs Hst. apply IH; [eapply Hk; exact Hst|].
    intros r mo'' tr Hp. apply (Hf r mo'' (evs ++ tr)). cbn. exists rsp, mo', evs, tr. auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ev_step_oknodes : forall L e s mo, event_pre L e -> oknodes (ev_step e s) mo.
Proof.
  intros L e s mo Hpre.
  destruct e as [req|addr len prot flags|addr len|addr len prot|? ? ?|?|ma mol mnl]; cbn [event_pre] in Hpre; try contradiction; try (destruct Hpre as [[] ?]); unfold ev_step.
  - destruct (req =? 0); unfold mbind, msys, mret, mget, mupd, enode, ebind; cbn [ITree.bind fst snd oknodes].
    + split; [exact I|]. intros rsp mo' evs _. destruct (dec_brk0 rsp); exact I.
    + split; [exact I|]. intros rsp mo' evs _. destruct (dec_brk (ps_brk s) req rsp) as [[|]|]; exact I.
  - assert (Hfl : Z.land (bv_unsigned (Z_to_bv 64 flags)) MAP_NORESERVE = 0).
    { destruct Hpre as [(_ & _ & -> & _)|(cur & _ & _ & _ & _ & ->)]; rewrite unsigned_lit by (cbv; split; congruence); reflexivity. }
    destruct (negb (Z.land flags MAP_FIXED_Z =? 0)); [| destruct (prot =? 0)]; unfold mbind, msys, mret, mget, mupd, enode, ebind; cbn [ITree.bind fst snd oknodes].
    + split; [exact Hfl|]. intros rsp mo' evs _. destruct (dec_mmap_fixed addr len rsp); exact I.
    + split; [exact Hfl|]. intros rsp mo' evs _. destruct (dec_mmap_none len [] rsp); exact I.
    + split; [exact Hfl|]. intros rsp mo' evs _. destruct (dec_mmap len [] rsp); exact I.
  - unfold mbind, msys, mret, mget, mupd, enode, ebind; cbn [ITree.bind fst snd oknodes]. split; [exact I|]. intros rsp mo' evs _. destruct (dec_munmap addr len rsp); exact I.
  - unfold mbind, msys, mret, mget, mupd, enode, ebind; cbn [ITree.bind fst snd oknodes]. split; [exact I|]. intros rsp mo' evs _. destruct (dec_mprotect_rw addr len rsp); exact I.
  - unfold mbind, msys, mret, mget, mupd, enode, ebind; cbn [ITree.bind fst snd oknodes]. split; [exact I|]. intros rsp mo' evs _. destruct (dec_mremap ma mol mnl [] [] rsp); exact I.
Qed.

#[using="Type"] Lemma membedF_oknodes {R} : forall (t : Malloc.M R) L Post G s mo,
  frame_ok G -> ftree L t Post -> KL L (ps_brk s) mo -> G s mo ->
  oknodes (membedF peekG t s) mo.
Proof.
  induction t as [r|e k IH]; intros L Post G s mo HG Hok HK HGs; [exact I|].
  cbn [membedF]. unfold mbind, ebind. cbn [ftree] in Hok.
  destruct (is_peek e) eqn:Ep.
  - destruct e as [| | | |p c h| |]; cbn in Ep; try discriminate. cbn [ev_stepF]. unfold peekG, msys, enode. cbn [ITree.bind oknodes].
    split; [exact I|]. intros rsp mo' evs Hst. destruct (nstep_dec_peek _ _ _ _ _ Hst) as (-> & -> & Hv & _). cbn [ITree.bind].
    eapply IH; [exact HG| apply Hok; exact Hv| exact HK| exact HGs].
  - assert (Hev : event_pre L e /\ (forall a, if answer_ok L e a then ftree (event_post L e a) (k a) Post else rejects (k a)) /\ ev_stepF peekG e = ev_step e).
    { destruct e; cbn in Ep; try discriminate; try (destruct Hok; fail); destruct Hok as [H1 H2]; try contradiction; auto. }
    destruct Hev as (Hpre & Hk & ->).
    apply oknodes_bind; [apply (ev_step_oknodes L); exact Hpre|].
    intros [|[z s1]] mo1 tr Hp; cbn [ITree.bind]; [exact I|].
    pose proof (ev_step_spec L e G s HG Hpre s mo (conj eq_refl (conj HK HGs))) as W.
    pose proof (twf_tpath _ _ _ _ _ _ W Hp) as Q. cbn [fst snd] in Q. destruct Q as (Hans & HK1 & HG1 & _ & _).
    specialize (Hk z). rewrite Hans in Hk.
    eapply IH; [exact HG| exact Hk| exact HK1| exact HG1].
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem membedF_wreach_C {R} : forall (t : Malloc.M R) L Post G s mo B,
  frame_ok G -> ftree L t Post -> fbnd8 B L t -> 0 <= B /\ B + PINB <= BLIVE ->
  DCTX B L G s mo ->
  wreach (npeek segs) nstep (membedF peekG t s) mo
    (fun tr res mo' => tr = [] /\ exists r s', res = Ok (r, s') /\ gpath t r /\ exists L', fpath L t L' r /\ Post L' r /\ DCTX B L' G s' mo'
                       /\ ps_m s' = ps_m s /\ ps_rest s' = ps_rest s /\ vm_only mo mo').
Proof.
  intros t L Post G s mo B HG Hok Hbd HBB HD. pose proof HD as (HK & HLI & HGs & HB).
  pose proof (membedF_spec peekG (@peekG_spec St) t Post G L s HG Hok s mo (conj eq_refl (conj HK HGs))) as W.
  pose proof (membedF_oknodes t L Post G s mo HG Hok HK HGs) as OK.
  eapply wreach_mono; [exact (twf_drive _ mo _ W OK)|].
  intros tr [|[r s']] mo' [Hp HP]; [destruct HP|].
  destruct (membedF_tpath_G t L Post G s mo tr r s' mo' B HG Hok Hbd HBB HD Hp) as (-> & GP & L' & FP & HPost & HD' & Hm & Hx & Hvo).
  split; [reflexivity|]. exists r, s'. split; [reflexivity|]. split; [exact GP|]. exists L'. auto 10.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma oknodes_no_texit {R} : forall (t : itree node R) mo tr, oknodes t mo -> texit nstep nexit t mo tr -> False.
Proof.
  induction t as [r|n k IH]; intros mo tr Hok Hx; cbn in Hx; [exact Hx|].
  destruct Hok as [Hn Hk]. destruct Hx as [(code & mo' & Hex & _)|(rsp & mo' & evs & tr' & Hst & Hx & _)].
  - destruct n; cbn in Hex; try exact Hex. exact Hn.
  - eapply IH; [eapply Hk; exact Hst| exact Hx].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

End Drive.

End WithCeil.

(* [comment removed for export] *)
Section Both.
Context {CEG CEC : CEIL}.
Context {StG : Type} {ASG : AllocSt StG} {StC : Type} {ASC : AllocSt StC}.
Variable segs : list Segment.

#[using="Type"] Theorem membedF_fsimw {RG RC} (tG : Malloc.M RG) (tC : Malloc.M RC) LG LC PostG PostC
    (GG : StG -> Model -> Prop) (GC : StC -> Model -> Prop) (sG0 : StG) (sC0 : StC) moG0 moC0 B :
  frame_ok GG -> frame_ok GC ->
  ftree (CE:=CEG) LG tG PostG -> fbnd8 (CE:=CEG) B LG tG ->
  ftree (CE:=CEC) LC tC PostC -> fbnd8 (CE:=CEC) B LC tC ->
  0 <= B /\ B + PINB <= BLIVE ->
  DCTX (CE:=CEG) B LG GG sG0 moG0 -> DCTX (CE:=CEC) B LC GC sC0 moC0 ->
  fsimw (npeek segs)
    (fun sG moG sC moC => sG = sG0 /\ moG = moG0 /\ sC = sC0 /\ moC = moC0)
    (membedF (CE:=CEG) peekG tG) (membedF (CE:=CEC) peekG tC)
    (fun rG rC sG moG sC moC =>
       gpath tG rG /\ gpath tC rC
       /\ (exists LG', fpath (CE:=CEG) LG tG LG' rG /\ PostG LG' rG /\ DCTX (CE:=CEG) B LG' GG sG moG)
       /\ (exists LC', fpath (CE:=CEC) LC tC LC' rC /\ PostC LC' rC /\ DCTX (CE:=CEC) B LC' GC sC moC)
       /\ ps_m sG = ps_m sG0 /\ ps_rest sG = ps_rest sG0 /\ vm_only moG0 moG
       /\ ps_m sC = ps_m sC0 /\ ps_rest sC = ps_rest sC0 /\ vm_only moC0 moC).
Proof.
  intros HGG HGC FTG BDG FTC BDC HBB HDG HDC sG moG sC moC (-> & -> & -> & ->). split.
  - intros trG rG sG' moG' Hp.
    destruct (membedF_tpath_G tG LG PostG GG sG0 moG0 trG rG sG' moG' B HGG FTG BDG HBB HDG Hp) as (-> & GPG & LG' & FPG & HPG & HDG' & HmG & HxG & HvoG).
    eapply wreach_mono; [exact (membedF_wreach_C segs tC LC PostC GC sC0 moC0 B HGC FTC BDC HBB HDC)|].
    intros trC res moC' (-> & rC & sC' & -> & GPC & LC' & FPC & HPC & HDC' & HmC & HxC & HvoC).
    exists rC, sC'. split; [reflexivity|]. split; [reflexivity|].
    split; [exact GPG|]. split; [exact GPC|]. split; [exists LG'; auto|]. split; [exists LC'; auto|]. auto 10.
  - intros trG Hx. exfalso. destruct HDG as (HK & _ & HGs & _).
    exact (oknodes_no_texit _ _ _ (membedF_oknodes tG LG PostG GG sG0 moG0 HGG FTG HK HGs) Hx).
Qed.
End Both.
