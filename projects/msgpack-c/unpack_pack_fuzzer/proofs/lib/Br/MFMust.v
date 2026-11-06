(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState Mem ITree Nodes NodesM Decode DecodeM.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import Prelim STree Malloc MallocCtrl KInv.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Monad MSafe Prog KLink KStep KOwn PgArith A_MallocBlocks.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require MI_Contracts.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import RelSpec.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import StateGlue NodeSound TreeBridgeN KRel MPath Room Grant MMeas NoRefuse.
Set Keyed Unification.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Lemma is_err_below_ceiling : forall a nZ, 0 <= nZ -> a + nZ <= alloc_ceiling + 4096 -> 0 <= a -> is_err a = false.
Proof. intros a nZ Hn Ha H0. pose_ceil. unfold is_err, TWO64. apply Z.ltb_ge. lia. Qed.

Lemma ev_mmap_anon_noref : forall len prot s mo z s1 mo1 j,
  0 < len -> mmap_len len <= 2 ^ 27 -> (prot = PROT_RW \/ prot = Malloc.PROT_NONE) ->
  room mo j -> 0 <= j <= 28 -> mo_ok mo -> ceil_ok (m_vmmaps mo) ->
  tpath nstep (ev_step (EMmap 0 len prot (Malloc.MAP_PRIVATE + MAP_ANON)) s) mo [] (Ok (z, s1)) mo1 ->
  is_err z = false.
Proof.
  intros len prot s mo z s1 mo1 j Hlen HnZ Hprot R Hj Hmo Hck H.
  pose proof (mmap_len_bound len Hlen) as Hb.
  assert (HlenU : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  assert (Hw : w_is0 (Z_to_bv 64 len) = false) by (rewrite w_is0_lit by lia; apply Z.eqb_neq; lia).
  unfold ev_step in H. change (negb (Z.land (Malloc.MAP_PRIVATE + MAP_ANON) MAP_FIXED_Z =? 0)) with false in H. cbn iota in H.
  destruct Hprot as [-> | ->].
  - change (PROT_RW =? 0) with false in H. cbn iota in H.
    apply tpath_mbind_inv in H as (ans & s2 & mo2 & H1 & H2).
    apply tpath_msys_inv in H1 as (-> & rsp & Hst & Hdec).
    apply tpath_mret_inv in H2 as [E ->]. inversion E; subst z s1. clear E.
    apply (proj1 (nstep_mmap_rw_inv 0 len mo rsp mo2 [] Hw)) in Hst as [_ Hst]. rewrite HlenU in Hst. fold (mmap_len len) in Hst.
    destruct Hst as [(e & HIn & _ & _) | (a & (E1 & E2 & E3 & E4 & E5) & -> & ->)].
    + exfalso. rewrite (room_grant_not_refusable mo j (mmap_len len) R Hj Hmo Hck ltac:(lia)) in HIn. exact HIn.
    + unfold dec_mmap in Hdec. cbn [eff_copies eff_copyins] in Hdec.
      destruct (bv_eqb a a && bv_eqb (Z_to_bv 64 (mmap_len len)) (Z_to_bv 64 (mmap_len len)) && mmap_addr_ok len [] (bv_unsigned a)); [| discriminate].
      inversion Hdec; subst ans. unfold ceil_ok in Hck.
      apply (is_err_below_ceiling (bv_unsigned a) (mmap_len len)); [lia| lia|]. pose proof (bv_unsigned_in_range 64 a). lia.
  - change (Malloc.PROT_NONE =? 0) with true in H. cbn iota in H.
    apply tpath_mbind_inv in H as (ans & s2 & mo2 & H1 & H2).
    apply tpath_msys_inv in H1 as (-> & rsp & Hst & Hdec).
    apply tpath_mret_inv in H2 as [E ->]. inversion E; subst z s1. clear E.
    apply (proj1 (nstep_mmap_none_inv 0 len mo rsp mo2 [] Hw)) in Hst as [_ Hst]. rewrite HlenU in Hst. fold (mmap_len len) in Hst.
    destruct Hst as [(e & HIn & _ & _) | (a & (E1 & E2 & E3 & E4) & -> & ->)].
    + exfalso. rewrite (room_reserve_not_refusable mo j (mmap_len len) R Hj Hmo Hck ltac:(lia)) in HIn. exact HIn.
    + unfold dec_mmap_none in Hdec. cbn [eff_copies eff_copyins] in Hdec.
      destruct (bv_eqb a a && bv_eqb (Z_to_bv 64 (mmap_len len)) (Z_to_bv 64 (mmap_len len)) && mmap_addr_ok len [] (bv_unsigned a)); [| discriminate].
      inversion Hdec; subst ans. unfold ceil_ok in Hck.
      apply (is_err_below_ceiling (bv_unsigned a) (mmap_len len)); [lia| lia|]. pose proof (bv_unsigned_in_range 64 a). lia.
Qed.

Lemma ev_mprotect_noref : forall L a len prot s mo z s1 mo1 j,
  event_pre L (EMprotect a len prot) -> KL L (ps_brk s) mo -> room mo j -> 0 <= j <= 28 -> mo_ok mo ->
  tpath nstep (ev_step (EMprotect a len prot) s) mo [] (Ok (z, s1)) mo1 -> z = 0.
Proof.
  intros L a len prot s mo z s1 mo1 j Hpre HK R Hj Hmo H.
  pose proof (ev_step_spec L (EMprotect a len prot) GT s frame_ok_GT Hpre s mo (conj eq_refl (conj HK I))) as W.
  pose proof (ev_step_nsafe _ s mo _ (NMprotect a len prot) W eq_refl) as Hs.
  cbn [nsafe] in Hs. cbv zeta in Hs. destruct Hs as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
  unfold ev_step in H.
  apply tpath_mbind_inv in H as (ans & s2 & mo2 & H1 & H2).
  apply tpath_msys_inv in H1 as (-> & rsp & Hst & Hdec).
  apply tpath_mret_inv in H2 as [E ->]. inversion E; subst z s1. clear E.
  pose proof (nstep_mprotect_inv a len prot mo rsp mo2 []) as INV. cbv zeta in INV. specialize (INV C1 C2 C3 C4 C5 C6 C7).
  apply (proj1 INV) in Hst as [_ [(e & HIn & _ & _) | (_ & -> & _)]]; clear INV.
  - exfalso. rewrite (room_mprotect_not_refusable mo j _ _ R Hj Hmo) in HIn. exact HIn.
  - unfold dec_mprotect_rw, dec_mprotect in Hdec. cbn [eff_copies eff_copyins] in Hdec.
    change (bv_unsigned (Z_to_bv 64 0) =? 0) with true in Hdec. cbn [andb] in Hdec.
    destruct (bv_eqb _ _ && bv_eqb _ _) in Hdec; [| discriminate]. inversion Hdec; subst ans. reflexivity.
Qed.

Fixpoint noref {R} (t : Malloc.M R) (zs : list Z) {struct t} : Prop :=
  match t, zs with
  | SVis e k, z :: zs' =>
      match e with
      | EMmap _ _ _ flags => (Z.land flags MAP_FIXED_Z =? 0) = true -> is_err z = false
      | EMprotect _ _ _ => z = 0
      | _ => True
      end /\ noref (k z) zs'
  | _, _ => True
  end.

Lemma room_prefix : forall mo mo' j (k : nat) E,
  room mo j -> 0 <= j -> msteps k E mo mo' -> (k <= 64)%nat -> E <= (2 ^ 26 + 2 ^ 20) -> room mo' (j + 1).
Proof.
  intros mo mo' j k E [A B C D] Hj [M1 M2 M3 M4] Hk HE. constructor.
  - apply M3; [| unfold PGSZ; lia | exact A]. lia.
  - lia.
  - nia.
  - rewrite M4. exact D.
Qed.

Lemma msteps_snoc1 : forall k E mo mo1 mo2 e,
  msteps k E mo mo1 -> mstep (esize e) mo1 mo2 -> 0 <= E -> msteps (S k) (E + esize e) mo mo2.
Proof.
  intros k E mo mo1 mo2 e [A1 A2 A3 A4] [B1 B2 B3 B4] HE. pose proof (esize_nonneg e). constructor.
  - lia. - lia.
  - intros B HB H3 Hs. apply B3; [lia|]. apply A3; [lia | exact H3 | exact Hs].
  - congruence.
Qed.

Theorem membed_noref : forall {R} (t : Malloc.M R) L Post s mo r s' mo' mo0 j (k0 : nat) E0,
  ctree_ok L t Post -> KL L (ps_brk s) mo -> mo_ok mo ->
  room mo0 j -> 0 <= j < 28 -> msteps k0 E0 mo0 mo -> 0 <= E0 ->
  (forall zs, okpath L t zs -> (k0 + length (evs_of t zs) <= 64)%nat /\ E0 + esum (evs_of t zs) <= (2 ^ 26 + 2 ^ 20)) ->
  tpath nstep (membed t s) mo [] (Ok (r, s')) mo' ->
  exists zs, follow t zs = Some r /\ okpath L t zs /\ noref t zs.
Proof.
  intros R t. induction t as [r0 | e k IH]; intros L Post s mo r s' mo' mo0 j k0 E0 CT HK Hmo R0 Hj MS0 HE0 HB Htp.
  - cbn [membed] in Htp. apply tpath_mret_inv in Htp as [E ->]. inversion E; subst.
    exists []. cbn [follow okpath noref]. auto.
  - cbn [membed] in Htp. apply tpath_mbind_inv in Htp as (z & s1 & mo1 & H1 & H2).
    destruct CT as [Hpre Hk].
    destruct (kev_measure L e s mo z s1 mo1 Hpre HK Hmo H1) as (Hok & HK1 & Hm & _ & _ & Hmo1 & Hva1 & M1).

    assert (HB1 : forall zs, okpath (event_post L e z) (k z) zs ->
              (S k0 + length (evs_of (k z) zs) <= 64)%nat /\ (E0 + esize e) + esum (evs_of (k z) zs) <= (2 ^ 26 + 2 ^ 20)).
    { intros zs Hzs. destruct (HB (z :: zs)) as [B1 B2].
      - destruct e; try (cbn [event_pre] in Hpre; contradiction); cbn [okpath]; auto.
      - destruct e; try (cbn [event_pre] in Hpre; contradiction); cbn [evs_of esum length] in B1, B2; split; lia. }
    pose proof (msteps_snoc1 k0 E0 mo0 mo mo1 e MS0 M1 HE0) as MS1.
    pose proof (esize_nonneg e) as He0.
    destruct (IH z (event_post L e z) Post s1 mo1 r s' mo' mo0 j (S k0) (E0 + esize e) (Hk z Hok) HK1 Hmo1 R0 Hj MS1 ltac:(lia) HB1 H2)
      as (zs & Hf & Hokp & Hnr).

    destruct (HB1 zs Hokp) as [Bk BE]. pose proof (esum_nonneg (evs_of (k z) zs)) as Hs0.
    assert (RM : room mo (j + 1)) by (apply (room_prefix mo0 mo j k0 E0 R0 ltac:(lia) MS0); lia).
    exists (z :: zs).
    destruct e as [req | a len prot flags | a len | a len prot | p c h | w]; try (cbn [event_pre] in Hpre; contradiction);
      cbn [follow okpath noref]; (split; [exact Hf|]); (split; [split; [exact Hok | exact Hokp]|]); (split; [| exact Hnr]); try exact I.
    +
      intros NF. cbn [event_pre] in Hpre. destruct Hpre as [(Hq & -> & -> & Hprot & Hlen) | (cur & Hph & -> & -> & -> & ->)].
      * cbn [esize] in BE. apply (ev_mmap_anon_noref len prot s mo z s1 mo1 (j + 1)); try assumption.
        -- lia.
        -- unfold mmap_len. rewrite Z.max_r in BE by (unfold page_round_up_Z, page_size; lia). lia.
        -- destruct Hprot as [-> | ->]; [right | left]; reflexivity.
        -- lia.
        -- exact (kl_ceil _ _ _ HK).
      * exfalso. revert NF. vm_compute. discriminate.
    +
      apply (ev_mprotect_noref L a len prot s mo z s1 mo1 (j + 1) Hpre HK RM ltac:(lia) Hmo H1).
Qed.

Theorem raw_malloc_noref : forall n s LB mo r s' mo' j,
  KREL s LB mo -> mo_ok mo -> 0 <= n -> room mo j -> 0 <= j < 28 ->
  (forall L zs, MI_Contracts.SIMREL (ps_m s) L -> okpath L (cmalloc (ps_m s) n) zs ->
     (length (evs_of (cmalloc (ps_m s) n) zs) <= 64)%nat /\ esum (evs_of (cmalloc (ps_m s) n) zs) <= (2 ^ 26 + 2 ^ 20)) ->
  mpath (raw_malloc n) s mo r s' mo' ->
  exists L zs st' p, MI_Contracts.SIMREL (ps_m s) L /\ follow (cmalloc (ps_m s) n) zs = Some (st', p)
    /\ okpath L (cmalloc (ps_m s) n) zs /\ noref (cmalloc (ps_m s) n) zs
    /\ r = match p with Some slot => Some (slot, fresh_off st' slot n) | None => None end.
Proof.
  intros n s LB mo r s' mo' j [(L & Hc & HK & _) _] Hmo Hn R Hj Hb Hp.
  destruct (mpath_raw_malloc_inv _ _ _ _ _ _ Hp) as (st' & p & s1 & Ht & _ & Hr).
  assert (HB : forall zs, okpath L (cmalloc (ps_m s) n) zs ->
            (0 + length (evs_of (cmalloc (ps_m s) n) zs) <= 64)%nat /\ 0 + esum (evs_of (cmalloc (ps_m s) n) zs) <= (2 ^ 26 + 2 ^ 20)).
  { intros zs Hzs. destruct (Hb L zs Hc Hzs) as [B1 B2]. split; lia. }
  destruct (membed_noref _ L _ s mo (st', p) s1 mo' mo j 0%nat 0 (MI_Contracts.cmalloc_contract_sim _ _ _ Hc Hn) HK Hmo R Hj
              (msteps_refl mo) ltac:(lia) HB Ht) as (zs & Hf & Hok & Hnr).
  exists L, zs, st', p. auto.
Qed.

End CEIL.
