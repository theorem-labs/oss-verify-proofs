(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState Mem ITree Nodes NodesM Decode DecodeM.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import Prelim STree Malloc MallocCtrl KInv.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Monad MSafe Prog KLink KStep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import RelSpec.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import StateGlue NodeSound TreeBridgeN KRel.

Set Keyed Unification.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Section Plumbing.
Context {St : Type}.

Lemma tpath_ret_iff : forall {R} (r0 r : R) mo tr mo',
  tpath nstep (Ret r0 : itree node R) mo tr r mo' <-> r0 = r /\ mo' = mo /\ tr = [].
Proof. intros. cbn. tauto. Qed.

Lemma tpath_mret : forall {A} (a : A) (s : St) mo,
  tpath nstep (mret a s) mo [] (Ok (a, s)) mo.
Proof. intros. cbn. repeat split; reflexivity. Qed.

Lemma tpath_mbind : forall {A B} (m : Monad.M St A) (f : A -> Monad.M St B) s mo a s1 mo1 r mo',
  tpath nstep (m s) mo [] (Ok (a, s1)) mo1 ->
  tpath nstep (f a s1) mo1 [] r mo' ->
  tpath nstep (mbind m f s) mo [] r mo'.
Proof.
  intros A B m f s mo a s1 mo1 r mo' H1 H2. unfold mbind. apply (proj2 (tpath_ebind _ _ _ _ _ _ _ _)).
  right. exists [], (a, s1), mo1, []. split; [exact H1|]. split; [exact H2 | reflexivity].
Qed.

Lemma tpath_msys : forall {A} n (dec : resp -> option A) (s : St) mo rsp a mo',
  nstep n mo rsp mo' [] -> dec rsp = Some a ->
  tpath nstep (msys n dec s) mo [] (Ok (a, s)) mo'.
Proof.
  intros A n dec s mo rsp a mo' Hst Hdec. unfold msys. apply (proj2 (tpath_enode _ _ _ _ _ _ _ _)).
  exists rsp. split; [exact Hst|]. rewrite Hdec. reflexivity.
Qed.

Lemma tpath_mget : forall (s : St) mo, tpath nstep (mget s) mo [] (Ok (s, s)) mo.
Proof. intros. cbn. repeat split; reflexivity. Qed.

Lemma tpath_mupd : forall (f : St -> St) (s : St) mo, tpath nstep (mupd f s) mo [] (Ok (tt, f s)) mo.
Proof. intros. cbn. repeat split; reflexivity. Qed.

End Plumbing.

Fixpoint mreal {R} (t : stree ev Z R) (zs : list Z) (s : PState) (mo : Model) (r : R) (s' : PState) (mo' : Model) {struct t} : Prop :=
  match t, zs with
  | SRet r0, [] => r0 = r /\ s' = s /\ mo' = mo
  | SVis e k, z :: zs' => exists s1 mo1, tpath nstep (ev_step e s) mo [] (Ok (z, s1)) mo1 /\ mreal (k z) zs' s1 mo1 r s' mo'
  | _, _ => False
  end.

Lemma mreal_membed : forall {R} (t : stree ev Z R) zs s mo r s' mo',
  mreal t zs s mo r s' mo' -> tpath nstep (membed t s) mo [] (Ok (r, s')) mo'.
Proof.
  intros R t. induction t as [r0 | e k IH]; intros zs s mo r s' mo' H.
  - destruct zs; cbn in H; [| destruct H]. destruct H as (-> & -> & ->). cbn. repeat split; reflexivity.
  - destruct zs as [| z zs]; cbn in H; [destruct H|]. destruct H as (s1 & mo1 & Hev & Hk).
    cbn [membed]. eapply tpath_mbind; [exact Hev|]. apply (IH z zs). exact Hk.
Qed.

Lemma mpath_raw_malloc : forall n s mo zs st' (p : option cptr) s1 mo',
  mreal (cmalloc (ps_m s) n) zs s mo (st', p) s1 mo' ->
  mpath (raw_malloc n) s mo
        (match p with Some slot => Some (slot, fresh_off st' slot n) | None => None end)
        (set_m st' s1) mo'.
Proof.
  intros n s mo zs st' p s1 mo' H. unfold mpath, raw_malloc.
  eapply tpath_mbind; [apply tpath_mget|].
  eapply tpath_mbind; [apply (mreal_membed _ _ _ _ _ _ _ H)|]. cbn beta iota.
  eapply tpath_mbind; [apply tpath_mupd|]. apply tpath_mret.
Qed.

Lemma mpath_raw_free : forall (p : bptr) s mo zs st' s1 mo',
  mreal (cfree (ps_m s) (Some (fst p))) zs s mo st' s1 mo' ->
  mpath (raw_free p) s mo tt (set_m st' s1) mo'.
Proof.
  intros p s mo zs st' s1 mo' H. unfold mpath, raw_free.
  eapply tpath_mbind; [apply tpath_mget|].
  eapply tpath_mbind; [apply (mreal_membed _ _ _ _ _ _ _ H)|]. cbn beta iota.
  apply tpath_mupd.
Qed.

Definition malloc_can_fail (s : PState) (mo : Model) (n : Z) : Prop :=
  exists s' mo', mpath (raw_malloc n) s mo None s' mo'.
Definition malloc_can_succeed (s : PState) (mo : Model) (n : Z) : Prop :=
  exists p s' mo', mpath (raw_malloc n) s mo (Some p) s' mo'.

Definition malloc_must_succeed (s : PState) (mo : Model) (n : Z) : Prop :=
  forall r s' mo', mpath (raw_malloc n) s mo r s' mo' -> r <> None.

Lemma ENOMEM_val : ENOMEM = 12. Proof. reflexivity. Qed.

Lemma ev_brk0_path : forall s mo,
  let b := vm_brk (m_vmmaps mo) in
  tpath nstep (ev_step (EBrk 0) s) mo [] (Ok (bv_unsigned b, set_brk_ps (bv_unsigned b) s))
        (with_brk_next mo (Z_to_bv 64 0) b).
Proof.
  intros s mo b. unfold ev_step. change (0 =? 0) with true. cbn iota.
  set (eff := mkEffectU b [] (brk_zeros (Z_to_bv 64 0) b b) (brk_unmaps b b) [] []).
  assert (Hst : nstep (NBrk 0) mo eff (with_brk_next mo (Z_to_bv 64 0) b) []).
  { apply (proj2 (NodesM.nstep_brk_inv 0 mo eff _ [])). exists b. split; [apply brk_r_ok_same|].
    split; [|split; [reflexivity | split; reflexivity]].
    intros Hrr. exfalso. unfold brk_refusal_b in Hrr. change (w_is0 (Z_to_bv 64 0)) with true in Hrr. cbn in Hrr. discriminate Hrr. }
  destruct (nstep_dec_brk0 _ _ _ _ Hst) as (_ & Hdec & _ & _).
  eapply (tpath_mbind _ _ s mo (bv_unsigned b) s); [eapply tpath_msys; [exact Hst | exact Hdec]|].
  eapply (tpath_mbind _ _ _ _ tt (set_brk_ps (bv_unsigned b) s)); [apply tpath_mupd | apply tpath_mret].
Qed.

Lemma brk_only_old : forall mo req,
  let h := m_vmmaps mo in
  w_is0 req = false -> bv_unsigned (min_brk h) <= bv_unsigned req -> bv_unsigned (vm_brk h) < bv_unsigned req ->
  brk_grow_ok mo req req = false ->
  forall r, brk_r_ok mo req r = true -> r = vm_brk h.
Proof.
  intros mo req h Hz Hmin Hgt Hg r Hr. unfold brk_r_ok in Hr. fold h in Hr. rewrite Hz in Hr.
  replace (bv_unsigned req <? bv_unsigned (min_brk h)) with false in Hr by (symmetry; apply Z.ltb_ge; lia).
  replace (bv_unsigned req <? bv_unsigned (vm_brk h)) with false in Hr by (symmetry; apply Z.ltb_ge; lia).
  cbn [orb] in Hr. apply andb_true_iff in Hr as [Hr Hgr].
  apply orb_true_iff in Hr as [E|E]; apply LinuxProcessSemantics.LinuxProcessSem.Fs.bv_eqb_eq in E; subst r.
  - congruence.
  - reflexivity.
Qed.

Lemma ev_brk_refuse_path : forall req s mo,
  let b := vm_brk (m_vmmaps mo) in
  0 < req < 2^64 -> ps_brk s = bv_unsigned b ->
  (forall r, brk_r_ok mo (Z_to_bv 64 req) r = true -> r = b) ->
  tpath nstep (ev_step (EBrk req) s) mo [] (Ok (ps_brk s, s)) (with_brk_next mo (Z_to_bv 64 req) b).
Proof.
  intros req s mo b Hreq Hps Honly. unfold ev_step. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn iota.
  set (eff := mkEffectU b [] (brk_zeros (Z_to_bv 64 req) b b) (brk_unmaps b b) [] []).
  assert (Hst : nstep (NBrk req) mo eff (with_brk_next mo (Z_to_bv 64 req) b) []).
  { apply (proj2 (NodesM.nstep_brk_inv req mo eff _ [])). exists b. split; [apply brk_r_ok_same|].
    split; [|split; [reflexivity | split; reflexivity]].
    intros Hrr r' Hr'. rewrite (Honly r' Hr'). exact Hrr. }
  assert (Hzs : brk_zeros (Z_to_bv 64 req) b b = []).
  { unfold brk_zeros, brk_is_grow. rewrite Z.ltb_irrefl, andb_false_r. reflexivity. }
  assert (Hus : brk_unmaps b b = []).
  { unfold brk_unmaps, brk_page_range. rewrite Z.ltb_irrefl. destruct (0 <? _)%Z; reflexivity. }
  assert (Hdec : dec_brk (ps_brk s) req eff = Some BrkSame).
  { unfold eff. rewrite Hzs, Hus. unfold dec_brk. cbn [eff_copies eff_copyins]. rewrite Hps, Z.eqb_refl. reflexivity. }
  eapply (tpath_mbind _ _ s mo s s); [apply tpath_mget|].
  eapply (tpath_mbind _ _ s mo BrkSame s); [eapply tpath_msys; [exact Hst | exact Hdec]|].
  cbn iota. apply tpath_mret.
Qed.

Lemma ev_brk_grow_path : forall req s mo,
  0 < bv_unsigned (vm_brk (m_vmmaps mo)) ->
  bv_unsigned (vm_start_brk (m_vmmaps mo)) <= bv_unsigned (vm_brk (m_vmmaps mo)) ->
  bv_unsigned (vm_brk (m_vmmaps mo)) < req < 2^64 ->
  ps_brk s = bv_unsigned (vm_brk (m_vmmaps mo)) ->
  brk_grow_ok mo (Z_to_bv 64 req) (Z_to_bv 64 req) = true ->
  tpath nstep (ev_step (EBrk req) s) mo [] (Ok (req, set_brk_ps req s))
        (with_brk_next mo (Z_to_bv 64 req) (Z_to_bv 64 req)).
Proof.
  intros req s mo Hb Hsb Hreq Hps Hg. unfold ev_step. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn iota.
  assert (Hok : brk_r_ok mo (Z_to_bv 64 req) (Z_to_bv 64 req) = true).
  { unfold brk_r_ok. cbv zeta. rewrite w_is0_lit by lia.
    replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    unfold min_brk. rewrite unsigned_lit by lia.
    replace (req <? bv_unsigned (vm_start_brk (m_vmmaps mo))) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (req <? bv_unsigned (vm_brk (m_vmmaps mo))) with false by (symmetry; apply Z.ltb_ge; lia).
    cbn [orb]. rewrite bv_eqb_refl. cbn [orb andb]. exact Hg. }
  assert (Hst : nstep (NBrk req) mo
                  (mkEffectU (Z_to_bv 64 req) [] (brk_zeros (Z_to_bv 64 req) (Z_to_bv 64 req) (vm_brk (m_vmmaps mo)))
                     (brk_unmaps (Z_to_bv 64 req) (vm_brk (m_vmmaps mo))) [] [])
                  (with_brk_next mo (Z_to_bv 64 req) (Z_to_bv 64 req)) []).
  { apply (proj2 (NodesM.nstep_brk_inv req mo _ _ [])). exists (Z_to_bv 64 req). split; [exact Hok|].
    split; [|split; [reflexivity | split; reflexivity]].
    intros Hrr. exfalso. unfold brk_refusal_b in Hrr. cbv zeta in Hrr.
    apply andb_true_iff in Hrr as [_ Hrr]. apply LinuxProcessSemantics.LinuxProcessSem.Fs.bv_eqb_eq in Hrr. apply (f_equal bv_unsigned) in Hrr.
    rewrite unsigned_lit in Hrr by lia. lia. }
  destruct (nstep_dec_brk req mo _ _ [] Hb Hsb ltac:(lia) Hst) as (_ & _ & a & Hdec & Ha).
  destruct a.
  - eapply (tpath_mbind _ _ s mo s s); [apply tpath_mget|].
    eapply (tpath_mbind _ _ s mo BrkGrown s); [eapply tpath_msys; [exact Hst | rewrite Hps; exact Hdec]|].
    cbn iota. eapply (tpath_mbind _ _ _ _ tt (set_brk_ps req s)); [apply tpath_mupd | apply tpath_mret].
  - exfalso. rewrite m_vmmaps_with_brk_next in Ha.
    destruct (brk_model_next_grown (m_vmmaps mo) req Hb Hreq) as (_ & _ & _ & _ & P5).
    rewrite P5 in Ha. apply (f_equal bv_unsigned) in Ha. rewrite unsigned_lit in Ha by lia. lia.
Qed.

Lemma ev_mmap_fixed_guard_path : forall a s mo,
  0 < a -> a + PGSZ <= alloc_ceiling -> a mod 4096 = 0 -> ceil_ok (m_vmmaps mo) ->
  region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 PGSZ) = true ->
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 PGSZ) = true ->
  exists mo', tpath nstep (ev_step (EMmap a PGSZ PROT_NONE MAPFX) s) mo [] (Ok (a, s)) mo'.
Proof.
  intros a s mo Ha Hc Hal Hceil Hrf Hmc. pose_ceil. pose proof Hceil as Hceil'. unfold ceil_ok in Hceil'.
  set (h := m_vmmaps mo) in *. set (aw := Z_to_bv 64 a) in *. set (n := Z_to_bv 64 PGSZ) in *.
  assert (Haw : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; unfold PGSZ in *; lia).
  set (mo' := with_mmap_replacement (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED)) aw n
                (with_vmmaps (mkVmMapsFull (vm_reserved h) (vm_maps h)
                   ((aw, n) :: maps_subtract (vm_noaccess h) (bv_unsigned aw) (bv_unsigned aw + bv_unsigned n))
                   (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo)).
  pose proof (nstep_mmap_fixed_inv0 a PGSZ mo (mkEffectU aw [] [] [(aw, n)] [] []) mo' []) as INV. cbv zeta in INV.
  rewrite (unsigned_lit PGSZ) in INV by (unfold PGSZ; lia). change (page_round_up_Z PGSZ) with PGSZ in INV. fold aw n h in INV.
  specialize (INV eq_refl ltac:(rewrite Haw; lia) ltac:(rewrite Haw; change page_size with 4096; exact Hal) ltac:(rewrite Haw; lia) Hrf Hmc).
  assert (Hst : nstep (NMmap a PGSZ PROT_NONE MAPFX) mo (mkEffectU aw [] [] [(aw, n)] [] []) mo' []).
  { apply (proj2 INV). split; [reflexivity|]. right; left. split; reflexivity. }
  assert (Hd : dec_mmap_fixed a PGSZ (mkEffectU aw [] [] [(aw, n)] [] []) = Some FxDone).
  { unfold dec_mmap_fixed; cbn [eff_copies eff_copyins]. change (mmap_len PGSZ) with PGSZ. fold n. subst aw n. rewrite !bv_eqb_refl. cbn [andb].
    rewrite errno_of_small by (rewrite Haw; unfold PGSZ in *; lia). rewrite ?bv_eqb_refl. reflexivity. }
  exists mo'. unfold ev_step. change (negb (Z.land MAPFX MAP_FIXED_Z =? 0)) with true. cbn iota.
  eapply (tpath_mbind _ _ s mo FxDone s); [eapply tpath_msys; [exact Hst | exact Hd]|]. apply tpath_mret.
Qed.

Definition grant_ok (mo : Model) (a : word) (nZ : Z) : Prop :=
  let h := m_vmmaps mo in
  bv_unsigned a mod page_size = 0 /\ 0 < bv_unsigned a /\ bv_unsigned a + nZ <= alloc_top h
  /\ region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true
  /\ vm_backing_used mo + nZ <= vm_limit h.

Lemma ev_mmap_grant_path : forall len prot s mo (a : word),
  let h := m_vmmaps mo in let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  0 < len -> nZ < 2^64 -> (prot = PROT_RW \/ prot = Malloc.PROT_NONE) -> mo_ok mo -> ceil_ok h ->
  grant_ok mo a nZ ->
  exists mo', tpath nstep (ev_step (EMmap 0 len prot (Malloc.MAP_PRIVATE + MAP_ANON)) s) mo [] (Ok (bv_unsigned a, s)) mo'
    /\ mo_ok mo' /\ vm_agree mo mo'
    /\ vm_maps (m_vmmaps mo') = (a, n) :: vm_maps h /\ vm_brk (m_vmmaps mo') = vm_brk h
    /\ region_free (vm_reserved h ++ vm_maps h) a n = true.
Proof.
  intros len prot s mo a h nZ n Hlen HnZ Hprot Hmo Hck Hg.
  pose proof Hg as (G1 & G2 & G3 & G4 & G5). fold h in G3, G4, G5 |- *.
  assert (Hnr : mmap_noreserve_b (Z_to_bv 64 (Malloc.MAP_PRIVATE + MAP_ANON)) = false) by reflexivity.
  assert (Hbk : mmap_noreserve_backed_ok (Z_to_bv 64 (Malloc.MAP_PRIVATE + MAP_ANON)) mo nZ = true).
  { unfold mmap_noreserve_backed_ok. rewrite Hnr. apply Z.leb_le. exact G5. }
  assert (Hge : len <= nZ) by (unfold nZ, page_round_up_Z, page_size; lia).
  assert (HlenU : bv_unsigned (Z_to_bv 64 len) = len).
  { rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn [Z.of_N Z.pow_pos Pos.iter Z.mul Pos.mul]. lia. }
  assert (Hw : w_is0 (Z_to_bv 64 len) = false) by (rewrite w_is0_lit by lia; apply Z.eqb_neq; lia).
  unfold ev_step. change (negb (Z.land (Malloc.MAP_PRIVATE + MAP_ANON) MAP_FIXED_Z =? 0)) with false. cbn iota.
  destruct Hprot as [-> | ->].
  - change (PROT_RW =? 0) with false. cbn iota.
    set (mo' := with_mmap_backing (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)) a n
                  (with_vmmaps (mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h) (vm_noaccess h)
                                 (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo)).
    set (eff := mkEffect a [] [(a, n)]).
    assert (Hst : nstep (NMmap 0 len PROT_RW (Malloc.MAP_PRIVATE + MAP_ANON)) mo eff mo' []).
    { apply (proj2 (nstep_mmap_rw_inv 0 len mo eff mo' [] Hw)). split; [reflexivity|]. right.
      exists a. rewrite HlenU. fold h nZ n. split; [| split; reflexivity]. repeat split; assumption. }
    destruct (nstep_dec_mmap len [] mo eff mo' [] Hlen ltac:(unfold mmap_len; exact HnZ) Hck ltac:(constructor) Hst)
      as (_ & VA & x & Hdec & Hx).
    assert (Hx' : x = MmOk (bv_unsigned a)).
    { unfold eff, dec_mmap in Hdec. cbn [eff_copies eff_copyins] in Hdec. rewrite !bv_eqb_refl in Hdec.
      destruct (mmap_addr_ok len [] (bv_unsigned a)); cbn [andb] in Hdec; congruence. }
    subst x. destruct Hx as (_ & _ & Hvm).
    exists mo'. split; [| split; [exact (vm_agree_mo_ok _ _ VA Hmo) | split; [exact VA | split; [| split]]]].
    + eapply (tpath_mbind _ _ s mo (MmOk (bv_unsigned a)) s); [eapply tpath_msys; [exact Hst | exact Hdec] | apply tpath_mret].
    + unfold mo'. rewrite with_mmap_backing_noreserve_false by exact Hnr. reflexivity.
    + unfold mo'. rewrite with_mmap_backing_noreserve_false by exact Hnr. reflexivity.
    + exact G4.
  - change (Malloc.PROT_NONE =? 0) with true. cbn iota.
    set (mo' := with_mmap_backing (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)) a n
                  (with_vmmaps (mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h) ((a, n) :: vm_noaccess h)
                                 (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo)).
    set (eff := mkEffectU a [] [] [(a, n)] [] []).
    assert (Hst : nstep (NMmap 0 len Malloc.PROT_NONE (Malloc.MAP_PRIVATE + MAP_ANON)) mo eff mo' []).
    { apply (proj2 (nstep_mmap_none_inv 0 len mo eff mo' [] Hw)). split; [reflexivity|]. right.
      exists a. rewrite HlenU. fold h nZ n. split; [| split; reflexivity]. repeat split; assumption. }
    destruct (nstep_dec_mmap_none len [] mo eff mo' [] Hlen ltac:(unfold mmap_len; exact HnZ) Hck ltac:(constructor) Hst)
      as (_ & VA & x & Hdec & Hx).
    assert (Hx' : x = MmOk (bv_unsigned a)).
    { unfold eff, dec_mmap_none in Hdec. cbn [eff_copies eff_copyins] in Hdec. rewrite !bv_eqb_refl in Hdec.
      destruct (mmap_addr_ok len [] (bv_unsigned a)); cbn [andb] in Hdec; congruence. }
    subst x. destruct Hx as (_ & _ & Hvm).
    exists mo'. split; [| split; [exact (vm_agree_mo_ok _ _ VA Hmo) | split; [exact VA | split; [| split]]]].
    + eapply (tpath_mbind _ _ s mo (MmOk (bv_unsigned a)) s); [eapply tpath_msys; [exact Hst | exact Hdec] | apply tpath_mret].
    + unfold mo'. rewrite with_mmap_backing_noreserve_false by exact Hnr. reflexivity.
    + unfold mo'. rewrite with_mmap_backing_noreserve_false by exact Hnr. reflexivity.
    + exact G4.
Qed.

Lemma is_errno_form_neg_errno : forall e, 1 <= e <= 4095 -> is_errno_form (neg_errno e) = true.
Proof. intros e He. unfold is_errno_form, neg_errno, TWO64. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. Qed.

Lemma is_err_neg_errno : forall e, 1 <= e <= 4095 -> is_err (neg_errno e) = true.
Proof. intros e He. unfold is_err, neg_errno, TWO64. apply Z.ltb_lt. lia. Qed.

End CEIL.
