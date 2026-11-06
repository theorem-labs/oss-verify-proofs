(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState Mem ITree Nodes NodesM Decode DecodeM.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import Prelim STree Malloc MallocCtrl KInv.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Monad MSafe Prog KLink KStep KOwn PgArith A_MallocBlocks.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require MI_Contracts.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import RelSpec.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import StateGlue NodeSound TreeBridgeN KRel MPath Room.

Set Keyed Unification.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Section Inv.
Context {St : Type}.

Lemma tpath_mbind_inv : forall {A B} (m : Monad.M St A) (f : A -> Monad.M St B) s mo r mo',
  tpath nstep (mbind m f s) mo [] (Ok r) mo' ->
  exists a s1 mo1, tpath nstep (m s) mo [] (Ok (a, s1)) mo1 /\ tpath nstep (f a s1) mo1 [] (Ok r) mo'.
Proof.
  intros A B m f s mo r mo' H. unfold mbind in H. apply (proj1 (tpath_ebind _ _ _ _ _ _ _ _)) in H.
  destruct H as [[_ E] | (tr1 & [a s1] & mo1 & tr2 & H1 & H2 & E)]; [discriminate|].
  destruct tr1; [| discriminate]. destruct tr2; [| discriminate]. exists a, s1, mo1. auto.
Qed.

Lemma tpath_msys_inv : forall {A} n (dec : resp -> option A) (s : St) mo a s' mo',
  tpath nstep (msys n dec s) mo [] (Ok (a, s')) mo' ->
  s' = s /\ exists rsp, nstep n mo rsp mo' [] /\ dec rsp = Some a.
Proof.
  intros A n dec s mo a s' mo' H. unfold msys in H. apply (proj1 (tpath_enode _ _ _ _ _ _ _ _)) in H.
  destruct H as (rsp & Hst & E). destruct (dec rsp) as [a'|] eqn:D; [| discriminate].
  inversion E; subst. split; [reflexivity|]. exists rsp. auto.
Qed.

Lemma tpath_mret_inv : forall {A} (a : A) (s : St) mo r mo',
  tpath nstep (mret a s) mo [] r mo' -> r = Ok (a, s) /\ mo' = mo.
Proof. intros A a s mo r mo' H. cbn in H. destruct H as (<- & -> & _). auto. Qed.

Lemma tpath_mget_inv : forall (s : St) mo r mo', tpath nstep (mget s) mo [] r mo' -> r = Ok (s, s) /\ mo' = mo.
Proof. intros s mo r mo' H. cbn in H. destruct H as (<- & -> & _). auto. Qed.

Lemma tpath_mupd_inv : forall (f : St -> St) (s : St) mo r mo', tpath nstep (mupd f s) mo [] r mo' -> r = Ok (tt, f s) /\ mo' = mo.
Proof. intros f s mo r mo' H. cbn in H. destruct H as (<- & -> & _). auto. Qed.

Lemma tpath_munr_inv : forall {A} (s : St) mo (a : A * St) mo', tpath nstep (munr (A:=A) s) mo [] (Ok a) mo' -> False.
Proof. intros A s mo a mo' H. cbn in H. destruct H as (E & _). discriminate. Qed.

End Inv.

Definition enode_of (e : ev) : option node :=
  match e with
  | EBrk req => Some (NBrk req)
  | EMmap a len prot flags => Some (NMmap a len prot flags)
  | EMunmap a len => Some (NMunmap a len)
  | EMprotect a len prot => Some (NMprotect a len prot)
  | _ => None
  end.

Lemma ev_step_inv : forall e s mo z s1 mo1,
  tpath nstep (ev_step e s) mo [] (Ok (z, s1)) mo1 ->
  exists n rsp, enode_of e = Some n /\ nstep n mo rsp mo1 [] /\ ps_m s1 = ps_m s /\ ps_fa s1 = ps_fa s /\ ps_so s1 = ps_so s.
Proof.
  intros e s mo z s1 mo1 H. destruct e as [req | a len prot flags | a len | a len prot | p c h | w]; cbn [enode_of].
  - unfold ev_step in H. destruct (Z.eqb_spec req 0) as [-> | Hne].
    + apply tpath_mbind_inv in H as (r & s2 & mo2 & H1 & H2).
      apply tpath_msys_inv in H1 as (-> & rsp & Hst & _).
      apply tpath_mbind_inv in H2 as (u & s3 & mo3 & H2 & H3).
      apply tpath_mupd_inv in H2 as [E ->]. inversion E; subst.
      apply tpath_mret_inv in H3 as [E3 ->]. inversion E3; subst.
      exists (NBrk 0), rsp. split; [reflexivity|]. split; [exact Hst|]. cbn [ps_m ps_fa ps_so set_brk_ps]. repeat split; reflexivity.
    + apply tpath_mbind_inv in H as (s' & s2 & mo2 & H1 & H2).
      apply tpath_mget_inv in H1 as [E0 ->]. inversion E0; subst.
      apply tpath_mbind_inv in H2 as (ans & s3 & mo3 & H2 & H3).
      apply tpath_msys_inv in H2 as (-> & rsp & Hst & _).
      exists (NBrk req), rsp. split; [reflexivity|].
      destruct ans.
      * apply tpath_mbind_inv in H3 as (u & s4 & mo4 & H3 & H4).
        apply tpath_mupd_inv in H3 as [E5 ->]. inversion E5; subst.
        apply tpath_mret_inv in H4 as [E4 ->]. inversion E4; subst. split; [exact Hst|]. cbn [ps_m ps_fa ps_so set_brk_ps]. repeat split; reflexivity.
      * apply tpath_mret_inv in H3 as [E3 ->]. inversion E3; subst. split; [exact Hst|]. repeat split; reflexivity.
  - unfold ev_step in H.
    destruct (negb (Z.land flags MAP_FIXED_Z =? 0)); [| destruct (prot =? 0)];
      apply tpath_mbind_inv in H as (ans & s2 & mo2 & H1 & H2);
      apply tpath_msys_inv in H1 as (-> & rsp & Hst & _);
      apply tpath_mret_inv in H2 as [E ->]; inversion E; subst;
      exists (NMmap a len prot flags), rsp; (split; [reflexivity|]); (split; [exact Hst|]); repeat split; reflexivity.
  - unfold ev_step in H.
    apply tpath_mbind_inv in H as (ans & s2 & mo2 & H1 & H2).
    apply tpath_msys_inv in H1 as (-> & rsp & Hst & _).
    apply tpath_mret_inv in H2 as [E ->]; inversion E; subst.
    exists (NMunmap a len), rsp. split; [reflexivity|]. split; [exact Hst|]. repeat split; reflexivity.
  - unfold ev_step in H.
    apply tpath_mbind_inv in H as (ans & s2 & mo2 & H1 & H2).
    apply tpath_msys_inv in H1 as (-> & rsp & Hst & _).
    apply tpath_mret_inv in H2 as [E ->]; inversion E; subst.
    exists (NMprotect a len prot), rsp. split; [reflexivity|]. split; [exact Hst|]. repeat split; reflexivity.
  - exfalso. unfold ev_step in H. exact (tpath_munr_inv _ _ _ _ H).
  - exfalso. unfold ev_step in H. exact (tpath_munr_inv _ _ _ _ H).
Qed.

Definition esize (e : ev) : Z :=
  match e with
  | EMmap _ len _ _ => Z.max 0 (page_round_up_Z len)
  | EBrk _ => 3 * PGSZ
  | _ => 0
  end.

Lemma live_bytes_app : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. induction l1 as [|[a n] l1 IH]; intros l2; cbn [live_bytes app]; [reflexivity | rewrite IH; lia]. Qed.

Lemma live_bytes_nonneg : forall l, 0 <= live_bytes l.
Proof. induction l as [|[a n] l IH]; cbn [live_bytes]; [lia|]. pose proof (bv_unsigned_in_range 64 n). lia. Qed.

Lemma live_bytes_filter : forall f l, live_bytes (List.filter f l) <= live_bytes l.
Proof.
  induction l as [|[a n] l IH]; cbn [live_bytes List.filter]; [lia|].
  pose proof (bv_unsigned_in_range 64 n). destruct (f (a, n)); cbn [live_bytes]; lia.
Qed.

Lemma length_filter_le : forall {A} (f : A -> bool) l, (length (List.filter f l) <= length l)%nat.
Proof. induction l as [|x l IH]; cbn; [lia|]. destruct (f x); cbn; lia. Qed.

Lemma sizes_le_filter : forall B f l, sizes_le B l -> sizes_le B (List.filter f l).
Proof.
  intros B f l H. unfold sizes_le in *. induction l as [|x l IH]; cbn; [constructor|].
  inversion H; subst. destruct (f x); [constructor; auto|]. apply IH; auto.
Qed.

Lemma iv_subtract_length : forall a sz lo hi, (length (iv_subtract a sz lo hi) <= 2)%nat.
Proof. intros. unfold iv_subtract. destruct (_ <? _); destruct (_ <? _); cbn; lia. Qed.

Lemma iv_subtract_length1 : forall a sz lo hi,
  ~ (bv_unsigned a < lo /\ hi < bv_unsigned a + bv_unsigned sz) -> (length (iv_subtract a sz lo hi) <= 1)%nat.
Proof.
  intros a sz lo hi H. unfold iv_subtract.
  destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn; lia.
Qed.

Lemma iv_subtract_live : forall a sz lo hi, lo < hi -> live_bytes (iv_subtract a sz lo hi) <= bv_unsigned sz.
Proof.
  intros a sz lo hi Hlh. pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
  unfold iv_subtract.
  destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn [live_bytes app];
    rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N Z.pow_pos Pos.iter Z.mul Pos.mul].
  - assert (E1 : (Z.min (bv_unsigned sz) (lo - bv_unsigned a)) mod 18446744073709551616 = Z.min (bv_unsigned sz) (lo - bv_unsigned a)) by (apply Z.mod_small; lia).
    assert (E2 : (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi) mod 18446744073709551616 = bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi) by (apply Z.mod_small; lia).
    rewrite E1, E2. lia.
  - assert (E1 : (Z.min (bv_unsigned sz) (lo - bv_unsigned a)) mod 18446744073709551616 = Z.min (bv_unsigned sz) (lo - bv_unsigned a)) by (apply Z.mod_small; lia).
    rewrite E1. lia.
  - assert (E2 : (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi) mod 18446744073709551616 = bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi) by (apply Z.mod_small; lia).
    rewrite E2. lia.
  - lia.
Qed.

Lemma iv_subtract_sizes : forall B a sz lo hi, lo < hi -> bv_unsigned sz <= B -> sizes_le B (iv_subtract a sz lo hi).
Proof.
  intros B a sz lo hi Hlh Hsz. pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
  unfold iv_subtract, sizes_le.
  destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn [app];
    repeat constructor; cbn [snd]; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N Z.pow_pos Pos.iter Z.mul Pos.mul];
    rewrite ?Z.mod_small by lia; lia.
Qed.

Lemma maps_subtract_live : forall maps lo hi, lo < hi -> live_bytes (maps_subtract maps lo hi) <= live_bytes maps.
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi Hlh; cbn [maps_subtract live_bytes]; [lia|].
  rewrite live_bytes_app. pose proof (iv_subtract_live a sz lo hi Hlh). specialize (IH lo hi Hlh). lia.
Qed.

Lemma maps_subtract_sizes : forall B maps lo hi, lo < hi -> sizes_le B maps -> sizes_le B (maps_subtract maps lo hi).
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi Hlh H; cbn [maps_subtract]; [constructor|].
  inversion H; subst. unfold sizes_le. apply Forall_app. split; [apply iv_subtract_sizes; auto | apply IH; auto].
Qed.

Lemma maps_subtract_length0 : forall maps lo hi,
  (forall e, In e maps -> ~ (elo e < lo /\ hi < ehi e)) ->
  (length (maps_subtract maps lo hi) <= length maps)%nat.
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi H; cbn [maps_subtract length]; [lia|].
  rewrite length_app. pose proof (iv_subtract_length1 a sz lo hi (H (a, sz) (or_introl eq_refl))) as H1.
  specialize (IH lo hi (fun e He => H e (or_intror He))). lia.
Qed.

Lemma maps_subtract_length1 : forall maps lo hi, pwdisj maps -> lo < hi ->
  (length (maps_subtract maps lo hi) <= S (length maps))%nat.
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi Hpw Hlh; cbn [maps_subtract length]; [lia|].
  inversion Hpw as [| e l Hd Hpw']; subst. rewrite length_app.
  destruct (Z_lt_dec (bv_unsigned a) lo) as [H1|H1]; [destruct (Z_lt_dec hi (bv_unsigned a + bv_unsigned sz)) as [H2|H2]|].
  -
    pose proof (iv_subtract_length a sz lo hi).
    assert (Hrest : (length (maps_subtract maps lo hi) <= length maps)%nat).
    { apply maps_subtract_length0. intros e' He' [A1 A2]. specialize (Hd e' He'). unfold edisj, elo, ehi in *. cbn [fst snd] in Hd. lia. }
    lia.
  - pose proof (iv_subtract_length1 a sz lo hi ltac:(lia)). specialize (IH lo hi Hpw' Hlh). lia.
  - pose proof (iv_subtract_length1 a sz lo hi ltac:(lia)). specialize (IH lo hi Hpw' Hlh). lia.
Qed.

Record mstep (E : Z) (mo mo1 : Model) : Prop := MSTEP {
  ms_count : (length (vmaps mo1) <= S (length (vmaps mo)))%nat;
  ms_live  : vm_live_bytes (m_vmmaps mo1) <= vm_live_bytes (m_vmmaps mo) + E;
  ms_sizes : forall B, E <= B -> sizes_le B (vmaps mo) -> sizes_le B (vmaps mo1);
  ms_limit : vm_limit (m_vmmaps mo1) = vm_limit (m_vmmaps mo) }.

Lemma mstep_mono : forall E E' mo mo1, E <= E' -> mstep E mo mo1 -> mstep E' mo mo1.
Proof. intros E E' mo mo1 HE [A B C D]. constructor; auto; [lia|]. intros BB H1 H2. apply C; [lia | exact H2]. Qed.

Lemma mstep_same : forall E mo mo1, 0 <= E -> m_vmmaps mo1 = m_vmmaps mo -> mstep E mo mo1.
Proof.
  intros E mo mo1 HE Hvm. constructor; unfold vmaps; rewrite ?Hvm; auto; lia.
Qed.

Lemma mstep_same_maps : forall E mo mo1, 0 <= E ->
  vm_reserved (m_vmmaps mo1) = vm_reserved (m_vmmaps mo) -> vm_maps (m_vmmaps mo1) = vm_maps (m_vmmaps mo) ->
  vm_limit (m_vmmaps mo1) = vm_limit (m_vmmaps mo) -> mstep E mo mo1.
Proof.
  intros E mo mo1 HE Hr Hm Hl. constructor; unfold vmaps, vm_live_bytes; rewrite ?Hr, ?Hm, ?Hl; auto; lia.
Qed.

Lemma mstep_cons_map : forall E mo mo1 x n,
  0 <= bv_unsigned n <= E ->
  vm_reserved (m_vmmaps mo1) = vm_reserved (m_vmmaps mo) ->
  vm_maps (m_vmmaps mo1) = (x, n) :: vm_maps (m_vmmaps mo) ->
  vm_limit (m_vmmaps mo1) = vm_limit (m_vmmaps mo) ->
  mstep E mo mo1.
Proof.
  intros E mo mo1 x n Hn Hr Hm Hl. constructor; unfold vmaps, vm_live_bytes; rewrite ?Hr, ?Hm, ?Hl.
  - rewrite !length_app. cbn [length]. lia.
  - cbn [live_bytes]. lia.
  - intros B HB Hs. unfold sizes_le in *. apply Forall_app in Hs as [H1 H2]. apply Forall_app. split; [exact H1|]. constructor; [cbn [snd]; lia | exact H2].
  - reflexivity.
Qed.

Lemma mstep_mmap_anon : forall len prot mo rsp mo1,
  0 < len < 2 ^ 63 -> (prot = PROT_RW \/ prot = Malloc.PROT_NONE) ->
  nstep (NMmap 0 len prot MAPF) mo rsp mo1 [] -> mstep (page_round_up_Z len) mo mo1.
Proof.
  intros len prot mo rsp mo1 Hlen Hprot Hst.
  assert (HlenU : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  assert (Hw : w_is0 (Z_to_bv 64 len) = false) by (rewrite w_is0_lit by lia; apply Z.eqb_neq; lia).
  assert (Hn : bv_unsigned (Z_to_bv 64 (page_round_up_Z len)) = page_round_up_Z len).
  { apply unsigned_lit. unfold page_round_up_Z, page_size. lia. }
  destruct Hprot as [-> | ->].
  - apply (proj1 (nstep_mmap_rw_inv 0 len mo rsp mo1 [] Hw)) in Hst as [_ [(e & _ & _ & ->) | (a & _ & _ & ->)]].
    + apply mstep_same; [unfold page_round_up_Z, page_size; lia | reflexivity].
    + rewrite HlenU. rewrite with_mmap_backing_noreserve_false by reflexivity.
      eapply mstep_cons_map; [| reflexivity | reflexivity | reflexivity]. rewrite Hn. unfold page_round_up_Z, page_size; lia.
  - apply (proj1 (nstep_mmap_none_inv 0 len mo rsp mo1 [] Hw)) in Hst as [_ [(e & _ & _ & ->) | (a & _ & _ & ->)]].
    + apply mstep_same; [unfold page_round_up_Z, page_size; lia | reflexivity].
    + rewrite HlenU. rewrite with_mmap_backing_noreserve_false by reflexivity.
      eapply mstep_cons_map; [| reflexivity | reflexivity | reflexivity]. rewrite Hn. unfold page_round_up_Z, page_size; lia.
Qed.

Lemma mstep_mmap_fixed : forall addr len mo rsp mo1,
  nsafe (NMmap addr len Malloc.PROT_NONE MAPFX) mo -> vmwf (vm_maps (m_vmmaps mo)) -> 0 < len < 2 ^ 63 ->
  nstep (NMmap addr len Malloc.PROT_NONE MAPFX) mo rsp mo1 [] -> mstep (page_round_up_Z len) mo mo1.
Proof.
  intros addr len mo rsp mo1 Hs Hwf Hlen Hst.
  assert (Hpos : 0 <= page_round_up_Z len) by (unfold page_round_up_Z, page_size; lia).
  cbn [nsafe] in Hs. cbv zeta in Hs. destruct Hs as (Hw & _ & _ & [Hrw | [Hno | Hfx]]).
  - exfalso. unfold mmap_rw_shape in Hrw. vm_compute in Hrw. discriminate Hrw.
  - exfalso. destruct Hno as [_ Hno]. vm_compute in Hno. discriminate Hno.
  - destruct Hfx as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8).
    assert (HlenU : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
    rewrite HlenU in M4, M7, M8.
    assert (HnU : bv_unsigned (Z_to_bv 64 (page_round_up_Z len)) = page_round_up_Z len).
    { apply unsigned_lit. unfold page_round_up_Z, page_size. lia. }
    assert (Hnpos : 0 < page_round_up_Z len) by (unfold page_round_up_Z, page_size; lia).
    change MAPFX with (MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED) in Hst.
    change Malloc.PROT_NONE with PROT_NONE in Hst.
    pose proof (nstep_mmap_fixed_inv0 addr len mo rsp mo1 []) as INV.
    cbv zeta in INV. rewrite HlenU in INV. specialize (INV Hw M4 M5 M6 M7 M8).
    apply (proj1 INV) in Hst. clear INV.
    destruct Hst as [_ [(e & _ & _ & ->) | [(_ & ->) | (e & _ & _ & ->)]]].
    + apply mstep_same; [exact Hpos | reflexivity].
    + unfold with_mmap_replacement. rewrite with_mmap_backing_noreserve_false by reflexivity.
      apply mstep_same_maps; [exact Hpos | reflexivity | reflexivity | reflexivity].
    + rewrite HnU. constructor; unfold vmaps, vm_live_bytes; unfold with_mmap_destroyed;
        rewrite ?m_vmmaps_vm_forget_range, ?m_vmmaps_with_vmmaps; cbn [vm_reserved vm_maps vm_limit].
      * rewrite !length_app.
        pose proof (maps_subtract_length1 (vm_maps (m_vmmaps mo)) (bv_unsigned (Z_to_bv 64 addr))
                      (bv_unsigned (Z_to_bv 64 addr) + page_round_up_Z len) (proj2 Hwf) ltac:(lia)) as HL. lia.
      * apply Z.le_trans with (live_bytes (vm_maps (m_vmmaps mo))); [| lia]. apply maps_subtract_live. lia.
      * intros B HB Hsz. unfold sizes_le in *.
        apply Forall_app in Hsz as [H1 H2]. apply Forall_app. split; [exact H1|].
        apply maps_subtract_sizes; [lia | exact H2].
      * reflexivity.
Qed.

Lemma mstep_brk : forall L req s mo rsp mo1,
  event_pre L (EBrk req) -> KL L (ps_brk s) mo ->
  nstep (NBrk req) mo rsp mo1 [] -> mstep (3 * PGSZ) mo mo1.
Proof.
  intros L req s mo rsp mo1 Hpre HK Hst.
  apply (proj1 (NodesM.nstep_brk_inv req mo rsp mo1 [])) in Hst as (r & Hr & _ & -> & -> & _).
  pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4). pose proof (kl_phase _ _ _ HK) as PH.
  pose proof alloc_ceiling_lt as AC.
  set (h := m_vmmaps mo) in *. set (b := vm_brk h) in *.
  assert (CASES : r = b \/ (r = Z_to_bv 64 req /\ bv_unsigned b < req < 2^64 /\ req - bv_unsigned b <= 3 * PGSZ)).
  { cbn [event_pre] in Hpre. destruct Hpre as [[-> Hph] | [(cur & Hph & ->) | (b0 & l & Hph & Hreg & ->)]].
    - left. unfold brk_r_ok in Hr. change (w_is0 (Z_to_bv 64 0)) with true in Hr. cbn [orb] in Hr. apply bv_eqb_eq in Hr. exact Hr.
    - rewrite Hph in PH. destruct PH as (Ecur & Eb & _ & _).
      assert (Hreq : bv_unsigned b < round_up_pg cur + 2 * PGSZ < 2^64).
      { rewrite round_up_pg_aligned by (rewrite Ecur; unfold PGSZ in S2; exact S2). unfold PGSZ in *. lia. }
      destruct (brk_r_ok_grow mo _ r ltac:(fold h b; lia) Hreq Hr) as [-> | [-> _]]; [left; reflexivity | right].
      split; [reflexivity|]. split; [exact Hreq|]. rewrite round_up_pg_aligned by (rewrite Ecur; unfold PGSZ in S2; exact S2). unfold PGSZ in *. lia.
    - rewrite Hph in PH. destruct PH as (b1 & l1 & Hreg1 & Eb & _). rewrite Hreg in Hreg1. inversion Hreg1; subst b1 l1.
      pose proof (kl_brkreg _ _ _ HK b0 l Hreg) as (R1 & R2 & R3 & R4 & R5 & R6). fold h in Eb.
      assert (Hreq : bv_unsigned b < b0 + l + PGSZ < 2^64) by (unfold PGSZ in *; lia).
      destruct (brk_r_ok_grow mo _ r ltac:(fold h b; lia) Hreq Hr) as [-> | [-> _]]; [left; reflexivity | right].
      split; [reflexivity|]. split; [exact Hreq|]. unfold PGSZ in *. lia. }
  destruct CASES as [-> | (-> & Hreq & Hle)].
  - destruct (brk_model_next_same h (Z_to_bv 64 req)) as (E1 & E2 & _ & _ & _).
    apply mstep_same_maps; [unfold PGSZ; lia | | |]; unfold h in *; rewrite m_vmmaps_with_brk_next; [exact E1 | exact E2 | reflexivity].
  - destruct (brk_model_next_grown h req ltac:(unfold b in *; lia) Hreq) as (E1 & E2 & _).
    eapply mstep_cons_map; unfold h in *; rewrite ?m_vmmaps_with_brk_next; [| exact E1 | exact E2 | reflexivity].
    rewrite unsigned_lit by (unfold b, PGSZ in *; lia). unfold b in *. lia.
Qed.

Lemma mstep_munmap : forall addr len mo rsp mo1,
  nsafe (NMunmap addr len) mo -> nstep (NMunmap addr len) mo rsp mo1 [] -> mstep 0 mo mo1.
Proof.
  intros addr len mo rsp mo1 Hs Hst. cbn [nsafe] in Hs. cbv zeta in Hs. destruct Hs as (C1 & C2 & C3 & C4).
  pose proof (nstep_munmap_inv addr len mo rsp mo1 []) as INV. cbv zeta in INV. specialize (INV C1 C2 C3 C4).
  apply (proj1 INV) in Hst as (_ & -> & ->). clear INV.
  constructor; unfold vmaps, vm_live_bytes; rewrite m_vmmaps_with_mmap_destroyed; cbn [vm_reserved vm_maps vm_limit]; unfold map_remove.
  - rewrite !length_app. pose proof (length_filter_le (fun p : word * word => negb (bv_eqb (fst p) (Z_to_bv 64 addr))) (vm_maps (m_vmmaps mo))). lia.
  - pose proof (live_bytes_filter (fun p : word * word => negb (bv_eqb (fst p) (Z_to_bv 64 addr))) (vm_maps (m_vmmaps mo))). lia.
  - intros B HB Hsz. unfold sizes_le in *. apply Forall_app in Hsz as [H1 H2]. apply Forall_app. split; [exact H1 | apply sizes_le_filter; exact H2].
  - reflexivity.
Qed.

Lemma mstep_mprotect : forall addr len prot mo rsp mo1,
  nsafe (NMprotect addr len prot) mo -> nstep (NMprotect addr len prot) mo rsp mo1 [] -> mstep 0 mo mo1.
Proof.
  intros addr len prot mo rsp mo1 Hs Hst. cbn [nsafe] in Hs. cbv zeta in Hs. destruct Hs as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
  pose proof (nstep_mprotect_inv addr len prot mo rsp mo1 []) as INV. cbv zeta in INV. specialize (INV C1 C2 C3 C4 C5 C6 C7).
  apply (proj1 INV) in Hst as [_ [(e & _ & _ & ->) | (_ & _ & ->)]]; clear INV.
  - apply mstep_same; [lia | reflexivity].
  - apply mstep_same_maps; [lia | | |]; rewrite m_vmmaps_mprotect_model_next; reflexivity.
Qed.

Lemma ev_step_nsafe : forall e s mo P n,
  MSafe.twf (ev_step e s) mo P -> enode_of e = Some n -> nsafe n mo.
Proof.
  intros e s mo P n W Hn. destruct e as [req | a len prot flags | a len | a len prot | p c h | w]; cbn [enode_of] in Hn;
    try discriminate; inversion Hn; subst n; unfold ev_step in W.
  - destruct (req =? 0); [destruct W as [Hs _]; exact Hs|]. destruct W as [Hs _]. exact Hs.
  - destruct (negb (Z.land flags MAP_FIXED_Z =? 0)); [| destruct (prot =? 0)]; destruct W as [Hs _]; exact Hs.
  - destruct W as [Hs _]. exact Hs.
  - destruct W as [Hs _]. exact Hs.
Qed.

Theorem kev_measure : forall L e s mo z s1 mo1,
  event_pre L e -> KL L (ps_brk s) mo -> mo_ok mo ->
  tpath nstep (ev_step e s) mo [] (Ok (z, s1)) mo1 ->
  answer_ok L e z = true /\ KL (event_post L e z) (ps_brk s1) mo1 /\ ps_m s1 = ps_m s /\ ps_fa s1 = ps_fa s /\ ps_so s1 = ps_so s
  /\ mo_ok mo1 /\ vm_agree mo mo1 /\ mstep (esize e) mo mo1.
Proof.
  intros L e s mo z s1 mo1 Hpre HK Hmo Htp.
  pose proof (ev_step_spec L e GT s frame_ok_GT Hpre s mo (conj eq_refl (conj HK I))) as W.
  pose proof (twf_tpath _ _ _ _ _ _ W Htp) as (Hok & HK1 & _ & Hm & Hfa & Hso). cbn [fst snd] in Hok, HK1, Hm, Hfa, Hso.
  destruct (ev_step_inv e s mo z s1 mo1 Htp) as (n & rsp & Hn & Hst & _).
  pose proof (ev_step_nsafe e s mo _ n W Hn) as Hsafe.
  destruct (NmodelM n mo rsp mo1 [] Hsafe Hmo Hst) as (_ & Hmo1 & Hva).
  split; [exact Hok|]. split; [exact HK1|]. split; [exact Hm|]. split; [exact Hfa|]. split; [exact Hso|].
  split; [exact Hmo1|]. split; [exact Hva|].
  destruct e as [req | a len prot flags | a len | a len prot | p c h | w]; cbn [enode_of] in Hn; try discriminate;
    inversion Hn; subst n; cbn [esize].
  - eapply mstep_brk; eassumption.
  - cbn [event_pre] in Hpre. destruct Hpre as [(Hq & -> & -> & Hprot & Hlen) | (cur & Hph & -> & -> & -> & ->)].
    + eapply mstep_mono; [apply Z.le_max_r|]. eapply mstep_mmap_anon; [| | exact Hst]; unfold LEN_MAX in Hlen; [lia | destruct Hprot as [-> | ->]; auto].
    + eapply mstep_mono; [apply Z.le_max_r|]. eapply mstep_mmap_fixed; [exact Hsafe | exact (kl_wf _ _ _ HK) | unfold PGSZ; lia | exact Hst].
  - eapply mstep_munmap; eassumption.
  - eapply mstep_mprotect; eassumption.
Qed.

Fixpoint okpath {R} (L : mled) (t : Malloc.M R) (zs : list Z) {struct t} : Prop :=
  match t, zs with
  | SRet _, [] => True
  | SVis e k, z :: zs' => answer_ok L e z = true /\ okpath (event_post L e z) (k z) zs'
  | _, _ => False
  end.

Fixpoint evs_of {R} (t : Malloc.M R) (zs : list Z) {struct t} : list ev :=
  match t, zs with
  | SVis e k, z :: zs' => e :: evs_of (k z) zs'
  | _, _ => []
  end.

Fixpoint esum (es : list ev) : Z := match es with [] => 0 | e :: es' => esize e + esum es' end.

Record msteps (k : nat) (E : Z) (mo mo1 : Model) : Prop := MSTEPS {
  mss_count : (length (vmaps mo1) <= k + length (vmaps mo))%nat;
  mss_live  : vm_live_bytes (m_vmmaps mo1) <= vm_live_bytes (m_vmmaps mo) + E;
  mss_sizes : forall B, E <= B -> 3 * PGSZ <= B -> sizes_le B (vmaps mo) -> sizes_le B (vmaps mo1);
  mss_limit : vm_limit (m_vmmaps mo1) = vm_limit (m_vmmaps mo) }.

Lemma esize_nonneg : forall e, 0 <= esize e.
Proof. intros e; destruct e; cbn [esize]; unfold PGSZ; lia. Qed.
Lemma esum_nonneg : forall es, 0 <= esum es.
Proof. induction es; cbn [esum]; [lia|]. pose proof (esize_nonneg a). lia. Qed.

Lemma msteps_refl : forall mo, msteps 0 0 mo mo.
Proof. intros mo. constructor; auto; lia. Qed.

Lemma msteps_cons : forall e k E mo mo1 mo2,
  mstep (esize e) mo mo1 -> msteps k E mo1 mo2 -> 0 <= E -> msteps (S k) (esize e + E) mo mo2.
Proof.
  intros e k E mo mo1 mo2 [A1 A2 A3 A4] [B1 B2 B3 B4] HE. pose proof (esize_nonneg e). constructor.
  - lia. - lia.
  - intros B HB H3 Hs. apply B3; [lia | exact H3 |]. apply A3; [lia | exact Hs].
  - congruence.
Qed.

Theorem membed_measure : forall {R} (t : Malloc.M R) L Post s mo r s' mo',
  ctree_ok L t Post -> KL L (ps_brk s) mo -> mo_ok mo ->
  tpath nstep (membed t s) mo [] (Ok (r, s')) mo' ->
  exists zs, follow t zs = Some r /\ okpath L t zs /\ length zs = length (evs_of t zs)
    /\ ps_m s' = ps_m s /\ mo_ok mo' /\ vm_agree mo mo'
    /\ msteps (length zs) (esum (evs_of t zs)) mo mo'.
Proof.
  intros R t. induction t as [r0 | e k IH]; intros L Post s mo r s' mo' CT HK Hmo Htp.
  - cbn [membed] in Htp. apply tpath_mret_inv in Htp as [E ->]. inversion E; subst.
    exists []. cbn [follow okpath evs_of esum length].
    split; [reflexivity|]. split; [exact I|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact Hmo|]. split; [apply vm_agree_refl | apply msteps_refl].
  - cbn [membed] in Htp. apply tpath_mbind_inv in Htp as (z & s1 & mo1 & H1 & H2).
    destruct CT as [Hpre Hk].
    destruct (kev_measure L e s mo z s1 mo1 Hpre HK Hmo H1) as (Hok & HK1 & Hm & _ & _ & Hmo1 & Hva1 & M1).
    destruct (IH z (event_post L e z) Post s1 mo1 r s' mo' (Hk z Hok) HK1 Hmo1 H2) as (zs & Hf & Hokp & Hlen & Hm' & Hmo' & Hva' & MS).
    exists (z :: zs). cbn [follow okpath evs_of esum length]. destruct e; try (cbn [event_pre] in Hpre; contradiction);
      (split; [exact Hf|]); (split; [split; [exact Hok | exact Hokp]|]); (split; [rewrite Hlen; reflexivity|]);
      (split; [congruence|]); (split; [exact Hmo'|]); (split; [eapply vm_agree_trans; eassumption|]);
      (eapply msteps_cons; [exact M1 | exact MS | apply esum_nonneg]).
Qed.

Lemma mpath_raw_malloc_inv : forall n s mo r s' mo',
  mpath (raw_malloc n) s mo r s' mo' ->
  exists st' p s1, tpath nstep (membed (cmalloc (ps_m s) n) s) mo [] (Ok ((st', p), s1)) mo'
    /\ s' = set_m st' s1 /\ r = match p with Some slot => Some (slot, fresh_off st' slot n) | None => None end.
Proof.
  intros n s mo r s' mo' H. unfold mpath, raw_malloc in H.
  apply tpath_mbind_inv in H as (s0 & s0' & mo0 & H0 & H). apply tpath_mget_inv in H0 as [E ->]. inversion E; subst.
  apply tpath_mbind_inv in H as ([st' p] & s1 & mo1 & H1 & H). cbn beta iota in H.
  apply tpath_mbind_inv in H as (u & s2 & mo2 & H2 & H3). apply tpath_mupd_inv in H2 as [E2 ->]. inversion E2; subst.
  apply tpath_mret_inv in H3 as [E3 ->]. inversion E3; subst.
  exists st', p, s1. split; [exact H1|]. split; reflexivity.
Qed.

Lemma mpath_raw_free_inv : forall p s mo u s' mo',
  mpath (raw_free p) s mo u s' mo' ->
  exists st' s1, tpath nstep (membed (cfree (ps_m s) (Some (fst p))) s) mo [] (Ok (st', s1)) mo' /\ s' = set_m st' s1.
Proof.
  intros p s mo u s' mo' H. unfold mpath, raw_free in H.
  apply tpath_mbind_inv in H as (s0 & s0' & mo0 & H0 & H). apply tpath_mget_inv in H0 as [E ->]. inversion E; subst.
  apply tpath_mbind_inv in H as (st' & s1 & mo1 & H1 & H). cbn beta iota in H.
  apply tpath_mupd_inv in H as [E2 ->]. inversion E2; subst.
  exists st', s1. split; [exact H1 | reflexivity].
Qed.

Theorem raw_malloc_measure : forall n s LB mo r s' mo' (k : nat) (E : Z),
  KREL s LB mo -> mo_ok mo -> 0 <= n ->
  (forall L zs, MI_Contracts.SIMREL (ps_m s) L -> okpath L (cmalloc (ps_m s) n) zs ->
     (length (evs_of (cmalloc (ps_m s) n) zs) <= k)%nat /\ esum (evs_of (cmalloc (ps_m s) n) zs) <= E) ->
  mpath (raw_malloc n) s mo r s' mo' ->
  exists k' E', (k' <= k)%nat /\ 0 <= E' <= E /\ msteps k' E' mo mo'.
Proof.
  intros n s LB mo r s' mo' k E [(L & Hc & HK & _) _] Hmo Hn Hb Hp.
  destruct (mpath_raw_malloc_inv _ _ _ _ _ _ Hp) as (st' & p & s1 & Ht & _ & _).
  destruct (membed_measure _ L _ s mo _ s1 mo' (MI_Contracts.cmalloc_contract_sim _ _ _ Hc Hn) HK Hmo Ht)
    as (zs & Hf & Hok & Hlen & _ & _ & _ & MS).
  destruct (Hb L zs Hc Hok) as [B1 B2].
  exists (length zs), (esum (evs_of (cmalloc (ps_m s) n) zs)). split; [lia|]. split; [split; [apply esum_nonneg | exact B2] | exact MS].
Qed.

Theorem raw_free_measure : forall p A n s LB mo u s' mo' (k : nat) (E : Z),
  KREL s LB mo -> In (p, A, n) LB -> mo_ok mo ->
  (forall L zs, MI_Contracts.SIMREL (ps_m s) L -> In (fst p) (ld_live L) -> okpath L (cfree (ps_m s) (Some (fst p))) zs ->
     (length (evs_of (cfree (ps_m s) (Some (fst p))) zs) <= k)%nat /\ esum (evs_of (cfree (ps_m s) (Some (fst p))) zs) <= E) ->
  mpath (raw_free p) s mo u s' mo' ->
  exists k' E', (k' <= k)%nat /\ 0 <= E' <= E /\ msteps k' E' mo mo'.
Proof.
  intros p A n s LB mo u s' mo' k E [(L & Hc & HK & Hi) _] Hin Hmo Hb Hp.
  assert (Hlive : In (fst p) (ld_live L)).
  { apply Hi. rewrite map_map. apply in_map_iff. exists (p, A, n). split; [reflexivity | exact Hin]. }
  destruct (mpath_raw_free_inv _ _ _ _ _ _ Hp) as (st' & s1 & Ht & _).
  destruct (membed_measure _ L _ s mo _ s1 mo' (MI_Contracts.cfree_contract_sim _ _ _ Hc Hlive) HK Hmo Ht)
    as (zs & Hf & Hok & Hlen & _ & _ & _ & MS).
  destruct (Hb L zs Hc Hlive Hok) as [B1 B2].
  exists (length zs), (esum (evs_of (cfree (ps_m s) (Some (fst p))) zs)). split; [lia|]. split; [split; [apply esum_nonneg | exact B2] | exact MS].
Qed.

End CEIL.
