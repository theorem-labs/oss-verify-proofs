(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from projects/zlib/checksum_fuzzer/proofs/lib/Reusable/YK02.v at , lines 6-10, 16-16, 24-30, 44-57, 67-105, 154-161, 309-313, 322-329, 332-332, 380-400, 426-426, 430-430, 527-554, 578-581, 583-594, 599-602, 605-605, 640-650, 677-677, 770-795, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Mm.Mmap.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.AS Require Import SimInv ExitSim PropExec CatSim CatExec WallSim.
Unset Lia Cache.

Import ListNotations.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.



Lemma word_add_0_r : forall a : word, a + Z_to_bv 64 0 = a.
Proof.
  intro a. apply bv_eq.
  rewrite bv_add_unsigned.
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  rewrite Z.add_0_r, bv_wrap64_mod. apply Z.mod_small. apply u64_range.
Qed.



Lemma word_add_nat_S : forall (a : word) k,
  (a + 1) + nat_to_word k = a + nat_to_word (S k).
Proof.
  intros a k. apply bv_eq. unfold nat_to_word.
  rewrite !bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  change (bv_unsigned (1 : word)) with 1%Z.
  rewrite Zplus_mod_idemp_l, !Zplus_mod_idemp_r.
  f_equal. lia.
Qed.


Definition zmem (mem : word -> option byte) (b l : word) : word -> option byte :=
  fun a => if Z.leb (bv_unsigned b) (bv_unsigned a)
              && Z.ltb (bv_unsigned a) (bv_unsigned b + bv_unsigned l)
           then Some (Z_to_bv 8 0) else mem a.



Lemma zmem_out : forall mem b l a,
  (bv_unsigned a < bv_unsigned b \/ bv_unsigned b + bv_unsigned l <= bv_unsigned a)%Z ->
  zmem mem b l a = mem a.
Proof.
  intros mem b l a Hd. unfold zmem.
  destruct Hd as [Hd | Hd].
  - assert (E : (bv_unsigned b <=? bv_unsigned a)%Z = false) by (apply Z.leb_gt; lia).
    rewrite E. reflexivity.
  - assert (E : (bv_unsigned a <? bv_unsigned b + bv_unsigned l)%Z = false)
      by (apply Z.ltb_ge; lia).
    rewrite E, andb_false_r. reflexivity.
Qed.

Lemma rdn_zmem_out : forall segs mem b l (a : word) n,
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  (bv_unsigned a + Z.of_nat n <= bv_unsigned b
   \/ bv_unsigned b + bv_unsigned l <= bv_unsigned a)%Z ->
  rdn segs (zmem mem b l) a n = rdn segs mem a n.
Proof.
  intros segs mem b l a n Hnw Hd. apply rdn_ext; [exact Hnw|].
  intros x Hx. apply zmem_out. lia.
Qed.

Lemma rdn_zmem_in1 : forall segs mem b l (a : word),
  (bv_unsigned b <= bv_unsigned a < bv_unsigned b + bv_unsigned l)%Z ->
  rdn segs (zmem mem b l) a 1 = Some [Z_to_bv 8 0].
Proof.
  intros segs mem b l a [Hlo Hhi]. cbn [rdn]. unfold zmem.
  rewrite (proj2 (Z.leb_le _ _) Hlo), (proj2 (Z.ltb_lt _ _) Hhi).
  reflexivity.
Qed.

Lemma wbytes_app : forall {bs1 bs2 : list byte} m (a : word),
  wbytes m a (bs1 ++ bs2) = wbytes (wbytes m a bs1) (a + nat_to_word (length bs1)) bs2.
Proof.
  induction bs1 as [|b bs1 IH]; intros bs2 m a.
  - cbn [app wbytes length].
    replace (a + nat_to_word 0) with a; [reflexivity|].
    symmetry. exact (word_add_0_r a).
  - cbn [app wbytes length].
    rewrite IH, word_add_nat_S. reflexivity.
Qed.










Definition vm_model (h : VmMaps) : Model :=
  mkModel [] h IEof [] None None None.

Definition brk_grow_ok (h : VmMaps) (req r : word) : bool :=
  Mmap.brk_grow_ok (vm_model h) req r.

Definition brk_r_ok (h : VmMaps) (req r : word) : Prop :=
  Mmap.brk_r_ok (vm_model h) req r = true.











Lemma brk_grants_query : forall r old, brk_grants (Z_to_bv 64 0) r old = [].
Proof.
  intros r old. unfold brk_grants, brk_is_grow, w_is0.
  rewrite bv_eqb_refl. reflexivity.
Qed.



Lemma brk_unmaps_keep : forall old, brk_unmaps old old = [].
Proof.
  intros old. unfold brk_unmaps. cbv zeta.
  destruct (0 <? bv_unsigned old)%Z eqn:E; [|reflexivity].
  unfold brk_page_range. rewrite Z.ltb_irrefl. reflexivity.
Qed.





Lemma page_round_up_Z_aligned : forall z,
  (0 <= z)%Z -> (z mod page_size = 0)%Z -> page_round_up_Z z = z.
Proof.
  intros z Hz Hmod. unfold page_round_up_Z, page_size in *.
  pose proof (Z.div_mod z 4096 ltac:(lia)) as Hdiv.
  replace (z + 4096 - 1)%Z with
    (4095 + (z / 4096) * 4096)%Z by lia.
  rewrite Z.div_add by lia.
  rewrite Z.div_small by lia. lia.
Qed.

Lemma page_round_up_Z_bounds : forall z,
  (0 <= z)%Z ->
  (z <= page_round_up_Z z <= z + page_size - 1)%Z.
Proof.
  intros z Hz. unfold page_round_up_Z, page_size.
  pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)) as Hmod.
  lia.
Qed.








Definition growable (reserved : list (word * word)) (lim top : Z) (t r : word)
    : Prop :=
  r <> Z_to_bv 64 0 /\ (bv_unsigned r + bv_unsigned t < 2 ^ 64)%Z /\
  (t = Z_to_bv 64 0 \/
   (((if (page_round_up_Z (bv_unsigned r)
          <? page_round_up_Z (bv_unsigned r + bv_unsigned t))%Z
      then (page_round_up_Z (bv_unsigned r + bv_unsigned t)
            <=? top)%Z
           && region_free reserved
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned r)))
                (Z_to_bv 64 (page_round_up_Z
                               (bv_unsigned r + bv_unsigned t)
                              + page_size - page_round_up_Z (bv_unsigned r)))
      else true)
     && (bv_unsigned t <=? lim)%Z)%bool = true)).

Definition T1 (reserved : list (word * word)) (lim top : Z) (t : word)
    (bufs : list (list byte))
    (r : word) : (list (list byte) * word) -> Prop :=
  fun o => (o = ([], Z_to_bv 64 4)
            /\ (r = Z_to_bv 64 0
                \/ (2 ^ 64 <= bv_unsigned r + bv_unsigned t)%Z
                \/ t <> Z_to_bv 64 0))
        \/ (growable reserved lim top t r /\ o = (bufs, Z_to_bv 64 0)).

Definition T2 (want : word) (bufs : list (list byte)) (r2 : word)
    : (list (list byte) * word) -> Prop :=
  fun o => (r2 = want /\ o = (bufs, Z_to_bv 64 0))
        \/ (r2 <> want /\ o = ([], Z_to_bv 64 4)).




Lemma region_free_above : forall (l : list (word * word)) (lo n : word),
  Forall (fun p => (bv_unsigned (fst p) + bv_unsigned (snd p)
                    <= bv_unsigned lo)%Z) l ->
  region_free l lo n = true.
Proof.
  induction l as [|[a sz] l IH]; intros lo n Hf; [reflexivity|].
  inversion Hf as [|? ? Ha Hl]; subst. cbn [fst snd] in Ha.
  cbn [region_free]. unfold iv_overlap.
  assert (E : (bv_unsigned lo <? bv_unsigned a + bv_unsigned sz)%Z = false)
    by (apply Z.ltb_ge; lia).
  rewrite E. cbn [andb negb]. apply IH. exact Hl.
Qed.




Lemma brk_model_next_query : forall h r,
  r = vm_brk h ->
  brk_model_next h (Z_to_bv 64 0) r
  = mkVmMapsFull (vm_reserved h) (vm_maps h) (vm_noaccess h)
      (vm_start_brk h) r (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
Proof.
  intros h r ->. unfold brk_model_next, brk_maps_next.
  rewrite Z.ltb_irrefl, andb_false_r.
  rewrite brk_grants_query, brk_unmaps_keep. reflexivity.
Qed.







Section WithSegs.
Variable segs : list Segment.

Inductive to_outcomes : machine_state -> Model -> ((list (list byte) * word) -> Prop) -> Prop :=
| tou_wexit : forall ms model bufs code (U : (list (list byte) * word) -> Prop),
    fd1chan model ->
    to_wallexit segs (Z_to_bv 64 1) bufs code ms ->
    bufs_modeled bufs ->
    (forall o, U o <-> o = (bufs, code)) ->
    to_outcomes ms model U
| tou_step : forall ms ms' model U,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_outcomes ms' model U ->
    to_outcomes ms model U
| tou_brk : forall ms model x8
    (T : SyscallEffect -> Model -> (list (list byte) * word) -> Prop)
    (U : (list (list byte) * word) -> Prop),
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 214%Z ->
    (forall eff model' evs,
       syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
       to_outcomes (advance_past_svc (apply_effect ms eff)) model' (T eff model')) ->
    (forall o, U o <->
       (exists eff model' evs,
          syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)
          /\ T eff model' o)) ->
    to_outcomes ms model U.

















End WithSegs.






End WithFP1.
