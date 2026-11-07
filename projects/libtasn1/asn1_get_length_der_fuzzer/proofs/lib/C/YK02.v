(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Trevor Hansen, 2026-11: module names. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Mm.Mmap.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YK16 YK0o YK11 YK0j YK0i YK1i.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Section d.
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

Lemma apply_zeros_one : forall mem b l,
apply_zeros mem [(b, l)] = zmem mem b l.
Proof.
intros mem b l. apply functional_extensionality. intro a.
unfold apply_zeros, zeros_cover, zmem. cbn [existsb fst snd].
rewrite orb_false_r. reflexivity.
Qed.
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


Lemma with_vmmaps_halted : forall h m, m_halted (with_vmmaps h m) = m_halted m.
Proof. reflexivity. Qed.
Lemma with_vmmaps_vm : forall h m, m_vmmaps (with_vmmaps h m) = h.
Proof. reflexivity. Qed.
Lemma with_vmmaps_lazy : forall h m,
m_vm_lazy (with_vmmaps h m) = m_vm_lazy m.
Proof. reflexivity. Qed.



Lemma in_sysno_sys_input214 : forall segs ms x8,
in_sysno (sys_input segs ms x8) = x8.
Proof. reflexivity. Qed.

Lemma syscall_spec_brk : forall segs ms x8 model o,
bv_unsigned x8 = 214%Z ->
(syscall_spec (sys_input segs ms x8) model o
<-> brk_spec (ms_gpr ms 0) (sys_input segs ms x8) model o).
Proof.
intros segs ms x8 model o Hno. unfold syscall_spec, dispatch.
rewrite in_sysno_sys_input214, Hno. reflexivity.
Qed.
Definition vm_model (h : VmMaps) : Model :=
mkModel [] h IEof [] None None None.
Definition brk_grow_ok (h : VmMaps) (req r : word) : bool :=
Mmap.brk_grow_ok (vm_model h) req r.
Definition brk_r_ok (h : VmMaps) (req r : word) : Prop :=
Mmap.brk_r_ok (vm_model h) req r = true.
Definition brk_resolution_ok (m : Model) (req r : word) : Prop :=
Mmap.brk_r_ok m req r = true.
Definition brk_model (req r : word) (m : Model) : Model :=
with_brk_next m req r.

Lemma check_brk_ok_inv : forall req eff m m' evs,
check_brk req eff m = CheckOk m' evs ->
eff = mkEffectU (eff_ret eff) []
(brk_zeros req (eff_ret eff) (vm_brk (m_vmmaps m)))
(brk_unmaps (eff_ret eff) (vm_brk (m_vmmaps m))) [] []
/\ evs = []
/\ brk_resolution_ok m req (eff_ret eff)
/\ m' = brk_model req (eff_ret eff) m.
Proof.
intros req [r ws zs us cs copyins] m m' evs H.
unfold check_brk in H.
destruct ws as [|? ?]; [|discriminate].
destruct cs as [|? ?]; [|discriminate].
destruct copyins as [|? ?]; [|discriminate].
destruct (Mmap.brk_r_ok m req r) eqn:HR; [|cbn [andb] in H; discriminate].
destruct (listNN_eqb zs (brk_zeros req r (vm_brk (m_vmmaps m)))) eqn:HZ;
[|cbn [andb] in H; discriminate].
destruct (listNN_eqb us (brk_unmaps r (vm_brk (m_vmmaps m)))) eqn:HU;
[|cbn [andb] in H; discriminate].
cbn [andb] in H.
apply listNN_eqb_eq in HZ. subst zs.
apply listNN_eqb_eq in HU. subst us.
inversion H; clear H; subst.
cbn [eff_ret]. unfold brk_resolution_ok, brk_model.
repeat split; try reflexivity. exact HR.
Qed.
Lemma check_brk_ok_intro : forall req r m,
brk_resolution_ok m req r ->
check_brk req (mkEffectU r [] (brk_zeros req r (vm_brk (m_vmmaps m)))
(brk_unmaps r (vm_brk (m_vmmaps m))) [] []) m
= CheckOk (brk_model req r m) [].
Proof.
intros req r m HR. unfold brk_resolution_ok in HR.
unfold check_brk. rewrite HR.
rewrite (proj2 (listNN_eqb_eq _ _) eq_refl).
rewrite (proj2 (listNN_eqb_eq _ _) eq_refl).
unfold brk_model. reflexivity.
Qed.
Lemma brk_ok_iff : forall segs ms x8 model eff model' evs,
bv_unsigned x8 = 214%Z ->
(syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) <->
(eff = mkEffectU (eff_ret eff) []
(brk_zeros (ms_gpr ms 0) (eff_ret eff) (vm_brk (m_vmmaps model)))
(brk_unmaps (eff_ret eff) (vm_brk (m_vmmaps model))) [] []
/\ evs = []
/\ brk_resolution_ok model (ms_gpr ms 0) (eff_ret eff)
/\ model' = brk_model (ms_gpr ms 0) (eff_ret eff) model)).
Proof.
intros segs ms x8 model eff model' evs Hno. split.
- intro H. apply (proj1 (syscall_spec_brk _ _ _ _ _ Hno)) in H.
apply check_brk_complete_ok in H.
apply check_brk_ok_inv in H. exact H.
- intros (Heff & -> & Hok & ->).
apply (proj2 (syscall_spec_brk _ _ _ _ _ Hno)). apply check_brk_sound_ok.
rewrite Heff at 1. cbn [eff_ret].
apply check_brk_ok_intro. exact Hok.
Qed.
Lemma brk_ok_intro : forall segs ms x8 model r,
bv_unsigned x8 = 214%Z ->
brk_resolution_ok model (ms_gpr ms 0) r ->
syscall_spec (sys_input segs ms x8) model
(Ok (mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
(brk_unmaps r (vm_brk (m_vmmaps model))) [] [])
(brk_model (ms_gpr ms 0) r model) []).
Proof.
intros segs ms x8 model r Hno Hok.
apply (brk_ok_iff segs ms x8 model _ _ _ Hno). cbn [eff_ret]. auto.
Qed.
Lemma brk_no_unmodeled : forall segs ms x8 model,
bv_unsigned x8 = 214%Z ->
~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
intros segs ms x8 model Hno H.
apply (proj1 (syscall_spec_brk _ _ _ _ _ Hno)) in H.
apply (check_brk_complete_unmodeled _ _ _ (mkEffect (Z_to_bv 64 0) [] [])) in H.
unfold check_brk in H.
destruct (Mmap.brk_r_ok model (ms_gpr ms 0) (Z_to_bv 64 0)
&& listNN_eqb []
(brk_zeros (ms_gpr ms 0) (Z_to_bv 64 0) (vm_brk (m_vmmaps model)))
&& listNN_eqb []
(brk_unmaps (Z_to_bv 64 0) (vm_brk (m_vmmaps model))));
discriminate.
Qed.

Lemma brk_zeros_grow : forall req r old,
req <> Z_to_bv 64 0 ->
(0 < bv_unsigned old)%Z -> (bv_unsigned old < bv_unsigned r)%Z ->
brk_zeros req r old =
brk_page_range (page_round_up_Z (bv_unsigned old))
(page_round_up_Z (bv_unsigned r)).
Proof.
intros req r old Hreq Hold Hlt. unfold brk_zeros, brk_is_grow.
assert (E1 : w_is0 req = false)
by (unfold w_is0; apply bv_eqb_neq; exact Hreq).
assert (E2 : (0 <? bv_unsigned old)%Z = true) by (apply Z.ltb_lt; lia).
assert (E3 : (bv_unsigned old <? bv_unsigned r)%Z = true) by (apply Z.ltb_lt; lia).
rewrite E1, E2, E3. reflexivity.
Qed.
Lemma brk_grants_grow : forall req r old,
req <> Z_to_bv 64 0 ->
(0 < bv_unsigned old)%Z -> (bv_unsigned old < bv_unsigned r)%Z ->
brk_grants req r old = [(old, r - old)].
Proof.
intros req r old Hreq Hold Hlt. unfold brk_grants, brk_is_grow.
assert (E1 : w_is0 req = false)
by (unfold w_is0; apply bv_eqb_neq; exact Hreq).
assert (E2 : (0 <? bv_unsigned old)%Z = true) by (apply Z.ltb_lt; lia).
assert (E3 : (bv_unsigned old <? bv_unsigned r)%Z = true) by (apply Z.ltb_lt; lia).
rewrite E1, E2, E3. reflexivity.
Qed.
Lemma brk_zeros_query : forall r old, brk_zeros (Z_to_bv 64 0) r old = [].
Proof.
intros r old. unfold brk_zeros, brk_is_grow, w_is0.
rewrite bv_eqb_refl. reflexivity.
Qed.
Lemma brk_grants_query : forall r old, brk_grants (Z_to_bv 64 0) r old = [].
Proof.
intros r old. unfold brk_grants, brk_is_grow, w_is0.
rewrite bv_eqb_refl. reflexivity.
Qed.
Lemma brk_zeros_keep : forall req old, brk_zeros req old old = [].
Proof.
intros req old. unfold brk_zeros, brk_is_grow.
rewrite Z.ltb_irrefl, !andb_false_r. reflexivity.
Qed.
Lemma brk_grants_keep : forall req old, brk_grants req old old = [].
Proof.
intros req old. unfold brk_grants, brk_is_grow.
rewrite Z.ltb_irrefl, !andb_false_r. reflexivity.
Qed.
Lemma brk_unmaps_keep : forall old, brk_unmaps old old = [].
Proof.
intros old. unfold brk_unmaps. cbv zeta.
destruct (0 <? bv_unsigned old)%Z eqn:E; [|reflexivity].
unfold brk_page_range. rewrite Z.ltb_irrefl. reflexivity.
Qed.

Lemma brk_unmaps_grow : forall r old,
(bv_unsigned old <= bv_unsigned r)%Z -> brk_unmaps r old = [].
Proof.
intros r old H. unfold brk_unmaps. cbv zeta.
destruct (0 <? bv_unsigned old)%Z eqn:E0; [|reflexivity].
assert (E : (page_round_up_Z (bv_unsigned r)
<? page_round_up_Z (bv_unsigned old))%Z = false)
by (apply Z.ltb_ge, page_round_up_Z_mono, H).
unfold brk_page_range. rewrite E. reflexivity.
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


Lemma region_free_prefix : forall maps b small big,
(bv_unsigned small <= bv_unsigned big)%Z ->
region_free maps b big = true -> region_free maps b small = true.
Proof.
induction maps as [|[a sz] maps IH]; intros b small big Hle Hfree;
[reflexivity|].
cbn [region_free] in Hfree |- *.
apply andb_true_iff in Hfree as [Hhead Htail].
apply andb_true_iff. split; [|eapply IH; eassumption].
apply negb_true_iff in Hhead. apply negb_true_iff.
unfold iv_overlap in Hhead |- *.
apply andb_false_iff in Hhead. apply andb_false_iff.
destruct Hhead as [Hhead|Hhead]; [left|right];
apply Z.ltb_ge in Hhead; apply Z.ltb_ge; lia.
Qed.

Lemma brk_zeros_aligned_grow : forall req r old,
req <> Z_to_bv 64 0 ->
(0 < bv_unsigned old)%Z -> (bv_unsigned old < bv_unsigned r)%Z ->
(bv_unsigned old mod page_size = 0)%Z ->
brk_zeros req r old =
[(old, Z_to_bv 64 (page_round_up_Z (bv_unsigned r) - bv_unsigned old))].
Proof.
intros req r old Hreq Hpos Hlt Halign.
rewrite brk_zeros_grow by assumption.
rewrite (page_round_up_Z_aligned (bv_unsigned old)) by lia.
unfold brk_page_range.
assert (Hround : (bv_unsigned old < page_round_up_Z (bv_unsigned r))%Z).
{ pose proof (page_round_up_Z_bounds (bv_unsigned r) ltac:(lia)). lia. }
rewrite (proj2 (Z.ltb_lt _ _) Hround).
rewrite Z_to_bv_bv_unsigned. reflexivity.
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
Lemma brk_r_ok_query_iff : forall h r,
brk_r_ok h (Z_to_bv 64 0) r <-> r = vm_brk h.
Proof.
intros h r. unfold brk_r_ok, Mmap.brk_r_ok.
cbv [vm_model mkModel m_vmmaps m_vm]. cbv zeta.
unfold w_is0. rewrite bv_eqb_refl. cbn [orb].
apply bv_eqb_eq.
Qed.

Lemma region_free_above_top : forall reserved (lo n : word),
(reserved_top reserved <= bv_unsigned lo)%Z ->
region_free reserved lo n = true.
Proof.
induction reserved as [|[a sz] l IH]; intros lo n Hr;
cbn [reserved_top] in *; [reflexivity|].
cbn [region_free]. unfold iv_overlap.
assert (E : (bv_unsigned lo <? bv_unsigned a + bv_unsigned sz)%Z = false)
by (apply Z.ltb_ge; lia).
rewrite E. cbn [andb negb]. apply IH. lia.
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
Lemma brk_model_query : forall r m,
r = vm_brk (m_vmmaps m) ->
brk_model (Z_to_bv 64 0) r m
= with_vmmaps
(mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
(vm_noaccess (m_vmmaps m)) (vm_start_brk (m_vmmaps m)) r
(vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m))
(vm_init_sp (m_vmmaps m))) m.
Proof.
intros r m ->. unfold brk_model, with_brk_next. cbv zeta.
rewrite brk_unmaps_keep. cbn [forget_vm_ranges].
rewrite brk_model_next_query by reflexivity. reflexivity.
Qed.




Section e.
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

Lemma forget_vm_ranges_frame : forall ranges model,
m_halted (forget_vm_ranges ranges model) = m_halted model /\
m_fs (forget_vm_ranges ranges model) = m_fs model /\
m_fds (forget_vm_ranges ranges model) = m_fds model /\
(m_vm_lazy model = [] -> m_vm_lazy (forget_vm_ranges ranges model) = []).
Proof.
induction ranges as [|[a n] ranges IH]; intros model; cbn [forget_vm_ranges].
- auto.
- specialize (IH (vm_forget_range (bv_unsigned a)
(bv_unsigned a + bv_unsigned n) model)).
destruct IH as (Hhalt & Hfs & Hfds & Hlazy).
unfold vm_forget_range, with_vm_backing in Hhalt, Hfs, Hfds, Hlazy.
cbn [m_halted m_fs m_fds m_vm_lazy] in Hhalt, Hfs, Hfds, Hlazy.
repeat split; try assumption.
intro Hempty. apply Hlazy. rewrite Hempty. reflexivity.
Qed.
Lemma brk_step_shape : forall ms x8 model eff model' evs,
m_halted model = None ->
m_vm_lazy model = [] ->
bv_unsigned x8 = 214%Z ->
syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
evs = [] /\ m_halted model' = None /\ m_fs model' = m_fs model
/\ m_fds model' = m_fds model
/\ m_vm_lazy model' = m_vm_lazy model.
Proof.
intros ms x8 model eff model' evs Hh Hlazy Hno Hs.
apply (brk_ok_iff segs ms x8 model eff model' evs Hno) in Hs.
destruct Hs as (_ & -> & _ & ->).
unfold brk_model, with_brk_next. cbv zeta.
destruct (forget_vm_ranges_frame
(brk_unmaps (eff_ret eff) (vm_brk (m_vmmaps model)))
(with_vmmaps
(brk_model_next (m_vmmaps model) (ms_gpr ms 0) (eff_ret eff)) model))
as (Hhalt & Hfs & Hfds & Hlazy').
repeat split.
- rewrite Hhalt. unfold with_vmmaps. cbn [m_halted]. exact Hh.
- rewrite Hfs. unfold with_vmmaps. reflexivity.
- rewrite Hfds. unfold with_vmmaps. reflexivity.
- rewrite Hlazy. apply Hlazy'.
unfold with_vmmaps. cbn [m_vm_lazy]. exact Hlazy.
Qed.
Lemma sstep_brk_inv : forall ms model x8 evs st,
m_halted model = None ->
m_vm_lazy model = [] ->
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 214%Z ->
sstep segs (mkCfg ms model) evs st ->
exists eff model',
syscall_spec (sys_input segs ms x8) model (Ok eff model' []) /\
evs = [] /\
st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model').
Proof.
intros ms model x8 evs st Hh Hlazy Hsvc Hno Hss.
inversion Hss; subst; try congruence.
-
assert (Hx : x0 = x8) by congruence; subst x0.
destruct (brk_step_shape ms x8 model eff model' evs Hh Hlazy Hno H3)
as (He & _ & _ & _ & Hlazy').
subst evs.
rewrite (materialize_model_accesses_no_lazy _ _
(eq_trans Hlazy' Hlazy)) in H7.
inversion H7; subst model''.
exists eff, model'; auto.
-
exfalso.
match goal with
| Hspec : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
Hmat : materialize_model_accesses ?model' _ = None |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (brk_step_shape ms x8 model eff model' evs0 Hh Hlazy Hno Hspec)
as (He & _ & _ & _ & Hlazy'); subst evs0;
rewrite (materialize_model_accesses_no_lazy _ _ (eq_trans Hlazy' Hlazy)) in Hmat;
discriminate
end.
-
exfalso.
match goal with
| Hsvc' : ms_svc_pending ms = Some ?x,
Hspec : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
Hhalt : m_halted ?model' = Some ?code |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (brk_step_shape ms x8 model eff model' evs0 Hh Hlazy Hno Hspec) as (_ & Hm & _ & _);
congruence
end.
-
exfalso.
match goal with
| Hsvc' : ms_svc_pending ms = Some ?x,
Hspec : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
Hkill : m_killed ?model' = Some ?sig |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (brk_step_shape ms x8 model eff model' evs0 Hh Hlazy Hno Hspec) as (_ & Hm & _ & _);
assert (Hhn : m_halted model' = None) by congruence;
rewrite (m_killed_of_m_halted_none _ Hhn) in Hkill; discriminate
end.
-
exfalso.
match goal with
| Hsvc' : ms_svc_pending ms = Some ?x,
Hspec : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
assert (Hx : x = x8) by congruence; subst x;
exact (brk_no_unmodeled segs ms x8 model Hno Hspec)
end.
Qed.
Definition outcome_trace (fs : Fs.Fs) (o : list (list byte) * word) : list event :=
wevents (fst o) ++ [ExitEv (snd o) fs].
Definition outcomes_post (fs : Fs.Fs) (U : (list (list byte) * word) -> Prop) : post :=
fun tr o => exists out, U out /\ tr = outcome_trace fs out /\ exits_with (snd out) tr o.









End e.





End d.
