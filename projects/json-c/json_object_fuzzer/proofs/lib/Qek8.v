(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Fs.ReadWrite.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWXq QQny Q3bI Qo8J.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.OmniRun.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite.
Import QWXq.Mq2 QQny Q3bI Qo8J.Mq2.

Import ListNotations.
Open Scope bv_scope.

Definition M_loop (model : Model) : Prop :=
fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) /\
fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) /\
m_halted model = None /\
m_vm_lazy model = [].

Fixpoint wseg_ok (segs : list Segment) (a : word) (n : nat) : bool :=
match n with
| O => true
| S n' =>
match find_segment segs (bv_unsigned a) 1 with
| Some seg =>
(seg_writable seg
&& match segment_byte_at (seg_bytes seg)
(Z.to_N (bv_unsigned a - Z.of_N (seg_base seg))) with
| Some _ => true
| None => false
end
&& wseg_ok segs (a + 1) n')%bool
| None => false
end
end.

Inductive chunks (cnt : word) : InputStream -> list (list byte) -> InputStream -> Prop :=
| chunks_nil : forall s, chunks cnt s [] s
| chunks_cons : forall s bs blocks s'',
(1 <= Z.of_nat (length bs))%Z ->
(Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
fst (stream_take s (length bs)) = bs ->
chunks cnt (snd (stream_take s (length bs))) blocks s'' ->
chunks cnt s (bs :: blocks) s''.

Definition iter_ev_ch (rch : word) (bs : list byte) : list event :=
map (ReadEv rch) bs ++ map (WriteEv (Z_to_bv 64 1)) bs.

Definition iter_ev (bs : list byte) : list event :=
iter_ev_ch (Z_to_bv 64 0) bs.

Definition eof_tail (s : InputStream) (fs : Fs.Fs) : list event :=
match s with
| IEof => [ExitEv (Z_to_bv 64 0) fs]
| ICons _ _ => []
end.

Definition stream_traces_ch (rch : word) (cnt : word) (fs : Fs.Fs)
(s : InputStream) (tr : list event) : Prop :=
exists blocks s',
chunks cnt s blocks s' /\
is_prefix tr (flat_map (iter_ev_ch rch) blocks ++ eof_tail s' fs).

Definition stream_traces (cnt : word) (fs : Fs.Fs) (s : InputStream)
(tr : list event) : Prop :=
stream_traces_ch (Z_to_bv 64 0) cnt fs s tr.

Section Loop.
Variable segs : list Segment.
Variable LH : machine_state -> Prop.
Variable cnt : word.

Hypothesis Hcnt : (0 < bv_unsigned cnt <= rw_bytes_max)%Z.

Definition lh_next (ms : machine_state) : Prop :=
exists ms', msteps segs ms ms' /\ LH ms'.

Definition WrPend (bs : list byte) (ms : machine_state) : Prop :=
(1 <= length bs)%nat /\
to_wall segs (Z_to_bv 64 1) ms bs lh_next.

Inductive to_wr (bs : list byte) : machine_state -> Prop :=
| twr_here : forall ms, WrPend bs ms -> to_wr bs ms
| twr_step : forall ms ms',
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
to_wr bs ms' -> to_wr bs ms.

Definition ReadPend (ms : machine_state) : Prop :=
exists buf x8,
ms_svc_pending ms = Some x8 /\
bv_unsigned x8 = 63%Z /\
ms_gpr ms 0 = Z_to_bv 64 0 /\
ms_gpr ms 1 = buf /\
ms_gpr ms 2 = cnt /\
(exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w) /\

access_okb buf (bv_unsigned cnt) = true /\
to_exit segs (Z_to_bv 64 0) (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) /\
(forall bs,
(1 <= Z.of_nat (length bs))%Z ->
(Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
to_wr bs (advance_past_svc (apply_effect ms
(mkEffect (len_word bs) [(buf, bs)] [])))).

Inductive to_rd : machine_state -> Prop :=
| trd_here : forall ms, ReadPend ms -> to_rd ms
| trd_step : forall ms ms',
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
to_rd ms' -> to_rd ms.

Lemma msteps_to_rd : forall ms ms',
msteps segs ms ms' -> to_rd ms' -> to_rd ms.
Proof.
intros ms ms' H; induction H; [auto|].
intro Hrd. eapply trd_step; eauto.
Qed.

Hypothesis H_LH : forall ms, LH ms -> to_rd ms.

Definition sinv (c : config) : Prop :=
(M_loop (cfg_model c) /\
(to_rd (cfg_ms c)
\/ exists bs, (1 <= length bs)%nat /\ buf_modeled bs /\
to_wall_tail segs (Z_to_bv 64 1) (cfg_ms c) bs lh_next))
\/ on_path segs (Z_to_bv 64 0) c.

End Loop.

End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Mm.Mmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWXq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWXq.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQny.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQny. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3bI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3bI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgpE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgpE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qo8J.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qo8J.Mq2.

Import ListNotations.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.

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

Lemma with_vmmaps_halted : forall h m, m_halted (with_vmmaps h m) = m_halted m.
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

Definition outcome_trace (fs : Fs.Fs) (o : list (list byte) * word) : list event :=
wevents (fst o) ++ [ExitEv (snd o) fs].

Definition outcomes_post (fs : Fs.Fs) (U : (list (list byte) * word) -> Prop) : post :=
fun tr o => exists out, U out /\ tr = outcome_trace fs out /\ exits_with (snd out) tr o.

End WithSegs.

End WithFP1.
