(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase State.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QU8l.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.State.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import QU8l.Mq0.

Local Ltac Z.euclidean_division_equations_cleanup ::= zify_cheap_cleanup. Local Ltac mkr__euclidean_division_equations_cleanup_0 := zify_cheap_cleanup.
Local Ltac Zify.zify_internal_to_euclidean_division_equations ::= zify_fast_euclid. Local Ltac mkr__zify_internal_to_euclidean_division_equations_1 := zify_fast_euclid.
Local Ltac lia ::= lia_tuned. Local Ltac mkr__lia_2 := lia_tuned.
Import ListNotations.
Open Scope bv_scope.

Definition no_higher_fit (maps : list (word * word)) (aZ nZ baseZ : Z)
: Prop :=
forall g : Z,
(g mod page_size = 0)%Z ->
(aZ + nZ <= g)%Z ->
(g + nZ <= baseZ)%Z ->
region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ) = false.

Definition fit_candidates (maps : list (word * word)) (aZ nZ : Z)
: list Z :=
(aZ + nZ)%Z
:: map (fun p => page_round_up_Z (bv_unsigned (fst p)
+ bv_unsigned (snd p))%Z)
maps.

Definition higher_fit_b (maps : list (word * word)) (aZ nZ baseZ : Z)
: bool :=
existsb (fun g => (g mod page_size =? 0)%Z
&& (aZ + nZ <=? g)%Z && (g + nZ <=? baseZ)%Z
&& region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ))
(fit_candidates maps aZ nZ).

Lemma page_round_up_Z_le : forall z b,
(z <= b)%Z -> (b mod page_size = 0)%Z -> (page_round_up_Z z <= b)%Z.
Proof.
intros z b Hzb Hb. unfold page_round_up_Z, page_size in *.
pose proof (Z.div_mod b 4096 ltac:(lia)) as Hbm.
assert (Hq : ((z + 4096 - 1) / 4096 < b / 4096 + 1)%Z)
by (apply Z.div_lt_upper_bound; lia).
apply Z.le_trans with (m := (b / 4096 * 4096)%Z); [|lia].
apply Z.mul_le_mono_nonneg_r; lia.
Qed.

Definition search_candidates (maps : list (word * word)) (loZ : Z)
: list Z :=
loZ :: map (fun p => page_round_up_Z (bv_unsigned (fst p)
+ bv_unsigned (snd p))%Z)
maps.

Definition place_fits (maps : list (word * word)) (loZ hiZ nZ : Z) (g : Z)
: bool :=
(g mod page_size =? 0)%Z && (loZ <=? g)%Z && (g + nZ <=? hiZ)%Z
&& region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ).

Definition place (maps : list (word * word)) (loZ hiZ nZ : Z)
: option Z :=
find (place_fits maps loZ hiZ nZ) (search_candidates maps loZ).

Definition place_in_model (h : VmMaps) (nZ : Z) : option Z :=
place (vm_reserved h ++ vm_maps h) page_size (alloc_top h) nZ.

Example place_accepts_a_negative_length :
place_in_model (mkVmMaps [] [] 0 0 0) (-4096) = Some 4096%Z.
Proof. vm_compute. reflexivity. Qed.

Definition witness_ledger : list (word * word) :=
[(Z_to_bv 64 4096, Z_to_bv 64 8192)].

Definition demo_top : Z := alloc_top (mkVmMaps [] [] 0 0 0).

Example place_skips_the_occupied_floor :
place witness_ledger page_size demo_top 4096 = Some 12288%Z.
Proof. vm_compute. reflexivity. Qed.

Example place_complete_premises_are_satisfiable :
(0 <= page_size)%Z /\ (0 < 4096)%Z
/\ (page_size mod page_size = 0)%Z /\ (4096 mod page_size = 0)%Z
/\ (demo_top < two_pow_64)%Z
/\ (12288 mod page_size = 0)%Z /\ (page_size <= 12288)%Z
/\ (12288 + 4096 <= demo_top)%Z
/\ region_free witness_ledger (Z_to_bv 64 12288) (Z_to_bv 64 4096) = true.
Proof.
unfold page_size, demo_top, two_pow_64. rewrite alloc_top_mkVmMaps.
repeat split; try (vm_compute; reflexivity); try lia.
Qed.

Definition full_ledger : list (word * word) :=
[(Z_to_bv 64 4096, Z_to_bv 64 (demo_top - 4096))].

Example place_finds_nothing_when_full :
place full_ledger page_size demo_top 4096 = None.
Proof. vm_compute. reflexivity. Qed.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QU8l.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QU8l.

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Definition is_exit_no (no : word) : Prop :=
bv_unsigned no = 93%Z \/ bv_unsigned no = 94%Z.

Section WithSegs.
Variable segs : list Segment.
Variable code : word.

Inductive to_exit : machine_state -> Prop :=
| te_here : forall ms x8,
ms_svc_pending ms = Some x8 ->
is_exit_no x8 ->
ms_gpr ms 0 = code ->
to_exit ms
| te_step : forall ms ms',
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
to_exit ms' ->
to_exit ms.

Fixpoint sim_c (fuel : nat) (ms : machine_state) : bool :=
match fuel with
| O => false
| S fuel' =>
match ms_svc_pending ms with
| Some x8 => ((bv_unsigned x8 =? 93)%Z || (bv_unsigned x8 =? 94)%Z)
&& bv_eqb (ms_gpr ms 0) code
| None =>
match RiscvSemantics.step segs ms with
| MachineOk ms' => sim_c fuel' ms'
| MachineFault | MachineUnmodeled => false
end
end
end.

Lemma sstep_instr_inv : forall ms model ms' evs st,
m_vm_lazy model = [] ->
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
sstep segs (mkCfg ms model) evs st ->
evs = [] /\ st = SNext (mkCfg ms' model).
Proof.
intros ms model ms' evs st Hlazy Hsvc Hstep Hss.
inversion Hss; subst.
-
match goal with H : mi_account_step segs ms model = MachineOk _ |- _ =>
rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
rewrite Hstep in H; inversion H; subst end.
split; reflexivity.
-
match goal with H : mi_account_step segs ms model = MachineFault |- _ =>
rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
rewrite Hstep in H; discriminate end.
-
match goal with H : mi_account_step segs ms model = MachineUnmodeled |- _ =>
rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
rewrite Hstep in H; discriminate end.
-  congruence.
-  congruence.
-  congruence.
-  congruence.
-  congruence.
Qed.

Lemma star_halted_nil : forall c tr c',
m_halted (cfg_model c) <> None -> star segs c tr c' -> tr = [] /\ c' = c.
Proof.
intros c tr c' Hh Hstar. inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst.
- split; reflexivity.
- exfalso. destruct c as [ms model]. cbn in Hh.
inversion Hss; subst; cbn in Hh; congruence.
Qed.

Definition exit_post (fs : Fs.Fs) : post :=
fun tr o => tr = [ExitEv (bv_and code (Z_to_bv 64 255)) fs]
/\ exits_with (bv_and code (Z_to_bv 64 255)) tr o.

Definition on_path (c : config) : Prop :=
(m_halted (cfg_model c) = None /\ m_vm_lazy (cfg_model c) = [] /\
to_exit (cfg_ms c))
\/ m_halted (cfg_model c) <> None.

End WithSegs.

Definition overlay_argc_bytes (sp : word) (argc : nat)
(base_mem : word -> option byte) : word -> option byte :=
let bytes := word_le8 (nat_to_word argc) in
fun addr =>
if (bv_unsigned addr =? bv_unsigned sp)%Z then nth_error bytes 0
else if (bv_unsigned addr =? bv_unsigned sp + 1)%Z then nth_error bytes 1
else if (bv_unsigned addr =? bv_unsigned sp + 2)%Z then nth_error bytes 2
else if (bv_unsigned addr =? bv_unsigned sp + 3)%Z then nth_error bytes 3
else if (bv_unsigned addr =? bv_unsigned sp + 4)%Z then nth_error bytes 4
else if (bv_unsigned addr =? bv_unsigned sp + 5)%Z then nth_error bytes 5
else if (bv_unsigned addr =? bv_unsigned sp + 6)%Z then nth_error bytes 6
else if (bv_unsigned addr =? bv_unsigned sp + 7)%Z then nth_error bytes 7
else base_mem addr.

Definition enum_state (segs : list Segment) (init_pc : N) (ph : PhdrInfo)
(init_sp : word) (init_rnd : EntryDraw) (argc : nat)
(base : word -> option byte) (uid : word)
(hw : word) : machine_state :=
{| ms_regs       := ms_regs (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw); ms_fregs := ms_fregs (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw);
ms_pc_val     := ms_pc_val (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw);
ms_svc_pending := ms_svc_pending (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw);
ms_resv       := ms_resv (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw); ms_fcsr := ms_fcsr (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw);
ms_mem        := overlay_argc_bytes init_sp argc base;
ms_rom        := ms_rom (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw) |}.

