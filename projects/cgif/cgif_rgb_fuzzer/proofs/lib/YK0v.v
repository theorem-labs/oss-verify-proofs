(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (munmap_model is the revision's mmap_fixed_destroyed_next, with maps_subtract_exact for an exact entry; munmap's check accepts the injected errnos, so its node lemma, inversion and walk have the refused branch; grant_ok asks Linux's own placement, linux_place_is; mmap's producers and the tmw mmap constructor take the place_declined_b premise; Placement imported). *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Placement.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Mm.Mmap.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK16 YK0o YK11 YK0j YK0i YK14 YK1d YK02.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Section d.
Context {fx : FPState}.

Lemma step_sb_any : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
RiscvSemantics.store_ok segs mem
(v_addi (getr regs rs1) (bv_signed imm)) 1%nat = true ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst regs (v_addi pc 4)
(wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
[Z_to_bv 8 (bv_unsigned (getr regs rs2))]) rom).
Proof.
intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
rewrite <- N_to_le_bytes_1_small.
apply (step_sb segs regs pc mem rom w rs1 rs2 imm); assumption.
Qed.
Lemma step_sb_at : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12)
(a v : word) (b : byte),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
v_addi (getr regs rs1) (bv_signed imm) = a ->
getr regs rs2 = v ->
Z_to_bv 8 (bv_unsigned v) = b ->
RiscvSemantics.store_ok segs mem a 1%nat = true ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst regs (v_addi pc 4) (wbytes mem a [b]) rom).
Proof.
intros segs regs pc mem rom w rs1 rs2 imm a v b Hf He Hd Ha Hv Hb Hok.
rewrite (step_sb_any segs regs pc mem rom w rs1 rs2 imm Hf He Hd).
- rewrite Ha, Hv, Hb. reflexivity.
- rewrite Ha. exact Hok.
Qed.

Definition zfill (a n : word) (m : word -> option byte) : word -> option byte :=
zmem m a n.
Lemma zfill_out : forall a n m (x : word),
(bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
zfill a n m x = m x.
Proof. intros a n m x Hx. exact (zmem_out m a n x Hx). Qed.

Definition munmap_model (addr n : word) (m : Model) : Model :=
  with_mmap_destroyed addr n (mmap_fixed_destroyed_next (m_vmmaps m) addr n) m.

Lemma iv_subtract_outside : forall (b s : word) lo hi,
  (0 < bv_unsigned s)%Z -> (lo < hi)%Z ->
  (bv_unsigned b + bv_unsigned s <= lo \/ hi <= bv_unsigned b)%Z ->
  iv_subtract b s lo hi = [(b, s)].
Proof.
  intros b s lo hi Hs Hlh Hd. unfold iv_subtract. cbv zeta.
  destruct Hd as [Hd|Hd].
  - rewrite (proj2 (Z.ltb_lt (bv_unsigned b) lo)) by lia.
    rewrite (proj2 (Z.ltb_ge hi (bv_unsigned b + bv_unsigned s))) by lia.
    rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite (proj2 (Z.ltb_ge (bv_unsigned b) lo)) by lia.
    rewrite (proj2 (Z.ltb_lt hi (bv_unsigned b + bv_unsigned s))) by lia.
    rewrite Z.max_l by lia.
    replace (bv_unsigned b + bv_unsigned s - bv_unsigned b)%Z
      with (bv_unsigned s) by lia.
    rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma maps_subtract_exact : forall l (a n : word),
  (0 < bv_unsigned n)%Z ->
  (forall b s, In (b, s) l -> (0 < bv_unsigned s)%Z) ->
  (forall b s, In (b, s) l -> b = a -> s = n) ->
  (forall b s, In (b, s) l -> b <> a ->
     (bv_unsigned b + bv_unsigned s <= bv_unsigned a
      \/ bv_unsigned a + bv_unsigned n <= bv_unsigned b)%Z) ->
  maps_subtract l (bv_unsigned a) (bv_unsigned a + bv_unsigned n)
  = map_remove l a.
Proof.
  induction l as [|[b s] r IH]; intros a n Hn Hpos Hu Hd; [reflexivity|].
  assert (IHr : maps_subtract r (bv_unsigned a) (bv_unsigned a + bv_unsigned n)
                = map_remove r a).
  { apply IH; [exact Hn
              | intros b' s' H; apply (Hpos b' s'); right; exact H
              | intros b' s' H; apply (Hu b' s'); right; exact H
              | intros b' s' H; apply (Hd b' s'); right; exact H]. }
  cbn [maps_subtract]. rewrite IHr.
  unfold map_remove. cbn [List.filter fst]. fold (map_remove r a).
  destruct (bv_eqb b a) eqn:E; cbn [negb].
  - apply bv_eqb_eq in E. subst b.
    rewrite (Hu a s (or_introl eq_refl) eq_refl).
    unfold iv_subtract. cbv zeta.
    rewrite (proj2 (Z.ltb_ge _ _) (Z.le_refl (bv_unsigned a))).
    rewrite (proj2 (Z.ltb_ge _ _) (Z.le_refl (bv_unsigned a + bv_unsigned n))).
    reflexivity.
  - assert (Hne : b <> a) by (intros ->; rewrite bv_eqb_refl in E; discriminate).
    rewrite (iv_subtract_outside b s); [reflexivity | | lia |].
    + exact (Hpos b s (or_introl eq_refl)).
    + exact (Hd b s (or_introl eq_refl) Hne).
Qed.
Definition mmap_model (a n : word) (m : Model) : Model :=
with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
((a, n) :: vm_maps (m_vmmaps m))
(vm_noaccess (m_vmmaps m))
(vm_start_brk (m_vmmaps m))
(vm_brk (m_vmmaps m))
(vm_limit (m_vmmaps m))
(vm_mmap_base (m_vmmaps m))
(vm_init_sp (m_vmmaps m))) m.
Definition page_round_up (len : word) : word :=
Z_to_bv 64 (page_round_up_Z (bv_unsigned len)).
Definition grant_ok (hint : word) (m : Model) (a : word) (n : Z) : bool :=
  linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a
  && (bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
  && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n)
  && (vm_backing_used m + n <=? vm_limit (m_vmmaps m))%Z.

Lemma grant_ok_intro : forall hint m a n,
  (0 < n)%Z -> (n mod page_size = 0)%Z ->
  linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a = true ->
  (vm_backing_used m + n <= vm_limit (m_vmmaps m))%Z ->
  grant_ok hint m a n = true.
Proof.
  intros hint m a n Hn Hnal Hpl Hbud.
  destruct (linux_place_is_admissible _ _ _ _ _ Hn Hnal Hpl)
    as (Hal & Hpos & Htop & Hfree).
  unfold grant_ok. rewrite Hpl, Hfree.
  rewrite (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos),
    (proj2 (Z.leb_le _ _) Htop), (proj2 (Z.leb_le _ _) Hbud).
  reflexivity.
Qed.
Lemma munmap_model_halted : forall addr n m, m_halted (munmap_model addr n m) = m_halted m.
Proof. reflexivity. Qed.


Lemma munmap_model_no_lazy : forall addr n m,
m_vm_lazy m = [] -> m_vm_lazy (munmap_model addr n m) = [].
Proof.
intros addr n m Hlazy. unfold munmap_model, with_mmap_destroyed,
vm_forget_range, with_vm_backing, with_vmmaps.
cbn [m_vm_lazy]. rewrite Hlazy. reflexivity.
Qed.
Lemma mmap_model_halted : forall a n m, m_halted (mmap_model a n m) = m_halted m.
Proof. reflexivity. Qed.


Lemma mmap_model_lazy : forall a n m,
m_vm_lazy (mmap_model a n m) = m_vm_lazy m.
Proof. reflexivity. Qed.
Lemma grant_ok_unpack : forall hint m a n,
  grant_ok hint m a n = true ->
  (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z /\
  (bv_unsigned a + n <= alloc_top (m_vmmaps m))%Z /\
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n) = true /\
  (vm_backing_used m + n <= vm_limit (m_vmmaps m))%Z.
Proof.
  intros hint m a n H. unfold grant_ok in H.
  rewrite !andb_true_iff in H.
  destruct H as [[[[[_ H1] H2] H3] H4] H5].
  apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3.
  apply Z.leb_le in H5.
  auto 7.
Qed.

Lemma grant_ok_place : forall hint m a n,
  grant_ok hint m a n = true ->
  linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a = true.
Proof.
  intros hint m a n H. unfold grant_ok in H.
  rewrite !andb_true_iff in H. tauto.
Qed.
Lemma region_free_cons : forall (b s : word) r (lo n : word),
region_free ((b, s) :: r) lo n = true ->
(bv_unsigned lo + bv_unsigned n <= bv_unsigned b
\/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo)%Z
/\ region_free r lo n = true.
Proof.
intros b s r lo n H. cbn [region_free] in H.
apply andb_true_iff in H. destruct H as [H1 H2].
split; [|exact H2].
apply negb_true_iff in H1. unfold iv_overlap in H1.
apply andb_false_iff in H1.
destruct H1 as [H1 | H1]; [right | left]; apply Z.ltb_ge in H1; lia.
Qed.





Definition mmap_args_ok (ms : machine_state) : Prop :=
ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 3
/\ ms_gpr ms 3 = Z_to_bv 64 34 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
/\ ms_gpr ms 5 = Z_to_bv 64 0.
Lemma mmap_args_ok_gates : forall ms,
mmap_args_ok ms ->
mmap_off_aligned_b (ms_gpr ms 5) = true /\
mmap_anon_b (ms_gpr ms 3) = true /\
w_is0 (ms_gpr ms 1) = false /\
mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5)
= true.
Proof.
intros ms (H1 & H2 & H3 & H4 & H5).
split; [unfold mmap_off_aligned_b; rewrite H5; reflexivity|].
split; [unfold mmap_anon_b; rewrite H3; reflexivity|].
split; [unfold w_is0; apply bv_eqb_neq; exact H1|].
unfold mmap_modeled_b. rewrite H2, H3, H5. reflexivity.
Qed.
Definition munmap_args_ok (ms : machine_state) (model : Model) : Prop :=
(bv_unsigned (ms_gpr ms 0) mod page_size = 0)%Z /\
ms_gpr ms 1 <> Z_to_bv 64 0 /\
(bv_unsigned (ms_gpr ms 0) + page_round_up_Z (bv_unsigned (ms_gpr ms 1)) <= TASK_SIZE)%Z /\
map_has (vm_maps (m_vmmaps model)) (ms_gpr ms 0)
(page_round_up (ms_gpr ms 1)) = true.
Definition munmap_eff (ms : machine_state) : SyscallEffect :=
mkEffectU (Z_to_bv 64 0) [] [] [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))] [] [].
Lemma syscall_spec_munmap : forall segs ms x8 model o,
bv_unsigned x8 = 215%Z ->
(syscall_spec (sys_input segs ms x8) model o
<-> munmap_spec (ms_gpr ms 0) (ms_gpr ms 1) (sys_input segs ms x8) model o).
Proof.
intros segs ms x8 model o Hno.
unfold syscall_spec, dispatch.
rewrite in_sysno_sys_input, Hno. reflexivity.
Qed.
Lemma munmap_check_modeled : forall ms model eff,
  munmap_args_ok ms model ->
  check_munmap (ms_gpr ms 0) (ms_gpr ms 1) eff model
  = match eff with
    | mkEffectU r [] [] us [] [] =>
        if errno_ret_in munmap_errnos r
        then match us with
             | [] => CheckOk model []
             | _ => CheckReject
             end
        else if w_is0 r
                && listNN_eqb us [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))]
        then CheckOk (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []
        else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms model eff (Hal & Hlen & Hnw & Hhas).
  unfold check_munmap.
  rewrite (proj2 (Z.eqb_eq _ _) Hal).
  unfold w_is0 at 1. rewrite (bv_eqb_neq _ _ Hlen).
  cbn [negb orb]. cbv zeta.
  rewrite (proj2 (Z.ltb_ge _ _) Hnw). cbv beta iota.
  unfold page_round_up in Hhas. rewrite Hhas. reflexivity.
Qed.
Lemma munmap_ok : forall segs ms x8 model,
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (munmap_eff ms)
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
Proof.
  intros segs ms x8 model Hno Ha.
  apply (proj2 (syscall_spec_munmap _ _ _ _ _ Hno)). apply check_munmap_sound_ok.
  rewrite (munmap_check_modeled ms model _ Ha).
  unfold munmap_eff, w_is0.
  replace (errno_ret_in munmap_errnos (Z_to_bv 64 0)) with false by reflexivity.
  cbv beta iota. rewrite bv_eqb_refl.
  rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

Lemma munmap_fail_ok : forall segs ms x8 model e,
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  In e munmap_errnos ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffect (errno_ret e) [] []) model []).
Proof.
  intros segs ms x8 model e Hno Ha HIn.
  apply (proj2 (syscall_spec_munmap _ _ _ _ _ Hno)). apply check_munmap_sound_ok.
  rewrite (munmap_check_modeled ms model _ Ha).
  rewrite errno_ret_in_intro by assumption. reflexivity.
Qed.

Lemma ENOMEM_in_munmap_errnos : In ENOMEM munmap_errnos.
Proof. left. reflexivity. Qed.
Lemma munmap_ok_inv : forall segs ms x8 model eff model' evs,
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  evs = [] /\
  ((exists e, In e munmap_errnos /\
     eff = mkEffect (errno_ret e) [] [] /\ model' = model)
   \/ (eff = munmap_eff ms /\
       model' = munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)).
Proof.
  intros segs ms x8 model eff model' evs Hno Ha Hspec.
  apply (proj1 (syscall_spec_munmap _ _ _ _ _ Hno)) in Hspec.
  apply check_munmap_complete_ok in Hspec.
  rewrite (munmap_check_modeled ms model eff Ha) in Hspec.
  destruct eff as [r ws zs us cs copyins]; destruct ws as [|? ?];
    [destruct zs as [|? ?]|]; try discriminate.
  destruct cs as [|? ?]; [destruct copyins as [|? ?]|]; try discriminate.
  destruct (errno_ret_in munmap_errnos r) eqn:He.
  - destruct us as [|? ?]; [|discriminate].
    inversion Hspec; clear Hspec; subst.
    apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
    split; [reflexivity|]. left. exists e. auto.
  - destruct (w_is0 r
              && listNN_eqb us [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))])
      eqn:HC; [|discriminate].
    inversion Hspec; clear Hspec; subst.
    apply andb_true_iff in HC as [Hr Hus].
    unfold w_is0 in Hr. apply bv_eqb_eq in Hr; subst r.
    apply listNN_eqb_eq in Hus; subst us.
    split; [reflexivity|]. right. unfold munmap_eff. auto.
Qed.
Lemma munmap_no_unmodeled : forall segs ms x8 model,
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
  intros segs ms x8 model Hno Ha Hspec.
  apply (proj1 (syscall_spec_munmap _ _ _ _ _ Hno)) in Hspec.
  apply (check_munmap_complete_unmodeled _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
    in Hspec.
  rewrite (munmap_check_modeled ms model _ Ha) in Hspec.
  replace (errno_ret_in munmap_errnos (Z_to_bv 64 0)) with false in Hspec
    by reflexivity.
  cbv beta iota in Hspec.
  destruct (w_is0 (Z_to_bv 64 0)
            && listNN_eqb [] [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))]);
    discriminate.
Qed.
Lemma syscall_spec_mmap : forall segs ms x8 model o,
bv_unsigned x8 = 222%Z ->
(syscall_spec (sys_input segs ms x8) model o
<-> mmap_spec (ms_gpr ms 0) (ms_gpr ms 1) (ms_gpr ms 2) (ms_gpr ms 3)
(ms_gpr ms 4) (ms_gpr ms 5) (sys_input segs ms x8) model o).
Proof.
intros segs ms x8 model o Hno.
unfold syscall_spec, dispatch.
rewrite in_sysno_sys_input, Hno. reflexivity.
Qed.
Lemma ENOMEM_in_mmap_errnos : In ENOMEM mmap_errnos.
Proof. left. reflexivity. Qed.

(* The revision's decline (Mmap.place_declined_b) sits AHEAD of the [match eff]
in the freely-placed arm, so it gates the errno refusal too: this PRODUCER is
false as it stood even though it returns a refusal, and the sweep's name-keyed
list did not reach it. Same premise, same place as [mmap_succ_ok]'s. *)
Lemma mmap_fail_ok : forall segs ms x8 model e,
bv_unsigned x8 = 222%Z -> mmap_args_ok ms -> In e mmap_errnos ->
place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
  (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
syscall_spec (sys_input segs ms x8) model
(Ok (mkEffect (errno_ret e) [] []) model []).
Proof.
intros segs ms x8 model e Hno Ha HIn Hdecl.
destruct (mmap_args_ok_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
apply (proj2 (syscall_spec_mmap _ _ _ _ _ Hno)). apply check_mmap_sound_ok.
unfold check_mmap, check_mmap_fixed_overflow. cbv beta.
rewrite Hoff, Hanon, Hl, Hmb. cbn [negb]. cbv beta iota zeta.
rewrite Hdecl. cbv beta iota zeta.
rewrite errno_ret_in_intro by assumption. reflexivity.
Qed.
Lemma grant_not_errno : forall hint model a n,
(0 <= n)%Z -> grant_ok hint model a n = true ->
errno_ret_in mmap_errnos a = false.
Proof.
intros hint model a n Hn Hg.
destruct (grant_ok_unpack _ _ _ _ Hg) as (_ & _ & Hce & _).
apply errno_ret_in_below; [reflexivity|].
alloc_top_bounds. unfold two_pow_64 in *. lia.
Qed.
(* The revision declines a hint it cannot place (Mmap.place_declined_b, outside
the [alt]), so a PRODUCER is false as it stood: it must say that this call is
one the model answers. The condition is about the HINT, not the chosen address,
so [grant_ok] does not give it -- [linux_place_is] can hold while the hint ends
inside the stack's guard gap. It is a premise rather than a conjunct of
[mmap_args_ok] so that the obligation stays visible at every call site. *)
Lemma mmap_succ_ok : forall segs ms x8 model a,
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])
        (mmap_model a (page_round_up (ms_gpr ms 1)) model) []).
Proof.
  intros segs ms x8 model a Hno Ha Hdecl Hg.
  destruct (mmap_args_ok_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
  destruct Ha as (_ & _ & Hflags & _ & _).
  apply (proj2 (syscall_spec_mmap _ _ _ _ _ Hno)). apply check_mmap_sound_ok.
  unfold check_mmap, check_mmap_fixed_overflow. cbv beta.
  rewrite Hoff, Hanon, Hl, Hmb. cbn [negb]. cbv beta iota zeta.
  rewrite Hdecl. cbv beta iota zeta.
  rewrite (grant_not_errno (ms_gpr ms 0) model a
             (page_round_up_Z (bv_unsigned (ms_gpr ms 1))));
    [ | apply page_round_up_Z_nonneg; pose proof (u64_range (ms_gpr ms 1)); lia
      | exact Hg ].
  unfold grant_ok in Hg. rewrite !andb_true_iff in Hg.
  destruct Hg as [[[[[Hp H1] H2] H3] H4] H5].
  rewrite Hflags.
  assert (Hnr : mmap_noreserve_b (Z_to_bv 64 34) = false)
    by (vm_compute; reflexivity).
  unfold mmap_noreserve_backed_ok, with_mmap_backing. rewrite Hnr.
  rewrite Hp, H5.
  unfold page_round_up. cbn [listNN_eqb]. rewrite !bv_eqb_refl.
  reflexivity.
Qed.
Lemma mmap_ok_inv : forall segs ms x8 model eff model' evs,
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  evs = [] /\
  ((exists e, In e mmap_errnos /\ eff = mkEffect (errno_ret e) [] []
      /\ model' = model) \/
   (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true
      /\ eff = mkEffect a [] [(a, page_round_up (ms_gpr ms 1))]
      /\ model' = mmap_model a (page_round_up (ms_gpr ms 1)) model)).
Proof.
  intros segs ms x8 model eff model' evs Hno Ha Hspec.
  destruct (mmap_args_ok_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
  destruct Ha as (_ & _ & Hflags & _ & _).
  apply (proj1 (syscall_spec_mmap _ _ _ _ _ Hno)) in Hspec.
  apply check_mmap_complete_ok in Hspec.
  unfold check_mmap, check_mmap_fixed_overflow in Hspec. cbv beta in Hspec.
  rewrite Hoff, Hanon, Hl, Hmb in Hspec. cbn [negb] in Hspec.
  rewrite Hflags in Hspec.
  (* A CONSUMER needs no premise: [CheckUnmodeled] is a different constructor
  from [CheckOk], so the revision's decline branch dies by discrimination and
  the statement keeps its full strength. *)
  destruct (place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
  (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) eqn:Hdecl; [discriminate|].
  assert (Hnr : mmap_noreserve_b (Z_to_bv 64 34) = false)
    by (vm_compute; reflexivity).
  unfold mmap_noreserve_backed_ok, with_mmap_backing in Hspec.
  rewrite Hnr in Hspec.
  destruct eff as [r ws zs us cs copyins].
  cbv beta iota zeta in Hspec.
  destruct ws as [|w ws]; [|discriminate].
  destruct us as [|u us]; [|discriminate].
  destruct cs as [|c cs]; [|discriminate].
  destruct copyins as [|copyin copyins]; [|discriminate].
  destruct (errno_ret_in mmap_errnos r) eqn:Herr; rewrite ?Herr in Hspec;
    cbv beta iota in Hspec.
  - destruct zs as [|z zs]; [|discriminate].
    inversion Hspec; subst.
    split; [reflexivity|]. left.
    apply errno_ret_in_true in Herr. destruct Herr as (e & HIn & ->).
    exists e. auto.
  - destruct (linux_place_is (m_vmmaps model) (kb_thp (m_kernel model))
                (ms_gpr ms 0) (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) r
              && (vm_backing_used model
                  + page_round_up_Z (bv_unsigned (ms_gpr ms 1))
                  <=? vm_limit (m_vmmaps model))%Z) eqn:Hcond;
      rewrite ?Hcond in Hspec.
    2:{ rewrite andb_false_l in Hspec. discriminate. }
    destruct (listNN_eqb zs
                [(r, Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))]) eqn:Hzs;
      rewrite ?Hzs in Hspec.
    2:{ rewrite andb_false_r in Hspec. discriminate. }
    cbn [andb] in Hspec.
    apply listNN_eqb_eq in Hzs. subst zs.
    inversion Hspec; subst.
    split; [reflexivity|]. right.
    exists r. split; [|split].
    + apply andb_true_iff in Hcond as [Hpl Hbud].
      apply (grant_ok_intro _ _ _ _ (proj1 (mmap_grant_len_ok _ Hl))
               (proj2 (mmap_grant_len_ok _ Hl)) Hpl).
      now apply Z.leb_le.
    + unfold page_round_up. reflexivity.
    + reflexivity.
Qed.
(* A NO-UNMODELED statement is false as it stood: the revision answers
[unmodeled] for a hint it declines. The premise says this call is not one of
those; everything below it is the old proof. *)
Lemma mmap_no_unmodeled : forall segs ms x8 model,
bv_unsigned x8 = 222%Z ->
mmap_args_ok ms ->
place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
  (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
intros segs ms x8 model Hno Ha Hdecl Hspec.
destruct (mmap_args_ok_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
apply (proj1 (syscall_spec_mmap _ _ _ _ _ Hno)) in Hspec.
apply (check_mmap_complete_unmodeled _ _ _ _ _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
in Hspec.
unfold check_mmap, check_mmap_fixed_overflow in Hspec. cbv beta in Hspec.
rewrite Hoff, Hanon, Hl, Hmb in Hspec. cbn [negb] in Hspec.
rewrite Hdecl in Hspec.
cbv beta iota zeta in Hspec.
assert (E : errno_ret_in mmap_errnos (Z_to_bv 64 0) = false) by reflexivity.
rewrite E in Hspec. cbv beta iota in Hspec.
match type of Hspec with (if ?b then _ else _) = _ => destruct b end;
discriminate.
Qed.

Definition unfill (a n : word) (m : word -> option byte) : word -> option byte :=
fun x => if Z.leb (bv_unsigned a) (bv_unsigned x)
&& Z.ltb (bv_unsigned x) (bv_unsigned a + bv_unsigned n)
then None else m x.
Lemma unfill_out : forall a n m (x : word),
(bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
unfill a n m x = m x.
Proof.
intros a n m x Hx. unfold unfill.
destruct Hx as [Hx | Hx].
- rewrite (proj2 (Z.leb_gt (bv_unsigned a) (bv_unsigned x))) by lia. reflexivity.
- rewrite (proj2 (Z.ltb_ge (bv_unsigned x) (bv_unsigned a + bv_unsigned n))) by lia.
rewrite andb_false_r. reflexivity.
Qed.


Section f.
Variable segs : list Segment.
Inductive twm : machine_state -> Model -> list (list byte) -> word -> Prop :=
| twm_exit : forall ms model x8,
ms_svc_pending ms = Some x8 ->
is_exit_no x8 ->
twm ms model [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
| twm_write : forall ms model buf bufs code,
(1 <= length buf)%nat ->
twm_pend ms model buf bufs code ->
twm ms model (buf :: bufs) code
| twm_munmap : forall ms model x8 bufs code,
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 215%Z ->
munmap_args_ok ms model ->
(forall e, In e munmap_errnos ->
twm (advance_past_svc (set_gpr0 ms (errno_ret e))) model bufs code) ->
twm (advance_past_svc (apply_effect ms (munmap_eff ms)))
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) bufs code ->
twm ms model bufs code
| twm_step : forall ms ms' model bufs code,
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
twm ms' model bufs code ->
twm ms model bufs code
with twm_pend : machine_state -> Model -> list byte -> list (list byte) -> word -> Prop :=
| twmp_write : forall ms model x8 rest bufs code,
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = Z_to_bv 64 1 ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some rest ->
access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
(1 <= length rest)%nat ->
(forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
twm_tail (advance_past_svc (set_gpr0 ms (len_word (firstn n rest)))) model
(skipn n rest) bufs code) ->
twm_pend ms model rest bufs code
with twm_tail : machine_state -> Model -> list byte -> list (list byte) -> word -> Prop :=
| twmt_done : forall ms model bufs code,
twm ms model bufs code ->
twm_tail ms model [] bufs code
| twmt_more : forall ms model rest bufs code,
(1 <= length rest)%nat ->
twm_pend ms model rest bufs code ->
twm_tail ms model rest bufs code
| twmt_step : forall ms ms' model rest bufs code,
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
twm_tail ms' model rest bufs code ->
twm_tail ms model rest bufs code.
Scheme twm_min := Minimality for twm Sort Prop
with twm_pend_min := Minimality for twm_pend Sort Prop
with twm_tail_min := Minimality for twm_tail Sort Prop.
Combined Scheme twm_mutind from twm_min, twm_pend_min, twm_tail_min.

Lemma msteps_twm : forall ms ms' model bufs code,
msteps segs ms ms' -> twm ms' model bufs code -> twm ms model bufs code.
Proof.
intros ms ms' model bufs code H; induction H; [auto|].
intro Hw. eapply twm_step; eauto.
Qed.
Lemma msteps_twm_tail : forall ms ms' model rest bufs code,
msteps segs ms ms' -> twm_tail ms' model rest bufs code ->
twm_tail ms model rest bufs code.
Proof.
intros ms ms' model rest bufs code H; induction H; [auto|].
intro Hw. eapply twmt_step; eauto.
Qed.




Lemma sstep_munmap_inv : forall ms model x8 evs st,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [] /\
  ((exists e, In e munmap_errnos /\
      st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model)) \/
   st = SNext (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                     (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model))).
Proof.
  intros ms model x8 evs st Hh Hlazy Hsvc Hno Hargs Hss.
  inversion Hss; subst; try congruence.
  - (* sstep_syscall *)
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (Hevs & Hcase);
      subst evs0
    end.
    split; [reflexivity|].
    destruct Hcase as [(e & HIn & -> & ->) | (-> & ->)].
    + left. exists e.
      match goal with
      | Hmat : materialize_model_accesses model _ = Some _ |- _ =>
        rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat;
        inversion Hmat; subst
      end.
      split; [assumption |].
      rewrite apply_effect_no_write. reflexivity.
    + right.
      match goal with
      | Hmat : materialize_model_accesses
          (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) _ = Some _ |- _ =>
        rewrite (materialize_model_accesses_no_lazy _ _
          (munmap_model_no_lazy _ _ _ Hlazy)) in Hmat;
        inversion Hmat; subst
      end.
      reflexivity.
  - (* sstep_syscall_materialization_fault: no lazy range can fault *)
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (_ & Hcase);
      destruct Hcase as [(? & ? & -> & ->) | (-> & ->)];
      [ rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat
      | rewrite (materialize_model_accesses_no_lazy _ _
          (munmap_model_no_lazy _ _ _ Hlazy)) in Hmat ];
      discriminate
    end.
  - (* sstep_exit : munmap leaves haltedness unchanged *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (_ & Hcase);
      destruct Hcase as [(? & ? & _ & ->) | (_ & ->)];
      [ rewrite Hh in H6
      | rewrite munmap_model_halted, Hh in H6 ];
      discriminate
    end.
  - (* sstep_killed : munmap leaves it unkilled for the same reason *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some ?sig |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (_ & Hcase);
      destruct Hcase as [(? & ? & _ & ->) | (_ & ->)];
      [ rewrite (m_killed_of_m_halted_none _ Hh) in H6
      | rewrite m_killed_of_m_halted_none in H6;
        [| rewrite munmap_model_halted; exact Hh] ];
      discriminate
    end.
  - (* sstep_syscall_unmodeled *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      exact (munmap_no_unmodeled segs ms x8 model Hno Hargs H3)
    end.
Qed.
Definition twm_post (bufs : list (list byte)) (code : word) (fs : Fs.Fs) : post :=
fun tr o => tr = wevents bufs ++ [ExitEv code fs] /\ exits_with code tr o.
Definition twm_rest_post (rest : list byte) (bufs : list (list byte)) (code : word)
(fs : Fs.Fs) : post :=
fun tr o => tr = map (WriteEv (Z_to_bv 64 1)) rest ++ wevents bufs ++ [ExitEv code fs]
/\ exits_with code tr o.




Inductive tmw : machine_state -> Model -> list (list byte) -> word
-> list (list byte) -> word -> Prop :=
| tmw_mmap : forall ms model x8 bf cf bs cs,
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 222%Z ->
mmap_args_ok ms ->
(* The threading boundary: the premise belongs on this CONSTRUCTOR, exactly as
the model carries it at 727298f3:theories/Common/MmapSim.v:1345-1357. Every
consumer of [tmw] gets it by inversion, so nothing above here needs a new
premise and the threading stops at this line. [tmw_step] carries none. *)
place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
  (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
(forall e, In e mmap_errnos ->
twm (advance_past_svc (set_gpr0 ms (errno_ret e))) model bf cf) ->
(forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
twm (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
(mmap_model a (page_round_up (ms_gpr ms 1)) model) bs cs) ->
(exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
tmw ms model bf cf bs cs
| tmw_step : forall ms ms' model bf cf bs cs,
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
tmw ms' model bf cf bs cs ->
tmw ms model bf cf bs cs.
Lemma msteps_tmw : forall ms ms' model bf cf bs cs,
msteps segs ms ms' -> tmw ms' model bf cf bs cs -> tmw ms model bf cf bs cs.
Proof.
intros ms ms' model bf cf bs cs H; induction H; [auto|].
intro Hw. eapply tmw_step; eauto.
Qed.

Lemma sstep_mmap_inv : forall ms model x8 evs st,
m_halted model = None ->
m_vm_lazy model = [] ->
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 222%Z ->
mmap_args_ok ms ->
place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
  (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
sstep segs (mkCfg ms model) evs st ->
evs = [] /\
((exists e, In e mmap_errnos /\
st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model)) \/
(exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true /\
st = SNext (mkCfg (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
(mmap_model a (page_round_up (ms_gpr ms 1)) model)))).
Proof.
intros ms model x8 evs st Hh Hlazy Hsvc Hno Hargs Hdecl Hss.
inversion Hss; subst; try congruence.
-
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (Hevs & Hcase);
subst evs0
end.
split; [reflexivity|].
destruct Hcase as [(e & HIn & -> & ->) | (a & Hg & -> & ->)].
+ left. exists e.
match goal with
| Hmat : materialize_model_accesses model _ = Some _ |- _ =>
rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat;
inversion Hmat; subst
end.
split; [assumption |].
rewrite apply_effect_no_write. reflexivity.
+ match goal with
| Hmat : materialize_model_accesses (mmap_model a _ model) _ = Some _ |- _ =>
rewrite (materialize_model_accesses_no_lazy _ _
(eq_trans (mmap_model_lazy _ _ _) Hlazy)) in Hmat;
inversion Hmat; subst
end.
right. exists a. auto.
-
exfalso.
match goal with
| H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
Hmat : materialize_model_accesses ?model' _ = None |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
as (_ & Hcase);
destruct Hcase as [(? & ? & ? & Hm) | (? & ? & ? & Hm)]; subst model';
[ rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat
| rewrite (materialize_model_accesses_no_lazy _ _
(eq_trans (mmap_model_lazy _ _ _) Hlazy)) in Hmat ];
discriminate
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_halted ?model' = Some ?code |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (_ & Hcase);
destruct Hcase as [(? & ? & ? & Hm) | (? & ? & ? & Hm)]; subst model';
[ rewrite Hh in H6; discriminate
| rewrite mmap_model_halted, Hh in H6; discriminate ]
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_killed ?model' = Some ?sig |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (_ & Hcase);
destruct Hcase as [(e & _ & _ & Hm) | (a & _ & _ & Hm)]; subst model';
[ rewrite (m_killed_of_m_halted_none _ Hh) in H6; discriminate
| assert (Hhn : m_halted
(mmap_model a (page_round_up (ms_gpr ms 1)) model) = None)
by (rewrite mmap_model_halted; exact Hh);
rewrite (m_killed_of_m_halted_none _ Hhn) in H6; discriminate ]
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
assert (Hx : x = x8) by congruence; subst x;
exact (mmap_no_unmodeled segs ms x8 model Hno Hargs Hdecl H3)
end.
Qed.
Definition tmw_post (bf : list (list byte)) (cf : word) (bs : list (list byte)) (cs : word)
(fs : Fs.Fs) : post :=
fun tr o => (tr = wevents bf ++ [ExitEv cf fs] /\ exits_with cf tr o)
\/ (tr = wevents bs ++ [ExitEv cs fs] /\ exits_with cs tr o).



Definition two_traces (bf : list (list byte)) (cf : word)
(bs : list (list byte)) (cs : word)
(fs : Fs.Fs) (tr : list event) : Prop :=
is_prefix tr (wevents bf ++ [ExitEv cf fs]) \/
is_prefix tr (wevents bs ++ [ExitEv cs fs]).







End f.






End d.
