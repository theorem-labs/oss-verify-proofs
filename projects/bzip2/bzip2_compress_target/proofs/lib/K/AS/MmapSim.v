(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the place_declined_b premise of the tmw_mmap constructor, Linux's mmap placement and munmap over maps_subtract). *)
(* [comment removed for export] *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Mm.Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Placement.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Common Require CfgStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import SimInv ExitSim PropExec CatSim CatExec SeqExec StreamSim AllocSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Set Keyed Unification.

Import ListNotations.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zfill (a n : word) (m : word -> option byte) : word -> option byte :=
  zmem m a n.

Lemma zfill_out : forall a n m (x : word),
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
  zfill a n m x = m x.
Proof. intros a n m x Hx. exact (zmem_out m a n x Hx). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition munmap_model (addr n : word) (m : Model) : Model :=
  with_mmap_destroyed addr n (mmap_fixed_destroyed_next (m_vmmaps m) addr n) m.

(** A cut that one entry exactly fills, on a ledger whose every other
    entry misses it, removes that entry and nothing else: the form a
    proof that tracks its ledger entry by entry can read [munmap_model]'s
    [vm_maps] in. *)
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

(* [comment removed for export] *)
Definition page_round_up (len : word) : word :=
  Z_to_bv 64 (page_round_up_Z (bv_unsigned len)).

(* [comment removed for export] *)
Definition grant_ok (hint : word) (m : Model) (a : word) (n : Z) : bool :=
  Placement.linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a
  && (bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
  && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n)
  && (vm_backing_used m + n <=? vm_limit (m_vmmaps m))%Z.

Lemma munmap_model_halted : forall addr n m, m_halted (munmap_model addr n m) = m_halted m.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma munmap_model_no_lazy : forall addr n m,
  m_vm_lazy m = [] -> m_vm_lazy (munmap_model addr n m) = [].
Proof.
  intros addr n m Hlazy. unfold munmap_model, with_mmap_destroyed,
    vm_forget_range, with_vm_backing, with_vmmaps.
  cbn [m_vm_lazy]. rewrite Hlazy. reflexivity.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mmap_args_ok (ms : machine_state) : Prop :=
  ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 3
  /\ ms_gpr ms 3 = Z_to_bv 64 34 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
  /\ ms_gpr ms 5 = Z_to_bv 64 0.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition munmap_args_ok (ms : machine_state) (model : Model) : Prop :=
  (bv_unsigned (ms_gpr ms 0) mod page_size = 0)%Z /\
  ms_gpr ms 1 <> Z_to_bv 64 0 /\
  (bv_unsigned (ms_gpr ms 0) + page_round_up_Z (bv_unsigned (ms_gpr ms 1)) <= TASK_SIZE)%Z /\
  map_has (vm_maps (m_vmmaps model)) (ms_gpr ms 0)
    (page_round_up (ms_gpr ms 1)) = true.

(* [comment removed for export] *)
Definition munmap_eff (ms : machine_state) : SyscallEffect :=
  mkEffectU (Z_to_bv 64 0) [] [] [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))] [] [].

(* [comment removed for export] *)
Lemma syscall_spec_munmap : forall segs ms x8 model o,
  bv_unsigned x8 = 215%Z ->
  (syscall_spec (sys_input segs ms x8) model o
   <-> munmap_spec (ms_gpr ms 0) (ms_gpr ms 1) (sys_input segs ms x8) model o).
Proof.
  intros segs ms x8 model o Hno.
  unfold syscall_spec, dispatch.
  rewrite in_sysno_sys_input, Hno. reflexivity.
Qed.

(* [comment removed for export] *)
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

(** The refusal the same arm admits beside the cut: nothing changes.
    Linux answers it when [vma_iter_clear_gfp] (mm/vma.c, Linux
    v6.18.46) cannot get a maple-tree node, and re-attaches the VMAs it
    detached, so the mapping keeps its pages. *)
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

(** The two answers are the only ones: the cut, or a refusal from
    [munmap_errnos] that changes nothing. *)
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


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma adv_mmap_grant : forall regs pc sv mem rom a n,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := sv;
       ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}
    (mkEffect a [] [(a, n)]))
  = mkst (regupd regs 10 a) (v_addi pc 4) (zfill a n mem) rom.
Proof.
  intros regs pc sv mem rom a n.
  assert (Hm : apply_zeros (apply_unmaps mem []) [(a, n)] = zfill a n mem).
  { cbn [apply_unmaps]. unfold zfill. exact (apply_zeros_one mem a n). }
  unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies
       apply_writes apply_copies].
  unfold mkst, regupd.
  rewrite b_npc4, Hm. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
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

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma adv_munmap : forall regs pc sv mem rom a n,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := sv;
       ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}
    (mkEffectU (Z_to_bv 64 0) [] [] [(a, n)] [] []))
  = mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (unfill a n mem) rom.
Proof.
  intros regs pc sv mem rom a n.
  assert (Hm : apply_writes (apply_zeros (apply_unmaps mem [(a, n)]) []) []
               = unfill a n mem).
  { cbn [apply_writes apply_zeros].
    apply functional_extensionality. intro x.
    unfold apply_unmaps, zeros_cover, unfill. cbn [existsb fst snd].
    rewrite orb_false_r. reflexivity. }
  unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies].
  unfold mkst, regupd.
  rewrite b_npc4, Hm. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
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
(** The put-style retry loop realizing one buffer: a write-pending state
    offering the remainder [rest]; the environment delivers any nonempty
    prefix, the loop reissues on the rest.  The trace contribution of the
    whole node is exactly the FULL buffer (WallSim's [to_wall] shape,
    inlined here because the continuation is the mutual [twm]). *)
with twm_pend : machine_state -> Model -> list byte -> list (list byte) -> word -> Prop :=
| twmp_write : forall ms model x8 rest bufs code,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 64%Z ->
    ms_gpr ms 0 = Z_to_bv 64 1 ->
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some rest ->
    (* the range [vfs_write]'s [access_ok] accepts; see [CatSim.write1_check_n] *)
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

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma twm_tail_write_rec : forall regs pc mem rom model rest bufs code,
  bv_unsigned (getr regs 17) = 64%Z ->
  reg_get regs 10 = Z_to_bv 64 1 ->
  ms_read_bytes {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                   ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
                   ms_mem := mem; ms_rom := rom |}
    (reg_get regs 11) (reg_get regs 12) = Some rest ->
  access_okb (reg_get regs 11) (bv_unsigned (reg_get regs 12)) = true ->
  (1 <= length rest)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
     twm_tail (mkst (regupd regs 10 (len_word (firstn n rest))) (v_addi pc 4) mem rom)
       model (skipn n rest) bufs code) ->
  twm_tail {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
              ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
              ms_mem := mem; ms_rom := rom |}
    model rest bufs code.
Proof.
  intros regs pc mem rom model rest bufs code H17 H10 Hr Hok Hnb Hcont.
  assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
  assert (E12 : Z_to_bv 5 (10 + Z.of_nat 2) = (12 : reg)) by (apply bv_eq; reflexivity).
  apply twmt_more; [exact Hnb|].
  eapply twmp_write.
  - cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E10. exact H10.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E11, E12. exact Hr.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E11, E12. exact Hok.
  - exact Hnb.
  - intros n Hn1 Hn2. rewrite adv_set. exact (Hcont n Hn1 Hn2).
Qed.

(* [comment removed for export] *)
Lemma twm_munmap_rec : forall regs pc mem rom model bufs code (a nlen : word),
  bv_unsigned (getr regs 17) = 215%Z ->
  reg_get regs 10 = a ->
  reg_get regs 11 = nlen ->
  (bv_unsigned a mod page_size = 0)%Z ->
  nlen <> Z_to_bv 64 0 ->
  (bv_unsigned a + page_round_up_Z (bv_unsigned nlen) <= TASK_SIZE)%Z ->
  map_has (vm_maps (m_vmmaps model)) a (page_round_up nlen) = true ->
  (forall e, In e munmap_errnos ->
     twm (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom)
         model bufs code) ->
  twm (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
            (unfill a (page_round_up nlen) mem) rom)
      (munmap_model a (page_round_up nlen) model) bufs code ->
  twm {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
         ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := mem; ms_rom := rom |}
      model bufs code.
Proof.
  intros regs pc mem rom model bufs code a nlen H17 Ha Hn Hal Hlen Hnw Hhas Hfail Hcont.
  assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
  eapply twm_munmap.
  - cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold munmap_args_ok, ms_gpr. cbn [ms_regs].
    rewrite E10, E11, Ha, Hn. auto.
  - intros e He. rewrite adv_set. exact (Hfail e He).
  - unfold munmap_eff, ms_gpr. cbn [ms_regs].
    rewrite E10, E11, Ha, Hn.
    rewrite adv_munmap. exact Hcont.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* The cut returns 0, which is not one of [munmap_errnos], so it is not a
   refusal; the ENOMEM child of the same node is one, and the
   config-filtered step drops it. *)
Lemma munmap_ret0_not_refusal : forall segs' ms model x8,
  bv_unsigned x8 = 215%Z ->
  refusal_b (sys_input segs' ms x8) model (Z_to_bv 64 0) = false.
Proof.
  intros segs' ms model x8 Hno.
  apply CfgStep.refusal_b_munmap_below; [exact Hno|].
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. lia.
Qed.

Lemma sstep_cfg_munmap_inv : forall ms model x8 evs st,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  sstep_cfg segs CfgStep.kit_cfg (mkCfg ms model) evs st ->
  evs = [] /\
  st = SNext (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                    (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)).
Proof.
  intros ms model x8 evs st Hh Hlazy Hsvc Hno Hargs Hss.
  destruct (sstep_munmap_inv ms model x8 evs st Hh Hlazy Hsvc Hno Hargs
              (sstep_cfg_sub segs CfgStep.kit_cfg _ _ _ Hss))
    as [-> [(e & He & ->) | ->]].
  - exfalso.
    apply CfgStep.sstep_cfg_next_iff in Hss as [_ Hns]. apply Hns.
    split; [| split].
    + exact (CfgStep.kit_pending_off_sysno segs ms model x8 215 Hsvc Hno eq_refl).
    + rewrite (CfgStep.child_refusal_b_set_gpr0 segs ms model x8 (errno_ret e) model Hsvc Hh).
      exact (CfgStep.refusal_b_munmap_errno (sys_input segs ms x8) model e Hno He).
    + exists x8, (munmap_eff ms),
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model), [].
      cbn [cfg_ms cfg_model]. split; [exact Hsvc | split].
      * exact (munmap_ok segs ms x8 model Hno Hargs).
      * unfold munmap_eff. cbn [eff_ret].
        exact (munmap_ret0_not_refusal segs ms model x8 Hno).
  - split; reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive tmw : machine_state -> Model -> list (list byte) -> word
                -> list (list byte) -> word -> Prop :=
| tmw_mmap : forall ms model x8 bf cf bs cs,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 222%Z ->
    mmap_args_ok ms ->
    (* LPS 727298f3 (#144/#146): [check_mmap] tests [place_declined_b] ahead of
       the modeled arm, so the spec is a conditional where it was an
       unconditional [CheckOk]; the premise is the model's own,
       727298f3:theories/Common/MmapSim.v:1349. *)
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

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma tmw_mmap_rec : forall regs pc mem rom model bf cf bs cs,
  bv_unsigned (getr regs 17) = 222%Z ->
  reg_get regs 11 <> Z_to_bv 64 0 ->
  reg_get regs 12 = Z_to_bv 64 3 ->
  reg_get regs 13 = Z_to_bv 64 34 ->
  reg_get regs 14 = Z_to_bv 64 (-1) ->
  reg_get regs 15 = Z_to_bv 64 0 ->
  place_declined_b (m_kernel model) (m_vmmaps model) (reg_get regs 10)
    (page_round_up_Z (bv_unsigned (reg_get regs 11))) = false ->
  (forall e, In e mmap_errnos ->
     twm (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model bf cf) ->
  (forall a, grant_ok (reg_get regs 10) model a (page_round_up_Z (bv_unsigned (reg_get regs 11))) = true ->
     twm (mkst (regupd regs 10 a) (v_addi pc 4)
               (zfill a (page_round_up (reg_get regs 11)) mem) rom)
         (mmap_model a (page_round_up (reg_get regs 11)) model) bs cs) ->
  (exists a, grant_ok (reg_get regs 10) model a (page_round_up_Z (bv_unsigned (reg_get regs 11))) = true) ->
  tmw {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
         ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := mem; ms_rom := rom |}
      model bf cf bs cs.
Proof.
  intros regs pc mem rom model bf cf bs cs H17 H11 H12 H13 H14 H15
    Hdecl Hfail Hsucc Hex.
  assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
  assert (E12 : Z_to_bv 5 (10 + Z.of_nat 2) = (12 : reg)) by (apply bv_eq; reflexivity).
  assert (E13 : Z_to_bv 5 (10 + Z.of_nat 3) = (13 : reg)) by (apply bv_eq; reflexivity).
  assert (E14 : Z_to_bv 5 (10 + Z.of_nat 4) = (14 : reg)) by (apply bv_eq; reflexivity).
  assert (E15 : Z_to_bv 5 (10 + Z.of_nat 5) = (15 : reg)) by (apply bv_eq; reflexivity).
  eapply tmw_mmap.
  - cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold mmap_args_ok, ms_gpr. cbn [ms_regs].
    rewrite E11, E12, E13, E14, E15.
    auto.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E11. exact Hdecl.
  - intros e HIn. rewrite adv_set. apply Hfail; assumption.
  - intros a Hg. rewrite adv_mmap_grant.
    unfold ms_gpr in *. cbn [ms_regs] in *. rewrite E11 in *.
    apply Hsucc. exact Hg.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E11. exact Hex.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP1.
