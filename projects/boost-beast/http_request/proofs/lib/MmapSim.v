(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import RelSpec SimInv ExitSim PropExec CatSim CatExec SeqExec StreamSim AllocSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma v_srli_div : forall (x : word) (sh : Z), (0 <= sh < 64)%Z ->
  bv_unsigned (v_srli x sh) = (bv_unsigned x / 2 ^ sh)%Z.
Proof.
  intros x sh Hsh. unfold v_srli.
  rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  rewrite Z.shiftr_div_pow2 by lia.
  pose proof (u64_range x) as Hx.
  assert (Hp : (0 < 2 ^ sh)%Z) by (apply Z.pow_pos_nonneg; lia).
  assert (Hle : (bv_unsigned x / 2 ^ sh <= bv_unsigned x)%Z)
    by (apply Z.div_le_upper_bound; nia).
  assert (H0 : (0 <= bv_unsigned x / 2 ^ sh)%Z) by (apply Z.div_pos; lia).
  apply Z.mod_small. lia.
Qed.

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

Lemma wbytes_snoc : forall (bs : list byte) (m : word -> option byte)
                           (a : word) (b : byte),
  wbytes m a (bs ++ [b]) = wbytes (wbytes m a bs) (a + nat_to_word (length bs)) [b].
Proof.
  induction bs as [|x bs IH]; intros m a b.
  - cbn [app wbytes length]. rewrite word_add_0. reflexivity.
  - cbn [app wbytes length].
    rewrite IH. f_equal.
    rewrite word1_nat, nat_to_word_add_merge. reflexivity.
Qed.

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
Lemma rdn_zfill_out : forall segs a n m (x : word) k,
  (bv_unsigned x + Z.of_nat k <= 2 ^ 64)%Z ->
  (bv_unsigned x + Z.of_nat k <= bv_unsigned a
   \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
  rdn segs (zfill a n m) x k = rdn segs m x k.
Proof.
  intros segs a n m x k Hnw Hd. exact (rdn_zmem_out segs m a n x k Hnw Hd).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition munmap_model (addr n : word) (m : Model) : Model :=
  with_mmap_destroyed addr n
    (mkVmMapsFull (vm_reserved (m_vmmaps m))
               (map_remove (vm_maps (m_vmmaps m)) addr)
               (maps_subtract (vm_noaccess (m_vmmaps m))
                  (bv_unsigned addr)
                  (bv_unsigned addr + bv_unsigned n))
               (vm_start_brk (m_vmmaps m))
               (vm_brk (m_vmmaps m))
               (vm_limit (m_vmmaps m))
               (vm_mmap_base (m_vmmaps m))
               (vm_init_sp (m_vmmaps m))) m.

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
Definition place_ok (h : VmMaps) (a : word) (n : Z) : bool :=
  (bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + n <=? alloc_top h)%Z
  && region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 n).

(* [comment removed for export] *)
Definition grant_ok (hint : word) (m : Model) (a : word) (n : Z) : bool :=
  (bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
  && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n)
  && (vm_backing_used m + n <=? vm_limit (m_vmmaps m))%Z.

Lemma munmap_model_halted : forall addr n m, m_halted (munmap_model addr n m) = m_halted m.
Proof. reflexivity. Qed.
Lemma munmap_model_fs : forall addr n m, m_fs (munmap_model addr n m) = m_fs m.
Proof. reflexivity. Qed.
Lemma munmap_model_fd1chan : forall addr n m, fd1chan m -> fd1chan (munmap_model addr n m).
Proof. intros addr n m H. exact H. Qed.
Lemma munmap_model_no_lazy : forall addr n m,
  m_vm_lazy m = [] -> m_vm_lazy (munmap_model addr n m) = [].
Proof.
  intros addr n m Hlazy. unfold munmap_model, with_mmap_destroyed,
    vm_forget_range, with_vm_backing, with_vmmaps.
  cbn [m_vm_lazy]. rewrite Hlazy. reflexivity.
Qed.
Lemma mmap_model_halted : forall a n m, m_halted (mmap_model a n m) = m_halted m.
Proof. reflexivity. Qed.
Lemma mmap_model_fs : forall a n m, m_fs (mmap_model a n m) = m_fs m.
Proof. reflexivity. Qed.
Lemma mmap_model_fd1chan : forall a n m, fd1chan m -> fd1chan (mmap_model a n m).
Proof. intros a n m H. exact H. Qed.
Lemma mmap_model_lazy : forall a n m,
  m_vm_lazy (mmap_model a n m) = m_vm_lazy m.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma place_ok_unpack : forall h a n,
  place_ok h a n = true ->
  (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z /\
  (bv_unsigned a + n <= alloc_top h)%Z /\
  region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 n) = true.
Proof.
  intros h a n H. unfold place_ok in H.
  rewrite !andb_true_iff in H.
  destruct H as [[[H1 H2] H3] H4].
  apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3.
  auto.
Qed.

Lemma place_ok_intro : forall h a n,
  (bv_unsigned a mod page_size = 0)%Z -> (0 < bv_unsigned a)%Z ->
  (bv_unsigned a + n <= alloc_top h)%Z ->
  region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 n) = true ->
  place_ok h a n = true.
Proof.
  intros h a n H1 H2 H3 H4. unfold place_ok.
  rewrite (proj2 (Z.eqb_eq _ _) H1), (proj2 (Z.ltb_lt _ _) H2), (proj2 (Z.leb_le _ _) H3), H4.
  reflexivity.
Qed.

Lemma grant_ok_unpack : forall hint m a n,
  grant_ok hint m a n = true ->
  (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z /\
  (bv_unsigned a + n <= alloc_top (m_vmmaps m))%Z /\
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n) = true /\
  (vm_backing_used m + n <= vm_limit (m_vmmaps m))%Z.
Proof.
  intros hint m a n H. unfold grant_ok in H.
  rewrite !andb_true_iff in H.
  destruct H as [[[[H1 H2] H3] H4] H5].
  apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3.
  apply Z.leb_le in H5.
  auto 7.
Qed.

Lemma grant_ok_intro : forall hint m a n,
  place_ok (m_vmmaps m) a n = true ->
  (vm_backing_used m + n <= vm_limit (m_vmmaps m))%Z ->
  grant_ok hint m a n = true.
Proof.
  intros hint m a n Hp Hb. unfold grant_ok. unfold place_ok in Hp.
  rewrite Hp, (proj2 (Z.leb_le _ _) Hb). reflexivity.
Qed.

Lemma grant_ok_place : forall hint m a n,
  grant_ok hint m a n = true -> place_ok (m_vmmaps m) a n = true.
Proof.
  intros hint m a n H. unfold grant_ok in H. unfold place_ok.
  rewrite andb_true_iff in H. exact (proj1 H).
Qed.

(* [comment removed for export] *)
Lemma grant_ok_hint_irrel : forall h1 h2 m a n, grant_ok h1 m a n = grant_ok h2 m a n.
Proof. reflexivity. Qed.

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
Definition alloc_top_min : Z := 0x7fff7f800000%Z.
Definition alloc_top_max : Z := 0x7fffff800000%Z.

Lemma alloc_top_unfold : forall h, alloc_top h = (bv_unsigned (vm_init_sp h) - stack_max_size)%Z.
Proof. reflexivity. Qed.
Lemma stack_max_size_val : stack_max_size = 0x800000%Z.
Proof. reflexivity. Qed.
Lemma alloc_top_range : forall h,
  (sp_window_lo <= bv_unsigned (vm_init_sp h) <= sp_window_hi)%Z ->
  (alloc_top_min <= alloc_top h <= alloc_top_max)%Z.
Proof.
  intros h H. unfold alloc_top, alloc_top_min, alloc_top_max, sp_window_lo, sp_window_hi,
    stack_max_size in *. lia.
Qed.

(* [comment removed for export] *)
Lemma source_alloc_limit_val : source_alloc_limit = 0x400000000%Z.
Proof. vm_compute. reflexivity. Qed.
Lemma target_alloc_limit_val : target_alloc_limit = 0x8000000000%Z.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma in_arg3_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 3 = ms_gpr ms 3.
Proof. reflexivity. Qed.

Lemma in_arg4_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 4 = ms_gpr ms 4.
Proof. reflexivity. Qed.

Lemma in_arg5_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 5 = ms_gpr ms 5.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition mmap_args_ok (ms : machine_state) : Prop :=
  ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 3
  /\ ms_gpr ms 3 = Z_to_bv 64 34 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
  /\ ms_gpr ms 5 = Z_to_bv 64 0.

(* [comment removed for export] *)
Lemma mmap_args_ok_gates : forall ms,
  mmap_args_ok ms ->
  mmap_off_aligned_b (ms_gpr ms 5) = true /\
  mmap_anon_b (ms_gpr ms 3) = true /\
  w_is0 (ms_gpr ms 1) = false /\
  mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = true.
Proof.
  intros ms (H1 & H2 & H3 & H4 & H5).
  rewrite H2, H3, H5.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [unfold w_is0; apply bv_eqb_neq; exact H1|].
  vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_noreserve_backed_ok_34 : forall m nZ,
  mmap_noreserve_backed_ok (Z_to_bv 64 34) m nZ
  = (vm_backing_used m + nZ <=? vm_limit (m_vmmaps m))%Z.
Proof.
  intros m nZ. unfold mmap_noreserve_backed_ok.
  replace (mmap_noreserve_b (Z_to_bv 64 34)) with false by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma with_mmap_backing_34 : forall a n m,
  with_mmap_backing (Z_to_bv 64 34) a n m = m.
Proof.
  intros a n m. unfold with_mmap_backing.
  replace (mmap_noreserve_b (Z_to_bv 64 34)) with false by (vm_compute; reflexivity).
  reflexivity.
Qed.

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
Lemma munmap_outcome_si : forall segs ms x8 model o,
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  syscall_spec (sys_input segs ms x8) model o <->
  o = Ok (munmap_eff ms)
         (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) [].
Proof.
  intros segs ms x8 model o Hno (Hal & Hlen & Hnw & Hhas).
  rewrite (syscall_spec_215 _ model o) by (rewrite in_sysno_sys_input; exact Hno).
  rewrite in_arg0_sys_input, in_arg1_sys_input.
  unfold munmap_eff, munmap_model, page_round_up.
  apply munmap_exact_outcome; [exact Hal | unfold w_is0; apply bv_eqb_neq; exact Hlen | exact Hnw |].
  unfold page_round_up in Hhas. exact Hhas.
Qed.

Lemma munmap_ok : forall segs ms x8 model,
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (munmap_eff ms)
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
Proof.
  intros segs ms x8 model Hno Ha. apply (munmap_outcome_si segs ms x8 model _ Hno Ha). reflexivity.
Qed.

Lemma munmap_ok_inv : forall segs ms x8 model eff model' evs,
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  eff = munmap_eff ms /\
  model' = munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model
  /\ evs = [].
Proof.
  intros segs ms x8 model eff model' evs Hno Ha Hspec.
  apply (munmap_outcome_si segs ms x8 model _ Hno Ha) in Hspec.
  apply Ok_inj in Hspec as (-> & -> & ->). auto.
Qed.

Lemma munmap_no_unmodeled : forall segs ms x8 model,
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
  intros segs ms x8 model Hno Ha Hspec.
  apply (munmap_outcome_si segs ms x8 model _ Hno Ha) in Hspec.
  exact (Unmodeled_Ok _ _ _ Hspec).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ENOMEM_in_mmap_errnos : In ENOMEM mmap_errnos.
Proof. left. reflexivity. Qed.

Lemma mmap_errno_range : forall e,
  In e mmap_errnos -> (1 <= e)%Z /\ (e <= 4095)%Z.
Proof. intros e HIn. exact (errnos_ok_range mmap_errnos e eq_refl HIn). Qed.

(* [comment removed for export] *)
Lemma mmap_outcome_si : forall segs ms x8 model o,
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  let nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
  let n := page_round_up (ms_gpr ms 1) in
  syscall_spec (sys_input segs ms x8) model o <->
  mmap_err_out model o
  \/ exists a, grant_ok (ms_gpr ms 0) model a nZ = true
               /\ o = Ok (mkEffect a [] [(a, n)]) (mmap_model a n model) [].
Proof.
  intros segs ms x8 model o Hno Ha. cbv zeta.
  destruct (mmap_args_ok_gates ms Ha) as (Hoff & Hanon & Hl & Hmb).
  destruct Ha as (_ & _ & H3 & _ & _).
  rewrite (syscall_spec_222 _ model o) by (rewrite in_sysno_sys_input; exact Hno).
  rewrite in_arg0_sys_input, in_arg1_sys_input, in_arg2_sys_input,
          in_arg3_sys_input, in_arg4_sys_input, in_arg5_sys_input.
  rewrite (mmap_rw_outcome _ _ _ _ _ _ _ model o Hoff Hanon Hl Hmb).
  rewrite H3, mmap_noreserve_backed_ok_34.
  unfold grant_ok, mmap_model, page_round_up.
  split.
  - intros [He | (a & (G1 & G2 & G3 & G4 & G5) & ->)]; [left; exact He | right].
    exists a. rewrite with_mmap_backing_34.
    rewrite (proj2 (Z.eqb_eq _ _) G1), (proj2 (Z.ltb_lt _ _) G2), (proj2 (Z.leb_le _ _) G3), G4, G5.
    split; reflexivity.
  - intros [He | (a & Hg & ->)]; [left; exact He | right].
    exists a. rewrite with_mmap_backing_34.
    rewrite !andb_true_iff in Hg. destruct Hg as [[[[G1 G2] G3] G4] G5].
    apply Z.eqb_eq in G1. apply Z.ltb_lt in G2. apply Z.leb_le in G3.
    split; [repeat split; assumption | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma mmap_fail_ok : forall segs ms x8 model e,
  bv_unsigned x8 = 222%Z -> mmap_args_ok ms ->
  In e mmap_errnos ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffect (errno_ret e) [] []) model []).
Proof.
  intros segs ms x8 model e Hno Ha He.
  apply (proj2 (mmap_outcome_si segs ms x8 model _ Hno Ha)).
  left. exists e. auto.
Qed.

(* [comment removed for export] *)
Lemma mmap_succ_ok : forall segs ms x8 model a,
  bv_unsigned x8 = 222%Z -> mmap_args_ok ms ->
  grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])
        (mmap_model a (page_round_up (ms_gpr ms 1)) model) []).
Proof.
  intros segs ms x8 model a Hno Ha Hg.
  apply (proj2 (mmap_outcome_si segs ms x8 model _ Hno Ha)).
  right. exists a. auto.
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
  apply (proj1 (mmap_outcome_si segs ms x8 model _ Hno Ha)) in Hspec.
  destruct Hspec as [(e & He & H) | (a & Hg & H)]; apply Ok_inj in H as (-> & -> & ->).
  - split; [reflexivity|]. left. exists e. auto.
  - split; [reflexivity|]. right. exists a. auto.
Qed.

Lemma mmap_no_unmodeled : forall segs ms x8 model,
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
  intros segs ms x8 model Hno Ha Hspec.
  apply (proj1 (mmap_outcome_si segs ms x8 model _ Hno Ha)) in Hspec.
  destruct Hspec as [(e & _ & H) | (a & _ & H)]; exact (Unmodeled_Ok _ _ _ H).
Qed.

(* [comment removed for export] *)
Lemma grant_ok_not_errno : forall hint model a nZ e,
  grant_ok hint model a nZ = true -> (0 <= nZ)%Z ->
  (1 <= e <= 4095)%Z ->
  a <> errno_ret e.
Proof.
  intros hint model a nZ e Hg HnZ He ->.
  destruct (grant_ok_unpack _ _ _ _ Hg) as (_ & _ & Htop & _).
  pose proof (alloc_top_lt (m_vmmaps model)) as Hlt.
  rewrite (errno_ret_unsigned e) in Htop by lia.
  unfold alloc_top, stack_max_size, two_pow_64 in *.
  pose proof (word_unsigned_range (vm_init_sp (m_vmmaps model))). unfold two_pow_64 in *. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma adv_mmap_grant : forall regs pc sv mem rom a n,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc; ms_svc_pending := sv;
       ms_resv := None; ms_fcsr := Z_to_bv 32 0; ms_mem := mem; ms_rom := rom |}
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

Lemma rdn_unfill_out : forall segs a n m (x : word) k,
  (bv_unsigned x + Z.of_nat k <= 2 ^ 64)%Z ->
  (bv_unsigned x + Z.of_nat k <= bv_unsigned a
   \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
  rdn segs (unfill a n m) x k = rdn segs m x k.
Proof.
  intros segs a n m x k Hnw Hd. apply rdn_ext; [exact Hnw|].
  intros y Hy. apply unfill_out. lia.
Qed.

(* [comment removed for export] *)
Lemma adv_munmap : forall regs pc sv mem rom a n,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc; ms_svc_pending := sv;
       ms_resv := None; ms_fcsr := Z_to_bv 32 0; ms_mem := mem; ms_rom := rom |}
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
    twm (advance_past_svc (apply_effect ms (munmap_eff ms)))
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) bufs code ->
    twm ms model bufs code
| twm_step : forall ms ms' model bufs code,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    twm ms' model bufs code ->
    twm ms model bufs code
(* [comment removed for export] *)
with twm_pend : machine_state -> Model -> list byte -> list (list byte) -> word -> Prop :=
| twmp_write : forall ms model x8 rest bufs code,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 64%Z ->
    ms_gpr ms 0 = Z_to_bv 64 1 ->
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some rest ->
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma twm_write_ret : forall regs pc mem rom model buf bufs code,
  bv_unsigned (getr regs 17) = 64%Z ->
  reg_get regs 10 = Z_to_bv 64 1 ->
  ms_read_bytes {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc;
                   ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := Z_to_bv 32 0;
                   ms_mem := mem; ms_rom := rom |}
    (reg_get regs 11) (reg_get regs 12) = Some buf ->
  (1 <= length buf)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
     twm_tail (mkst (regupd regs 10 (len_word (firstn n buf))) (v_addi pc 4) mem rom)
       model (skipn n buf) bufs code) ->
  twm {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc;
         ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := Z_to_bv 32 0;
         ms_mem := mem; ms_rom := rom |}
      model (buf :: bufs) code.
Proof.
  intros regs pc mem rom model buf bufs code H17 H10 Hr Hnb Hcont.
  assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
  assert (E12 : Z_to_bv 5 (10 + Z.of_nat 2) = (12 : reg)) by (apply bv_eq; reflexivity).
  apply twm_write; [exact Hnb|].
  eapply twmp_write.
  - cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E10. exact H10.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E11, E12. exact Hr.
  - exact Hnb.
  - intros n Hn1 Hn2. rewrite adv_set. exact (Hcont n Hn1 Hn2).
Qed.

(* [comment removed for export] *)
Lemma twm_tail_write_rec : forall regs pc mem rom model rest bufs code,
  bv_unsigned (getr regs 17) = 64%Z ->
  reg_get regs 10 = Z_to_bv 64 1 ->
  ms_read_bytes {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc;
                   ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := Z_to_bv 32 0;
                   ms_mem := mem; ms_rom := rom |}
    (reg_get regs 11) (reg_get regs 12) = Some rest ->
  (1 <= length rest)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
     twm_tail (mkst (regupd regs 10 (len_word (firstn n rest))) (v_addi pc 4) mem rom)
       model (skipn n rest) bufs code) ->
  twm_tail {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc;
              ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := Z_to_bv 32 0;
              ms_mem := mem; ms_rom := rom |}
    model rest bufs code.
Proof.
  intros regs pc mem rom model rest bufs code H17 H10 Hr Hnb Hcont.
  assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
  assert (E12 : Z_to_bv 5 (10 + Z.of_nat 2) = (12 : reg)) by (apply bv_eq; reflexivity).
  apply twmt_more; [exact Hnb|].
  eapply twmp_write.
  - cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E10. exact H10.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E11, E12. exact Hr.
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
  twm (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
            (unfill a (page_round_up nlen) mem) rom)
      (munmap_model a (page_round_up nlen) model) bufs code ->
  twm {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc;
         ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := Z_to_bv 32 0;
         ms_mem := mem; ms_rom := rom |}
      model bufs code.
Proof.
  intros regs pc mem rom model bufs code a nlen H17 Ha Hn Hal Hlen Hnw Hhas Hcont.
  assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
  eapply twm_munmap.
  - cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold munmap_args_ok, ms_gpr. cbn [ms_regs].
    rewrite E10, E11, Ha, Hn. auto.
  - unfold munmap_eff, ms_gpr. cbn [ms_regs].
    rewrite E10, E11, Ha, Hn.
    rewrite adv_munmap. exact Hcont.
Qed.

(* [comment removed for export] *)
Lemma twm_exit_coden : forall regs pc mem rom model (c : word),
  bv_unsigned (getr regs 17) = 93%Z ->
  reg_get regs 10 = c -> (bv_unsigned c < 256)%Z ->
  twm {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc;
         ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := Z_to_bv 32 0;
         ms_mem := mem; ms_rom := rom |}
      model [] c.
Proof.
  intros regs pc mem rom model c H17 H10 Hc.
  assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
  assert (Hg : bv_and (ms_gpr {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc;
                                 ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := Z_to_bv 32 0;
                                 ms_mem := mem; ms_rom := rom |} 0)
                      (Z_to_bv 64 255) = c).
  { unfold ms_gpr. cbn [ms_regs]. rewrite E10, H10.
    apply land_255_small. exact Hc. }
  rewrite <- Hg.
  eapply twm_exit.
  - cbn [ms_svc_pending]. reflexivity.
  - left. exact H17.
Qed.

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
  st = SNext (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                    (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)).
Proof.
  intros ms model x8 evs st Hh Hlazy Hsvc Hno Hargs Hss.
  inversion Hss; subst; try congruence.
  - (* [comment removed for export] *)
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (Heff & Hm & Hevs);
      subst eff model' evs0
    end.
    match goal with
    | Hmat : materialize_model_accesses
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) _ = Some _ |- _ =>
      rewrite (materialize_model_accesses_no_lazy _ _
        (munmap_model_no_lazy _ _ _ Hlazy)) in Hmat;
      inversion Hmat; subst
    end.
    split; reflexivity.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (Heff & Hm & Hevs); subst eff model' evs0;
      rewrite (materialize_model_accesses_no_lazy _ _
        (munmap_model_no_lazy _ _ _ Hlazy)) in Hmat;
      discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (_ & Hm & _);
      subst model'; rewrite munmap_model_halted, Hh in H6; discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some ?sig |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (_ & Hm & _);
      subst model';
      rewrite (m_killed_of_m_halted_none _ (eq_trans (munmap_model_halted _ _ _) Hh)) in H6;
      discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      exact (munmap_no_unmodeled segs ms x8 model Hno Hargs H3)
    end.
Qed.

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

(* [comment removed for export] *)
Lemma tmw_mmap_rec : forall regs pc mem rom model bf cf bs cs,
  bv_unsigned (getr regs 17) = 222%Z ->
  reg_get regs 11 <> Z_to_bv 64 0 ->
  reg_get regs 12 = Z_to_bv 64 3 ->
  reg_get regs 13 = Z_to_bv 64 34 ->
  reg_get regs 14 = Z_to_bv 64 (-1) ->
  reg_get regs 15 = Z_to_bv 64 0 ->
  (forall e, In e mmap_errnos ->
     twm (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model bf cf) ->
  (forall a, grant_ok (reg_get regs 10) model a (page_round_up_Z (bv_unsigned (reg_get regs 11))) = true ->
     twm (mkst (regupd regs 10 a) (v_addi pc 4)
               (zfill a (page_round_up (reg_get regs 11)) mem) rom)
         (mmap_model a (page_round_up (reg_get regs 11)) model) bs cs) ->
  (exists a, grant_ok (reg_get regs 10) model a (page_round_up_Z (bv_unsigned (reg_get regs 11))) = true) ->
  tmw {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc;
         ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := Z_to_bv 32 0;
         ms_mem := mem; ms_rom := rom |}
      model bf cf bs cs.
Proof.
  intros regs pc mem rom model bf cf bs cs H17 H11 H12 H13 H14 H15
    Hfail Hsucc Hex.
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
  - intros e HIn. rewrite adv_set. apply Hfail. exact HIn.
  - intros a Hg. rewrite adv_mmap_grant.
    unfold ms_gpr in *. cbn [ms_regs] in *. rewrite E11 in *.
    apply Hsucc. exact Hg.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E11. exact Hex.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sstep_mmap_inv : forall ms model x8 evs st,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [] /\
  ((exists e, In e mmap_errnos /\
      st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model)) \/
   (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true /\
      st = SNext (mkCfg (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                        (mmap_model a (page_round_up (ms_gpr ms 1)) model)))).
Proof.
  intros ms model x8 evs st Hh Hlazy Hsvc Hno Hargs Hss.
  inversion Hss; subst; try congruence.
  - (* [comment removed for export] *)
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
  - (* [comment removed for export] *)
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
  - (* [comment removed for export] *)
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
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some ?sig |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (_ & Hcase);
      destruct Hcase as [(? & ? & ? & Hm) | (? & ? & ? & Hm)]; subst model';
      [ rewrite (m_killed_of_m_halted_none _ Hh) in H6; discriminate
      | rewrite (m_killed_of_m_halted_none _ (eq_trans (mmap_model_halted _ _ _) Hh)) in H6;
        discriminate ]
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      exact (mmap_no_unmodeled segs ms x8 model Hno Hargs H3)
    end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Definition two_traces (bf : list (list byte)) (cf : word)
    (bs : list (list byte)) (cs : word)
    (fs : Fs.Fs) (tr : list event) : Prop :=
  is_prefix tr (wevents bf ++ [ExitEv cf fs]) \/
  is_prefix tr (wevents bs ++ [ExitEv cs fs]).


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


Definition mm_path (c : config) : Prop :=
  (m_halted (cfg_model c) = None /\ m_vm_lazy (cfg_model c) = [] /\
   fd1chan (cfg_model c) /\
   ((exists bf cf bs cs, tmw (cfg_ms c) (cfg_model c) bf cf bs cs
                         /\ bufs_modeled bf /\ bufs_modeled bs)
    \/ (exists rest bufs code,
          twm_tail (cfg_ms c) (cfg_model c) rest bufs code
          /\ buf_modeled rest /\ bufs_modeled bufs)))
  \/ m_halted (cfg_model c) <> None.


End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma two_traces_prefix_closed : forall bf cf bs cs fs tr tr',
  two_traces bf cf bs cs fs tr -> is_prefix tr' tr -> two_traces bf cf bs cs fs tr'.
Proof.
  intros bf cf bs cs fs tr tr' [H | H] Hp;
    [left | right]; eapply is_prefix_trans; eauto.
Qed.

