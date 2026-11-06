(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Classical.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Amb RelSpec
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg Nodes StoreOk AgentLib AgentNodes PlacementGap.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition t_alt3 (A B C : TSet) : TSet := t_alt2 A (t_alt2 B C).

Lemma with_fds_halted' : forall fds m, m_halted (with_fds fds m) = m_halted m.
Proof. intros fds m. reflexivity. Qed.

Lemma with_fds_lazy : forall fds m, m_vm_lazy (with_fds fds m) = m_vm_lazy m.
Proof. intros fds m. reflexivity. Qed.

Lemma with_tid_halted : forall t m, m_halted (with_tid t m) = m_halted m.
Proof. intros t m. reflexivity. Qed.

Lemma with_tid_lazy : forall t m, m_vm_lazy (with_tid t m) = m_vm_lazy m.
Proof. intros t m. reflexivity. Qed.

Lemma with_vmmaps_eta : forall m,
  with_vmmaps (m_vmmaps m) m = m.
Proof. intros m. destruct m as [? [? ? ?] ? ? ? ?]; reflexivity. Qed.

Lemma vmmaps_eta : forall h,
  mkVmMapsFull (vm_reserved h) (vm_maps h) (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) = h.
Proof. intros h. destruct h; reflexivity. Qed.

Lemma Z_to_bv_u_eq' : forall (a : word) (z : Z), z = bv_unsigned a -> Z_to_bv 64 z = a.
Proof. intros a z ->. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Section WithSegs.
Context {fx : FPState}.
Variable segs : list Segment.

Inductive three : Type := T1 | T2 | T3.

Lemma adv_ret_epend : forall regs pc mem rom x8 r,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffectU r [] [] [] [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof. intros. unfold epend. apply adv_eff_ret. Qed.

Lemma adv_write1_epend : forall regs pc mem rom x8 r buf data,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffect r [(buf, data)] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) (wbytes mem buf data) rom.
Proof. intros. unfold epend. rewrite adv_apply_write, write_to_mem_wbytes. reflexivity. Qed.

Lemma read_file_outcome_si : forall ms x8 model fd p off data wv,
  bv_unsigned x8 = 63%Z ->
  ms_gpr ms 0 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some (FdFile p off) ->
  fs_lookup (m_fs model) p = Some data ->
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) (ms_gpr ms 2) = Some wv ->
  (0 < bv_unsigned (ms_gpr ms 2))%Z -> (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z ->
  (bv_unsigned (ms_gpr ms 1) + bv_unsigned (ms_gpr ms 2) <= TASK_SIZE)%Z ->
  let bs := file_read data off (ms_gpr ms 2) in
  let m' := with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model in
  forall o, syscall_spec (sys_input segs ms x8) model o <->
            o = Ok (mkEffect (len_word bs) (delivered_writes (ms_gpr ms 1) bs) []) m' [].
Proof.
  intros ms x8 model fd p off data wv Hno H0 Hfd32 Hlk Hfs Hw Hpos Hcnt Hover. cbv zeta. intros o.
  assert (HL : (bv_unsigned (len_word (file_read data off (ms_gpr ms 2)))
                <= bv_unsigned (ms_gpr ms 2))%Z).
  { unfold len_word. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
    pose proof (u64_range (ms_gpr ms 2)) as Hc.
    rewrite length_file_read, Nat2Z.inj_min. unfold word_to_nat.
    rewrite Z.mod_small; lia. }
  rewrite (syscall_spec_63 _ model o) by (rewrite in_sysno_si; exact Hno).
  rewrite in_arg0_si, in_arg1_si, in_arg2_si, H0, (fd32_id fd Hfd32).
  assert (Hcl : Z_to_bv 64 (rw_count_clamp (ms_gpr ms 2)) = ms_gpr ms 2).
  { rewrite (rw_count_clamp_of_rw _ Hcnt). apply Z_to_bv_bv_unsigned. }
  rewrite (read_file_outcome fd (ms_gpr ms 1) (ms_gpr ms 2) (sys_input segs ms x8) model o p off data
             (firstn (word_to_nat (len_word (file_read data off (ms_gpr ms 2)))) wv) Hlk).
  - rewrite Hcl. reflexivity.
  - apply access_okb_intro. exact Hover.
  - exact Hfs.
  - rewrite Hcl, in_wmem_si. exact (read_bytes_map_prefix _ _ _ _ _ HL Hw).
Qed.

Section Openat.
  Variables (regs : bvmap 5 word) (pc : word) (mem : word -> option byte) (model : Model).
  Variable w : bv 32.
  Hypothesis HF : fetch_word segs pc = Some w.
  Hypothesis HE : is_ecall w = true.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis H17 : getr regs 17 = Z_to_bv 64 56.
  Hypothesis H10 : getr regs 10 = AT_FDCWD.

  Hypothesis Hfl : Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z.

  Let ms := epend regs pc mem (seg_rom segs) (getr regs 17).
  Let post (r : word) := mkst (regupd regs 10 r) (v_addi pc 4) mem (seg_rom segs).
  Let fds := m_fds model.

  Lemma Hno56 : bv_unsigned (getr regs 17) = 56%Z.
  Proof. rewrite H17. apply u64_lit. lia. Qed.

  Lemma openat_spec_head : forall o,
    syscall_spec (sys_input segs ms (getr regs 17)) model o <->
    openat_spec AT_FDCWD32 (getr regs 11) (getr regs 12) (sys_input segs ms (getr regs 17)) model o.
  Proof.
    intros o. cbv delta [ms].
    rewrite (syscall_spec_56 _ model o) by (rewrite in_sysno_si; exact Hno56).
    rewrite in_arg0_si, in_arg1_si, in_arg2_si, ms_gpr_epend0, ms_gpr_epend1, ms_gpr_epend2, H10.
    reflexivity.
  Qed.

  Lemma open_in_mem : in_mem (sys_input segs ms (getr regs 17)) = mrb segs mem.
  Proof. cbv delta [ms]. rewrite in_mem_si, ms_read_byte_epend. reflexivity. Qed.

  Lemma open_flags_modeled : modeled_open_flags (getr regs 12) = true.
  Proof. exact (modeled_open_flags_rd _ Hfl). Qed.

  Definition path_at (p : list byte) : Prop :=
    (length p <= 4095)%nat /\ ~ In (Z_to_bv 8 0) p
    /\ rdn segs mem (getr regs 11) (length p + 1) = Some (p ++ [Z_to_bv 8 0]).

  Lemma path_at_cstr : forall p, path_at p -> read_cstr (mrb segs mem) (getr regs 11) = CstrOk p.
  Proof. intros p (H1 & H2 & H3). apply read_cstr_of_rdn; assumption. Qed.

  Hypothesis Hfree : fd_lookup fds (alloc_fd fds) = None.

End Openat.

Definition brk_eff (ms : machine_state) (model : Model) (r : word) : SyscallEffect :=
  mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
               (brk_unmaps r (vm_brk (m_vmmaps model))) [] [].

Lemma node_brk : forall ms model x8,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214%Z ->
  (forall r, brk_resolution_ok model (ms_gpr ms 0) r ->
     ~ spurious_refusal_cfg CFG (sys_input segs ms x8) model (brk_eff ms model r)) ->
  node_ok segs (mkCfg ms model)
    {r : word | brk_resolution_ok model (ms_gpr ms 0) r}
    (fun _ => [])
    (fun i => mkCfg (advance_past_svc (apply_effect ms
                       (mkEffectU (proj1_sig i) []
                          (brk_zeros (ms_gpr ms 0) (proj1_sig i) (vm_brk (m_vmmaps model)))
                          (brk_unmaps (proj1_sig i) (vm_brk (m_vmmaps model))) [] [])))
                    (brk_model (ms_gpr ms 0) (proj1_sig i) model)).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno Hns. split.
  - intros [r Hr]. cbn [proj1_sig].
    pose proof (brk_ok_intro segs ms x8 model r Hno Hr) as Hspec.
    destruct (brk_step_shape segs ms x8 model _ _ _ Hh Hlazy Hno Hspec) as (_ & Hh' & _ & _ & Hlazy').
    apply (sstep_cfg_syscall segs CFG ms model x8 _ _ _ [] Hh Hsvc Hspec (Hns r Hr) Hh').
    apply materialize_model_accesses_no_lazy. rewrite Hlazy'. exact Hlazy.
  - intros e st Hss.
    destruct (sstep_brk_inv segs ms model x8 e st Hh Hlazy Hsvc Hno (sstep_cfg_sub segs CFG _ _ _ Hss))
      as (eff & model' & Hspec & -> & ->).
    apply (brk_ok_iff segs ms x8 model eff model' [] Hno) in Hspec.
    destruct Hspec as (Heff & _ & Hok & ->).
    exists (exist _ (eff_ret eff) Hok). cbn [proj1_sig]. rewrite <- Heff. split; reflexivity.
Qed.

Lemma brk_r_ok_grow_cases : forall m req r,
  let h := m_vmmaps m in
  (0 < bv_unsigned req)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned req)%Z ->
  (bv_unsigned (vm_brk h) <= bv_unsigned req)%Z ->
  brk_resolution_ok m req r <->
  (r = vm_brk h \/ (r = req /\ Mmap.brk_grow_ok m req req = true)).
Proof.
  intros m req r h Hpos Hs Hb.
  unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta. fold h.
  assert (E0 : w_is0 req = false).
  { unfold w_is0, bv_eqb. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. apply Z.eqb_neq. lia. }
  rewrite E0. unfold min_brk.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbn [orb].
  rewrite (proj2 (Z.ltb_ge _ _)) by lia.
  rewrite andb_true_iff, orb_true_iff, !bv_eqb_eq. split.
  - intros [[-> | ->] Hg]; [right; auto | left; reflexivity].
  - intros [-> | [-> Hg]]; split; [right; reflexivity | | left; reflexivity | exact Hg].
    unfold Mmap.brk_grow_ok, Mmap.brk_budget_ok. fold h. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.

Lemma brk_model_keep : forall m req,
  brk_model req (vm_brk (m_vmmaps m)) m = m.
Proof.
  intros m req. unfold brk_model, with_brk_next. cbv zeta.
  rewrite brk_unmaps_keep. cbn [forget_vm_ranges].
  unfold brk_model_next, brk_maps_next.
  rewrite Z.ltb_irrefl, andb_false_r, brk_grants_keep, brk_unmaps_keep.
  cbn [app maps_subtract_ranges fold_left]. rewrite vmmaps_eta. apply with_vmmaps_eta.
Qed.

Lemma brk_model_grow_eq : forall m (d : Z),
  let h := m_vmmaps m in
  let b := vm_brk h in
  (0 < d)%Z -> (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z ->
  brk_model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) m
  = with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
                   (vm_noaccess h) (vm_start_brk h)
                   (Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m.
Proof.
  intros m d h b Hd Hb0 Hnw Hbal Hdal.
  pose proof (u64_range b) as Hbr.
  set (req := Z_to_bv 64 (bv_unsigned b + d)).
  assert (Hureq : bv_unsigned req = (bv_unsigned b + d)%Z) by (unfold req; apply u64_lit; lia).
  assert (Hlt : (bv_unsigned b < bv_unsigned req)%Z) by (rewrite Hureq; lia).
  assert (Hreq0 : req <> Z_to_bv 64 0).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
  unfold brk_model, with_brk_next. cbv zeta. fold h. fold b.
  rewrite (brk_unmaps_grow req b) by lia. cbn [forget_vm_ranges].
  unfold brk_model_next, brk_maps_next. fold b.
  rewrite (proj2 (Z.ltb_ge (bv_unsigned req) (bv_unsigned b))) by lia. rewrite andb_false_r.
  rewrite (brk_grants_grow req req b Hreq0 Hb0 Hlt), (brk_unmaps_grow req b) by lia.
  cbn [app maps_subtract_ranges fold_left].
  replace (req - b) with (Z_to_bv 64 d); [reflexivity|].
  apply bv_eq. rewrite bv_sub_unsigned, Hureq.
  rewrite bv_wrap_small by (unfold bv_modulus; lia). rewrite u64_lit by lia. lia.
Qed.

Definition noaccess_model (a n : word) (m : Model) : Model :=
  with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
                 ((a, n) :: vm_maps (m_vmmaps m))
                 ((a, n) :: vm_noaccess (m_vmmaps m))
                 (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.

Definition grant_ok_na (hint : word) (m : Model) (a : word) (n : Z) : bool :=
  (bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
  && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n).

Definition mmap_noaccess_args_ok (ms : machine_state) : Prop :=
  ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 0
  /\ ms_gpr ms 3 = Z_to_bv 64 34 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
  /\ ms_gpr ms 5 = Z_to_bv 64 0.

Lemma mmap_noaccess_outcome_si : forall ms x8 model,
  bv_unsigned x8 = 222%Z -> mmap_noaccess_args_ok ms ->
  let n := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
  forall o, syscall_spec (sys_input segs ms x8) model o <->
    (exists e, In e mmap_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) model [])
    \/ (exists a, grant_ok_na (ms_gpr ms 0) model a n = true
         /\ o = Ok (mkEffectU a [] [] [(a, Z_to_bv 64 n)] [] []) (noaccess_model a (Z_to_bv 64 n) model) []).
Proof.
  intros ms x8 model Hno (H1 & H2 & H3 & H4 & H5) n o.
  rewrite (syscall_spec_222 _ model o) by (rewrite in_sysno_si; exact Hno).
  rewrite in_arg0_si, in_arg1_si, in_arg2_si, in_arg3_sys_input, in_arg4_sys_input, in_arg5_sys_input.
  rewrite H2, H3, H4, H5.
  assert (E1 : w_is0 (ms_gpr ms 1) = false) by (unfold w_is0; apply bv_eqb_neq; exact H1).
  rewrite (mmap_noaccess_outcome (ms_gpr ms 0) (ms_gpr ms 1) (Z_to_bv 64 0) (Z_to_bv 64 34)
             (Z_to_bv 64 (-1)) (Z_to_bv 64 0) (sys_input segs ms x8) model o E1
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
  unfold mmap_err_out, grant_ok_na, noaccess_model, with_mmap_backing.
  replace (mmap_noreserve_b (Z_to_bv 64 34)) with false by (vm_compute; reflexivity). fold n.
  split; (intros [H | (a & Hg & ->)]; [left; exact H | right; exists a; split; [|reflexivity]]).
  - destruct Hg as (G1 & G2 & G3 & G4).
    rewrite (proj2 (Z.eqb_eq _ _) G1), (proj2 (Z.ltb_lt _ _) G2), (proj2 (Z.leb_le _ _) G3), G4. reflexivity.
  - rewrite !andb_true_iff in Hg. destruct Hg as [[[G1 G2] G3] G4].
    apply Z.eqb_eq in G1. apply Z.ltb_lt in G2. apply Z.leb_le in G3. auto 10.
Qed.

Definition mprotect_model (addr n : word) (m : Model) : Model :=
  with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
                 (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                 (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.

Lemma mprotect_model_next_eq : forall m addr n, mprotect_model_next m addr n = mprotect_model addr n m.
Proof. reflexivity. Qed.

Lemma mprotect_outcome_si : forall ms x8 model (addr : word) (len : Z),
  bv_unsigned x8 = 226%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
  ms_gpr ms 2 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  forall o, syscall_spec (sys_input segs ms x8) model o <->
    (exists e, In e mprotect_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) model [])
    \/ (mprotect_budget_ok model addr n = true
        /\ o = Ok (mkEffect (Z_to_bv 64 0) [] [(addr, n)]) (mprotect_model addr n model) []).
Proof.
  intros ms x8 model addr len Hno H0 Hal H1 Hlen Hnw H2 n Hna Hma o.
  assert (Hlen' : (len < two_pow_64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range addr). lia. }
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; unfold two_pow_64 in Hlen'; lia).
  rewrite (syscall_spec_226 _ model o) by (rewrite in_sysno_si; exact Hno).
  rewrite in_arg0_si, in_arg1_si, in_arg2_si, H0, H2.
  rewrite <- mprotect_model_next_eq. subst n. rewrite <- Hu1.
  apply (mprotect_expose_outcome addr (ms_gpr ms 1) (Z_to_bv 64 3) _ model o);
    [vm_compute; reflexivity | exact Hal | | rewrite Hu1; exact Hnw | vm_compute; reflexivity
    | rewrite Hu1; exact Hna | rewrite Hu1; exact Hma].
  unfold w_is0, bv_eqb. rewrite Hu1. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. apply Z.eqb_neq. lia.
Qed.

Lemma ENOMEM_in_mprotect_errnos : In ENOMEM mprotect_errnos.
Proof. left. reflexivity. Qed.

Definition fixed_noaccess_model (addr n : word) (m : Model) : Model :=
  vm_forget_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
    (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
                   ((addr, n) :: maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m).

Definition fixed_destroyed_model (addr n : word) (m : Model) : Model :=
  vm_forget_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
    (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
                   (maps_subtract (vm_maps (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m).

Definition mmap_fixed_args_ok (ms : machine_state) : Prop :=
  ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 0
  /\ ms_gpr ms 3 = Z_to_bv 64 50 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
  /\ ms_gpr ms 5 = Z_to_bv 64 0.

Lemma mmap_fixed_outcome_si : forall ms x8 model (addr : word) (len : Z),
  bv_unsigned x8 = 222%Z -> mmap_fixed_args_ok ms ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  forall o, syscall_spec (sys_input segs ms x8) model o <->
    (exists e, In e mmap_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) model [])
    \/ o = Ok (mkEffectU addr [] [] [(addr, n)] [] []) (fixed_noaccess_model addr n model) []
    \/ (exists e, In e mmap_errnos /\
          o = Ok (mkEffectU (errno_ret e) [] [] [(addr, n)] [] []) (fixed_destroyed_model addr n model) []).
Proof.
  intros ms x8 model addr len Hno (H1 & H2 & H3 & H4 & H5) H0 Hal Hpos H1' Hlen Hce n Hrf Hmc o.
  pose proof (alloc_top_lt_2_64 (m_vmmaps model)) as Hcv. unfold two_pow_64 in Hcv.
  assert (Hlen' : (len < 2 ^ 64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range addr). lia. }
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1'; apply u64_lit; lia).
  rewrite (syscall_spec_222 _ model o) by (rewrite in_sysno_si; exact Hno).
  rewrite in_arg0_si, in_arg1_si, in_arg2_si, in_arg3_sys_input, in_arg4_sys_input, in_arg5_sys_input.
  rewrite H2, H3, H4, H5, H0.
  assert (E1 : w_is0 (ms_gpr ms 1) = false) by (unfold w_is0; apply bv_eqb_neq; exact H1).
  subst n. rewrite <- Hu1.
  rewrite (mmap_fixed_noaccess_outcome addr (ms_gpr ms 1) (Z_to_bv 64 0) (Z_to_bv 64 50)
             (Z_to_bv 64 (-1)) (Z_to_bv 64 0) (sys_input segs ms x8) model o E1
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             ltac:(rewrite Hu1; exact Hce) Hal Hpos ltac:(rewrite Hu1; exact Hrf) ltac:(rewrite Hu1; exact Hmc)).
  unfold mmap_err_out, fixed_noaccess_model, fixed_destroyed_model,
    with_mmap_destroyed, with_mmap_replacement, with_mmap_backing.
  replace (mmap_noreserve_b (Z_to_bv 64 50)) with false by (vm_compute; reflexivity).
  reflexivity.
Qed.

Definition tid_I : Type := { t : word | (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z }.

Lemma one_tid_ok : (0 < bv_unsigned (Z_to_bv 64 1) < PID_MAX_ENVELOPE)%Z.
Proof. unfold PID_MAX_ENVELOPE. rewrite u64_lit by lia. lia. Qed.

Lemma node_set_tid : forall ms model x8,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 96%Z ->
  m_tid model = None ->
  node_ok segs (mkCfg ms model) tid_I (fun _ => [])
    (fun i => mkCfg (advance_past_svc (set_gpr0 ms (proj1_sig i))) (with_tid (proj1_sig i) model)).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno Htid.
  assert (Hchk : forall o, syscall_spec (sys_input segs ms x8) model o <->
     exists t, (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z /\ o = Ok (mkEffect t [] []) (with_tid t model) []).
  { intros o. rewrite (syscall_spec_96 _ model o) by (rewrite in_sysno_si; exact Hno).
    apply set_tid_fresh_outcome. exact Htid. }
  pose (effs := fun i : tid_I => mkEffectU (proj1_sig i) [] [] [] [] []).
  assert (Enx : forall i : tid_I,
    mkCfg (advance_past_svc (set_gpr0 ms (proj1_sig i))) (with_tid (proj1_sig i) model)
    = mkCfg (advance_past_svc (apply_effect ms (effs i))) (with_tid (proj1_sig i) model)).
  { intros [t Ht]. cbn [proj1_sig effs]. rewrite <- (apply_effect_no_write ms t). reflexivity. }
  assert (Hnode : node_ok segs (mkCfg ms model) tid_I (fun _ => [])
            (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (with_tid (proj1_sig i) model))).
  { apply (node_family segs ms model x8 tid_I effs (fun i => with_tid (proj1_sig i) model) (fun _ => []) _
             Hh Hsvc ltac:(rewrite Hno; reflexivity) Hchk).
    - intros [t Ht]. exists t. split; [exact Ht|reflexivity].
    - intros o (t & Ht & ->). exists (exist _ t Ht). reflexivity.
    - intros i. rewrite with_tid_halted. exact Hh.
    - intros i. rewrite with_tid_lazy. exact Hlazy. }
  destruct Hnode as [Hn1 Hn2]. split.
  - intros i. rewrite Enx. apply Hn1.
  - intros e st Hss. destruct (Hn2 e st Hss) as (i & -> & ->). exists i. rewrite Enx. split; reflexivity.
Qed.

End WithSegs.

Local Open Scope Z_scope.

Definition cand (N : Z) (j : nat) : Z := bottomup_floor + Z.of_nat j * (2 * N).

Definition zconflict (a n : Z) (p : word * word) : Prop :=
  a < bv_unsigned (fst p) + bv_unsigned (snd p) /\ bv_unsigned (fst p) < a + n.

Definition zconflictb (a n : Z) (p : word * word) : bool :=
  (a <? bv_unsigned (fst p) + bv_unsigned (snd p)) && (bv_unsigned (fst p) <? a + n).

