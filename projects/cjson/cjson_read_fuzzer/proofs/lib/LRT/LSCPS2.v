(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Monad.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require RelSpec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cells.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Step.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Exec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Spin.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require SRealizes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LMeasure.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRelSpec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LGap04.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cfg.
Module LNodesMM.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RelSpec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRelSpec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cfg.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac ceilb := let A := fresh "HCElo" in let B := fresh "HCEhi" in pose proof alloc_ceiling_lo as A; pose proof alloc_ceiling_hi as B.

(* [comment removed for export] *)
Definition is_err (w : word) : bool := (2^64 - 4095 <=? bv_unsigned w).

Lemma is_err_errno : forall e, 1 <= e <= 4095 -> is_err (errno_ret e) = true.
Proof.
  intros e He. unfold is_err, errno_ret. rewrite Z_to_bv_unsigned. apply Z.leb_le.
  unfold bv_wrap. change (bv_modulus 64) with (2^64).
  replace (- e) with ((2^64 - e) + (-1) * 2^64) by lia. rewrite Z_mod_plus_full, Z.mod_small by lia. lia.
Qed.

Lemma is_err_low {C : Ceil} : forall a : word, bv_unsigned a <= alloc_ceiling -> is_err a = false.
Proof. intros a Ha. unfold is_err. apply Z.leb_gt. ceilb. lia. Qed.

Lemma mmap_errnos_range : forall e, In e mmap_errnos -> 1 <= e <= 4095.
Proof. intros e [<-|[]]. unfold ENOMEM. lia. Qed.

Lemma ENOMEM_in : In ENOMEM mmap_errnos.
Proof. left; reflexivity. Qed.

Lemma mmap_grant_ret_nonrefusal : forall a : word,
  bv_unsigned a mod page_size = 0 -> ret_in_errnos mmap_errnos a = false.
Proof.
  intros a Ha. unfold mmap_errnos. rewrite ret_in_errnos_ENOMEM.
  destruct (bv_eqb a (errno_ret ENOMEM)) eqn:E; [|reflexivity].
  apply bv_eqb_eq in E. subst a. vm_compute in Ha. discriminate Ha.
Qed.

(* [comment removed for export] *)
Lemma eager_used_total' : forall mo,
  nowrap (vm_maps (m_vmmaps mo)) ->
  eager_used mo = total (eagerf (vm_maps (m_vmmaps mo)) (vm_noaccess (m_vmmaps mo)) (m_vm_lazy mo)).
Proof.
  intros mo Hnw. pose proof (eager_used_total mo Hnw) as H. rewrite vm_backing_used_split in H. lia.
Qed.

Section WithSegs.
Variable segs : list Segment.
Context {ACEIL : Ceil}.   (* [comment removed for export] *)

Lemma lok_maps_nowrap : forall mo, LOK segs mo -> nowrap (vm_maps (m_vmmaps mo)).
Proof. intros mo HO a sz Hin. pose proof (lok_maps_ceil _ mo HO a sz Hin). unfold uz. ceilb. lia. Qed.

(* [comment removed for export] *)
Lemma real_budget : forall g mo mat n,
  LOK segs mo -> BINV mo g -> matok (g_win g) mat -> n <= g_res g ->
  vm_backing_used (real mo mat) + n <= vm_limit (m_vmmaps (real mo mat)).
Proof.
  intros g mo mat n HO (HW & HR & HB) HM Hn. rewrite real_used, real_vmmaps, page_size_eq.
  pose proof (matok_length _ _ HM). nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mm_add_map (a n : word) (mo : Model) : Model :=
  let h := m_vmmaps mo in
  with_vmmaps (mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h) (vm_noaccess h)
                 (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo.

Lemma mm_add_map_real : forall a n mo mat, mm_add_map a n (real mo mat) = real (mm_add_map a n mo) mat.
Proof. reflexivity. Qed.

Lemma mm_add_map_lazy : forall a n mo, m_vm_lazy (mm_add_map a n mo) = m_vm_lazy mo. Proof. reflexivity. Qed.
Lemma mm_add_map_vmmaps : forall a n mo,
  m_vmmaps (mm_add_map a n mo) =
  mkVmMapsFull (vm_reserved (m_vmmaps mo)) ((a, n) :: vm_maps (m_vmmaps mo)) (vm_noaccess (m_vmmaps mo))
    (vm_start_brk (m_vmmaps mo)) (vm_brk (m_vmmaps mo)) (vm_limit (m_vmmaps mo)) (vm_mmap_base (m_vmmaps mo)) (vm_init_sp (m_vmmaps mo)).
Proof. reflexivity. Qed.
Lemma mm_add_map_lzf : forall a n mo, lzf (mm_add_map a n mo) = lzf mo. Proof. reflexivity. Qed.
Lemma mm_add_map_vm_only : forall a n mo, vm_only mo (mm_add_map a n mo).
Proof. intros. repeat split; reflexivity. Qed.

Lemma mm_add_map_LOK : forall a n mo, LOK segs mo ->
  bv_unsigned a + bv_unsigned n <= alloc_ceiling ->
  region_free (vm_maps (m_vmmaps mo)) a n = true ->
  LOK segs (mm_add_map a n mo).
Proof.
  intros a n mo HO Hc Hf. destruct HO. constructor; rewrite ?mm_add_map_vmmaps, ?mm_add_map_lazy; cbn; try assumption.
  - intros b k [Hin|Hin]; [injection Hin as <- <-; exact Hc| eauto].
  - apply pwd_cons_free; assumption.
  - intros x Hx. cbn [in_rangesb existsb fst snd]. fold (in_rangesb (vm_maps (m_vmmaps mo)) x).
    rewrite (lok_lazy_maps x Hx). apply orb_true_r.
  - intros x Hx. cbn [in_rangesb existsb fst snd]. fold (in_rangesb (vm_maps (m_vmmaps mo)) x).
    rewrite (lok_na_maps x Hx). apply orb_true_r.
Qed.

Lemma mm_add_map_eager : forall a n mo, LOK segs mo ->
  bv_unsigned a + bv_unsigned n <= alloc_ceiling ->
  eager_used (mm_add_map a n mo) <= eager_used mo + bv_unsigned n.
Proof.
  intros a n mo HO Hc.
  pose proof (lok_maps_nowrap mo HO) as Hnw.
  assert (Hnw' : nowrap (vm_maps (m_vmmaps (mm_add_map a n mo)))).
  { rewrite mm_add_map_vmmaps. cbn. apply nowrap_cons. split; [unfold uz; ceilb; lia| exact Hnw]. }
  rewrite (eager_used_total' _ Hnw'), (eager_used_total' _ Hnw). rewrite mm_add_map_vmmaps, mm_add_map_lazy. cbn [vm_maps vm_noaccess].
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 n). change (bv_modulus 64) with (2^64) in *.
  set (NA := vm_noaccess (m_vmmaps mo)). set (L := m_vm_lazy mo). set (M := vm_maps (m_vmmaps mo)).
  assert (E : forall x, eagerf ((a, n) :: M) NA L x = ind (uz a) (uz a + uz n) x * (nz NA x * nz L x) + eagerf M NA L x).
  { intros x. unfold eagerf. cbn [cov]. lia. }
  rewrite (total_ext _ _ (fun x _ => E x)). rewrite total_add.
  enough (total (fun x => ind (uz a) (uz a + uz n) x * (nz NA x * nz L x)) <= bv_unsigned n) by lia.
  apply (Z.le_trans _ ((uz a + uz n) - uz a)); [| unfold uz; lia].
  apply total_ind_le; unfold uz; try (ceilb; lia).
  - intros x _. destruct (nz_01 NA x) as [-> | ->]; destruct (nz_01 L x) as [-> | ->]; lia.
  - intros x _. destruct (nz_01 NA x) as [-> | ->]; destruct (nz_01 L x) as [-> | ->]; lia.
Qed.

(* [comment removed for export] *)
Definition mmap_grant (mo : Model) (a : word) (n : Z) : Prop :=
  bv_unsigned a mod page_size = 0 /\ 0 < bv_unsigned a /\ bv_unsigned a + n <= alloc_ceiling /\
  region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a (Z_to_bv 64 n) = true.

(* [comment removed for export] *)
Definition mmap_placeable (mo : Model) (n : Z) : Prop :=
  exists a : word, mmap_grant mo a n.

(* [comment removed for export] *)
Lemma mmap_placeable_gap : forall mo n, LOK segs mo ->
  (mmap_placeable mo n <-> vm_gap_available (m_vmmaps mo) n = true).
Proof.
  intros mo n HO. rewrite vm_gap_available_iff. rewrite (lok_top _ _ HO). unfold mmap_placeable, mmap_grant. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma real_backed_ok : forall g mo mat flags n,
  LOK segs mo -> BINV mo g -> matok (g_win g) mat -> n <= g_res g ->
  mmap_noreserve_backed_ok flags (real mo mat) n = true.
Proof.
  intros g mo mat flags n HO HB HM Hn. unfold mmap_noreserve_backed_ok. destruct (mmap_noreserve_b flags); [reflexivity|].
  apply Z.leb_le. apply (real_budget g); assumption.
Qed.

(* [comment removed for export] *)
Theorem lscps_mmap_rw_forced : forall (P : machine_state -> Model -> lghost -> Prop) ms mo G R len,
  at_node segs (NMmap 0 len mm_prot_rw mm_flags_anon) ms ->
  0 < len -> len + 4096 <= 2^64 ->
  let n := page_round_up_Z len in
  n <= R ->
  (forall e, In e mmap_errnos -> ~ mmap_placeable mo n -> LSCPS segs P (nret ms (efferr e)) mo (mkG G R)) ->
  (forall a, mmap_grant mo a n ->
     LSCPS segs P (nret ms (mkEffect a [] [(a, Z_to_bv 64 n)])) (mm_add_map a (Z_to_bv 64 n) mo) (mkG G (R - n))) ->
  LSCPS segs P ms mo (mkG G R).
Proof.
  intros P ms mo G R len HA Hlen0 Hlen1 n HnR Href Hgrant.
  destruct HA as (Hsvc & Ha0 & Ha1 & Ha2 & Ha3 & Ha4 & Ha5).
  assert (Hn : len <= n /\ n mod 4096 = 0 /\ n < len + 4096 /\ n = page_round_up_Z len).
  { subst n. unfold page_round_up_Z. rewrite page_size_eq. Z.div_mod_to_equations. lia. }
  clearbody n. destruct Hn as (Hn1 & Hn2 & Hn3 & En).
  assert (Hun : bv_unsigned (Z_to_bv 64 n : word) = n).
  { apply unsigned_lit. lia. }
  apply (lscps_sysnode segs P (fun _ => false) ms mo (mkG G R) (Z_to_bv 64 222) Hsvc).
  intros mr mat HI. pose proof HI as ([HWX HO] & HB & HLR & [HM HVD]).
  pose proof (lok_top _ _ HO) as HTOP.
  (* [comment removed for export] *)
  assert (SPEC : forall o, syscall_spec (sys_input segs (msw ms mr) (Z_to_bv 64 222)) (real mo mat) o <->
            mmap_err_out (real mo mat) o
            \/ exists a, ((bv_unsigned a mod page_size = 0) /\ (0 < bv_unsigned a) /\ (bv_unsigned a + n <= alloc_top (m_vmmaps mo))
                          /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a (Z_to_bv 64 n) = true
                          /\ mmap_noreserve_backed_ok (Z_to_bv 64 mm_flags_anon) (real mo mat) n = true)
                         /\ o = Ok (mkEffect a [] [(a, Z_to_bv 64 n)]) (real (mm_add_map a (Z_to_bv 64 n) mo) mat) []).
  { intros o. rewrite (syscall_spec_222 _ _ o) by reflexivity.
    rewrite !in_a0_si, !in_a1_si, !in_a2_si, !in_a3_si, !in_a4_si, !in_a5_si.
    change (areg (msw ms mr) 10) with (areg ms 10). change (areg (msw ms mr) 11) with (areg ms 11).
    change (areg (msw ms mr) 12) with (areg ms 12). change (areg (msw ms mr) 13) with (areg ms 13).
    change (areg (msw ms mr) 14) with (areg ms 14). change (areg (msw ms mr) 15) with (areg ms 15).
    rewrite Ha0, Ha1, Ha2, Ha3, Ha4, Ha5.
    pose proof (mmap_rw_outcome (Z_to_bv 64 0) (Z_to_bv 64 len) (Z_to_bv 64 mm_prot_rw) (Z_to_bv 64 mm_flags_anon)
                  (Z_to_bv 64 (-1)) (Z_to_bv 64 0) (sys_input segs (msw ms mr) (Z_to_bv 64 222)) (real mo mat) o) as RW.
    cbv zeta in RW. rewrite (unsigned_lit len) in RW by lia. rewrite <- En in RW. rewrite real_vmmaps in RW.
    assert (E1 : w_is0 (Z_to_bv 64 len) = false).
    { unfold w_is0. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. lia. }
    specialize (RW eq_refl eq_refl E1 eq_refl). rewrite RW. reflexivity. }
  pose proof (bv_unsigned_in_range 64) as UR.
  assert (HBK : mmap_noreserve_backed_ok (Z_to_bv 64 mm_flags_anon) (real mo mat) n = true).
  { apply (real_backed_ok (mkG G R)); assumption. }
  assert (Hno : bv_unsigned (in_sysno (sys_input segs (msw ms mr) (Z_to_bv 64 222))) = 222) by reflexivity.
  assert (HR : forall r, refusal_b (sys_input segs (msw ms mr) (Z_to_bv 64 222)) (real mo mat) r = ret_in_errnos mmap_errnos r)
    by (intros r; exact (refusal_b_222 _ _ r Hno)).
  assert (Hoff : injected_family_off ACFG (sys_input segs (msw ms mr) (Z_to_bv 64 222)) = true)
    by (apply acfg_family_off_alloc; right; right; left; exact Hno).
  assert (Hhr : m_halted (real mo mat) = None) by (rewrite real_halted; exact (lok_halt _ _ HO)).
  split.
  - (* [comment removed for export] *)
    intros o Ho. apply SPEC in Ho. destruct Ho as [(e & He & ->) | (a & (C1 & C2 & C3 & C4 & C5) & ->)].
    + (* [comment removed for export] *)
      destruct (vm_gap_available (m_vmmaps mo) n) eqn:EG.
      { right. pose proof (proj1 (vm_gap_available_iff _ _) EG) as (a & C1 & C2 & C3 & C4).
        eexists _, _, _. split; [reflexivity|]. split; [|exact Hhr].
        apply (refusal_spurious_of_grant ACFG _ _ _ (mkEffect a [] [(a, Z_to_bv 64 n)]) (real (mm_add_map a (Z_to_bv 64 n) mo) mat) []);
          [exact Hoff
          | rewrite HR; cbn [eff_ret]; apply ret_in_errnos_errno; exact He
          | apply SPEC; right; exists a; split; [repeat split; assumption | reflexivity]
          | rewrite HR; cbn [eff_ret]; apply mmap_grant_ret_nonrefusal; exact C1]. }
      left.
      assert (HNP : ~ mmap_placeable mo n).
      { intros HP. apply (mmap_placeable_gap mo n HO) in HP. congruence. }
      exists (efferr e), mo, (mkG G R), (ms_mem ms), mat.
      split; [reflexivity|]. split; [reflexivity|]. split; [apply vm_only_refl|]. split.
      { unfold efferr, eff0. rewrite mem_nret_plain. cbn [ms_mem msw]. exact HI. }
      pose proof (Href e He HNP) as K. unfold efferr, eff0 in K |- *. cbn [eff_ret].
      rewrite <- (mem_nret_plain ms (errno_ret e)), msw_nret_self.
      right; split; [reflexivity | exact K].
    + (* [comment removed for export] *)
      left. rewrite HTOP in C3.
      set (nw := (Z_to_bv 64 n : word)) in *.
      assert (Hfm : region_free (vm_maps (m_vmmaps mo)) a nw = true).
      { rewrite region_free_app in C4. apply andb_true_iff in C4. exact (proj2 C4). }
      exists (mkEffect a [] [(a, nw)]), (mm_add_map a nw mo), (mkG G (R - n)), (apply_zeros (ms_mem ms) [(a, nw)]), mat.
      split; [reflexivity|]. split; [reflexivity|]. split; [apply mm_add_map_vm_only|]. split.
      { (* [comment removed for export] *)
        rewrite mem_nret_zeros. cbn [ms_mem msw].
        pose proof (UR a) as Ra. change (bv_modulus 64) with (2^64) in Ra.
        assert (AZ : forall m x, apply_zeros m [(a, nw)] x = if in_range (bv_unsigned a) n x then Some (Z_to_bv 8 0) else m x).
        { intros m x. rewrite <- (Z_to_bv_bv_unsigned a) at 1. change (Z_to_bv 64 (bv_unsigned a)) with (wa (bv_unsigned a)).
          unfold nw. apply apply_zeros_spec; ceilb; lia. }
        split; [split; [exact HWX| apply mm_add_map_LOK; [exact HO| rewrite Hun; exact C3| exact Hfm]]|].
        split.
        { destruct HB as (HBw & HBr & HBe). unfold BINV. cbn [g_win g_res] in *. split; [exact HBw|]. split; [lia|].
          pose proof (mm_add_map_eager a nw mo HO ltac:(rewrite Hun; exact C3)). rewrite Hun in H.
          change (vm_limit (m_vmmaps (mm_add_map a nw mo))) with (vm_limit (m_vmmaps mo)). lia. }
        split; [| split; [exact HM|]].
        { destruct HLR as [Hm Hhid]. split.
          * apply (magree_transfer _ _ _ _ _ _ _ _ _ Hm). intros x. rewrite mm_add_map_lzf. rewrite (AZ mr x).
            destruct (in_range (bv_unsigned a) n x) eqn:Er.
            -- left. unfold lmem. rewrite (AZ (ms_mem ms) x), Er. reflexivity.
            -- right. rewrite (AZ (ms_mem ms) x), Er. repeat split; try reflexivity.
               unfold lexc. rewrite mm_add_map_lzf. cbn [g_win]. exact (fun H => H).
          * intros x Hl Hw. rewrite mm_add_map_lazy in Hl. cbn [g_win] in Hw. rewrite (AZ (ms_mem ms) x).
            destruct (in_range (bv_unsigned a) n x) eqn:Er; [| apply Hhid; assumption].
            exfalso. unfold in_range in Er. apply andb_true_iff in Er as [E2 E3]. apply Z.leb_le in E2. apply Z.ltb_lt in E3.
            pose proof (lok_lazy_maps _ _ HO x Hl) as Hmx. apply in_rangesb_true in Hmx as (b & k & Hin & Hbx).
            eapply (region_free_false_of _ a nw b k x Hfm Hin); [rewrite Hun; lia| exact Hbx]. }
        (* [comment removed for export] *)
        intros x Hx. rewrite (AZ (ms_mem ms) x) in Hx. unfold in_range in Hx.
        rewrite mm_add_map_vmmaps. cbn [vm_maps in_rangesb existsb fst snd]. fold (in_rangesb (vm_maps (m_vmmaps mo)) x). rewrite Hun.
        destruct (Z.leb_spec0 (bv_unsigned a) (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (bv_unsigned a + n)); cbn [andb orb] in Hx |- *.
        1: right; right; reflexivity.
        all: destruct (HVD x Hx) as [A|[A|A]]; [left; exact A| right; left; exact A| right; right; rewrite A; rewrite ?orb_true_r; reflexivity]. }
      pose proof (Hgrant a (conj C1 (conj C2 (conj C3 C4)))) as K.
      rewrite <- (mem_nret_zeros ms a (a, nw) []), msw_nret_self. cbn [eff_ret].
      right. split; [reflexivity | exact K].
  - (* [comment removed for export] *)
    destruct (vm_gap_available (m_vmmaps mo) n) eqn:EG.
    + pose proof (proj1 (vm_gap_available_iff _ _) EG) as (a & C1 & C2 & C3 & C4).
      exists (mkEffect a [] [(a, Z_to_bv 64 n)]), (real (mm_add_map a (Z_to_bv 64 n) mo) mat), [].
      split; [apply SPEC; right; exists a; split; [repeat split; assumption | reflexivity]|].
      split; [| reflexivity].
      apply spurious_refusal_not_refusal. rewrite HR. cbn [eff_ret]. apply mmap_grant_ret_nonrefusal. exact C1.
    + exists (efferr ENOMEM), (real mo mat), [].
      split; [apply SPEC; left; exists ENOMEM; split; [apply ENOMEM_in| reflexivity]|].
      split; [| reflexivity].
      apply nsp_forced. intros eff' m' evs' Hs'. rewrite HR.
      apply SPEC in Hs'. destruct Hs' as [(e & He & Heq) | (a & (C1 & C2 & C3 & C4 & C5) & Heq)].
      * apply Ok_inj in Heq as (-> & _ & _). cbn [eff_ret]. apply ret_in_errnos_errno. exact He.
      * exfalso. assert (EG' : vm_gap_available (m_vmmaps mo) n = true).
        { apply vm_gap_available_iff. exists a. repeat split; assumption. }
        congruence.
Qed.

(* [comment removed for export] *)
Theorem lscps_mmap_rw : forall (P : machine_state -> Model -> lghost -> Prop) ms mo G R len,
  at_node segs (NMmap 0 len mm_prot_rw mm_flags_anon) ms ->
  0 < len -> len + 4096 <= 2^64 ->
  page_round_up_Z len <= R ->
  (forall e, In e mmap_errnos -> LSCPS segs P (nret ms (efferr e)) mo (mkG G R)) ->
  (forall a, mmap_grant mo a (page_round_up_Z len) ->
     LSCPS segs P (nret ms (mkEffect a [] [(a, Z_to_bv 64 (page_round_up_Z len))]))
           (mm_add_map a (Z_to_bv 64 (page_round_up_Z len)) mo) (mkG G (R - page_round_up_Z len))) ->
  LSCPS segs P ms mo (mkG G R).
Proof. intros P ms mo G R len HA H0 H1 HR Href Hg. eapply lscps_mmap_rw_forced; eauto. Qed.

(* [comment removed for export] *)
Theorem lscps_mmap_rw_grant : forall (P : machine_state -> Model -> lghost -> Prop) ms mo G R len,
  at_node segs (NMmap 0 len mm_prot_rw mm_flags_anon) ms ->
  0 < len -> len + 4096 <= 2^64 ->
  page_round_up_Z len <= R ->
  mmap_placeable mo (page_round_up_Z len) ->
  (forall a, mmap_grant mo a (page_round_up_Z len) ->
     LSCPS segs P (nret ms (mkEffect a [] [(a, Z_to_bv 64 (page_round_up_Z len))]))
           (mm_add_map a (Z_to_bv 64 (page_round_up_Z len)) mo) (mkG G (R - page_round_up_Z len))) ->
  LSCPS segs P ms mo (mkG G R).
Proof.
  intros P ms mo G R len HA H0 H1 HR HP Hg. eapply lscps_mmap_rw_forced; eauto.
  intros e _ HNP. exfalso. exact (HNP HP).
Qed.

(* [comment removed for export] *)
Theorem lscps_mmap_rw_spin : forall (P : machine_state -> Model -> lghost -> Prop) ms mo G R len,
  at_node segs (NMmap 0 len mm_prot_rw mm_flags_anon) ms ->
  0 < len -> len + 4096 <= 2^64 ->
  page_round_up_Z len <= R ->
  mmap_placeable mo (page_round_up_Z len) ->
  (forall e, In e mmap_errnos -> evt segs (jself segs) (nret ms (efferr e))) ->
  (forall a, mmap_grant mo a (page_round_up_Z len) ->
     LSCPS segs P (nret ms (mkEffect a [] [(a, Z_to_bv 64 (page_round_up_Z len))]))
           (mm_add_map a (Z_to_bv 64 (page_round_up_Z len)) mo) (mkG G (R - page_round_up_Z len))) ->
  LSCPS segs P ms mo (mkG G R).
Proof. intros P ms mo G R len HA H0 H1 HR HP _ Hg. eapply lscps_mmap_rw_grant; eauto. Qed.

Theorem lscps_mmap_rw_gen : forall (spin : bool) (P : machine_state -> Model -> lghost -> Prop) ms mo G R len,
  at_node segs (NMmap 0 len mm_prot_rw mm_flags_anon) ms ->
  0 < len -> len + 4096 <= 2^64 ->
  let n := page_round_up_Z len in
  n <= R ->
  (forall e, In e mmap_errnos ->
     if spin then evt segs (jself segs) (nret ms (efferr e)) else LSCPS segs P (nret ms (efferr e)) mo (mkG G R)) ->
  (forall a, mmap_grant mo a n ->
     LSCPS segs P (nret ms (mkEffect a [] [(a, Z_to_bv 64 n)])) (mm_add_map a (Z_to_bv 64 n) mo) (mkG G (R - n))) ->
  (if spin then mmap_placeable mo n else True) ->
  LSCPS segs P ms mo (mkG G R).
Proof.
  intros spin P ms mo G R len HA H0 H1 n HR Href Hg HP. destruct spin.
  - eapply lscps_mmap_rw_grant; eauto.
  - eapply lscps_mmap_rw; eauto.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mm_flags_anon_nr : Z := 16418.   (* [comment removed for export] *)

Lemma lazy_interior_aligned : forall (a n : word),
  bv_unsigned a mod 4096 = 0 -> bv_unsigned n mod 4096 = 0 -> 0 < bv_unsigned n ->
  bv_unsigned a + bv_unsigned n <= 2^64 ->
  lazy_interior a n = [(a, n)].
Proof.
  intros a n Ha Hn Hp Hc. unfold lazy_interior. rewrite page_size_eq.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 n). change (bv_modulus 64) with (2^64) in *.
  replace ((bv_unsigned a + 4096 - 1) / 4096 * 4096) with (bv_unsigned a) by (Z.div_mod_to_equations; lia).
  replace ((bv_unsigned a + bv_unsigned n) / 4096 * 4096) with (bv_unsigned a + bv_unsigned n) by (Z.div_mod_to_equations; lia).
  destruct (Z.ltb_spec0 (bv_unsigned a) (bv_unsigned a + bv_unsigned n)); [| lia].
  replace (bv_unsigned a + bv_unsigned n - bv_unsigned a) with (bv_unsigned n) by lia.
  rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* [comment removed for export] *)
Definition mm_add_lazy (a n : word) (mo : Model) : Model :=
  with_vm_backing ((a, n) :: m_vm_lazy mo) (m_vm_materialized mo) (mm_add_map a n mo).

Lemma mm_add_lazy_lazy : forall a n mo, m_vm_lazy (mm_add_lazy a n mo) = (a, n) :: m_vm_lazy mo. Proof. reflexivity. Qed.
Lemma mm_add_lazy_vmmaps : forall a n mo, m_vmmaps (mm_add_lazy a n mo) = m_vmmaps (mm_add_map a n mo). Proof. reflexivity. Qed.
Lemma mm_add_lazy_vm_only : forall a n mo, vm_only mo (mm_add_lazy a n mo).
Proof. intros. repeat split; reflexivity. Qed.
Lemma mm_add_lazy_real : forall a n mo mat,
  lazy_interior a n = [(a, n)] ->
  vm_add_lazy a n (mm_add_map a n (real mo mat)) = real (mm_add_lazy a n mo) mat.
Proof. intros a n mo mat E. unfold vm_add_lazy. rewrite E. reflexivity. Qed.

Lemma mm_add_lazy_LOK : forall a n mo, LOK segs mo -> no_wx segs ->
  bv_unsigned a + bv_unsigned n <= alloc_ceiling ->
  region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a n = true ->
  LOK segs (mm_add_lazy a n mo).
Proof.
  intros a n mo HO HWX Hc Hf.
  assert (Hfm : region_free (vm_maps (m_vmmaps mo)) a n = true).
  { rewrite region_free_app in Hf. apply andb_true_iff in Hf. exact (proj2 Hf). }
  pose proof (mm_add_map_LOK a n mo HO Hc Hfm) as HO'. pose proof (lok_resv _ _ HO) as Hresv.
  destruct HO' as [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10]. constructor; rewrite ?mm_add_lazy_vmmaps, ?mm_add_lazy_lazy; try assumption.
  - intros lo sz [Hin|Hin]; [injection Hin as <- <-; exact Hc| exact (lok_lazy_ceil _ _ HO lo sz Hin)].
  - intros x Hx. cbn [in_rangesb existsb fst snd] in Hx. fold (in_rangesb (m_vm_lazy mo) x) in Hx.
    apply orb_true_iff in Hx as [Hx|Hx]; [| exact (lok_lazy_noseg _ _ HO x Hx)].
    apply andb_true_iff in Hx as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B.
    rewrite Hresv in Hf. eapply region_free_noseg; [exact HWX| exact Hf| lia].
  - intros x Hx. rewrite mm_add_map_vmmaps. cbn [vm_maps in_rangesb existsb fst snd] in Hx |- *.
    fold (in_rangesb (m_vm_lazy mo) x) in Hx. fold (in_rangesb (vm_maps (m_vmmaps mo)) x).
    apply orb_true_iff in Hx as [Hx|Hx]; [rewrite Hx; reflexivity|].
    rewrite (lok_lazy_maps _ _ HO x Hx). apply orb_true_r.
Qed.

Lemma mm_add_lazy_eager : forall a n mo, LOK segs mo ->
  bv_unsigned a + bv_unsigned n <= alloc_ceiling ->
  eager_used (mm_add_lazy a n mo) <= eager_used mo.
Proof.
  intros a n mo HO Hc.
  pose proof (lok_maps_nowrap mo HO) as Hnw.
  assert (Hnw' : nowrap (vm_maps (m_vmmaps (mm_add_lazy a n mo)))).
  { rewrite mm_add_lazy_vmmaps, mm_add_map_vmmaps. cbn. apply nowrap_cons. split; [unfold uz; ceilb; lia| exact Hnw]. }
  rewrite (eager_used_total' _ Hnw'), (eager_used_total' _ Hnw). rewrite mm_add_lazy_vmmaps, mm_add_map_vmmaps, mm_add_lazy_lazy. cbn [vm_maps vm_noaccess].
  apply total_le. intros x _. unfold eagerf. cbn [cov]. rewrite nz_cons.
  pose proof (cov_nonneg (vm_maps (m_vmmaps mo)) x).
  destruct (ind_01 (uz a) (uz a + uz n) x) as [-> | ->];
  destruct (nz_01 (vm_noaccess (m_vmmaps mo)) x) as [-> | ->]; destruct (nz_01 (m_vm_lazy mo) x) as [-> | ->]; lia.
Qed.

(* [comment removed for export] *)
Theorem lscps_mmap_rw_nr_forced : forall (P : machine_state -> Model -> lghost -> Prop) ms mo G R len,
  at_node segs (NMmap 0 len mm_prot_rw mm_flags_anon_nr) ms ->
  0 < len -> len + 4096 <= 2^64 ->
  let n := page_round_up_Z len in
  (forall e, In e mmap_errnos -> ~ mmap_placeable mo n -> LSCPS segs P (nret ms (efferr e)) mo (mkG G R)) ->
  (forall a, mmap_grant mo a n ->
     LSCPS segs P (msw (nret ms (mkEffect a [] [(a, Z_to_bv 64 n)])) (ms_mem ms)) (mm_add_lazy a (Z_to_bv 64 n) mo) (mkG G R)) ->
  LSCPS segs P ms mo (mkG G R).
Proof.
  intros P ms mo G R len HA Hlen0 Hlen1 n Href Hgrant.
  destruct HA as (Hsvc & Ha0 & Ha1 & Ha2 & Ha3 & Ha4 & Ha5).
  assert (Hn : len <= n /\ n mod 4096 = 0 /\ n < len + 4096 /\ n = page_round_up_Z len).
  { subst n. unfold page_round_up_Z. rewrite page_size_eq. Z.div_mod_to_equations. lia. }
  clearbody n. destruct Hn as (Hn1 & Hn2 & Hn3 & En).
  assert (Hun : bv_unsigned (Z_to_bv 64 n : word) = n).
  { apply unsigned_lit. lia. }
  apply (lscps_sysnode segs P (fun _ => false) ms mo (mkG G R) (Z_to_bv 64 222) Hsvc).
  intros mr mat HI. pose proof HI as ([HWX HO] & HB & HLR & [HM HVD]).
  pose proof (lok_top _ _ HO) as HTOP.
  assert (SPEC : forall o, syscall_spec (sys_input segs (msw ms mr) (Z_to_bv 64 222)) (real mo mat) o <->
            mmap_err_out (real mo mat) o
            \/ exists a, ((bv_unsigned a mod page_size = 0) /\ (0 < bv_unsigned a) /\ (bv_unsigned a + n <= alloc_top (m_vmmaps mo))
                          /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a (Z_to_bv 64 n) = true
                          /\ mmap_noreserve_backed_ok (Z_to_bv 64 mm_flags_anon_nr) (real mo mat) n = true)
                         /\ o = Ok (mkEffect a [] [(a, Z_to_bv 64 n)])
                                  (vm_add_lazy a (Z_to_bv 64 n) (mm_add_map a (Z_to_bv 64 n) (real mo mat))) []).
  { intros o. rewrite (syscall_spec_222 _ _ o) by reflexivity.
    rewrite !in_a0_si, !in_a1_si, !in_a2_si, !in_a3_si, !in_a4_si, !in_a5_si.
    change (areg (msw ms mr) 10) with (areg ms 10). change (areg (msw ms mr) 11) with (areg ms 11).
    change (areg (msw ms mr) 12) with (areg ms 12). change (areg (msw ms mr) 13) with (areg ms 13).
    change (areg (msw ms mr) 14) with (areg ms 14). change (areg (msw ms mr) 15) with (areg ms 15).
    rewrite Ha0, Ha1, Ha2, Ha3, Ha4, Ha5.
    pose proof (mmap_rw_outcome (Z_to_bv 64 0) (Z_to_bv 64 len) (Z_to_bv 64 mm_prot_rw) (Z_to_bv 64 mm_flags_anon_nr)
                  (Z_to_bv 64 (-1)) (Z_to_bv 64 0) (sys_input segs (msw ms mr) (Z_to_bv 64 222)) (real mo mat) o) as RW.
    cbv zeta in RW. rewrite (unsigned_lit len) in RW by lia. rewrite <- En in RW. rewrite real_vmmaps in RW.
    assert (E1 : w_is0 (Z_to_bv 64 len) = false).
    { unfold w_is0. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. lia. }
    specialize (RW eq_refl eq_refl E1 eq_refl). rewrite RW. reflexivity. }
  pose proof (bv_unsigned_in_range 64) as UR.
  assert (Hno : bv_unsigned (in_sysno (sys_input segs (msw ms mr) (Z_to_bv 64 222))) = 222) by reflexivity.
  assert (HR : forall r, refusal_b (sys_input segs (msw ms mr) (Z_to_bv 64 222)) (real mo mat) r = ret_in_errnos mmap_errnos r)
    by (intros r; exact (refusal_b_222 _ _ r Hno)).
  assert (Hoff : injected_family_off ACFG (sys_input segs (msw ms mr) (Z_to_bv 64 222)) = true)
    by (apply acfg_family_off_alloc; right; right; left; exact Hno).
  assert (Hhr : m_halted (real mo mat) = None) by (rewrite real_halted; exact (lok_halt _ _ HO)).
  split.
  - intros o Ho. apply SPEC in Ho. destruct Ho as [(e & He & ->) | (a & (C1 & C2 & C3 & C4 & C5) & ->)].
    + destruct (vm_gap_available (m_vmmaps mo) n) eqn:EG.
      { right. pose proof (proj1 (vm_gap_available_iff _ _) EG) as (a & C1 & C2 & C3 & C4).
        eexists _, _, _. split; [reflexivity|]. split; [|exact Hhr].
        apply (refusal_spurious_of_grant ACFG _ _ _ (mkEffect a [] [(a, Z_to_bv 64 n)])
                 (vm_add_lazy a (Z_to_bv 64 n) (mm_add_map a (Z_to_bv 64 n) (real mo mat))) []);
          [exact Hoff
          | rewrite HR; exact (ret_in_errnos_errno _ _ He)
          | apply SPEC; right; exists a; split; [repeat split; assumption | reflexivity]
          | rewrite HR; cbn [eff_ret]; apply mmap_grant_ret_nonrefusal; exact C1]. }
      left.
      assert (HNP : ~ mmap_placeable mo n).
      { intros HP. apply (mmap_placeable_gap mo n HO) in HP. congruence. }
      exists (efferr e), mo, (mkG G R), (ms_mem ms), mat.
      split; [reflexivity|]. split; [reflexivity|]. split; [apply vm_only_refl|]. split.
      { unfold efferr, eff0. rewrite mem_nret_plain. cbn [ms_mem msw]. exact HI. }
      pose proof (Href e He HNP) as K. unfold efferr, eff0 in K |- *. cbn [eff_ret].
      rewrite <- (mem_nret_plain ms (errno_ret e)), msw_nret_self.
      right; split; [reflexivity | exact K].
    + left. rewrite HTOP in C3.
      set (nw := (Z_to_bv 64 n : word)) in *.
      pose proof (UR a) as Ra. change (bv_modulus 64) with (2^64) in Ra.
      assert (EL : lazy_interior a nw = [(a, nw)]).
      { apply lazy_interior_aligned; rewrite ?Hun; try lia; try (rewrite page_size_eq in C1; exact C1); try (ceilb; lia). }
      exists (mkEffect a [] [(a, nw)]), (mm_add_lazy a nw mo), (mkG G R), (ms_mem ms), mat.
      split; [rewrite (mm_add_lazy_real a nw mo mat EL); reflexivity|].
      split; [reflexivity|]. split; [apply mm_add_lazy_vm_only|].
      assert (AZ : forall m x, apply_zeros m [(a, nw)] x = if in_range (bv_unsigned a) n x then Some (Z_to_bv 8 0) else m x).
      { intros m x. rewrite <- (Z_to_bv_bv_unsigned a) at 1. change (Z_to_bv 64 (bv_unsigned a)) with (wa (bv_unsigned a)).
        unfold nw. apply apply_zeros_spec; ceilb; lia. }
      (* [comment removed for export] *)
      assert (FR : forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + n -> ms_mem ms x = None).
      { intros x Hx. destruct (ms_mem ms x) eqn:Ex; [|reflexivity]. exfalso.
        destruct (HVD x ltac:(congruence)) as [A|[A|A]].
        - ceilb. lia.
        - apply A. rewrite (lok_resv _ _ HO) in C4. eapply region_free_noseg; [exact HWX| exact C4| rewrite Hun; exact Hx].
        - apply in_rangesb_true in A as (b' & k & Hin & Hbx).
          assert (Hfm : region_free (vm_maps (m_vmmaps mo)) a nw = true).
          { rewrite region_free_app in C4. apply andb_true_iff in C4. exact (proj2 C4). }
          eapply (region_free_false_of _ a nw b' k x Hfm Hin); [rewrite Hun; exact Hx| exact Hbx]. }
      split.
      { rewrite mem_nret_zeros. cbn [ms_mem msw].
        split; [split; [exact HWX| apply mm_add_lazy_LOK; [exact HO| exact HWX| rewrite Hun; exact C3| exact C4]]|].
        split.
        { destruct HB as (HBw & HBr & HBe). unfold BINV. cbn [g_win g_res] in *. split; [exact HBw|]. split; [exact HBr|].
          pose proof (mm_add_lazy_eager a nw mo HO ltac:(rewrite Hun; exact C3)).
          change (vm_limit (m_vmmaps (mm_add_lazy a nw mo))) with (vm_limit (m_vmmaps mo)). lia. }
        split; [| split; [exact HM|]].
        { destruct HLR as [Hm Hhid]. split.
          * assert (LZ : forall x, lzf (mm_add_lazy a nw mo) x = (in_range (bv_unsigned a) n x || lzf mo x)%bool).
            { intros x. unfold lzf. rewrite mm_add_lazy_lazy, mm_add_lazy_vmmaps, mm_add_map_vmmaps.
              cbn [vm_noaccess in_rangesb existsb fst snd]. fold (in_rangesb (m_vm_lazy mo) x). fold (in_rangesb (vm_noaccess (m_vmmaps mo)) x).
              rewrite Hun. unfold in_range.
              destruct (Z.leb_spec0 (bv_unsigned a) (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (bv_unsigned a + n)); cbn [andb orb];
                try reflexivity.
              destruct (in_rangesb (vm_noaccess (m_vmmaps mo)) x) eqn:Ena; [| reflexivity]. exfalso.
              pose proof (lok_na_maps _ _ HO x Ena) as Hmx. apply in_rangesb_true in Hmx as (b & k & Hin & Hbx).
              assert (Hfm : region_free (vm_maps (m_vmmaps mo)) a nw = true).
              { rewrite region_free_app in C4. apply andb_true_iff in C4. exact (proj2 C4). }
              eapply (region_free_false_of _ a nw b k x Hfm Hin); [rewrite Hun; lia| exact Hbx]. }
            apply (magree_transfer _ _ _ _ _ _ _ _ _ Hm). intros x. rewrite (AZ mr x), LZ. unfold in_range.
            destruct (Z.leb_spec0 (bv_unsigned a) (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (bv_unsigned a + n)); cbn [andb orb];
              try (right; repeat split; try reflexivity; unfold lexc; rewrite LZ; unfold in_range;
                   destruct (Z.leb_spec0 (bv_unsigned a) (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (bv_unsigned a + n)); cbn [andb orb]; try lia;
                   exact (fun H => H)).
            left. unfold lmem. rewrite (FR x) by lia. rewrite LZ. unfold in_range.
            rewrite (proj2 (Z.leb_le _ _) ltac:(eassumption)). rewrite (proj2 (Z.ltb_lt (bv_unsigned x) _) ltac:(eassumption)). reflexivity.
          * intros x Hl Hw. rewrite mm_add_lazy_lazy in Hl. cbn [in_rangesb existsb fst snd] in Hl. fold (in_rangesb (m_vm_lazy mo) x) in Hl.
            apply orb_true_iff in Hl as [Hl|Hl]; [| apply Hhid; assumption].
            apply andb_true_iff in Hl as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. rewrite Hun in B. apply FR. lia. }
        intros x Hx. destruct (HVD x Hx) as [A|[A|A]]; [left; exact A| right; left; exact A| right; right].
        rewrite mm_add_lazy_vmmaps, mm_add_map_vmmaps. cbn [vm_maps in_rangesb existsb fst snd]. fold (in_rangesb (vm_maps (m_vmmaps mo)) x).
        rewrite A. apply orb_true_r. }
      pose proof (Hgrant a (conj C1 (conj C2 (conj C3 C4)))) as K. cbn [eff_ret].
      right. split; [reflexivity | exact K].
  - destruct (vm_gap_available (m_vmmaps mo) n) eqn:EG.
    + pose proof (proj1 (vm_gap_available_iff _ _) EG) as (a & C1 & C2 & C3 & C4).
      eexists (mkEffect a [] [(a, Z_to_bv 64 n)]), _, [].
      split; [apply SPEC; right; exists a; split; [repeat split; assumption | reflexivity]|].
      split; [| reflexivity].
      apply spurious_refusal_not_refusal. rewrite HR. cbn [eff_ret]. apply mmap_grant_ret_nonrefusal. exact C1.
    + exists (efferr ENOMEM), (real mo mat), [].
      split; [apply SPEC; left; exists ENOMEM; split; [apply ENOMEM_in| reflexivity]|].
      split; [| reflexivity].
      apply nsp_forced. intros eff' m' evs' Hs'. rewrite HR.
      apply SPEC in Hs'. destruct Hs' as [(e & He & Heq) | (a & (C1 & C2 & C3 & C4 & C5) & Heq)].
      * apply Ok_inj in Heq as (-> & _ & _). cbn [eff_ret]. apply ret_in_errnos_errno. exact He.
      * exfalso. assert (EG' : vm_gap_available (m_vmmaps mo) n = true).
        { apply vm_gap_available_iff. exists a. repeat split; assumption. }
        congruence.
Qed.


(* [comment removed for export] *)
Theorem lscps_mmap_rw_nr_gen : forall (spin : bool) (P : machine_state -> Model -> lghost -> Prop) ms mo G R len,
  at_node segs (NMmap 0 len mm_prot_rw mm_flags_anon_nr) ms ->
  0 < len -> len + 4096 <= 2^64 ->
  let n := page_round_up_Z len in
  (forall e, In e mmap_errnos ->
     if spin then evt segs (jself segs) (nret ms (efferr e)) else LSCPS segs P (nret ms (efferr e)) mo (mkG G R)) ->
  (forall a, mmap_grant mo a n ->
     LSCPS segs P (msw (nret ms (mkEffect a [] [(a, Z_to_bv 64 n)])) (ms_mem ms)) (mm_add_lazy a (Z_to_bv 64 n) mo) (mkG G R)) ->
  (if spin then mmap_placeable mo n else True) ->
  LSCPS segs P ms mo (mkG G R).
Proof.
  intros spin P ms mo G R len HA H0 H1 n Href Hg HP. eapply lscps_mmap_rw_nr_forced; eauto.
  intros e He HNP. destruct spin; [exfalso; exact (HNP HP) | exact (Href e He)].
Qed.

(* [comment removed for export] *)
Theorem lscps_mmap_rw_nr_grant : forall (P : machine_state -> Model -> lghost -> Prop) ms mo G R len,
  at_node segs (NMmap 0 len mm_prot_rw mm_flags_anon_nr) ms ->
  0 < len -> len + 4096 <= 2^64 ->
  mmap_placeable mo (page_round_up_Z len) ->
  (forall a, mmap_grant mo a (page_round_up_Z len) ->
     LSCPS segs P (msw (nret ms (mkEffect a [] [(a, Z_to_bv 64 (page_round_up_Z len))])) (ms_mem ms))
           (mm_add_lazy a (Z_to_bv 64 (page_round_up_Z len)) mo) (mkG G R)) ->
  LSCPS segs P ms mo (mkG G R).
Proof.
  intros P ms mo G R len HA H0 H1 HP Hg. eapply lscps_mmap_rw_nr_forced; eauto.
  intros e _ HNP. exfalso. exact (HNP HP).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma inzr_maps_subtract : forall l lo hi (x : word), nowrap l -> lo <= hi ->
  in_rangesb (maps_subtract l lo hi) x = (in_rangesb l x && negb ((lo <=? bv_unsigned x) && (bv_unsigned x <? hi)))%bool.
Proof.
  intros l lo hi x Hnw Hlh. rewrite !in_rangesb_inzr.
  pose proof (nz_maps_subtract l lo hi (bv_unsigned x) Hnw Hlh) as Hz. unfold nz in Hz.
  destruct (inzr (maps_subtract l lo hi) (bv_unsigned x)); destruct (inzr l (bv_unsigned x));
    destruct ((lo <=? bv_unsigned x) && (bv_unsigned x <? hi))%bool; cbn in Hz |- *; try reflexivity; lia.
Qed.

Lemma nowrap_of_ceil : forall l,
  (forall b k, In (b, k) l -> bv_unsigned b + bv_unsigned k <= alloc_ceiling) -> nowrap l.
Proof. intros l H b k Hin. pose proof (H b k Hin). unfold uz. ceilb. lia. Qed.

Lemma bound_maps_subtract : forall B l lo hi, B <= 2^64 ->
  (forall b k, In (b, k) l -> bv_unsigned b + bv_unsigned k <= B) ->
  forall b k, In (b, k) (maps_subtract l lo hi) -> bv_unsigned b + bv_unsigned k <= B.
Proof.
  intros B l lo hi HB H. induction l as [|[a sz] l IH]; intros b k Hin; cbn [maps_subtract] in Hin; [destruct Hin|].
  apply in_app_or in Hin as [Hin|Hin].
  - pose proof (H a sz (or_introl eq_refl)) as Ha.
    destruct (iv_subtract_sub a sz lo hi (b, k) ltac:(unfold uz; pose proof (bv_unsigned_in_range 64 sz); lia) Hin) as [A B'].
    cbn [fst snd] in A, B'. unfold uz in *. lia.
  - apply IH; [intros b' k' Hin'; apply H; right; exact Hin'| exact Hin].
Qed.

Lemma ceil_maps_subtract : forall l lo hi,
  (forall b k, In (b, k) l -> bv_unsigned b + bv_unsigned k <= alloc_ceiling) ->
  forall b k, In (b, k) (maps_subtract l lo hi) -> bv_unsigned b + bv_unsigned k <= alloc_ceiling.
Proof. intros l lo hi. apply bound_maps_subtract. ceilb. lia. Qed.

Lemma wf_maps_subtract : forall l lo hi,
  (forall b k, In (b, k) l -> bv_unsigned b + bv_unsigned k <= 2^64) ->
  forall b k, In (b, k) (maps_subtract l lo hi) -> bv_unsigned b + bv_unsigned k <= 2^64.
Proof. intros l lo hi. apply bound_maps_subtract. lia. Qed.

Lemma nowrap_of_wf : forall l,
  (forall b k, In (b, k) l -> bv_unsigned b + bv_unsigned k <= 2^64) -> nowrap l.
Proof. intros l H b k Hin. exact (H b k Hin). Qed.

Lemma map_contains_inzr : forall maps (lo n x : word),
  map_contains maps lo n = true -> bv_unsigned lo <= bv_unsigned x < bv_unsigned lo + bv_unsigned n ->
  in_rangesb maps x = true.
Proof.
  intros maps lo n x H Hx. unfold map_contains in H. apply existsb_exists in H as ([b k] & Hin & Hb).
  cbn [fst snd] in Hb. apply andb_true_iff in Hb as [A B]. apply Z.leb_le in A. apply Z.leb_le in B.
  apply in_rangesb_true. exists b, k. split; [exact Hin| lia].
Qed.

Lemma region_free_reserved_noseg : forall (a n x : word) mo, no_wx segs -> LOK segs mo ->
  region_free (vm_reserved (m_vmmaps mo)) a n = true ->
  bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n -> noseg segs x.
Proof.
  intros a n x mo HWX HO Hf Hx. rewrite (lok_resv _ _ HO) in Hf.
  apply (region_free_noseg segs [] a n x HWX); [rewrite app_nil_r; exact Hf| exact Hx].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mm_commit (addr n : word) (mo : Model) : Model :=
  vm_forget_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
    (with_vmmaps (mmap_fixed_rw_next (m_vmmaps mo) addr n) mo).

Definition mfilter (lo hi : Z) (mat : list word) : list word := List.filter (page_outside_range lo hi) mat.

Lemma matok_mfilter : forall G lo hi mat, matok G mat -> matok G (mfilter lo hi mat).
Proof.
  intros G lo hi mat [A B]. split; [apply NoDup_filter; exact A|].
  intros p Hp. apply B. unfold mfilter in Hp. apply filter_In in Hp. exact (proj1 Hp).
Qed.

Lemma mm_commit_real : forall addr n mo mat,
  with_mmap_replacement (Z_to_bv 64 mm_flags_fixed) addr n
     (with_vmmaps (mmap_fixed_rw_next (m_vmmaps (real mo mat)) addr n) (real mo mat))
  = real (mm_commit addr n mo) (mfilter (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) mat).
Proof. reflexivity. Qed.

Lemma mm_commit_lazy : forall addr n mo,
  m_vm_lazy (mm_commit addr n mo) = maps_subtract (m_vm_lazy mo) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n).
Proof. reflexivity. Qed.
Lemma mm_commit_maps : forall addr n mo, vm_maps (m_vmmaps (mm_commit addr n mo)) = vm_maps (m_vmmaps mo).
Proof. reflexivity. Qed.
Lemma mm_commit_na : forall addr n mo,
  vm_noaccess (m_vmmaps (mm_commit addr n mo)) = maps_subtract (vm_noaccess (m_vmmaps mo)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n).
Proof. reflexivity. Qed.
Lemma mm_commit_vm_only : forall addr n mo, vm_only mo (mm_commit addr n mo).
Proof. intros. repeat split; reflexivity. Qed.
Lemma mm_commit_LOK : forall addr n mo, LOK segs mo -> LOK segs (mm_commit addr n mo).
Proof.
  intros addr n mo HO. pose proof (bv_unsigned_in_range 64 n) as Hn.
  pose proof (nowrap_of_wf _ (lok_na_ceil _ _ HO)) as Hna. pose proof (nowrap_of_ceil _ (lok_lazy_ceil _ _ HO)) as Hlz.
  destruct HO as [Oh Or Ob Omc Opwd Onc Olc Ons Olm Onm]. constructor; rewrite ?mm_commit_maps, ?mm_commit_na, ?mm_commit_lazy; try assumption.
  - eapply wf_maps_subtract. exact Onc.
  - eapply ceil_maps_subtract. exact Olc.
  - intros x Hx. rewrite inzr_maps_subtract in Hx by (try exact Hlz; lia). apply andb_true_iff in Hx as [Hx _]. exact (Ons x Hx).
  - intros x Hx. rewrite inzr_maps_subtract in Hx by (try exact Hlz; lia). apply andb_true_iff in Hx as [Hx _]. exact (Olm x Hx).
  - intros x Hx. rewrite inzr_maps_subtract in Hx by (try exact Hna; lia). apply andb_true_iff in Hx as [Hx _]. exact (Onm x Hx).
Qed.

Lemma mm_commit_eager : forall addr n mo, LOK segs mo ->
  map_contains (vm_maps (m_vmmaps mo)) addr n = true ->
  eager_used (mm_commit addr n mo) <= eager_used mo + bv_unsigned n.
Proof.
  intros addr n mo HO Hmc.
  pose proof (lok_maps_nowrap mo HO) as Hnw.
  pose proof (nowrap_of_wf _ (lok_na_ceil _ _ HO)) as Hna. pose proof (nowrap_of_ceil _ (lok_lazy_ceil _ _ HO)) as Hlz.
  pose proof (bv_unsigned_in_range 64 addr) as Ha. pose proof (bv_unsigned_in_range 64 n) as Hn. change (bv_modulus 64) with (2^64) in *.
  assert (Hc : bv_unsigned addr + bv_unsigned n <= alloc_ceiling).
  { unfold map_contains in Hmc. apply existsb_exists in Hmc as ([b k] & Hin & Hb). cbn [fst snd] in Hb.
    apply andb_true_iff in Hb as [A B]. apply Z.leb_le in A. apply Z.leb_le in B. pose proof (lok_maps_ceil _ _ HO b k Hin). lia. }
  rewrite (eager_used_total' (mm_commit addr n mo) Hnw), (eager_used_total' _ Hnw).
  rewrite mm_commit_maps, mm_commit_na, mm_commit_lazy.
  set (M := vm_maps (m_vmmaps mo)) in *. set (NA := vm_noaccess (m_vmmaps mo)) in *. set (L := m_vm_lazy mo) in *.
  transitivity (total (fun x => eagerf M NA L x + ind (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) x * cov M x)).
  - apply total_le. intros x Hx. unfold eagerf. rewrite !nz_maps_subtract by (try assumption; lia).
    pose proof (cov_nonneg M x). unfold ind.
    destruct ((bv_unsigned addr <=? x) && (x <? bv_unsigned addr + bv_unsigned n))%bool;
      destruct (nz_01 NA x) as [-> | ->]; destruct (nz_01 L x) as [-> | ->]; lia.
  - rewrite total_add.
    enough (total (fun x => ind (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) x * cov M x) <= bv_unsigned n) by lia.
    apply (Z.le_trans _ ((bv_unsigned addr + bv_unsigned n) - bv_unsigned addr)); [| lia].
    apply total_ind_le; try (ceilb; lia).
    + intros x _. apply cov_le_1. exact (lok_maps_pwd _ _ HO).
    + intros x _. apply cov_nonneg.
Qed.


Definition mmap_fixed_site (mo : Model) (A n : Z) : Prop :=
  A mod 4096 = 0 /\ 0 < A /\ A + n <= alloc_ceiling /\
  region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 A) (Z_to_bv 64 n) = true /\
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 A) (Z_to_bv 64 n) = true.

Ltac node_args Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 ms mr :=
  rewrite !in_a0_si, !in_a1_si, !in_a2_si, !in_a3_si, !in_a4_si, !in_a5_si;
  change (areg (msw ms mr) 10) with (areg ms 10); change (areg (msw ms mr) 11) with (areg ms 11);
  change (areg (msw ms mr) 12) with (areg ms 12); change (areg (msw ms mr) 13) with (areg ms 13);
  change (areg (msw ms mr) 14) with (areg ms 14); change (areg (msw ms mr) 15) with (areg ms 15);
  rewrite Ha0, Ha1, Ha2, Ha3, Ha4, Ha5.

(* [comment removed for export] *)
Theorem lscps_mmap_fixed_rw_grant : forall (P : machine_state -> Model -> lghost -> Prop) ms mo G R A len,
  at_node segs (NMmap A len mm_prot_rw mm_flags_fixed) ms ->
  0 < len -> len + 4096 <= 2^64 ->
  let n := page_round_up_Z len in
  mmap_fixed_site mo A n ->
  n <= R ->
  (* [comment removed for export] *)
  LSCPS segs P (nret ms (mkEffect (Z_to_bv 64 A) [] [(Z_to_bv 64 A, Z_to_bv 64 n)]))
        (mm_commit (Z_to_bv 64 A) (Z_to_bv 64 n) mo) (mkG G (R - n)) ->
  LSCPS segs P ms mo (mkG G R).
Proof.
  intros P ms mo G R A len HA Hlen0 Hlen1 n (S1 & S2 & S3 & S4 & S5) HnR Hgrant.
  destruct HA as (Hsvc & Ha0 & Ha1 & Ha2 & Ha3 & Ha4 & Ha5).
  assert (Hn : len <= n /\ n mod 4096 = 0 /\ n < len + 4096 /\ n = page_round_up_Z len).
  { subst n. unfold page_round_up_Z. rewrite page_size_eq. Z.div_mod_to_equations. lia. }
  clearbody n. destruct Hn as (Hn1 & Hn2 & Hn3 & En).
  pose proof (bv_unsigned_in_range 64) as UR.
  assert (Hun : bv_unsigned (Z_to_bv 64 n : word) = n) by (apply unsigned_lit; lia).
  assert (HuA : bv_unsigned (Z_to_bv 64 A : word) = A) by (apply unsigned_lit; ceilb; lia).
  set (nw := (Z_to_bv 64 n : word)) in *. set (Aw := (Z_to_bv 64 A : word)) in *.
  apply (lscps_sysnode segs P (fun _ => false) ms mo (mkG G R) (Z_to_bv 64 222) Hsvc).
  intros mr mat HI. pose proof HI as ([HWX HO] & HB & HLR & [HM HVD]).
  pose proof (lok_top _ _ HO) as HTOP.
  assert (SPEC : forall o, syscall_spec (sys_input segs (msw ms mr) (Z_to_bv 64 222)) (real mo mat) o <->
     mmap_err_out (real mo mat) o
     \/ (mmap_fixed_rw_budget_ok (Z_to_bv 64 mm_flags_fixed) (real mo mat) Aw nw = true
         /\ o = Ok (mkEffect Aw [] [(Aw, nw)]) (real (mm_commit Aw nw mo) (mfilter A (A + n) mat)) [])
     \/ exists e, In e mmap_errnos /\
          o = Ok (mkEffectU (errno_ret e) [] [] [(Aw, nw)] [] [])
                 (with_mmap_destroyed Aw nw (mmap_fixed_destroyed_next (m_vmmaps mo) Aw nw) (real mo mat)) []).
  { intros o. rewrite (syscall_spec_222 _ _ o) by reflexivity. node_args Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 ms mr.
    pose proof (mmap_fixed_rw_outcome Aw (Z_to_bv 64 len) (Z_to_bv 64 mm_prot_rw) (Z_to_bv 64 mm_flags_fixed)
                  (Z_to_bv 64 (-1)) (Z_to_bv 64 0) (sys_input segs (msw ms mr) (Z_to_bv 64 222)) (real mo mat) o) as RW.
    cbv zeta in RW. rewrite (unsigned_lit len) in RW by lia. rewrite <- En in RW. rewrite real_vmmaps in RW. fold nw in RW.
    assert (E1 : w_is0 (Z_to_bv 64 len) = false).
    { unfold w_is0. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. lia. }
    rewrite ?HuA, ?Hun in RW.
    specialize (RW eq_refl eq_refl E1 eq_refl eq_refl eq_refl eq_refl ltac:(rewrite HTOP; exact S3) ltac:(rewrite page_size_eq; exact S1) S2 S4 S5).
    pose proof (mm_commit_real Aw nw mo mat) as EC. rewrite real_vmmaps, ?HuA, ?Hun in EC.
    rewrite RW, EC. reflexivity. }
  (* [comment removed for export] *)
  assert (AZ : forall m x, apply_zeros m [(Aw, nw)] x = if in_range A n x then Some (Z_to_bv 8 0) else m x).
  { intros m x. unfold Aw, nw. apply apply_zeros_spec; ceilb; lia. }
  pose proof (nowrap_of_wf _ (lok_na_ceil _ _ HO)) as Hna. pose proof (nowrap_of_ceil _ (lok_lazy_ceil _ _ HO)) as Hlz.
  pose proof (lok_maps_nowrap mo HO) as Hmp.
  assert (LZC : forall x : word, in_range A n x = false -> lzf (mm_commit Aw nw mo) x = lzf mo x).
  { intros x Hx. unfold lzf. rewrite mm_commit_lazy, mm_commit_na, !inzr_maps_subtract by (try assumption; rewrite ?HuA, ?Hun; lia).
    rewrite HuA, Hun. unfold in_range in Hx. rewrite Hx. cbn [negb]. rewrite !andb_true_r. reflexivity. }
  (* [comment removed for export] *)
  assert (HBUD : mmap_fixed_rw_budget_ok (Z_to_bv 64 mm_flags_fixed) (real mo mat) Aw nw = true).
  { unfold mmap_fixed_rw_budget_ok. rewrite mm_commit_real. unfold vm_backing_within_limit.
    apply Z.leb_le. rewrite real_used, real_vmmaps. change (vm_limit (m_vmmaps (mm_commit Aw nw mo))) with (vm_limit (m_vmmaps mo)).
    pose proof (mm_commit_eager Aw nw mo HO S5) as HE. rewrite Hun in HE.
    pose proof (matok_length _ _ (matok_mfilter G A (A + n) mat HM)) as HL.
    destruct HB as (HBw & HBr & HBe). cbn [g_win g_res] in *. rewrite HuA, Hun, page_size_eq. unfold mfilter in *. nia. }
  assert (Hno : bv_unsigned (in_sysno (sys_input segs (msw ms mr) (Z_to_bv 64 222))) = 222) by reflexivity.
  assert (HR : forall r, refusal_b (sys_input segs (msw ms mr) (Z_to_bv 64 222)) (real mo mat) r = ret_in_errnos mmap_errnos r)
    by (intros r; exact (refusal_b_222 _ _ r Hno)).
  assert (Hoff : injected_family_off ACFG (sys_input segs (msw ms mr) (Z_to_bv 64 222)) = true)
    by (apply acfg_family_off_alloc; right; right; left; exact Hno).
  assert (Hhr : m_halted (real mo mat) = None) by (rewrite real_halted; exact (lok_halt _ _ HO)).
  assert (HGS : syscall_spec (sys_input segs (msw ms mr) (Z_to_bv 64 222)) (real mo mat)
                  (Ok (mkEffect Aw [] [(Aw, nw)]) (real (mm_commit Aw nw mo) (mfilter A (A + n) mat)) []))
    by (apply SPEC; right; left; split; [exact HBUD | reflexivity]).
  assert (HGR : refusal_b (sys_input segs (msw ms mr) (Z_to_bv 64 222)) (real mo mat) (eff_ret (mkEffect Aw [] [(Aw, nw)])) = false)
    by (rewrite HR; cbn [eff_ret]; apply mmap_grant_ret_nonrefusal; rewrite HuA, page_size_eq; exact S1).
  split.
  - intros o Ho. apply SPEC in Ho. destruct Ho as [(e & He & ->) | [(Hbud & ->) | (e & He & ->)]].
    + (* [comment removed for export] *)
      right. eexists _, _, _. split; [reflexivity|]. split; [|exact Hhr].
      refine (refusal_spurious_of_grant ACFG _ _ _ _ _ _ Hoff _ HGS HGR).
      rewrite HR. exact (ret_in_errnos_errno _ _ He).
    + (* [comment removed for export] *)
      left.
      exists (mkEffect Aw [] [(Aw, nw)]), (mm_commit Aw nw mo), (mkG G (R - n)), (apply_zeros (ms_mem ms) [(Aw, nw)]), (mfilter A (A + n) mat).
      split; [reflexivity|]. split; [reflexivity|]. split; [apply mm_commit_vm_only|]. split.
      { rewrite mem_nret_zeros. cbn [ms_mem msw].
        split; [split; [exact HWX| apply mm_commit_LOK; exact HO]|]. split.
        { destruct HB as (HBw & HBr & HBe). unfold BINV. cbn [g_win g_res] in *. split; [exact HBw|]. split; [lia|].
          pose proof (mm_commit_eager Aw nw mo HO S5). rewrite Hun in H.
          change (vm_limit (m_vmmaps (mm_commit Aw nw mo))) with (vm_limit (m_vmmaps mo)). lia. }
        split; [| split; [apply matok_mfilter; exact HM|]].
        { destruct HLR as [Hm Hhid]. split.
          * apply (magree_transfer _ _ _ _ _ _ _ _ _ Hm). intros x. rewrite (AZ mr x).
            destruct (in_range A n x) eqn:Er.
            -- left. unfold lmem. rewrite (AZ (ms_mem ms) x), Er. reflexivity.
            -- right. rewrite (AZ (ms_mem ms) x), Er, (LZC x Er). repeat split; try reflexivity.
               unfold lexc. rewrite (LZC x Er). cbn [g_win]. exact (fun H => H).
          * intros x Hl Hw. rewrite mm_commit_lazy, inzr_maps_subtract in Hl by (try assumption; rewrite ?HuA, ?Hun; lia).
            rewrite HuA, Hun in Hl. apply andb_true_iff in Hl as [Hl Hr]. rewrite (AZ (ms_mem ms) x).
            unfold in_range. destruct ((A <=? bv_unsigned x) && (bv_unsigned x <? A + n))%bool; [discriminate|].
            apply Hhid; assumption. }
        intros x Hx. rewrite (AZ (ms_mem ms) x) in Hx. rewrite mm_commit_maps.
        unfold in_range in Hx. destruct (Z.leb_spec0 A (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (A + n)); cbn [andb] in Hx;
          try (apply HVD; exact Hx).
        right; right. apply (map_contains_inzr _ Aw nw); [exact S5| rewrite HuA, Hun; lia]. }
      cbn [eff_ret]. rewrite <- (mem_nret_zeros ms Aw (Aw, nw) []), msw_nret_self.
      right. split; [reflexivity | exact Hgrant].
    + right. eexists _, _, _. split; [reflexivity|]. split; [|exact Hhr].
      refine (refusal_spurious_of_grant ACFG _ _ _ _ _ _ Hoff _ HGS HGR).
      rewrite HR. exact (ret_in_errnos_errno _ _ He).
  - exists (mkEffect Aw [] [(Aw, nw)]), (real (mm_commit Aw nw mo) (mfilter A (A + n) mat)), [].
    split; [exact HGS|]. split; [| reflexivity]. apply spurious_refusal_not_refusal. exact HGR.
Qed.


(* [comment removed for export] *)
Theorem lscps_mmap_fixed_rw_gen : forall (spin : bool) (P : machine_state -> Model -> lghost -> Prop) ms mo G R A len,
  at_node segs (NMmap A len mm_prot_rw mm_flags_fixed) ms ->
  0 < len -> len + 4096 <= 2^64 ->
  let n := page_round_up_Z len in
  mmap_fixed_site mo A n ->
  n <= R ->
  (forall e, In e mmap_errnos ->
     if spin then evt segs (jself segs) (nret ms (efferr e)) else LSCPS segs P (nret ms (efferr e)) mo (mkG G R)) ->
  LSCPS segs P (nret ms (mkEffect (Z_to_bv 64 A) [] [(Z_to_bv 64 A, Z_to_bv 64 n)]))
        (mm_commit (Z_to_bv 64 A) (Z_to_bv 64 n) mo) (mkG G (R - n)) ->
  LSCPS segs P ms mo (mkG G R).
Proof. intros spin P ms mo G R A len HA H0 H1 n HS HR _ Hg. eapply lscps_mmap_fixed_rw_grant; eauto. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mm_unmap (addr n : word) (mo : Model) : Model :=
  let h := m_vmmaps mo in
  with_mmap_destroyed addr n
    (mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) addr)
       (maps_subtract (vm_noaccess h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
       (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo.

Lemma mm_unmap_real : forall addr n mo mat,
  with_mmap_destroyed addr n
    (mkVmMapsFull (vm_reserved (m_vmmaps (real mo mat))) (map_remove (vm_maps (m_vmmaps (real mo mat))) addr)
       (maps_subtract (vm_noaccess (m_vmmaps (real mo mat))) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
       (vm_start_brk (m_vmmaps (real mo mat))) (vm_brk (m_vmmaps (real mo mat))) (vm_limit (m_vmmaps (real mo mat)))
       (vm_mmap_base (m_vmmaps (real mo mat))) (vm_init_sp (m_vmmaps (real mo mat)))) (real mo mat)
  = real (mm_unmap addr n mo) (mfilter (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) mat).
Proof. reflexivity. Qed.

Lemma mm_unmap_lazy : forall addr n mo,
  m_vm_lazy (mm_unmap addr n mo) = maps_subtract (m_vm_lazy mo) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n).
Proof. reflexivity. Qed.
Lemma mm_unmap_maps : forall addr n mo, vm_maps (m_vmmaps (mm_unmap addr n mo)) = map_remove (vm_maps (m_vmmaps mo)) addr.
Proof. reflexivity. Qed.
Lemma mm_unmap_na : forall addr n mo,
  vm_noaccess (m_vmmaps (mm_unmap addr n mo)) = maps_subtract (vm_noaccess (m_vmmaps mo)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n).
Proof. reflexivity. Qed.
Lemma mm_unmap_vm_only : forall addr n mo, vm_only mo (mm_unmap addr n mo).
Proof. intros. repeat split; reflexivity. Qed.

Lemma map_has_In : forall maps (a n : word), map_has maps a n = true -> In (a, n) maps.
Proof.
  intros maps a n H. unfold map_has in H. apply existsb_exists in H as ([b k] & Hin & Hb). cbn [fst snd] in Hb.
  apply andb_true_iff in Hb as [E1 E2]. apply bv_eqb_true in E1. apply bv_eqb_true in E2. subst. exact Hin.
Qed.

Lemma In_map_remove : forall maps (a : word) e, In e (map_remove maps a) <-> In e maps /\ fst e <> a.
Proof.
  intros maps a e. unfold map_remove. rewrite filter_In. split.
  - intros [Hin Hb]. split; [exact Hin|]. intros E. rewrite E, bv_eqb_refl in Hb. discriminate.
  - intros [Hin Hne]. split; [exact Hin|]. rewrite (bv_eqb_neq _ _ Hne). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma pwd_based_unique : forall maps (a n : word) (b k : word) (x : Z),
  pwd maps -> In (a, n) maps -> 0 < bv_unsigned n -> In (b, k) maps -> b = a ->
  bv_unsigned b <= x < bv_unsigned b + bv_unsigned k -> bv_unsigned a <= x < bv_unsigned a + bv_unsigned n.
Proof.
  intros maps a n b k x Hp Hin Hn Hin' -> Hx.
  destruct (Z.eq_dec (bv_unsigned k) (bv_unsigned n)) as [E|NE]; [lia|].
  exfalso. assert (Hne : (a, n) <> (a, k)) by (intros E2; injection E2 as E3; subst; lia).
  (* [comment removed for export] *)
  pose proof (bv_unsigned_in_range 64 k).
  revert Hin Hin' Hne. induction Hp as [|e l Hd Hl IH]; intros Hin Hin' Hne; [destruct Hin|].
  destruct Hin as [E1|Hin]; destruct Hin' as [E2|Hin'].
  - apply Hne. congruence.
  - subst e. destruct (Hd _ Hin') as [D|D]; cbn [fst snd] in D; unfold uz in D; lia.
  - subst e. destruct (Hd _ Hin) as [D|D]; cbn [fst snd] in D; unfold uz in D; lia.
  - exact (IH Hin Hin' Hne).
Qed.

Lemma inzr_map_remove : forall maps (a n : word) (x : word),
  pwd maps -> In (a, n) maps -> 0 < bv_unsigned n ->
  in_rangesb (map_remove maps a) x = (in_rangesb maps x && negb ((bv_unsigned a <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned a + bv_unsigned n)))%bool.
Proof.
  intros maps a n x Hp Hin Hn.
  destruct (in_rangesb (map_remove maps a) x) eqn:E.
  - apply in_rangesb_true in E as (b & k & Hbk & Hx). apply In_map_remove in Hbk as [Hbk Hne]. cbn [fst] in Hne.
    symmetry. apply andb_true_iff. split; [apply in_rangesb_true; eauto|].
    apply negb_true_iff. destruct (Z.leb_spec0 (bv_unsigned a) (bv_unsigned x)) as [L1|L1]; destruct (Z.ltb_spec0 (bv_unsigned x) (bv_unsigned a + bv_unsigned n)) as [L2|L2]; cbn; try reflexivity.
    exfalso. (* [comment removed for export] *)
    revert Hin Hbk. induction Hp as [|e l0 Hd Hl IH]; intros Hin Hbk; [destruct Hin|].
    destruct Hin as [E1|Hin]; destruct Hbk as [E2|Hbk].
    + apply Hne. congruence.
    + subst e. destruct (Hd _ Hbk) as [D|D]; cbn [fst snd] in D; unfold uz in D; lia.
    + subst e. destruct (Hd _ Hin) as [D|D]; cbn [fst snd] in D; unfold uz in D; lia.
    + exact (IH Hin Hbk).
  - symmetry. apply andb_false_iff.
    destruct (in_rangesb maps x) eqn:E2; [right| left; reflexivity].
    apply in_rangesb_true in E2 as (b & k & Hbk & Hx).
    destruct (bv_eq_dec _ b a) as [->|Hne].
    + pose proof (pwd_based_unique maps a n a k (bv_unsigned x) Hp Hin Hn Hbk eq_refl Hx).
      apply negb_false_iff. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
    + exfalso. assert (in_rangesb (map_remove maps a) x = true); [| congruence].
      apply in_rangesb_true. exists b, k. split; [| exact Hx]. apply In_map_remove. split; [exact Hbk| exact Hne].
Qed.

Lemma cov_map_remove : forall maps (a n : word) x,
  pwd maps -> In (a, n) maps -> 0 < bv_unsigned n -> nowrap maps ->
  cov (map_remove maps a) x = cov maps x * (1 - ind (uz a) (uz a + uz n) x).
Proof.
  intros maps a n x Hp Hin Hn Hnw.
  pose proof (cov_le_1 maps x Hp) as H1. pose proof (cov_nonneg maps x) as H0.
  pose proof (cov_le_1 (map_remove maps a) x (pwd_filter _ _ Hp)) as H1'. pose proof (cov_nonneg (map_remove maps a) x) as H0'.
  destruct (Z_lt_le_dec x 0) as [Hneg|Hnn].
  { (* [comment removed for export] *)
    assert (Z1 : forall l, cov l x = 0).
    { intros l. apply (proj1 (inzr_cov l x)). apply inzr_false_spec. intros b k _ Hb. pose proof (bv_unsigned_in_range 64 b). unfold uz in *. lia. }
    rewrite !Z1. lia. }
  destruct (Z_lt_le_dec x (2^64)) as [Hlt|Hge].
  2:{ assert (Z1 : forall l, nowrap l -> cov l x = 0).
      { intros l Hl. apply (proj1 (inzr_cov l x)). apply inzr_false_spec. intros b k Hbk Hb. pose proof (Hl b k Hbk). lia. }
      rewrite !Z1; [lia| exact Hnw|]. intros b k Hbk. apply In_map_remove in Hbk. apply Hnw. exact (proj1 Hbk). }
  set (xw := (Z_to_bv 64 x : word)).
  assert (Ex : bv_unsigned xw = x) by (unfold xw; apply unsigned_lit; lia).
  pose proof (inzr_map_remove maps a n xw Hp Hin Hn) as E. rewrite !in_rangesb_inzr, Ex in E.
  unfold ind, uz. destruct ((bv_unsigned a <=? x) && (x <? bv_unsigned a + bv_unsigned n))%bool; cbn [negb] in E.
  - rewrite andb_false_r in E. pose proof (proj1 (inzr_cov _ x) E). lia.
  - rewrite andb_true_r in E. destruct (inzr maps x) eqn:E2.
    + pose proof (proj1 (inzr_cov_pos _ x) E). pose proof (proj1 (inzr_cov_pos _ x) E2). lia.
    + pose proof (proj1 (inzr_cov _ x) E). pose proof (proj1 (inzr_cov _ x) E2). lia.
Qed.

Lemma mm_unmap_LOK : forall addr n mo, LOK segs mo -> map_has (vm_maps (m_vmmaps mo)) addr n = true -> 0 < bv_unsigned n ->
  LOK segs (mm_unmap addr n mo).
Proof.
  intros addr n mo HO Hh Hn. pose proof (map_has_In _ _ _ Hh) as Hin.
  pose proof (nowrap_of_wf _ (lok_na_ceil _ _ HO)) as Hna. pose proof (nowrap_of_ceil _ (lok_lazy_ceil _ _ HO)) as Hlz.
  pose proof (lok_maps_pwd _ _ HO) as Hp.
  destruct HO as [Oh Or Ob Omc Opwd Onc Olc Ons Olm Onm]. constructor; rewrite ?mm_unmap_maps, ?mm_unmap_na, ?mm_unmap_lazy; try assumption.
  - intros b k Hbk. apply In_map_remove in Hbk. apply Omc. exact (proj1 Hbk).
  - apply pwd_filter. exact Opwd.
  - eapply wf_maps_subtract. exact Onc.
  - eapply ceil_maps_subtract. exact Olc.
  - intros x Hx. rewrite inzr_maps_subtract in Hx by (try exact Hlz; lia). apply andb_true_iff in Hx as [Hx _]. exact (Ons x Hx).
  - intros x Hx. rewrite (inzr_maps_subtract (m_vm_lazy mo)) in Hx by (try exact Hlz; lia).
    rewrite (inzr_map_remove _ addr n x Hp Hin Hn). apply andb_true_iff in Hx as [Hx Hr]. rewrite (Olm x Hx), Hr. reflexivity.
  - intros x Hx. rewrite (inzr_maps_subtract (vm_noaccess (m_vmmaps mo))) in Hx by (try exact Hna; lia).
    rewrite (inzr_map_remove _ addr n x Hp Hin Hn). apply andb_true_iff in Hx as [Hx Hr]. rewrite (Onm x Hx), Hr. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mm_unmap_eager : forall addr n mo, LOK segs mo -> map_has (vm_maps (m_vmmaps mo)) addr n = true -> 0 < bv_unsigned n ->
  (forall x : word, bv_unsigned addr <= bv_unsigned x < bv_unsigned addr + bv_unsigned n ->
     in_rangesb (vm_noaccess (m_vmmaps mo)) x = false /\ in_rangesb (m_vm_lazy mo) x = false) ->
  eager_used (mm_unmap addr n mo) + bv_unsigned n <= eager_used mo.
Proof.
  intros addr n mo HO Hh Hn Hplain. pose proof (map_has_In _ _ _ Hh) as Hin.
  pose proof (lok_maps_nowrap mo HO) as Hnw. pose proof (lok_maps_pwd _ _ HO) as Hp.
  pose proof (nowrap_of_wf _ (lok_na_ceil _ _ HO)) as Hna. pose proof (nowrap_of_ceil _ (lok_lazy_ceil _ _ HO)) as Hlz.
  pose proof (bv_unsigned_in_range 64 addr) as Ha. pose proof (bv_unsigned_in_range 64 n) as Hnr. change (bv_modulus 64) with (2^64) in *.
  pose proof (lok_maps_ceil _ _ HO addr n Hin) as Hc. ceilb.
  assert (Hnw' : nowrap (vm_maps (m_vmmaps (mm_unmap addr n mo)))).
  { rewrite mm_unmap_maps. intros b k Hbk. apply In_map_remove in Hbk. apply Hnw. exact (proj1 Hbk). }
  rewrite (eager_used_total' (mm_unmap addr n mo) Hnw'), (eager_used_total' _ Hnw).
  rewrite mm_unmap_maps, mm_unmap_na, mm_unmap_lazy.
  match goal with |- total ?f1 + _ <= total ?f2 =>
    enough (HH : total f1 + total (ind (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)) <= total f2)
      by (rewrite total_ind in HH by lia; lia) end.
  rewrite <- total_add. apply total_le. intros x Hx. unfold eagerf.
  rewrite (cov_map_remove _ addr n x Hp Hin Hn Hnw), !nz_maps_subtract by (try assumption; lia). unfold uz.
  pose proof (cov_le_1 _ x Hp) as H1. pose proof (cov_nonneg (vm_maps (m_vmmaps mo)) x) as H0.
  unfold ind. destruct (Z.leb_spec0 (bv_unsigned addr) x); destruct (Z.ltb_spec0 x (bv_unsigned addr + bv_unsigned n)); cbn [andb];
    try (destruct (nz_01 (vm_noaccess (m_vmmaps mo)) x) as [-> | ->]; destruct (nz_01 (m_vm_lazy mo) x) as [-> | ->]; lia).
  (* [comment removed for export] *)
  set (xw := (Z_to_bv 64 x : word)). assert (Ex : bv_unsigned xw = x) by (unfold xw; apply unsigned_lit; lia).
  destruct (Hplain xw ltac:(rewrite Ex; lia)) as [P1 P2]. rewrite !in_rangesb_inzr, Ex in P1, P2.
  unfold nz. rewrite P1, P2.
  assert (Hcov : 0 < cov (vm_maps (m_vmmaps mo)) x).
  { apply (proj1 (inzr_cov_pos _ x)). apply inzr_spec. exists addr, n. split; [exact Hin| unfold uz; lia]. }
  lia.
Qed.

Theorem lscps_munmap : forall (P : machine_state -> Model -> lghost -> Prop) ms mo G R A len,
  at_node segs (NMunmap A len) ms ->
  0 < len -> len + 4096 <= 2^64 ->
  let n := page_round_up_Z len in
  0 <= A -> A mod 4096 = 0 -> A + n <= alloc_ceiling ->
  map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 A) (Z_to_bv 64 n) = true ->
  (* [comment removed for export] *)
  (forall x : word, A <= bv_unsigned x < A + n ->
     in_rangesb (vm_noaccess (m_vmmaps mo)) x = false /\ in_rangesb (m_vm_lazy mo) x = false) ->
  LSCPS segs P (nret ms (mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 A, Z_to_bv 64 n)] [] []))
        (mm_unmap (Z_to_bv 64 A) (Z_to_bv 64 n) mo) (mkG G (R + n)) ->
  LSCPS segs P ms mo (mkG G R).
Proof.
  intros P ms mo G R A len HA Hlen0 Hlen1 n HA0 HA1 HA2 Hhas Hplain Hk.
  destruct HA as (Hsvc & Ha0 & Ha1).
  assert (Hn : len <= n /\ n mod 4096 = 0 /\ n < len + 4096 /\ n = page_round_up_Z len).
  { subst n. unfold page_round_up_Z. rewrite page_size_eq. Z.div_mod_to_equations. lia. }
  clearbody n. destruct Hn as (Hn1 & Hn2 & Hn3 & En).
  pose proof (bv_unsigned_in_range 64) as UR.
  assert (Hun : bv_unsigned (Z_to_bv 64 n : word) = n) by (apply unsigned_lit; lia).
  assert (HuA : bv_unsigned (Z_to_bv 64 A : word) = A) by (apply unsigned_lit; ceilb; lia).
  set (nw := (Z_to_bv 64 n : word)) in *. set (Aw := (Z_to_bv 64 A : word)) in *.
  apply (lscps_sysnode segs P (fun _ => false) ms mo (mkG G R) (Z_to_bv 64 215) Hsvc).
  intros mr mat HI. pose proof HI as ([HWX HO] & HB & HLR & [HM HVD]).
  assert (SPEC : forall o, syscall_spec (sys_input segs (msw ms mr) (Z_to_bv 64 215)) (real mo mat) o <->
     o = Ok (mkEffectU (Z_to_bv 64 0) [] [] [(Aw, nw)] [] []) (real (mm_unmap Aw nw mo) (mfilter A (A + n) mat)) []).
  { intros o. rewrite (syscall_spec_215 _ _ o) by reflexivity.
    rewrite !in_a0_si, !in_a1_si. change (areg (msw ms mr) 10) with (areg ms 10). change (areg (msw ms mr) 11) with (areg ms 11).
    rewrite Ha0, Ha1.
    pose proof (munmap_exact_outcome Aw (Z_to_bv 64 len) (sys_input segs (msw ms mr) (Z_to_bv 64 215)) (real mo mat) o) as RW.
    cbv zeta in RW. rewrite (unsigned_lit len) in RW by lia. rewrite <- En in RW. rewrite !real_vmmaps in RW. fold nw in RW.
    assert (E1 : w_is0 (Z_to_bv 64 len) = false).
    { unfold w_is0. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. lia. }
    rewrite ?HuA, ?Hun in RW.
    specialize (RW ltac:(rewrite page_size_eq; exact HA1) E1 ltac:(unfold TASK_SIZE; ceilb; lia) Hhas).
    pose proof (mm_unmap_real Aw nw mo mat) as ED. rewrite !real_vmmaps, ?HuA, ?Hun in ED.
    rewrite RW, ED. reflexivity. }
  assert (AU : forall m x, apply_unmaps m [(Aw, nw)] x = if in_range A n x then None else m x).
  { intros m x. unfold Aw, nw. apply apply_unmaps_spec; ceilb; lia. }
  pose proof (nowrap_of_wf _ (lok_na_ceil _ _ HO)) as Hna. pose proof (nowrap_of_ceil _ (lok_lazy_ceil _ _ HO)) as Hlz.
  pose proof (lok_maps_nowrap mo HO) as Hmp. pose proof (map_has_In _ _ _ Hhas) as Hin.
  assert (LZD : forall x : word, lzf (mm_unmap Aw nw mo) x = (lzf mo x && negb (in_range A n x))%bool).
  { intros x. unfold lzf. rewrite mm_unmap_lazy, mm_unmap_na, !inzr_maps_subtract by (try assumption; rewrite ?HuA, ?Hun; lia).
    rewrite HuA, Hun. unfold in_range.
    destruct (in_rangesb (m_vm_lazy mo) x); destruct (in_rangesb (vm_noaccess (m_vmmaps mo)) x);
      destruct ((A <=? bv_unsigned x) && (bv_unsigned x <? A + n))%bool; reflexivity. }
  split.
  - intros o Ho. left. apply SPEC in Ho. subst o.
    exists (mkEffectU (Z_to_bv 64 0) [] [] [(Aw, nw)] [] []), (mm_unmap Aw nw mo), (mkG G (R + n)), (apply_unmaps (ms_mem ms) [(Aw, nw)]), (mfilter A (A + n) mat).
    split; [reflexivity|]. split; [reflexivity|]. split; [apply mm_unmap_vm_only|]. split.
    { rewrite mem_nret_unmaps. cbn [ms_mem msw].
      split; [split; [exact HWX| apply mm_unmap_LOK; [exact HO| exact Hhas| rewrite Hun; lia]]|]. split.
      { destruct HB as (HBw & HBr & HBe). unfold BINV. cbn [g_win g_res] in *. split; [exact HBw|]. split; [lia|].
        pose proof (mm_unmap_eager Aw nw mo HO Hhas ltac:(rewrite Hun; lia) ltac:(rewrite HuA, Hun; exact Hplain)). rewrite Hun in H.
        change (vm_limit (m_vmmaps (mm_unmap Aw nw mo))) with (vm_limit (m_vmmaps mo)). lia. }
      split; [| split; [apply matok_mfilter; exact HM|]].
      { destruct HLR as [Hm Hhid]. split.
        * apply (magree_transfer _ _ _ _ _ _ _ _ _ Hm). intros x. rewrite (AU mr x).
          destruct (in_range A n x) eqn:Er.
          -- left. unfold lmem. rewrite (AU (ms_mem ms) x), Er, LZD, Er. cbn [negb]. rewrite andb_false_r. reflexivity.
          -- right. rewrite (AU (ms_mem ms) x), Er, LZD, Er. cbn [negb]. rewrite andb_true_r. repeat split; try reflexivity.
             unfold lexc. rewrite LZD, Er. cbn [negb]. rewrite andb_true_r. cbn [g_win]. exact (fun H => H).
        * intros x Hl Hw. rewrite mm_unmap_lazy, inzr_maps_subtract in Hl by (try assumption; rewrite ?HuA, ?Hun; lia).
          rewrite HuA, Hun in Hl. apply andb_true_iff in Hl as [Hl Hr]. rewrite (AU (ms_mem ms) x).
          unfold in_range. destruct ((A <=? bv_unsigned x) && (bv_unsigned x <? A + n))%bool; [reflexivity|].
          apply Hhid; assumption. }
      intros x Hx. rewrite (AU (ms_mem ms) x) in Hx. rewrite mm_unmap_maps, (inzr_map_remove _ Aw nw x (lok_maps_pwd _ _ HO) Hin) by (rewrite Hun; lia).
      rewrite HuA, Hun. unfold in_range in Hx.
      destruct ((A <=? bv_unsigned x) && (bv_unsigned x <? A + n))%bool; [congruence|].
      destruct (HVD x Hx) as [B|[B|B]]; [left; exact B| right; left; exact B| right; right; rewrite B; reflexivity]. }
    cbn [eff_ret]. rewrite <- (mem_nret_unmaps ms (Z_to_bv 64 0) (Aw, nw) []), msw_nret_self.
    right. split; [reflexivity| exact Hk].
  - eexists (mkEffectU (Z_to_bv 64 0) [] [] [(Aw, nw)] [] []), _, []. split; [apply SPEC; reflexivity|].
    split; [exact (nsp_no segs _ (Z_to_bv 64 215) _ _ _ eq_refl eq_refl) | reflexivity].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mmap_placeable_of_free : forall mo n g0,
  LOK segs mo -> 0 < n -> n mod 4096 = 0 ->
  g0 mod 4096 = 0 -> 0 < g0 ->
  g0 + n <= alloc_ceiling ->
  region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 g0) (Z_to_bv 64 n) = true ->
  mmap_placeable mo n.
Proof.
  intros mo n g0 HO Hn Hna Hga Hgp Hgb Hgf. exists (Z_to_bv 64 g0).
  assert (Hug : bv_unsigned (Z_to_bv 64 g0 : word) = g0) by (apply unsigned_lit; ceilb; lia).
  unfold mmap_grant. rewrite Hug, page_size_eq. repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma mmap_placeable_of_bounds : forall mo n K S,
  LOK segs mo -> 0 <= n ->
  Z.of_nat (length (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo))) <= K ->
  LGap04.zsumf LGap04.esz (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) <= S ->
  4096 + S + K * (n + 4095) + n <= alloc_ceiling ->
  mmap_placeable mo n.
Proof.
  intros mo n K S HO Hn HK HS Hroom. apply (mmap_placeable_gap mo n HO).
  apply (LGap04.vm_gap_available_of_bounds (m_vmmaps mo) n K S Hn HK HS). rewrite (lok_top _ _ HO). exact Hroom.
Qed.

(* [comment removed for export] *)
Lemma mmap_placeable_of_sum_from : forall mo n a0,
  LOK segs mo -> 0 <= n -> 4096 <= a0 -> a0 mod 4096 = 0 ->
  (forall e, In e (vm_reserved (m_vmmaps mo)) -> LGap04.elo e + LGap04.esz e <= a0) ->
  a0 + LGap04.zsumf (LGap04.jcost n) (vm_maps (m_vmmaps mo)) + n <= alloc_ceiling ->
  mmap_placeable mo n.
Proof.
  intros mo n a0 HO Hn Ha0 Hal Hres Hroom. apply (mmap_placeable_gap mo n HO).
  apply (LGap04.vm_gap_available_of_sum_from (m_vmmaps mo) n a0 Hn Ha0 Hal Hres). rewrite (lok_top _ _ HO). exact Hroom.
Qed.

(* [comment removed for export] *)
Theorem lscps_mmap_rw_nr : forall (P : machine_state -> Model -> lghost -> Prop) ms mo G R len,
  at_node segs (NMmap 0 len mm_prot_rw mm_flags_anon_nr) ms ->
  0 < len -> len + 4096 <= 2^64 ->
  (forall e, In e mmap_errnos -> LSCPS segs P (nret ms (efferr e)) mo (mkG G R)) ->
  (forall a, mmap_grant mo a (page_round_up_Z len) ->
     LSCPS segs P (msw (nret ms (mkEffect a [] [(a, Z_to_bv 64 (page_round_up_Z len))])) (ms_mem ms))
           (mm_add_lazy a (Z_to_bv 64 (page_round_up_Z len)) mo) (mkG G R)) ->
  LSCPS segs P ms mo (mkG G R).
Proof. intros. eapply (lscps_mmap_rw_nr_gen false); eauto. Qed.

Theorem lscps_mmap_rw_nr_spin : forall (P : machine_state -> Model -> lghost -> Prop) ms mo G R len,
  at_node segs (NMmap 0 len mm_prot_rw mm_flags_anon_nr) ms ->
  0 < len -> len + 4096 <= 2^64 ->
  mmap_placeable mo (page_round_up_Z len) ->
  (forall e, In e mmap_errnos -> evt segs (jself segs) (nret ms (efferr e))) ->
  (forall a, mmap_grant mo a (page_round_up_Z len) ->
     LSCPS segs P (msw (nret ms (mkEffect a [] [(a, Z_to_bv 64 (page_round_up_Z len))])) (ms_mem ms))
           (mm_add_lazy a (Z_to_bv 64 (page_round_up_Z len)) mo) (mkG G R)) ->
  LSCPS segs P ms mo (mkG G R).
Proof. intros P ms mo G R len HA H0 H1 HP _ Hg. eapply lscps_mmap_rw_nr_grant; eauto. Qed.

End WithSegs.
End LNodesMM.

(* [comment removed for export] *)
Module LNodesMM2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RelSpec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRelSpec LNodesMM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.
Context {ACEIL : Ceil}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition reveal0 (G : gwin) (a n : Z) (mv : mem) : mem :=
  fun x => if (in_range a n x && in_winb G x)%bool then Some (Z_to_bv 8 0) else mv x.

Lemma reveal0_out : forall G a n mv x, in_range a n x = false -> reveal0 G a n mv x = mv x.
Proof. intros G a n mv x H. unfold reveal0. rewrite H. reflexivity. Qed.
Lemma reveal0_win : forall G a n mv x, in_range a n x = true -> in_winb G x = true -> reveal0 G a n mv x = Some (Z_to_bv 8 0).
Proof. intros G a n mv x H1 H2. unfold reveal0. rewrite H1, H2. reflexivity. Qed.
Lemma reveal0_nowin : forall G a n mv x, in_winb G x = false -> reveal0 G a n mv x = mv x.
Proof. intros G a n mv x H. unfold reveal0. rewrite H, andb_false_r. reflexivity. Qed.

(* [comment removed for export] *)
Theorem lscps_mmap_rw_gen2 : forall (spin : bool) (P : machine_state -> Model -> lghost -> Prop) ms mo G R len,
  at_node segs (NMmap 0 len mm_prot_rw mm_flags_anon) ms ->
  0 < len -> len + 4096 <= 2^64 ->
  let n := page_round_up_Z len in
  n <= R ->
  (forall e, In e mmap_errnos ->
     if spin then evt segs (jself segs) (nret ms (efferr e)) else LSCPS segs P (nret ms (efferr e)) mo (mkG G R)) ->
  (forall a, mmap_grant mo a n ->
     LSCPS segs P (nret ms (mkEffect a [] [(a, Z_to_bv 64 n)])) (mm_add_map a (Z_to_bv 64 n) mo) (mkG G (R - n))) ->
  (if spin then mmap_placeable mo n else True) ->
  LSCPS segs P ms mo (mkG G R).
Proof. intros. eapply lscps_mmap_rw_gen; eauto. Qed.

Theorem lscps_mmap_rw_nr_forced2 : forall (P : machine_state -> Model -> lghost -> Prop) ms mo G R len,
  at_node segs (NMmap 0 len mm_prot_rw mm_flags_anon_nr) ms ->
  0 < len -> len + 4096 <= 2^64 ->
  let n := page_round_up_Z len in
  (forall e, In e mmap_errnos -> ~ mmap_placeable mo n -> LSCPS segs P (nret ms (efferr e)) mo (mkG G R)) ->
  (forall a, mmap_grant mo a n ->
     LSCPS segs P (msw (nret ms (mkEffect a [] [(a, Z_to_bv 64 n)])) (reveal0 G (bv_unsigned a) n (ms_mem ms)))
           (mm_add_lazy a (Z_to_bv 64 n) mo) (mkG G R)) ->
  LSCPS segs P ms mo (mkG G R).
Proof.
  intros P ms mo G R len HA Hlen0 Hlen1 n Href Hgrant.
  destruct HA as (Hsvc & Ha0 & Ha1 & Ha2 & Ha3 & Ha4 & Ha5).
  assert (Hn : len <= n /\ n mod 4096 = 0 /\ n < len + 4096 /\ n = page_round_up_Z len).
  { subst n. unfold page_round_up_Z. rewrite page_size_eq. Z.div_mod_to_equations. lia. }
  clearbody n. destruct Hn as (Hn1 & Hn2 & Hn3 & En).
  assert (Hun : bv_unsigned (Z_to_bv 64 n : word) = n).
  { apply unsigned_lit. lia. }
  apply (lscps_sysnode segs P (fun _ => false) ms mo (mkG G R) (Z_to_bv 64 222) Hsvc).
  intros mr mat HI. pose proof HI as ([HWX HO] & HB & HLR & [HM HVD]).
  pose proof (lok_top _ _ HO) as HTOP.
  assert (SPEC : forall o, syscall_spec (sys_input segs (msw ms mr) (Z_to_bv 64 222)) (real mo mat) o <->
            mmap_err_out (real mo mat) o
            \/ exists a, ((bv_unsigned a mod page_size = 0) /\ (0 < bv_unsigned a) /\ (bv_unsigned a + n <= alloc_top (m_vmmaps mo))
                          /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a (Z_to_bv 64 n) = true
                          /\ mmap_noreserve_backed_ok (Z_to_bv 64 mm_flags_anon_nr) (real mo mat) n = true)
                         /\ o = Ok (mkEffect a [] [(a, Z_to_bv 64 n)])
                                  (vm_add_lazy a (Z_to_bv 64 n) (mm_add_map a (Z_to_bv 64 n) (real mo mat))) []).
  { intros o. rewrite (syscall_spec_222 _ _ o) by reflexivity.
    rewrite !in_a0_si, !in_a1_si, !in_a2_si, !in_a3_si, !in_a4_si, !in_a5_si.
    change (areg (msw ms mr) 10) with (areg ms 10). change (areg (msw ms mr) 11) with (areg ms 11).
    change (areg (msw ms mr) 12) with (areg ms 12). change (areg (msw ms mr) 13) with (areg ms 13).
    change (areg (msw ms mr) 14) with (areg ms 14). change (areg (msw ms mr) 15) with (areg ms 15).
    rewrite Ha0, Ha1, Ha2, Ha3, Ha4, Ha5.
    pose proof (mmap_rw_outcome (Z_to_bv 64 0) (Z_to_bv 64 len) (Z_to_bv 64 mm_prot_rw) (Z_to_bv 64 mm_flags_anon_nr)
                  (Z_to_bv 64 (-1)) (Z_to_bv 64 0) (sys_input segs (msw ms mr) (Z_to_bv 64 222)) (real mo mat) o) as RW.
    cbv zeta in RW. rewrite (unsigned_lit len) in RW by lia. rewrite <- En in RW. rewrite real_vmmaps in RW.
    assert (E1 : w_is0 (Z_to_bv 64 len) = false).
    { unfold w_is0. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. lia. }
    specialize (RW eq_refl eq_refl E1 eq_refl). rewrite RW. reflexivity. }
  pose proof (bv_unsigned_in_range 64) as UR.
  assert (Hno : bv_unsigned (in_sysno (sys_input segs (msw ms mr) (Z_to_bv 64 222))) = 222) by reflexivity.
  assert (HR : forall r, refusal_b (sys_input segs (msw ms mr) (Z_to_bv 64 222)) (real mo mat) r = ret_in_errnos mmap_errnos r)
    by (intros r; exact (refusal_b_222 _ _ r Hno)).
  assert (Hoff : injected_family_off ACFG (sys_input segs (msw ms mr) (Z_to_bv 64 222)) = true)
    by (apply acfg_family_off_alloc; right; right; left; exact Hno).
  assert (Hhr : m_halted (real mo mat) = None) by (rewrite real_halted; exact (lok_halt _ _ HO)).
  split.
  - intros o Ho. apply SPEC in Ho. destruct Ho as [(e & He & ->) | (a & (C1 & C2 & C3 & C4 & C5) & ->)].
    + destruct (vm_gap_available (m_vmmaps mo) n) eqn:EG.
      { right. pose proof (proj1 (vm_gap_available_iff _ _) EG) as (a & C1 & C2 & C3 & C4).
        eexists _, _, _. split; [reflexivity|]. split; [|exact Hhr].
        apply (refusal_spurious_of_grant ACFG _ _ _ (mkEffect a [] [(a, Z_to_bv 64 n)])
                 (vm_add_lazy a (Z_to_bv 64 n) (mm_add_map a (Z_to_bv 64 n) (real mo mat))) []);
          [exact Hoff
          | rewrite HR; exact (ret_in_errnos_errno _ _ He)
          | apply SPEC; right; exists a; split; [repeat split; assumption | reflexivity]
          | rewrite HR; cbn [eff_ret]; apply mmap_grant_ret_nonrefusal; exact C1]. }
      left.
      assert (HNP : ~ mmap_placeable mo n).
      { intros HP. apply (mmap_placeable_gap segs mo n HO) in HP. congruence. }
      exists (efferr e), mo, (mkG G R), (ms_mem ms), mat.
      split; [reflexivity|]. split; [reflexivity|]. split; [apply vm_only_refl|]. split.
      { unfold efferr, eff0. rewrite mem_nret_plain. cbn [ms_mem msw]. exact HI. }
      pose proof (Href e He HNP) as K. unfold efferr, eff0 in K |- *. cbn [eff_ret].
      rewrite <- (mem_nret_plain ms (errno_ret e)), msw_nret_self.
      right; split; [reflexivity | exact K].
    + left. rewrite HTOP in C3.
set (nw := (Z_to_bv 64 n : word)) in *.
      pose proof (UR a) as Ra. change (bv_modulus 64) with (2^64) in Ra.
      assert (EL : lazy_interior a nw = [(a, nw)]).
      { apply lazy_interior_aligned; rewrite ?Hun; try lia; try (rewrite page_size_eq in C1; exact C1); try (ceilb; lia). }
      exists (mkEffect a [] [(a, nw)]), (mm_add_lazy a nw mo), (mkG G R), (reveal0 G (bv_unsigned a) n (ms_mem ms)), mat.
      split; [rewrite (mm_add_lazy_real a nw mo mat EL); reflexivity|].
      split; [reflexivity|]. split; [apply mm_add_lazy_vm_only|].
      assert (AZ : forall m x, apply_zeros m [(a, nw)] x = if in_range (bv_unsigned a) n x then Some (Z_to_bv 8 0) else m x).
      { intros m x. rewrite <- (Z_to_bv_bv_unsigned a) at 1. change (Z_to_bv 64 (bv_unsigned a)) with (wa (bv_unsigned a)).
        unfold nw. apply apply_zeros_spec; ceilb; lia. }
      (* [comment removed for export] *)
      assert (FR : forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + n -> ms_mem ms x = None).
      { intros x Hx. destruct (ms_mem ms x) eqn:Ex; [|reflexivity]. exfalso.
        destruct (HVD x ltac:(congruence)) as [A|[A|A]].
        - ceilb. lia.
        - apply A. rewrite (lok_resv _ _ HO) in C4. eapply region_free_noseg; [exact HWX| exact C4| rewrite Hun; exact Hx].
        - apply in_rangesb_true in A as (b' & k & Hin & Hbx).
          assert (Hfm : region_free (vm_maps (m_vmmaps mo)) a nw = true).
          { rewrite region_free_app in C4. apply andb_true_iff in C4. exact (proj2 C4). }
          eapply (region_free_false_of _ a nw b' k x Hfm Hin); [rewrite Hun; exact Hx| exact Hbx]. }
      assert (RV : forall x, reveal0 G (bv_unsigned a) n (ms_mem ms) x =
                          if (in_range (bv_unsigned a) n x && in_winb G x)%bool then Some (Z_to_bv 8 0) else ms_mem ms x) by (intros x; reflexivity).
      assert (LZ : forall x, lzf (mm_add_lazy a nw mo) x = (in_range (bv_unsigned a) n x || lzf mo x)%bool).
      { intros x. unfold lzf. rewrite mm_add_lazy_lazy, mm_add_lazy_vmmaps, mm_add_map_vmmaps.
        cbn [vm_noaccess in_rangesb existsb fst snd]. fold (in_rangesb (m_vm_lazy mo) x). fold (in_rangesb (vm_noaccess (m_vmmaps mo)) x).
        rewrite Hun. unfold in_range.
        destruct (Z.leb_spec0 (bv_unsigned a) (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (bv_unsigned a + n)); cbn [andb orb];
          try reflexivity.
        destruct (in_rangesb (vm_noaccess (m_vmmaps mo)) x) eqn:Ena; [| reflexivity]. exfalso.
        pose proof (lok_na_maps _ _ HO x Ena) as Hmx. apply in_rangesb_true in Hmx as (b & k & Hin & Hbx).
        assert (Hfm : region_free (vm_maps (m_vmmaps mo)) a nw = true).
        { rewrite region_free_app in C4. apply andb_true_iff in C4. exact (proj2 C4). }
        eapply (region_free_false_of _ a nw b k x Hfm Hin); [rewrite Hun; lia| exact Hbx]. }
      split.
      { rewrite mem_nret_zeros. cbn [ms_mem msw].
        split; [split; [exact HWX| apply mm_add_lazy_LOK; [exact HO| exact HWX| rewrite Hun; exact C3| exact C4]]|].
        split.
        { destruct HB as (HBw & HBr & HBe). unfold BINV. cbn [g_win g_res] in *. split; [exact HBw|]. split; [exact HBr|].
          pose proof (mm_add_lazy_eager segs a nw mo HO ltac:(rewrite Hun; exact C3)).
          change (vm_limit (m_vmmaps (mm_add_lazy a nw mo))) with (vm_limit (m_vmmaps mo)). lia. }
        split; [| split; [exact HM|]].
        { destruct HLR as [Hm Hhid]. split.
          * apply (magree_transfer _ _ _ _ _ _ _ _ _ Hm). intros x. unfold lmem. rewrite (AZ mr x), LZ, !RV. unfold in_range.
            destruct (Z.leb_spec0 (bv_unsigned a) (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (bv_unsigned a + n)); cbn [andb orb];
              try (right; repeat split; try reflexivity; unfold lexc; rewrite LZ; unfold in_range;
                   destruct (Z.leb_spec0 (bv_unsigned a) (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (bv_unsigned a + n)); cbn [andb orb]; try lia;
                   exact (fun H => H)).
            left. destruct (in_winb G x); [reflexivity|]. rewrite (FR x) by lia. reflexivity.
          * intros x Hl Hw. cbn [g_win] in Hw. rewrite RV, Hw, andb_false_r.
            rewrite mm_add_lazy_lazy in Hl. cbn [in_rangesb existsb fst snd] in Hl. fold (in_rangesb (m_vm_lazy mo) x) in Hl.
            apply orb_true_iff in Hl as [Hl|Hl]; [| apply Hhid; assumption].
            apply andb_true_iff in Hl as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. rewrite Hun in B. apply FR. lia. }
        intros x Hx. rewrite RV in Hx.
        rewrite mm_add_lazy_vmmaps, mm_add_map_vmmaps. cbn [vm_maps in_rangesb existsb fst snd]. fold (in_rangesb (vm_maps (m_vmmaps mo)) x). rewrite Hun.
        unfold in_range in Hx |- *.
        destruct (Z.leb_spec0 (bv_unsigned a) (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (bv_unsigned a + n)); cbn [andb orb] in Hx |- *.
        1: right; right; reflexivity.
        all: destruct (HVD x Hx) as [A|[A|A]]; [left; exact A| right; left; exact A| right; right; rewrite A; rewrite ?orb_true_r; reflexivity]. }
      pose proof (Hgrant a (conj C1 (conj C2 (conj C3 C4)))) as K. cbn [eff_ret].
      right. split; [reflexivity | exact K].
  - destruct (vm_gap_available (m_vmmaps mo) n) eqn:EG.
    + pose proof (proj1 (vm_gap_available_iff _ _) EG) as (a & C1 & C2 & C3 & C4).
      eexists (mkEffect a [] [(a, Z_to_bv 64 n)]), _, [].
      split; [apply SPEC; right; exists a; split; [repeat split; assumption | reflexivity]|].
      split; [| reflexivity].
      apply spurious_refusal_not_refusal. rewrite HR. cbn [eff_ret]. apply mmap_grant_ret_nonrefusal. exact C1.
    + exists (efferr ENOMEM), (real mo mat), [].
      split; [apply SPEC; left; exists ENOMEM; split; [apply ENOMEM_in| reflexivity]|].
      split; [| reflexivity].
      apply nsp_forced. intros eff' m' evs' Hs'. rewrite HR.
      apply SPEC in Hs'. destruct Hs' as [(e & He & Heq) | (a & (C1 & C2 & C3 & C4 & C5) & Heq)].
      * apply Ok_inj in Heq as (-> & _ & _). cbn [eff_ret]. apply ret_in_errnos_errno. exact He.
      * exfalso. assert (EG' : vm_gap_available (m_vmmaps mo) n = true).
        { apply vm_gap_available_iff. exists a. repeat split; assumption. }
        congruence.
Qed.
(* [comment removed for export] *)
Theorem lscps_mmap_rw_nr_gen2 : forall (spin : bool) (P : machine_state -> Model -> lghost -> Prop) ms mo G R len,
  at_node segs (NMmap 0 len mm_prot_rw mm_flags_anon_nr) ms ->
  0 < len -> len + 4096 <= 2^64 ->
  let n := page_round_up_Z len in
  (forall e, In e mmap_errnos ->
     if spin then evt segs (jself segs) (nret ms (efferr e)) else LSCPS segs P (nret ms (efferr e)) mo (mkG G R)) ->
  (forall a, mmap_grant mo a n ->
     LSCPS segs P (msw (nret ms (mkEffect a [] [(a, Z_to_bv 64 n)])) (reveal0 G (bv_unsigned a) n (ms_mem ms)))
           (mm_add_lazy a (Z_to_bv 64 n) mo) (mkG G R)) ->
  (if spin then mmap_placeable mo n else True) ->
  LSCPS segs P ms mo (mkG G R).
Proof.
  intros spin P ms mo G R len HA H0 H1 n Href Hg HP. eapply lscps_mmap_rw_nr_forced2; eauto.
  intros e He HNP. destruct spin; [exfalso; exact (HNP HP) | exact (Href e He)].
Qed.

Theorem lscps_mmap_rw_nr_grant2 : forall (P : machine_state -> Model -> lghost -> Prop) ms mo G R len,
  at_node segs (NMmap 0 len mm_prot_rw mm_flags_anon_nr) ms ->
  0 < len -> len + 4096 <= 2^64 ->
  mmap_placeable mo (page_round_up_Z len) ->
  (forall a, mmap_grant mo a (page_round_up_Z len) ->
     LSCPS segs P (msw (nret ms (mkEffect a [] [(a, Z_to_bv 64 (page_round_up_Z len))])) (reveal0 G (bv_unsigned a) (page_round_up_Z len) (ms_mem ms)))
           (mm_add_lazy a (Z_to_bv 64 (page_round_up_Z len)) mo) (mkG G R)) ->
  LSCPS segs P ms mo (mkG G R).
Proof.
  intros P ms mo G R len HA H0 H1 HP Hg. eapply lscps_mmap_rw_nr_forced2; eauto.
  intros e _ HNP. exfalso. exact (HNP HP).
Qed.

Theorem lscps_mmap_rw2 : forall (P : machine_state -> Model -> lghost -> Prop) ms mo G R len,
  at_node segs (NMmap 0 len mm_prot_rw mm_flags_anon) ms ->
  0 < len -> len + 4096 <= 2^64 ->
  page_round_up_Z len <= R ->
  (forall e, In e mmap_errnos -> LSCPS segs P (nret ms (efferr e)) mo (mkG G R)) ->
  (forall a, mmap_grant mo a (page_round_up_Z len) ->
     LSCPS segs P (nret ms (mkEffect a [] [(a, Z_to_bv 64 (page_round_up_Z len))]))
           (mm_add_map a (Z_to_bv 64 (page_round_up_Z len)) mo) (mkG G (R - page_round_up_Z len))) ->
  LSCPS segs P ms mo (mkG G R).
Proof. intros. eapply lscps_mmap_rw; eauto. Qed.

Theorem lscps_mmap_rw_spin2 : forall (P : machine_state -> Model -> lghost -> Prop) ms mo G R len,
  at_node segs (NMmap 0 len mm_prot_rw mm_flags_anon) ms ->
  0 < len -> len + 4096 <= 2^64 ->
  page_round_up_Z len <= R ->
  mmap_placeable mo (page_round_up_Z len) ->
  (forall e, In e mmap_errnos -> evt segs (jself segs) (nret ms (efferr e))) ->
  (forall a, mmap_grant mo a (page_round_up_Z len) ->
     LSCPS segs P (nret ms (mkEffect a [] [(a, Z_to_bv 64 (page_round_up_Z len))]))
           (mm_add_map a (Z_to_bv 64 (page_round_up_Z len)) mo) (mkG G (R - page_round_up_Z len))) ->
  LSCPS segs P ms mo (mkG G R).
Proof. intros. eapply lscps_mmap_rw_spin; eauto. Qed.

Theorem lscps_mmap_rw_nr2 : forall (P : machine_state -> Model -> lghost -> Prop) ms mo G R len,
  at_node segs (NMmap 0 len mm_prot_rw mm_flags_anon_nr) ms ->
  0 < len -> len + 4096 <= 2^64 ->
  (forall e, In e mmap_errnos -> LSCPS segs P (nret ms (efferr e)) mo (mkG G R)) ->
  (forall a, mmap_grant mo a (page_round_up_Z len) ->
     LSCPS segs P (msw (nret ms (mkEffect a [] [(a, Z_to_bv 64 (page_round_up_Z len))])) (reveal0 G (bv_unsigned a) (page_round_up_Z len) (ms_mem ms)))
           (mm_add_lazy a (Z_to_bv 64 (page_round_up_Z len)) mo) (mkG G R)) ->
  LSCPS segs P ms mo (mkG G R).
Proof. intros. eapply (lscps_mmap_rw_nr_gen2 false); eauto. Qed.

Theorem lscps_mmap_rw_nr_spin2 : forall (P : machine_state -> Model -> lghost -> Prop) ms mo G R len,
  at_node segs (NMmap 0 len mm_prot_rw mm_flags_anon_nr) ms ->
  0 < len -> len + 4096 <= 2^64 ->
  mmap_placeable mo (page_round_up_Z len) ->
  (forall e, In e mmap_errnos -> evt segs (jself segs) (nret ms (efferr e))) ->
  (forall a, mmap_grant mo a (page_round_up_Z len) ->
     LSCPS segs P (msw (nret ms (mkEffect a [] [(a, Z_to_bv 64 (page_round_up_Z len))])) (reveal0 G (bv_unsigned a) (page_round_up_Z len) (ms_mem ms)))
           (mm_add_lazy a (Z_to_bv 64 (page_round_up_Z len)) mo) (mkG G R)) ->
  LSCPS segs P ms mo (mkG G R).
Proof. intros P ms mo G R len HA H0 H1 HP _ Hg. eapply lscps_mmap_rw_nr_grant2; eauto. Qed.

End WithSegs.
End LNodesMM2.

(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Madvise.
Module LNodesMadv.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Madvise.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RelSpec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRelSpec LNodesMM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition at_madvise (A len : Z) (ms : machine_state) : Prop :=
  ms_svc_pending ms = Some (Z_to_bv 64 233)
  /\ areg ms 10 = Z_to_bv 64 A /\ areg ms 11 = Z_to_bv 64 len /\ areg ms 12 = Z_to_bv 64 4.

(* [comment removed for export] *)
Definition noaccess_pos (mo : Model) : Prop :=
  forall b k, In (b, k) (vm_noaccess (m_vmmaps mo)) -> 0 < bv_unsigned k.

Lemma region_free_of_pointwise : forall (L : list (word * word)) (a n : word),
  (forall b k, In (b, k) L -> 0 < bv_unsigned k) ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n -> in_rangesb L x = false) ->
  0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= 2^64 ->
  region_free L a n = true.
Proof.
  intros L a n Hpos Hpt Hn0 Hnw. apply region_free_intro. intros b k Hin.
  unfold iv_overlap. destruct (Z.ltb_spec0 (bv_unsigned a) (bv_unsigned b + bv_unsigned k)); [|reflexivity].
  destruct (Z.ltb_spec0 (bv_unsigned b) (bv_unsigned a + bv_unsigned n)); [|reflexivity]. exfalso.
  pose proof (Hpos b k Hin) as Hk.
  pose proof (bv_unsigned_in_range 64 a) as Ra. pose proof (bv_unsigned_in_range 64 b) as Rb.
  change (bv_modulus 64) with (2^64) in *.
  (* [comment removed for export] *)
  destruct (Z_le_gt_dec (bv_unsigned a) (bv_unsigned b)) as [Hab|Hab].
  - specialize (Hpt b ltac:(lia)). apply (proj1 (in_rangesb_false L b) Hpt b k Hin). lia.
  - specialize (Hpt a ltac:(lia)). apply (proj1 (in_rangesb_false L a) Hpt b k Hin). lia.
Qed.

Section WithSegs.
Variable segs : list Segment.
Context {ACEIL : Ceil}.

Theorem lscps_madvise_dontneed : forall (P : machine_state -> Model -> lghost -> Prop) ms mo G R A len,
  at_madvise A len ms ->
  0 < len -> len + 4096 <= 2^64 ->
  let n := page_round_up_Z len in
  A mod 4096 = 0 -> 0 <= A -> A + n <= alloc_ceiling ->
  (* [comment removed for export] *)
  region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 A) (Z_to_bv 64 n) = true ->
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 A) (Z_to_bv 64 n) = true ->
  region_free (vm_noaccess (m_vmmaps mo)) (Z_to_bv 64 A) (Z_to_bv 64 n) = true ->
  (* [comment removed for export] *)
  (forall x : word, A <= bv_unsigned x < A + n -> in_rangesb (m_vm_lazy mo) x = true -> in_winb G x = true) ->
  (* [comment removed for export] *)
  LSCPS segs P (nret ms (mkEffect (Z_to_bv 64 0) [] [(Z_to_bv 64 A, Z_to_bv 64 n)])) mo (mkG G R) ->
  LSCPS segs P ms mo (mkG G R).
Proof.
  intros P ms mo G R A len HA Hlen0 Hlen1 n HA1 HA0 HA2 Hrf Hmc Hna Hwin Hk.
  destruct HA as (Hsvc & Ha0 & Ha1 & Ha2).
  assert (Hn : len <= n /\ n mod 4096 = 0 /\ n < len + 4096 /\ n = page_round_up_Z len).
  { subst n. unfold page_round_up_Z. rewrite page_size_eq. Z.div_mod_to_equations. lia. }
  clearbody n. destruct Hn as (Hn1 & Hn2 & Hn3 & En).
  pose proof (bv_unsigned_in_range 64) as UR.
  assert (Hun : bv_unsigned (Z_to_bv 64 n : word) = n) by (apply unsigned_lit; lia).
  assert (HuA : bv_unsigned (Z_to_bv 64 A : word) = A) by (apply unsigned_lit; ceilb; lia).
  set (nw := (Z_to_bv 64 n : word)) in *. set (Aw := (Z_to_bv 64 A : word)) in *.
  apply (lscps_sysnode segs P (fun _ => false) ms mo (mkG G R) (Z_to_bv 64 233) Hsvc).
  intros mr mat HI. pose proof HI as ([HWX HO] & HB & HLR & [HM HVD]).
  assert (SPEC : forall o, syscall_spec (sys_input segs (msw ms mr) (Z_to_bv 64 233)) (real mo mat) o <->
     o = Ok (mkEffect (Z_to_bv 64 0) [] [(Aw, nw)]) (real mo (mfilter A (A + n) mat)) []).
  { intros o. rewrite (syscall_spec_233 _ _ o) by reflexivity.
    rewrite !in_a0_si, !in_a1_si, !in_a2_si.
    change (areg (msw ms mr) 10) with (areg ms 10). change (areg (msw ms mr) 11) with (areg ms 11).
    change (areg (msw ms mr) 12) with (areg ms 12). rewrite Ha0, Ha1, Ha2.
    pose proof (madvise_dontneed_outcome Aw (Z_to_bv 64 len) (Syscall.int32 (Z_to_bv 64 4))
                  (sys_input segs (msw ms mr) (Z_to_bv 64 233)) (real mo mat) o) as RW.
    cbv zeta in RW. rewrite (unsigned_lit len) in RW by lia. rewrite <- En in RW. rewrite real_vmmaps in RW. fold nw in RW.
    assert (E1 : w_is0 (Z_to_bv 64 len) = false).
    { unfold w_is0. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. lia. }
    rewrite ?HuA in RW.
    specialize (RW ltac:(rewrite page_size_eq; exact HA1) eq_refl E1 ltac:(unfold two_pow_64; ceilb; lia)
                   ltac:(unfold madvise_dontneed_ok; rewrite Hrf, Hmc, Hna; reflexivity)).
    rewrite RW. unfold madvise_dontneed_next, mfilter. rewrite real_lazy, real_mat, HuA, Hun. reflexivity. }
  assert (AZ : forall m x, apply_zeros m [(Aw, nw)] x = if in_range A n x then Some (Z_to_bv 8 0) else m x).
  { intros m x. unfold Aw, nw. apply apply_zeros_spec; ceilb; lia. }
  split.
  - intros o Ho. left. apply SPEC in Ho. subst o.
    exists (mkEffect (Z_to_bv 64 0) [] [(Aw, nw)]), mo, (mkG G R), (apply_zeros (ms_mem ms) [(Aw, nw)]), (mfilter A (A + n) mat).
    split; [reflexivity|]. split; [reflexivity|]. split; [apply vm_only_refl|]. split.
    { rewrite mem_nret_zeros. cbn [ms_mem msw].
      split; [split; [exact HWX| exact HO]|]. split; [exact HB|].
      split; [| split; [apply matok_mfilter; exact HM|]].
      { destruct HLR as [Hm Hhid]. split.
        * apply (magree_transfer _ _ _ _ _ _ _ _ _ Hm). intros x. rewrite (AZ mr x).
          destruct (in_range A n x) eqn:Er.
          -- left. unfold lmem. rewrite (AZ (ms_mem ms) x), Er. reflexivity.
          -- right. rewrite (AZ (ms_mem ms) x), Er. repeat split; try reflexivity. exact (fun H => H).
        * intros x Hl Hw. cbn [g_win] in Hw. rewrite (AZ (ms_mem ms) x).
          destruct (in_range A n x) eqn:Er; [| apply Hhid; assumption].
          exfalso. unfold in_range in Er. apply andb_true_iff in Er as [E2 E3]. apply Z.leb_le in E2. apply Z.ltb_lt in E3.
          rewrite (Hwin x ltac:(lia) Hl) in Hw. discriminate Hw. }
      intros x Hx. rewrite (AZ (ms_mem ms) x) in Hx.
      unfold in_range in Hx. destruct (Z.leb_spec0 A (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (A + n)); cbn [andb] in Hx;
        try (apply HVD; exact Hx).
      right; right. apply (map_contains_inzr _ Aw nw); [exact Hmc| rewrite HuA, Hun; lia]. }
    cbn [eff_ret]. rewrite <- (mem_nret_zeros ms (Z_to_bv 64 0) (Aw, nw) []), msw_nret_self.
    right. split; [reflexivity | exact Hk].
  - eexists (mkEffect (Z_to_bv 64 0) [] [(Aw, nw)]), _, []. split; [apply SPEC; reflexivity|].
    split; [exact (nsp_no segs _ (Z_to_bv 64 233) _ _ _ eq_refl eq_refl) | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma noaccess_pos_add_map : forall a n mo, noaccess_pos mo -> noaccess_pos (mm_add_map a n mo).
Proof. intros a n mo H b k Hin. exact (H b k Hin). Qed.

Lemma noaccess_pos_add_lazy : forall a n mo, noaccess_pos mo -> noaccess_pos (mm_add_lazy a n mo).
Proof. intros a n mo H b k Hin. exact (H b k Hin). Qed.

End WithSegs.
End LNodesMadv.

(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg RelSpec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil PropExec MState Mem Cells Step Frame Exec SCPS ITree Nodes SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import Spin SRealizes LMeasure LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LRelSpec.
Import LNodesMM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LRz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.
Context {ACEIL : Ceil}.   (* [comment removed for export] *)
Local Abbreviation LSCPS := (LSCPS.LSCPS segs).
Local Abbreviation LRZ := (LRz.LRZ segs).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma srz_alt2_spin : forall c (I : Type) (nx : I -> config) (cls : I -> option bool) (TA TB : TSet) (ia ib : I),
  node_ok segs c I (fun _ => []) nx ->
  cls ia = Some true -> cls ib = Some false ->
  (forall i, cls i = None -> jspinning segs (nx i)) ->
  (forall i, cls i = Some true -> srealizes segs (nx i) TA) ->
  (forall i, cls i = Some false -> srealizes segs (nx i) TB) ->
  srealizes segs c (t_alt2 TA TB).
Proof.
  intros c I nx cls TA TB ia ib Hnode Hia Hib Hsp HA HB.
  assert (HA0 : TA []) by (eapply srealizes_nonempty; apply (HA ia Hia)).
  assert (HB0 : TB []) by (eapply srealizes_nonempty; apply (HB ib Hib)).
  apply (srz_conseq segs c (t_alt (fun i : I => t_emit [] (match cls i with None => t_nil | Some true => TA | Some false => TB end)))).
  - apply (srz_node segs c I (fun _ => []) nx (fun i => match cls i with None => t_nil | Some true => TA | Some false => TB end) ia Hnode).
    intros i. destruct (cls i) as [[|]|] eqn:E.
    + apply HA. exact E.
    + apply HB. exact E.
    + apply srz_jspin. apply Hsp. exact E.
  - intro tr. unfold t_alt2. split.
    + intros [i Hi]. destruct (cls i) as [[|]|].
      * left. exact (proj1 (t_emit_nil_eq TA HA0 tr) Hi).
      * right. exact (proj1 (t_emit_nil_eq TB HB0 tr) Hi).
      * apply (t_emit_nil_eq t_nil eq_refl tr) in Hi. unfold t_nil in Hi. subst tr. left. exact HA0.
    + intros [H|H].
      * exists ia. rewrite Hia. exact (proj2 (t_emit_nil_eq TA HA0 tr) H).
      * exists ib. rewrite Hib. exact (proj2 (t_emit_nil_eq TB HB0 tr) H).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition LSCPS2 (PA PB : machine_state -> Model -> lghost -> Prop)
           (ms : machine_state) (mo : Model) (g : lghost) : Prop :=
  forall mr mat, LINV segs g mo mat (ms_mem ms) mr ->
  forall TA TB : TSet,
    (forall ms' mo' g' mr' mat',
        PA ms' mo' g' -> LINV segs g' mo' mat' (ms_mem ms') mr' -> vm_only mo mo' ->
        srealizes segs (mkCfg (msw ms' mr') (real mo' mat')) TA) ->
    (forall ms' mo' g' mr' mat',
        PB ms' mo' g' -> LINV segs g' mo' mat' (ms_mem ms') mr' -> vm_only mo mo' ->
        srealizes segs (mkCfg (msw ms' mr') (real mo' mat')) TB) ->
    srealizes segs (mkCfg (msw ms mr) (real mo mat)) (t_alt2 TA TB).

Lemma lscps2_mono : forall (PA PB QA QB : machine_state -> Model -> lghost -> Prop) ms mo g,
  LSCPS2 PA PB ms mo g ->
  (forall ms' mo' g', PA ms' mo' g' -> QA ms' mo' g') -> (forall ms' mo' g', PB ms' mo' g' -> QB ms' mo' g') ->
  LSCPS2 QA QB ms mo g.
Proof.
  intros PA PB QA QB ms mo g H HA HB mr mat HI TA TB KA KB. apply (H mr mat HI).
  - intros ms' mo' g' mr' mat' HP HI' HV. eapply KA; [apply HA, HP| exact HI'| exact HV].
  - intros ms' mo' g' mr' mat' HP HI' HV. eapply KB; [apply HB, HP| exact HI'| exact HV].
Qed.

(* [comment removed for export] *)
Lemma lscps_lscps2 : forall (P PA PB : machine_state -> Model -> lghost -> Prop) ms mo g,
  LSCPS P ms mo g -> (forall ms' mo' g', P ms' mo' g' -> LSCPS2 PA PB ms' mo' g') -> LSCPS2 PA PB ms mo g.
Proof.
  intros P PA PB ms mo g H K mr mat HI TA TB KA KB. apply (H mr mat HI). intros ms' mo' g' mr' mat' HP HI' HV.
  apply (K ms' mo' g' HP mr' mat' HI').
  - intros ms2 mo2 g2 mr2 mat2 HQ HI2 HV2. eapply KA; [exact HQ| exact HI2| eapply vm_only_trans; eassumption].
  - intros ms2 mo2 g2 mr2 mat2 HQ HI2 HV2. eapply KB; [exact HQ| exact HI2| eapply vm_only_trans; eassumption].
Qed.

(* [comment removed for export] *)
Lemma lscps2_lscps : forall (PA PB QA QB : machine_state -> Model -> lghost -> Prop) ms mo g,
  LSCPS2 PA PB ms mo g ->
  (forall ms' mo' g', PA ms' mo' g' -> LSCPS QA ms' mo' g') ->
  (forall ms' mo' g', PB ms' mo' g' -> LSCPS QB ms' mo' g') ->
  LSCPS2 QA QB ms mo g.
Proof.
  intros PA PB QA QB ms mo g H KA KB mr mat HI TA TB HA HB. apply (H mr mat HI).
  - intros ms' mo' g' mr' mat' HP HI' HV. apply (KA ms' mo' g' HP mr' mat' HI').
    intros ms2 mo2 g2 mr2 mat2 HQ HI2 HV2. eapply HA; [exact HQ| exact HI2| eapply vm_only_trans; eassumption].
  - intros ms' mo' g' mr' mat' HP HI' HV. apply (KB ms' mo' g' HP mr' mat' HI').
    intros ms2 mo2 g2 mr2 mat2 HQ HI2 HV2. eapply HB; [exact HQ| exact HI2| eapply vm_only_trans; eassumption].
Qed.

Lemma lscps2_eq : forall PA PB ms ms' mo g, ms = ms' -> LSCPS2 PA PB ms' mo g -> LSCPS2 PA PB ms mo g.
Proof. intros; subst; assumption. Qed.

Lemma lscps2_assume : forall (PA PB : machine_state -> Model -> lghost -> Prop) ms mo g,
  (no_wx segs -> LOK segs mo -> BINV mo g -> LSCPS2 PA PB ms mo g) -> LSCPS2 PA PB ms mo g.
Proof.
  intros PA PB ms mo g H mr mat HI.
  apply (H (LINV_no_wx _ _ _ _ _ _ HI) (LINV_LOK _ _ _ _ _ _ HI) (LINV_BINV _ _ _ _ _ _ HI) mr mat HI).
Qed.

(* [comment removed for export] *)
Lemma lscps2_evt_then : forall (Q : machine_state -> Prop) (PA PB : machine_state -> Model -> lghost -> Prop) ms mo g,
  evt segs Q ms -> (forall ms', Q ms' -> LSCPS2 PA PB ms' mo g) -> LSCPS2 PA PB ms mo g.
Proof.
  intros Q PA PB ms mo g He K. eapply lscps_lscps2; [apply lscps_evt; exact He|].
  cbv beta. intros ms' mo' g' (HQ & -> & ->). apply K. exact HQ.
Qed.

(* [comment removed for export] *)
Lemma lscps2_frame_post : forall (PA PB : machine_state -> Model -> lghost -> Prop) ms mo g,
  LSCPS2 PA PB ms mo g ->
  LSCPS2 (fun ms' mo' g' => PA ms' mo' g' /\ vm_only mo mo' /\ LOK segs mo' /\ BINV mo' g')
         (fun ms' mo' g' => PB ms' mo' g' /\ vm_only mo mo' /\ LOK segs mo' /\ BINV mo' g') ms mo g.
Proof.
  intros PA PB ms mo g H mr mat HI TA TB KA KB. apply (H mr mat HI).
  - intros ms' mo' g' mr' mat' HP HI' HV. eapply KA; [| exact HI'| exact HV].
    split; [exact HP|]. split; [exact HV|]. split; [eapply LINV_LOK; exact HI'| eapply LINV_BINV; exact HI'].
  - intros ms' mo' g' mr' mat' HP HI' HV. eapply KB; [| exact HI'| exact HV].
    split; [exact HP|]. split; [exact HV|]. split; [eapply LINV_LOK; exact HI'| eapply LINV_BINV; exact HI'].
Qed.

(* [comment removed for export] *)
Lemma lrz_lscps2 : forall (PA PB : machine_state -> Model -> lghost -> Prop) ms mo g TA TB,
  LSCPS2 PA PB ms mo g ->
  (forall ms' mo' g', PA ms' mo' g' -> vm_only mo mo' -> LRZ ms' mo' g' TA) ->
  (forall ms' mo' g', PB ms' mo' g' -> vm_only mo mo' -> LRZ ms' mo' g' TB) ->
  LRZ ms mo g (t_alt2 TA TB).
Proof.
  intros PA PB ms mo g TA TB H KA KB mr mat HI. apply (H mr mat HI TA TB).
  - intros ms' mo' g' mr' mat' HP HI' HV. apply (KA _ _ _ HP HV _ _ HI').
  - intros ms' mo' g' mr' mat' HP HI' HV. apply (KB _ _ _ HP HV _ _ HI').
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition outcome_ok2 (PA PB : machine_state -> Model -> lghost -> Prop) (cls : word -> option bool)
    (ms : machine_state) (mo : Model) (mr : mem) (o : outcome SyscallEffect) : Prop :=
  exists eff mo' g' mv' mat',
    o = Ok eff (real mo' mat') [] /\
    syscall_effect_accesses eff = [] /\
    vm_only mo mo' /\
    LINV segs g' mo' mat' mv' (ms_mem (nret (msw ms mr) eff)) /\
    match cls (eff_ret eff) with
    | None => evt segs (jself segs) (msw (nret ms eff) mv')
    | Some true => LSCPS PA (msw (nret ms eff) mv') mo' g'
    | Some false => LSCPS PB (msw (nret ms eff) mv') mo' g'
    end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma srz_alt2_spin2 : forall c (I : Type) (nx : I -> config) (cls : I -> option bool) (TA TB : TSet) (ia ib : I),
  node_ok segs c I (fun _ => []) nx ->
  cls ia = Some true -> cls ib = Some false ->
  (forall i, cls i = None -> jspinning segs (nx i)) ->
  (forall i, cls i = Some true -> srealizes segs (nx i) TA) ->
  (forall i, cls i = Some false -> srealizes segs (nx i) (t_alt2 TA TB)) ->
  srealizes segs c (t_alt2 TA TB).
Proof.
  intros c I nx cls TA TB ia ib Hnode Hia Hib Hsp HA HB.
  assert (HA0 : TA []) by (eapply srealizes_nonempty; apply (HA ia Hia)).
  assert (HAB0 : t_alt2 TA TB []) by (eapply srealizes_nonempty; apply (HB ib Hib)).
  apply (srz_conseq segs c (t_alt (fun i : I => t_emit [] (match cls i with None => t_nil | Some true => TA | Some false => t_alt2 TA TB end)))).
  - apply (srz_node segs c I (fun _ => []) nx (fun i => match cls i with None => t_nil | Some true => TA | Some false => t_alt2 TA TB end) ia Hnode).
    intros i. destruct (cls i) as [[|]|] eqn:E.
    + apply HA. exact E.
    + apply HB. exact E.
    + apply srz_jspin. apply Hsp. exact E.
  - intro tr. split.
    + intros [i Hi]. destruct (cls i) as [[|]|].
      * left. exact (proj1 (t_emit_nil_eq TA HA0 tr) Hi).
      * exact (proj1 (t_emit_nil_eq (t_alt2 TA TB) HAB0 tr) Hi).
      * apply (t_emit_nil_eq t_nil eq_refl tr) in Hi. unfold t_nil in Hi. subst tr. left. exact HA0.
    + intros H. destruct H as [H|H].
      * exists ia. rewrite Hia. exact (proj2 (t_emit_nil_eq TA HA0 tr) H).
      * exists ib. rewrite Hib. apply (proj2 (t_emit_nil_eq (t_alt2 TA TB) HAB0 tr)). right. exact H.
Qed.

(* [comment removed for export] *)
Definition outcome_ok22 (PA PB : machine_state -> Model -> lghost -> Prop) (cls : word -> option bool)
    (ms : machine_state) (mo : Model) (mr : mem) (o : outcome SyscallEffect) : Prop :=
  exists eff mo' g' mv' mat',
    o = Ok eff (real mo' mat') [] /\
    syscall_effect_accesses eff = [] /\
    vm_only mo mo' /\
    LINV segs g' mo' mat' mv' (ms_mem (nret (msw ms mr) eff)) /\
    match cls (eff_ret eff) with
    | None => evt segs (jself segs) (msw (nret ms eff) mv')
    | Some true => LSCPS PA (msw (nret ms eff) mv') mo' g'
    | Some false => LSCPS2 PA PB (msw (nret ms eff) mv') mo' g'
    end.

(* [comment removed for export] *)
End WithSegs.
