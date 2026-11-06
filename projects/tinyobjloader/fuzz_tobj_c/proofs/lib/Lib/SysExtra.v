(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@Corelib.Init.Datatypes"; "nil"; "prod"; "list"; "length"; "option"; "Some"; "nat"; "bool"; "cons"; "true"; "S"; "pair"; "@Stdlib.ZArith.BinInt.Z"; "le"; "of_nat"; "add"; "sub"; "to_nat"; "lt"; "mul"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "in_arg"; "SyscallEffect"; "event"; "FdEntry"; "in_mem"; "read_bytes_map"; "FdChannel"; "IOV_MAX"; "MemCopy"; "TASK_SIZE"; "access_okb"; "fd_lookup"; "iovs_access_okb"; "iovs_total"; "m_fds"; "mkEffectU"; "@Corelib.Lists.ListDef"; "skipn"; "firstn"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "obj_lo_of"; "DList"; "cell"; "eval"; "ob_base"; "ob_cells"; "ob_dflt"; "obj_hi_of"; "obj_holds"; "odefault"; "rl"; "sobj"; "valuation"; "covered"; "rd_bytes"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysExtra.WZ"; "writev0_reads"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_read_byte"; "@LinuxProcessSemantics.LinuxProcessSem.Specs"; "syscall_spec"; "@Corelib.Init.Peano"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs"; "check_syscall"; "@LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude"; "check_result"; "check_ret_only_copyins"; "@LinuxProcessSemantics.LinuxProcessSem.Monad"; "Ok"; "outcome"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall"; "fd32"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "iov_desc_accesses"; "iovecs_at"; "iovecs_readable"; "is_ret_ci"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "syscall_spec_ns"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundW
  SymSoundF SymSoundR SymComplete SymCall SymEntail SymExit SymFrame SymBytes Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WZ.
  Variables (i : SyscallInput) (m : Model) (ch : word).
  Variables (iovs : list (word * word)).
  Hypothesis Hno : bv_unsigned (in_sysno i) = 66%Z.
  Hypothesis Hfd : ltac2:(tb__ "0|0|
S0SaS1eA1S26S29Vm;A1S47S1bVi;U0A2A1A2SbS1eS21Vch;A1A2A3").
  Hypothesis Hch : ch <> Z_to_bv 64 0.
  Hypothesis Hcnt : ltac2:(tb__ "0|2|
S0S19S5Q40M0S1bVi;U2A2A2S13S9S7S3G0A1M1G1A2Viovs;A2A1A3").
  Hypothesis Hcnt1 : ltac2:(tb__ "0|2|
S1S12Z1S13S9S7S3Q40A1M0G0A2Viovs;A2A1M1A2S12G1S22A2A2").
  Hypothesis Hiov : ltac2:(tb__ "0|0|
S49S1fVi;A1S1bVi;U1A2Viovs;A3").

  Hypothesis Hiovok : ltac2:(tb__ "0|1|
S0SdS25S1bVi;U1A2S18Z10S13S9S7S3Q40A1M0G0A2Viovs;A2A1A2A2SfA3").
  Hypothesis Hbok : iovs_access_okb iovs = true.
  Hypothesis Hzero : iovs_total iovs = 0.

  Definition writev0_reads : list (word * nat) := ltac2:(tb__ "0|1|
S48S1bVi;U1A2S9S7S3Q40A1M0G0A2Viovs;A2A2").

  Lemma iovecs_readable_nil : ltac2:(tb__ "0|1|
S8S7S3Q40A1M0G0A2A1S0S19S28R1A1Z0A3S4aS1fVi;A1R2S6S3Q8A1A1A3F_;Fl;").
  Proof using iovs.
    induction l as [|[b len] r IH]; intros H; cbn; [reflexivity|].
    cbn [iovs_total] in H. pose proof (iovs_total_nonneg r). pose proof (bv_unsigned_in_range 64 len).
    assert (Hl : bv_unsigned len = 0) by lia.
    exists [], []. split; [|split; [apply IH; lia | reflexivity]].
    rewrite read_bytes_map_eq; unfold word_to_nat. rewrite Hl. reflexivity.
  Qed.

  Lemma writev0_check : ltac2:(tb__ "0|0|
S1cS0S43S42Vi;R1Vm;A3S44S3dR1S4Q40Z0A2Vm;S6S1dA1A5A3Feff;").
  Proof using Hch Hcnt Hcnt1 Hfd Hiov Hiovok Hbok Hno Hzero.
    intros eff. dispatch Hno. unfold check_writev. rewrite Hfd.
    destruct (w_is0 ch) eqn:E; [apply w_is0_spec in E; contradiction|].
    destruct (@writev_import i iovs [] Hcnt Hcnt1 Hiov Hiovok Hbok) as [Hi1 Hi2]. rewrite Hi1, Hi2.
    cbv zeta. rewrite iovs_total_cap, Hzero. cbn [Z.min Z.eqb]. reflexivity.
  Qed.

  Lemma writev0_inv : ltac2:(tb__ "0|0|
S46S1cA1S40Vi;Vm;R1A3S4bR2S4Q40Z0A2S3dVm;S6S1dA1A5F_;FR;").
  Proof using Hch Hcnt Hcnt1 Hfd Hiov Hiovok Hbok Hno Hzero. intros R. apply check_of_ret_only_copyins. exact writev0_check. Qed.

  Lemma writev0_intro_ss : ltac2:(tb__ "0|3|
S40Vi;Vm;S45S1cS2aS4Q40M0Z0A2S6S7S3G0A1M1S8S3Q8A1A1A2A1S6S7G1G1A2A1M2G2S6S23A1S3dA6Vm;S6S1dA1A4A3").
  Proof using Hch Hcnt Hcnt1 Hfd Hiov Hiovok Hbok Hno Hzero. apply intro_ret_only_copyins. exact writev0_check. Qed.

  Lemma writev0_intro : ltac2:(tb__ "0|3|
S4cVi;Vm;S45S1cS2aS4Q40M0Z0A2S6S7S3G0A1M1S8S3Q8A1A1A2A1S6S7G1G1A2A1M2G2S6S23A1S3dA6Vm;S6S1dA1A4A3").
  Proof using Hch Hcnt Hcnt1 Hfd Hiov Hiovok Hbok Hno Hzero.
    intros. split; [eapply writev0_intro_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. ns_auto.
  Qed.
End WZ.

Section Step.
  Variable segs : list Segment.

  Lemma writev01_iovecs_at : forall ms b,
    read_u64 (ms_read_byte ms) (ms_gpr ms 1) = Some b ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1 + 8)%bv = Some (Z_to_bv 64 0) ->
    iovecs_at (ms_read_byte ms) (ms_gpr ms 1) [(b, Z_to_bv 64 0)].
  Proof using .
    intros ms b H1 H2. cbn. split; [|split; [reflexivity|exact I]].
    unfold read_iovec_entry. rewrite H1, H2. reflexivity.
  Qed.

  Lemma writev01_bok : ltac2:(tb__ "0|3|
S3Q40M0A1M1S12S5G0R1A2S24A2S0SdS27SeS7G1G1A2M2S11G1G1R2S4G0Z0A2A4S6G2A1A3A1SfA3F_;Fb;").
  Proof using .
    intros b Hb. unfold iovs_access_okb. cbn [forallb fst snd].
    rewrite (access_okb_intro b (Z_to_bv 64 0)) by (rewrite bv_unsigned_Z_to_bv_0 || (change (bv_unsigned (Z_to_bv 64 0)) with 0%Z); lia).
    reflexivity.
  Qed.

  Lemma wstep_writev01_inv : forall tr ms m x8 ch b w',
    ms_svc_pending ms = Some x8 -> model_idle m ->
    bv_unsigned x8 = 66%Z ->
    fd_lookup (m_fds m) (fd32 (ms_gpr ms 0)) = Some (FdChannel ch) ->
    ch <> Z_to_bv 64 0 ->
    ms_gpr ms 2 = Z_to_bv 64 1 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1) = Some b ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1 + 8)%bv = Some (Z_to_bv 64 0) ->
    (bv_unsigned (ms_gpr ms 1) + 16 <= TASK_SIZE)%Z ->
    (bv_unsigned b <= TASK_SIZE)%Z ->
    wstep segs (tr, mkCfg ms m) w' ->
    w' = (tr, mkCfg (after_sys ms (Z_to_bv 64 0)) m).
  Proof using .
    intros tr ms m x8 ch b w' Hp Hi Hno Hfd Hch Hcnt H1 H2 Hiok Hbok Hw.
    refine (@wstep_retci_inv0 segs _ _ _ _ _ _ _ _ Hp (model_idle_halted Hi) _ Hi Hw).
    intros R. apply (@writev0_inv (sys_input segs ms x8) m ch [(b, Z_to_bv 64 0)] Hno Hfd Hch);
      [cbn; rewrite Hcnt; reflexivity | cbn; unfold IOV_MAX; lia | apply writev01_iovecs_at; assumption | apply access_okb_of_le; autorewrite with sys_input; cbn [length]; lia | apply writev01_bok; exact Hbok | reflexivity].
  Qed.

  Lemma wstep_writev01_intro : forall tr ms m x8 ch b,
    ms_svc_pending ms = Some x8 -> model_idle m ->
    bv_unsigned x8 = 66%Z ->
    fd_lookup (m_fds m) (fd32 (ms_gpr ms 0)) = Some (FdChannel ch) ->
    ch <> Z_to_bv 64 0 ->
    ms_gpr ms 2 = Z_to_bv 64 1 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1) = Some b ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1 + 8)%bv = Some (Z_to_bv 64 0) ->
    (bv_unsigned (ms_gpr ms 1) + 16 <= TASK_SIZE)%Z ->
    (bv_unsigned b <= TASK_SIZE)%Z ->
    wstep segs (tr, mkCfg ms m) (tr, mkCfg (after_sys ms (Z_to_bv 64 0)) m).
  Proof using .
    intros tr ms m x8 ch b Hp Hi Hno Hfd Hch Hcnt H1 H2 Hiok Hbok.
    refine (@wstep_retci_intro0 segs tr _ _ _ _ _ _ Hp (model_idle_halted Hi) _ Hi).
    apply (@writev0_intro (sys_input segs ms x8) m ch [(b, Z_to_bv 64 0)] Hno Hfd Hch);
      [cbn; rewrite Hcnt; reflexivity | cbn; unfold IOV_MAX; lia | apply writev01_iovecs_at; assumption | apply access_okb_of_le; autorewrite with sys_input; cbn [length]; lia | apply writev01_bok; exact Hbok | reflexivity].
  Qed.

  Lemma writev01_only_ok : forall ms m x8 ch b,
    model_idle m ->
    bv_unsigned x8 = 66%Z ->
    fd_lookup (m_fds m) (fd32 (ms_gpr ms 0)) = Some (FdChannel ch) ->
    ch <> Z_to_bv 64 0 ->
    ms_gpr ms 2 = Z_to_bv 64 1 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1) = Some b ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1 + 8)%bv = Some (Z_to_bv 64 0) ->
    (bv_unsigned (ms_gpr ms 1) + 16 <= TASK_SIZE)%Z ->
    (bv_unsigned b <= TASK_SIZE)%Z ->
    only_ok (sys_input segs ms x8) m.
  Proof using .
    intros ms m x8 ch b Hi Hno Hfd Hch Hcnt H1 H2 Hiok Hbok.
    eapply only_ok_retci; [|exact Hi].
    intros R. apply (@writev0_inv (sys_input segs ms x8) m ch [(b, Z_to_bv 64 0)] Hno Hfd Hch);
      [cbn; rewrite Hcnt; reflexivity | cbn; unfold IOV_MAX; lia | apply writev01_iovecs_at; assumption | apply access_okb_of_le; autorewrite with sys_input; cbn [length]; lia | apply writev01_bok; exact Hbok | reflexivity].
  Qed.
End Step.

Section WithSegs.
Variable segs : list Segment.

Lemma nth_skipn_cons : ltac2:(tb__ "0|2|
S8S3Q8A1M0A1M1ScG0S41R2S9G0R3A2A2S0G1SeG0S2dG0R3R4R2A4S2bG0S10R3A1R4A3A3S2bG0R3R4A3A3F_;Fd;Fi;FL;").
Proof using .
  induction L as [|x L IH]; intros i d Hlt; [cbn in Hlt; lia|].
  destruct i; [reflexivity|]. cbn. apply IH. cbn in Hlt. lia.
Qed.

Lemma list_obj_rd_bytes : ltac2:(tb__ "0|3|
S3aS3eS39S1aScS19S36Vsegs;R6R5R4A4S0S37S34R5A1S2fR4A1A3S19S1S12R4R1A2S17R1S14R4S13R5A1A2A2A2S2S3bRaS33R8A1R2A3A1F_;Fq;S12S2eR9R7A2R4A2S12S14R5S13R6A1A2S35RaR8A2A2S0SaS8S3Q8A1M0A1M1A1S3cRaS4Q40M2S14S5G2S31RbS32R9A1A2A2R6A2A2R7A3SbG1S2cG0R7S2bG0S16S15R6S2eRbR9A2A2A1S38RbR8A2A3A3A2A3F_;F_;F_;F_;F_;Foff;Fn;Fl;Fo;Fms;Frho;").
Proof using .
  intros rho ms o l n. induction n as [|n IH]; intros off Ho Hd Hnc Hlo Hhi.
  - reflexivity.
  - cbn [rd_bytes]. pose proof Ho as (Hbnd & _ & _ & Hdf & Hinv).
    rewrite Hd in Hdf, Hinv. cbn [dflt_holds dflt_inv] in Hdf, Hinv.
    rewrite (Hdf off ltac:(lia) (Hnc off ltac:(lia))).
    replace (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + off) + 1)%bv
      with (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + (off + 1))).
    2:{ apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
        change (bv_unsigned (1%bv : bv 64)) with 1. rewrite Zplus_mod_idemp_l. f_equal. lia. }
    rewrite (IH (off + 1) Ho Hd ltac:(intros q Hq; apply Hnc; lia) ltac:(lia) ltac:(lia)).
    f_equal.
    replace (Z.to_nat (off + 1 - obj_lo_of rho o)) with (S (Z.to_nat (off - obj_lo_of rho o))) by lia.
    rewrite <- (firstn_cons n). f_equal.
    destruct (Nat.lt_ge_cases (Z.to_nat (off - obj_lo_of rho o)) (length (rl rho l))) as [Hlt|Hge].
    + apply nth_skipn_cons. exact Hlt.
    + exfalso. lia.
Qed.

Lemma list_obj_read_bytes_map : ltac2:(tb__ "0|5|
S3aS3eS39S1aScS19S3Q40M0A1M1G1S36Vsegs;R8R7R6A4S0S37S34R7A1S2fR6A1A3S0S8S30A1S33R8A1S6S30A1A3S12S2eRbR9A2R6A2S12S14R7S13R8A1A2S35RcRaA2A2S0S19S5G0R7A2M2S14S5G0S31RdS32RbA1A2A2R8A2A3S0S19G2S13RaA1A3S0SaS8S3Q8A1M3A1M4A1S20S3fReA1R9R8A3SbG4S2cG3RbS2bG3S16S15RaS2eRfRdA2A2A1S38RfRcA2A3A3A2A3F_;F_;F_;F_;F_;F_;F_;Flen;Fa;Foff;Fn;Fl;Fo;Fms;Frho;").
Proof using .
  intros rho ms o l n off a len Ho Hd Hc Hlo Hhi Ha Hlen.
  rewrite read_bytes_map_eq; unfold word_to_nat. rewrite rd_bytes_read_aux, Hlen, Nat2Z.id.
  replace a with (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + off)) by (rewrite <- Ha; apply Z_to_bv_bv_unsigned).
  apply list_obj_rd_bytes; auto. intros q _ HC. rewrite Hc in HC. inversion HC.
Qed.

Lemma read_bytes_map_nil : ltac2:(tb__ "0|4|
S3Q40M0A1M1SaS3Q8A1M2A1F_;G1S0SaS8G2A1M3A1S20R2R1S4G0Z0A2A3SbG3S6G2A1A2A3Fa;Fmp;").
Proof using . intros. reflexivity. Qed.

Lemma triple1_writev2J : forall (ok : world -> Prop) (J J' : jpred) S rho ch bs1 bs2 e,
  ok_frameJ segs ok J -> ok_pframeJ segs ok J ->
  instr_at segs (ss_pc S) = Some Ecall ->
  reg_sv S 17 = SLit 66 -> reg_sv S 10 = SLit ch -> reg_sv S 12 = SLit 2 ->
  0 < ch < 2 ^ 32 -> (1 <= Z.of_nat (length (bs1 ++ bs2)) <= MAX_RW_COUNT)%Z ->
  sv_below (ss_next S) e = true ->
  (forall rho' tr md k, agree_below (ss_next S) rho rho' ->
     rw rho' (ss_next S) = Z_to_bv 64 (Z.of_nat k) ->
     J rho tr md -> (1 <= k <= length (bs1 ++ bs2))%nat ->
     fd_lookup (m_fds md) (Z_to_bv 64 ch) = Some (FdChannel (Z_to_bv 64 ch))
     /\ J' rho' (tr ++ map (WriteEv (Z_to_bv 64 ch)) (firstn k (bs1 ++ bs2))) md) ->
  (forall tr ms md, smatch_pending segs rho S (tr, mkCfg ms md) -> J rho tr md ->
     exists b1 l1 b2 l2,
       read_u64 (ms_read_byte ms) (eval rho (reg_sv S 11)) = Some b1
       /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv S 11) + 8)%bv = Some l1
       /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv S 11) + 16)%bv = Some b2
       /\ read_u64 (ms_read_byte ms) ((eval rho (reg_sv S 11) + 16) + 8)%bv = Some l2
       /\ read_bytes_map (ms_read_byte ms) b1 l1 = Some bs1
       /\ read_bytes_map (ms_read_byte ms) b2 l2 = Some bs2
       /\ bv_unsigned (eval rho e) = Z.of_nat (length (bs1 ++ bs2))
       /\ (bv_unsigned (eval rho (reg_sv S 11)) + 32 <= TASK_SIZE)%Z
       /\ (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z
       /\ (bv_unsigned b2 + bv_unsigned l2 <= TASK_SIZE)%Z) ->
  triple1 segs ok (SPJ segs J S rho)
    (fun w => exists rho', agree_below (ss_next S) rho rho' /\ SPJ segs J' (S_after_write S e) rho' w).
Proof using .
  intros ok J J' S rho ch bs1 bs2 e Hokf Hokp Hi H17 H10 H12 Hch Hlen He HK Hbs.
  apply triple1_ecall_detJ; [exact Hokf | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pending_swf segs _ _ _ _ _ Hsp) as Hwf.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 0 Hsp ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite H10 in G0. cbn [eval] in G0.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 1 Hsp ltac:(lia)) as G1. change (10 + Z.of_nat 1) with 11 in G1.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 2 Hsp ltac:(lia)) as G2. change (10 + Z.of_nat 2) with 12 in G2. rewrite H12 in G2. cbn [eval] in G2.
  destruct (Hbs tr ms md Hsp Hk) as (b1 & l1 & b2 & l2 & R1 & R2 & R3 & R4 & B1 & B2 & Hev & T0 & T1 & T2).
  rewrite <- G1 in R1, R2, R3, R4, T0.
  assert (Hag1 : agree_below (ss_next S) rho (rho_set_rw rho (ss_next S) (Z_to_bv 64 (Z.of_nat 1)))) by (apply agree_below_set_rw; lia).
  destruct (HK _ tr md 1%nat Hag1 (rho_set_rw_at _ _ _) Hk ltac:(lia)) as [Hlk _].
  assert (H66 : bv_unsigned (Z_to_bv 64 66) = 66%Z) by reflexivity.
  assert (Hfd' : fd_lookup (m_fds md) (fd32 (ms_gpr ms 0)) = Some (FdChannel (Z_to_bv 64 ch))).
  { rewrite G0, fd32_lit by lia. exact Hlk. }
  assert (Hch0 : Z_to_bv 64 ch <> Z_to_bv 64 0) by (apply Z_to_bv64_neq; lia).
  split.
  - eapply Hokp; [exact Hk | exact Hp |].
    eapply writev2_only_ok; [exact Hh | exact H66 | exact Hfd' | exact Hch0 | exact G2 | exact R1 | exact R2 | exact R3 | exact R4 | exact B1 | exact B2 | exact T0 | exact T1 | exact T2 | exact Hlen].
  - intros w' Hw.
    destruct (wstep_writev2_inv Hp Hh H66 Hfd' Hch0 G2 R1 R2 R3 R4 B1 B2 T0 T1 T2 Hlen Hw) as (k & Hk1 & ->).
    assert (Hag : agree_below (ss_next S) rho (rho_set_rw rho (ss_next S) (Z_to_bv 64 (Z.of_nat k)))) by (apply agree_below_set_rw; lia).
    exists (rho_set_rw rho (ss_next S) (Z_to_bv 64 (Z.of_nat k))). split; [exact Hag|].
    split; [|exact (proj2 (HK _ tr md k Hag (rho_set_rw_at _ _ _) Hk Hk1))].
    eapply smatch_after_write; [exact Hsp | exact He | exact Hev | lia].
Qed.

Lemma etriple_writev2J : forall (J J' : jpred) S rho ch bs1 bs2 e,
  instr_at segs (ss_pc S) = Some Ecall ->
  reg_sv S 17 = SLit 66 -> reg_sv S 10 = SLit ch -> reg_sv S 12 = SLit 2 ->
  0 < ch < 2 ^ 32 -> (1 <= Z.of_nat (length (bs1 ++ bs2)) <= MAX_RW_COUNT)%Z ->
  sv_below (ss_next S) e = true ->
  (forall rho' tr md k, agree_below (ss_next S) rho rho' ->
     rw rho' (ss_next S) = Z_to_bv 64 (Z.of_nat k) ->
     J rho tr md -> (1 <= k <= length (bs1 ++ bs2))%nat ->
     fd_lookup (m_fds md) (Z_to_bv 64 ch) = Some (FdChannel (Z_to_bv 64 ch))
     /\ J' rho' (tr ++ map (WriteEv (Z_to_bv 64 ch)) (firstn k (bs1 ++ bs2))) md) ->
  (forall tr ms md, smatch_pending segs rho S (tr, mkCfg ms md) -> J rho tr md ->
     exists b1 l1 b2 l2,
       read_u64 (ms_read_byte ms) (eval rho (reg_sv S 11)) = Some b1
       /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv S 11) + 8)%bv = Some l1
       /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv S 11) + 16)%bv = Some b2
       /\ read_u64 (ms_read_byte ms) ((eval rho (reg_sv S 11) + 16) + 8)%bv = Some l2
       /\ read_bytes_map (ms_read_byte ms) b1 l1 = Some bs1
       /\ read_bytes_map (ms_read_byte ms) b2 l2 = Some bs2
       /\ bv_unsigned (eval rho e) = Z.of_nat (length (bs1 ++ bs2))
       /\ (bv_unsigned (eval rho (reg_sv S 11)) + 32 <= TASK_SIZE)%Z
       /\ (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z
       /\ (bv_unsigned b2 + bv_unsigned l2 <= TASK_SIZE)%Z) ->
  etriple segs (SPJ segs J S rho)
    (fun w => exists rho', agree_below (ss_next S) rho rho'
              /\ rw rho' (ss_next S) = Z_to_bv 64 (Z.of_nat (length (bs1 ++ bs2)))
              /\ SPJ segs J' (S_after_write S e) rho' w).
Proof using .
  intros J J' S rho ch bs1 bs2 e Hi H17 H10 H12 Hch Hlen He HK Hbs.
  apply etriple_ecall_detJ; [exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pending_swf segs _ _ _ _ _ Hsp) as Hwf.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 0 Hsp ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite H10 in G0. cbn [eval] in G0.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 1 Hsp ltac:(lia)) as G1. change (10 + Z.of_nat 1) with 11 in G1.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 2 Hsp ltac:(lia)) as G2. change (10 + Z.of_nat 2) with 12 in G2. rewrite H12 in G2. cbn [eval] in G2.
  destruct (Hbs tr ms md Hsp Hk) as (b1 & l1 & b2 & l2 & R1 & R2 & R3 & R4 & B1 & B2 & Hev & T0 & T1 & T2).
  rewrite <- G1 in R1, R2, R3, R4, T0.
  set (n := length (bs1 ++ bs2)).
  assert (Hag : agree_below (ss_next S) rho (rho_set_rw rho (ss_next S) (Z_to_bv 64 (Z.of_nat n)))) by (apply agree_below_set_rw; lia).
  destruct (HK _ tr md n Hag (rho_set_rw_at _ _ _) Hk ltac:(lia)) as [Hlk Hk'].
  assert (H66 : bv_unsigned (Z_to_bv 64 66) = 66%Z) by reflexivity.
  assert (Hfd' : fd_lookup (m_fds md) (fd32 (ms_gpr ms 0)) = Some (FdChannel (Z_to_bv 64 ch))).
  { rewrite G0, fd32_lit by lia. exact Hlk. }
  assert (Hch0 : Z_to_bv 64 ch <> Z_to_bv 64 0) by (apply Z_to_bv64_neq; lia).
  eexists. split.
  { exact (@wstep_writev2_intro_prefix segs tr ms md _ _ _ _ _ _ _ _ n Hp Hh H66 Hfd' Hch0 G2 R1 R2 R3 R4 B1 B2 T0 T1 T2 Hlen ltac:(lia)). }
  exists (rho_set_rw rho (ss_next S) (Z_to_bv 64 (Z.of_nat n))). split; [exact Hag|].
  split; [apply rho_set_rw_at|].
  split; [|exact Hk'].
  eapply smatch_after_write; [exact Hsp | exact He | exact Hev | lia].
Qed.

Lemma triple1_writev1J : forall (ok : world -> Prop) (J J' : jpred) S rho ch bs1 e,
  ok_frameJ segs ok J -> ok_pframeJ segs ok J ->
  instr_at segs (ss_pc S) = Some Ecall ->
  reg_sv S 17 = SLit 66 -> reg_sv S 10 = SLit ch -> reg_sv S 12 = SLit 1 ->
  0 < ch < 2 ^ 32 -> (1 <= Z.of_nat (length bs1) <= MAX_RW_COUNT)%Z ->
  sv_below (ss_next S) e = true ->
  (forall rho' tr md k, agree_below (ss_next S) rho rho' ->
     rw rho' (ss_next S) = Z_to_bv 64 (Z.of_nat k) ->
     J rho tr md -> (1 <= k <= length bs1)%nat ->
     fd_lookup (m_fds md) (Z_to_bv 64 ch) = Some (FdChannel (Z_to_bv 64 ch))
     /\ J' rho' (tr ++ map (WriteEv (Z_to_bv 64 ch)) (firstn k bs1)) md) ->
  (forall tr ms md, smatch_pending segs rho S (tr, mkCfg ms md) -> J rho tr md ->
     exists b1 l1,
       read_u64 (ms_read_byte ms) (eval rho (reg_sv S 11)) = Some b1
       /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv S 11) + 8)%bv = Some l1
       /\ read_bytes_map (ms_read_byte ms) b1 l1 = Some bs1
       /\ bv_unsigned (eval rho e) = Z.of_nat (length bs1)
       /\ (bv_unsigned (eval rho (reg_sv S 11)) + 16 <= TASK_SIZE)%Z
       /\ (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z) ->
  triple1 segs ok (SPJ segs J S rho)
    (fun w => exists rho', agree_below (ss_next S) rho rho' /\ SPJ segs J' (S_after_write S e) rho' w).
Proof using .
  intros ok J J' S rho ch bs1 e Hokf Hokp Hi H17 H10 H12 Hch Hlen He HK Hbs.
  apply triple1_ecall_detJ; [exact Hokf | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pending_swf segs _ _ _ _ _ Hsp) as Hwf.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 0 Hsp ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite H10 in G0. cbn [eval] in G0.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 1 Hsp ltac:(lia)) as G1. change (10 + Z.of_nat 1) with 11 in G1.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 2 Hsp ltac:(lia)) as G2. change (10 + Z.of_nat 2) with 12 in G2. rewrite H12 in G2. cbn [eval] in G2.
  destruct (Hbs tr ms md Hsp Hk) as (b1 & l1 & R1 & R2 & B1 & Hev & T0 & T1).
  rewrite <- G1 in R1, R2, T0.
  assert (Hag1 : agree_below (ss_next S) rho (rho_set_rw rho (ss_next S) (Z_to_bv 64 (Z.of_nat 1)))) by (apply agree_below_set_rw; lia).
  destruct (HK _ tr md 1%nat Hag1 (rho_set_rw_at _ _ _) Hk ltac:(lia)) as [Hlk _].
  assert (H66 : bv_unsigned (Z_to_bv 64 66) = 66%Z) by reflexivity.
  assert (Hfd' : fd_lookup (m_fds md) (fd32 (ms_gpr ms 0)) = Some (FdChannel (Z_to_bv 64 ch))).
  { rewrite G0, fd32_lit by lia. exact Hlk. }
  assert (Hch0 : Z_to_bv 64 ch <> Z_to_bv 64 0) by (apply Z_to_bv64_neq; lia).
  split.
  - eapply Hokp; [exact Hk | exact Hp |].
    eapply writev1_only_ok; [exact Hh | exact H66 | exact Hfd' | exact Hch0 | exact G2 | exact R1 | exact R2 | exact B1 | exact T0 | exact T1 | exact Hlen].
  - intros w' Hw.
    destruct (wstep_writev1_inv Hp Hh H66 Hfd' Hch0 G2 R1 R2 B1 T0 T1 Hlen Hw) as (k & Hk1 & ->).
    assert (Hag : agree_below (ss_next S) rho (rho_set_rw rho (ss_next S) (Z_to_bv 64 (Z.of_nat k)))) by (apply agree_below_set_rw; lia).
    exists (rho_set_rw rho (ss_next S) (Z_to_bv 64 (Z.of_nat k))). split; [exact Hag|].
    split; [|exact (proj2 (HK _ tr md k Hag (rho_set_rw_at _ _ _) Hk Hk1))].
    eapply smatch_after_write; [exact Hsp | exact He | exact Hev | lia].
Qed.

Lemma etriple_writev1J : forall (J J' : jpred) S rho ch bs1 e,
  instr_at segs (ss_pc S) = Some Ecall ->
  reg_sv S 17 = SLit 66 -> reg_sv S 10 = SLit ch -> reg_sv S 12 = SLit 1 ->
  0 < ch < 2 ^ 32 -> (1 <= Z.of_nat (length bs1) <= MAX_RW_COUNT)%Z ->
  sv_below (ss_next S) e = true ->
  (forall rho' tr md k, agree_below (ss_next S) rho rho' ->
     rw rho' (ss_next S) = Z_to_bv 64 (Z.of_nat k) ->
     J rho tr md -> (1 <= k <= length bs1)%nat ->
     fd_lookup (m_fds md) (Z_to_bv 64 ch) = Some (FdChannel (Z_to_bv 64 ch))
     /\ J' rho' (tr ++ map (WriteEv (Z_to_bv 64 ch)) (firstn k bs1)) md) ->
  (forall tr ms md, smatch_pending segs rho S (tr, mkCfg ms md) -> J rho tr md ->
     exists b1 l1,
       read_u64 (ms_read_byte ms) (eval rho (reg_sv S 11)) = Some b1
       /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv S 11) + 8)%bv = Some l1
       /\ read_bytes_map (ms_read_byte ms) b1 l1 = Some bs1
       /\ bv_unsigned (eval rho e) = Z.of_nat (length bs1)
       /\ (bv_unsigned (eval rho (reg_sv S 11)) + 16 <= TASK_SIZE)%Z
       /\ (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z) ->
  etriple segs (SPJ segs J S rho)
    (fun w => exists rho', agree_below (ss_next S) rho rho'
              /\ rw rho' (ss_next S) = Z_to_bv 64 (Z.of_nat (length bs1))
              /\ SPJ segs J' (S_after_write S e) rho' w).
Proof using .
  intros J J' S rho ch bs1 e Hi H17 H10 H12 Hch Hlen He HK Hbs.
  apply etriple_ecall_detJ; [exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pending_swf segs _ _ _ _ _ Hsp) as Hwf.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 0 Hsp ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite H10 in G0. cbn [eval] in G0.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 1 Hsp ltac:(lia)) as G1. change (10 + Z.of_nat 1) with 11 in G1.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 2 Hsp ltac:(lia)) as G2. change (10 + Z.of_nat 2) with 12 in G2. rewrite H12 in G2. cbn [eval] in G2.
  destruct (Hbs tr ms md Hsp Hk) as (b1 & l1 & R1 & R2 & B1 & Hev & T0 & T1).
  rewrite <- G1 in R1, R2, T0.
  set (n := length bs1).
  assert (Hag : agree_below (ss_next S) rho (rho_set_rw rho (ss_next S) (Z_to_bv 64 (Z.of_nat n)))) by (apply agree_below_set_rw; lia).
  destruct (HK _ tr md n Hag (rho_set_rw_at _ _ _) Hk ltac:(lia)) as [Hlk Hk'].
  assert (H66 : bv_unsigned (Z_to_bv 64 66) = 66%Z) by reflexivity.
  assert (Hfd' : fd_lookup (m_fds md) (fd32 (ms_gpr ms 0)) = Some (FdChannel (Z_to_bv 64 ch))).
  { rewrite G0, fd32_lit by lia. exact Hlk. }
  assert (Hch0 : Z_to_bv 64 ch <> Z_to_bv 64 0) by (apply Z_to_bv64_neq; lia).
  eexists. split.
  { exact (@wstep_writev1_intro_prefix segs tr ms md _ _ _ _ _ n Hp Hh H66 Hfd' Hch0 G2 R1 R2 B1 T0 T1 Hlen ltac:(lia)). }
  exists (rho_set_rw rho (ss_next S) (Z_to_bv 64 (Z.of_nat n))). split; [exact Hag|].
  split; [apply rho_set_rw_at|].
  split; [|exact Hk'].
  eapply smatch_after_write; [exact Hsp | exact He | exact Hev | lia].
Qed.

Lemma triple1_writev01J : forall (ok : world -> Prop) (J : jpred) S rho ch,
  ok_frameJ segs ok J -> ok_pframeJ segs ok J ->
  instr_at segs (ss_pc S) = Some Ecall ->
  reg_sv S 17 = SLit 66 -> reg_sv S 10 = SLit ch -> reg_sv S 12 = SLit 1 ->
  0 < ch < 2 ^ 32 ->
  (forall rho tr md, J rho tr md -> fd_lookup (m_fds md) (Z_to_bv 64 ch) = Some (FdChannel (Z_to_bv 64 ch))) ->
  (forall tr ms md, smatch_pending segs rho S (tr, mkCfg ms md) -> J rho tr md ->
     exists b, read_u64 (ms_read_byte ms) (eval rho (reg_sv S 11)) = Some b
          /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv S 11) + 8)%bv = Some (Z_to_bv 64 0)
          /\ (bv_unsigned (eval rho (reg_sv S 11)) + 16 <= TASK_SIZE)%Z
          /\ (bv_unsigned b <= TASK_SIZE)%Z) ->
  triple1 segs ok (SPJ segs J S rho) (SPJ segs J (S_after S (SLit 0) (ss_objs S) (ss_next S)) rho).
Proof using .
  intros ok J S rho ch Hokf Hokp Hi H17 H10 H12 Hch HJ Hrd.
  apply triple1_ecall_detJ; [exact Hokf | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 0 Hsp ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite H10 in G0. cbn [eval] in G0.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 1 Hsp ltac:(lia)) as G1. change (10 + Z.of_nat 1) with 11 in G1.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 2 Hsp ltac:(lia)) as G2. change (10 + Z.of_nat 2) with 12 in G2. rewrite H12 in G2. cbn [eval] in G2.
  destruct (Hrd tr ms md Hsp Hk) as (b & R1 & R2 & T0 & T1). rewrite <- G1 in R1, R2, T0.
  assert (H66 : bv_unsigned (Z_to_bv 64 66) = 66%Z) by reflexivity.
  assert (Hfd' : fd_lookup (m_fds md) (fd32 (ms_gpr ms 0)) = Some (FdChannel (Z_to_bv 64 ch))).
  { rewrite G0, fd32_lit by lia. exact (HJ rho tr md Hk). }
  assert (Hch0 : Z_to_bv 64 ch <> Z_to_bv 64 0) by (apply Z_to_bv64_neq; lia).
  split.
  - eapply Hokp; [exact Hk | exact Hp |]. eapply writev01_only_ok; [exact Hh | exact H66 | exact Hfd' | exact Hch0 | exact G2 | exact R1 | exact R2 | exact T0 | exact T1].
  - intros w' Hw. rewrite (wstep_writev01_inv segs tr ms md _ _ b w' Hp Hh H66 Hfd' Hch0 G2 R1 R2 T0 T1 Hw).
    split; [|exact Hk]. change (SLit 0) with (SLit (bv_unsigned (Z_to_bv 64 0))).
    eapply smatch_after_ret_lit; [exact Hsp | exact Hh].
Qed.

Lemma etriple_writev01J : forall (J : jpred) S rho ch,
  instr_at segs (ss_pc S) = Some Ecall ->
  reg_sv S 17 = SLit 66 -> reg_sv S 10 = SLit ch -> reg_sv S 12 = SLit 1 ->
  0 < ch < 2 ^ 32 ->
  (forall rho tr md, J rho tr md -> fd_lookup (m_fds md) (Z_to_bv 64 ch) = Some (FdChannel (Z_to_bv 64 ch))) ->
  (forall tr ms md, smatch_pending segs rho S (tr, mkCfg ms md) -> J rho tr md ->
     exists b, read_u64 (ms_read_byte ms) (eval rho (reg_sv S 11)) = Some b
          /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv S 11) + 8)%bv = Some (Z_to_bv 64 0)
          /\ (bv_unsigned (eval rho (reg_sv S 11)) + 16 <= TASK_SIZE)%Z
          /\ (bv_unsigned b <= TASK_SIZE)%Z) ->
  etriple segs (SPJ segs J S rho) (SPJ segs J (S_after S (SLit 0) (ss_objs S) (ss_next S)) rho).
Proof using .
  intros J S rho ch Hi H17 H10 H12 Hch HJ Hrd.
  apply etriple_ecall_detJ; [exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 0 Hsp ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite H10 in G0. cbn [eval] in G0.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 1 Hsp ltac:(lia)) as G1. change (10 + Z.of_nat 1) with 11 in G1.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 2 Hsp ltac:(lia)) as G2. change (10 + Z.of_nat 2) with 12 in G2. rewrite H12 in G2. cbn [eval] in G2.
  destruct (Hrd tr ms md Hsp Hk) as (b & R1 & R2 & T0 & T1). rewrite <- G1 in R1, R2, T0.
  assert (H66 : bv_unsigned (Z_to_bv 64 66) = 66%Z) by reflexivity.
  assert (Hfd' : fd_lookup (m_fds md) (fd32 (ms_gpr ms 0)) = Some (FdChannel (Z_to_bv 64 ch))).
  { rewrite G0, fd32_lit by lia. exact (HJ rho tr md Hk). }
  assert (Hch0 : Z_to_bv 64 ch <> Z_to_bv 64 0) by (apply Z_to_bv64_neq; lia).
  eexists. split; [exact (wstep_writev01_intro segs tr ms md _ _ b Hp Hh H66 Hfd' Hch0 G2 R1 R2 T0 T1)|].
  split; [|exact Hk]. change (SLit 0) with (SLit (bv_unsigned (Z_to_bv 64 0))).
  eapply smatch_after_ret_lit; [exact Hsp | exact Hh].
Qed.

End WithSegs.
