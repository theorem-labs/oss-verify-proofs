(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "@Corelib.Init.Datatypes"; "bool"; "nil"; "list"; "prod"; "true"; "false"; "nat"; "cons"; "pair"; "andb"; "app"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "in_arg"; "SyscallEffect"; "MemCopy"; "event"; "mkEffectU"; "region_free"; "ENOMEM"; "errno_ret"; "alloc_top"; "m_vmmaps"; "page_size"; "vm_maps"; "vm_reserved"; "map_contains"; "VmMaps"; "with_vmmaps"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude"; "check_result"; "CheckReject"; "CheckOk"; "errno_ret_in"; "listNN_eqb"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.LinuxProcessSem.Monad"; "Ok"; "outcome"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_nZ"; "mmap_none_model"; "mmap_rw_model"; "is_ret"; "mmap_fixed_dead_model"; "@LinuxProcessSemantics.LinuxProcessSem.Specs"; "syscall_spec"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_fixed_noaccess_b"; "mmap_modeled_b"; "mmap_noaccess_b"; "mmap_fixed_rw_b"; "mmap_flags_core"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "mmap_errnos_when"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_noreserve_backed_ok"; "mmap_noreplace_noaccess_b"; "mmap_anon_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "mmap_fixed_fresh_refusable"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_noreplace_rw_b"; "mmap_off_aligned_b"; "mmap_fixed_rw_budget_ok"; "mmap_noreserve_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "mmap_fixed_commit_refusable"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "mmap_destructive_errnos"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_fixed_rw_next"; "mmap_noreplace_flags_b"; "with_mmap_replacement"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "modulo"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs"; "check_syscall"; "@LinuxProcessSemantics.Riscv.Prelude"; "bv_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysSpecStart"; "mmap_fixed_rw_ok_model"; "@LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mmap"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "w_nilb"; "@LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mmap"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall"; "w_is0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "syscall_spec_ns"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope bv_scope.

Lemma mmap_fixed_rw_b_intro : ltac2:(tb__ "0|2|
S1eQ40M0A1M1G1G1S0S26S1fG0R3A2Z3A3S0S26S33R3A1Z32A3S0G1R3S20G0Z0A2A3S1S0S3S32R6R5R4A3S7A3S1S0S3S30R6R5R4A3S8A3S1S0S3S31R6R5R4A3S8A3S0S3S2fR6R5R4A3S8A3A2A2A2F_;F_;F_;Foff;Fflags;Fprot;").
Proof.
  intros prot flags off Hp Hf ->.
  unfold mmap_fixed_rw_b, mmap_modeled_b, mmap_noaccess_b, mmap_fixed_noaccess_b.
  rewrite Hp, Hf. unfold PROT_READ, PROT_WRITE, PROT_NONE, MAP_PRIVATE, MAP_ANONYMOUS, MAP_FIXED. cbn.
  repeat split; reflexivity.
Qed.

Lemma mmap_fixed_none_b_intro : ltac2:(tb__ "0|3|
S1eQ40M0A1M1G1G1S0S26S1fG0R3A2Z0M2A3S0S26S33R3A1Z32A3S0G1R3S20G0G2A2A3S1S0S3S2fR6R5R4A3S7A3S1S0S3S30R6R5R4A3S8A3S0S3S31R6R5R4A3S8A3A2A2F_;F_;F_;Foff;Fflags;Fprot;").
Proof.
  intros prot flags off Hp Hf ->.
  unfold mmap_fixed_noaccess_b, mmap_modeled_b, mmap_noaccess_b.
  rewrite Hp, Hf. unfold PROT_READ, PROT_WRITE, PROT_NONE, MAP_PRIVATE, MAP_ANONYMOUS, MAP_FIXED. cbn.
  repeat split; reflexivity.
Qed.

Lemma mmap_flags_core_16434 : ltac2:(tb__ "0|1|
S1eQ40M0A1S0S26S1fG0R1A2Z4032A3S0S26S33R2A1Z32A3F_;Fflags;").
Proof. intros flags H. unfold mmap_flags_core. rewrite H. reflexivity. Qed.
Lemma mmap_noreserve_b_16434 : ltac2:(tb__ "0|1|
S1eQ40M0A1S0S26S1fG0R1A2Z4032A3S0S3S3cR2A1S7A3F_;Fflags;").
Proof. intros flags H. unfold mmap_noreserve_b. rewrite H. reflexivity. Qed.
Lemma mmap_flags_core_16418 : ltac2:(tb__ "0|1|
S1eQ40M0A1S0S26S1fG0R1A2Z4022A3S0S26S33R2A1Z22A3F_;Fflags;").
Proof. intros flags H. unfold mmap_flags_core. rewrite H. reflexivity. Qed.
Lemma mmap_noreserve_b_16418 : ltac2:(tb__ "0|1|
S1eQ40M0A1S0S26S1fG0R1A2Z4022A3S0S3S3cR2A1S7A3F_;Fflags;").
Proof. intros flags H. unfold mmap_noreserve_b. rewrite H. reflexivity. Qed.

Lemma mmap_fixed_rw_b_gates : ltac2:(tb__ "0|1|
S1eQ40A1M0G0G0S0S3S32R3R2R1A3S7A3S1S0S3S3aR2A1S7A3S0S3S37R3A1S7A3A2F_;Foff;Fflags;Fprot;").
Proof.
  intros prot flags off H. unfold mmap_fixed_rw_b in H. rewrite <- andb_assoc in H.
  apply andb_true_iff in H as [_ H]. eapply mmap_shape_gates; [exact H | reflexivity].
Qed.

Lemma region_free_app_l : ltac2:(tb__ "0|3|
S5S6S1eQ40A1M0G0A2M1A1M2G2G0G0S0S3S13SdG1R4R3A3R2R1A3S7A3S0S3S13R5R3R2A3S7A3F_;Fk;Fa;Fl2;Fl1;").
Proof.
  intros l1 l2 a k H. induction l1 as [|[b s] l1 IH]; [reflexivity|].
  cbn in H |- *. apply andb_true_iff in H as [H1 H2]. rewrite H1, (IH H2). reflexivity.
Qed.

Lemma map_contains_false_of_free : ltac2:(tb__ "0|2|
S5S6S1eQ40M0A1M1G1A2A1G1G1S45Z0S1fG0R1A2A2S0S3S13R4R3R2A3S7A3S0S3S1bR5R4R3A3S8A3F_;F_;Fk;Fa;Fl;").
Proof.
  intros l a k Hk H. unfold map_contains. induction l as [|[b s] l IH]; [reflexivity|].
  cbn in H. apply andb_true_iff in H as [H1 H2]. cbn [existsb fst snd]. rewrite (IH H2).
  unfold iv_overlap in H1. apply negb_true_iff in H1.
  pose proof (bv_unsigned_in_range _ a). pose proof (bv_unsigned_in_range _ s). pose proof (bv_unsigned_in_range _ b).
  match goal with |- ?c || false = false => destruct c eqn:E; [exfalso|reflexivity] end.
  apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
  apply andb_false_iff in H1. destruct H1 as [H1|H1]; apply Z.ltb_ge in H1; lia.
Qed.

Lemma errno_ret_in_nil_A : ltac2:(tb__ "0|0|
S1eQ40A1S0S3S24S4S26A1R1A2S8A3Fr;").
Proof. reflexivity. Qed.

Lemma mmap_place_not_errno_when : ltac2:(tb__ "0|1|
S3S1cS1eQ40M0A1S26S42Z0R1A2S42S43S1fG0R3A2R2A2S16R4A1A2S0S3S24S34R6A1R4A2S8A3F_;F_;FnZ;Fa;Fh;Fb;").
Proof.
  intros b h a nZ Hn Hc. unfold mmap_errnos_when. exact (mmap_place_not_errno h a nZ Hn Hc).
Qed.

Lemma region_free_app_r : ltac2:(tb__ "0|3|
S5S6S1eQ40A1M0G0A2M1A1M2G2G0G0S0S3S13SdG1R4R3A3R2R1A3S7A3S0S3S13R4R3R2A3S7A3F_;Fk;Fa;Fl2;Fl1;").
Proof.
  intros l1 l2 a k H. induction l1 as [|[b s] l1 IH]; [exact H|].
  cbn in H. apply andb_true_iff in H as [_ H2]. exact (IH H2).
Qed.

Section MmapFixedNoneFresh.
  Variables (i : SyscallInput) (m : Model).
  Hypothesis Hno : bv_unsigned (in_sysno i) = 222%Z.
  Let addr := in_arg i 0.
  Let len := in_arg i 1.
  Let flags := in_arg i 3.
  Let h := m_vmmaps m.
  Let n := mmap_n len.
  Hypothesis Hlen : len <> Z_to_bv 64 0.
  Hypothesis Hshape : ltac2:(tb__ "0|0|
S0S3S2fSeVi;U2A2SeVi;U3A2SeVi;U5A2A3S7A3").
  Hypothesis Hnot_none : ltac2:(tb__ "0|0|
S0S3S31SeVi;U2A2SeVi;U3A2SeVi;U5A2A3S8A3").
  Hypothesis Hnot_rw : ltac2:(tb__ "0|0|
S0S3S30SeVi;U2A2SeVi;U3A2SeVi;U5A2A3S8A3").
  Hypothesis Hceil : ltac2:(tb__ "0|0|
S42S43S1fQ40Vaddr;A2S29Vlen;A1A2S16S17Vm;A1A1A2").
  Hypothesis Halign : ltac2:(tb__ "0|0|
S0S26S44S1fQ40Vaddr;A2S18A2Z0A3").
  Hypothesis Hpos : (0 < bv_unsigned addr)%Z.

  Hypothesis Hfresh : ltac2:(tb__ "0|1|
S0S3S13SdS6S1eQ40A1M0G0A2S1aVh;A1S19Vh;A1A3Vaddr;Vn;A3S7A3").

  Lemma mmap_n_val : ltac2:(tb__ "0|0|
S0S26S1fQ40Vn;A2S29Vlen;A1A3").
  Proof using Hceil.
    unfold n, mmap_n. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
    pose proof (mmap_nZ_nonneg len). pose proof (bv_unsigned_in_range _ addr). pose proof (alloc_top_lt (m_vmmaps m)).
    change (bv_modulus 64) with two_pow_64. clear Hpos Hlen. unfold two_pow_64 in *. lia.
  Qed.

  Lemma mmap_n_pos : (0 < bv_unsigned n)%Z.
  Proof using Hceil Hlen.
    rewrite mmap_n_val. unfold mmap_nZ, page_round_up_Z, page_size.
    assert (Hl : (0 < bv_unsigned len)%Z).
    { pose proof (bv_unsigned_in_range _ len) as R.
      destruct (Z.eq_dec (bv_unsigned len) 0) as [E|]; [|clear Hpos; lia]. exfalso. apply Hlen.
      apply bv_eq. rewrite E. reflexivity. }
    clear Hpos. apply Z.mul_pos_pos; [|lia]. apply Z.div_str_pos. lia.
  Qed.

  Lemma mmap_fixed_none_fresh_reduce : ltac2:(tb__ "0|c|
SfS0S21S46Vi;R1Vm;A3SfS21Leff;R1S1eQ40M0A1M1S5S6G1S5S1eQ8A1A1A2M2A1M3S5S6G1G1A2M4A1M5G5S5S10A1M6S5S6G1S9A2M7A1M8G3S21Leff_writes;R5G5S21Leff_zeros;R4G6S21Leff_copies;R2G8S21Leff_copyins;R1S3S21L_;M9S24S34S8A1R6A2G5S21Lus;R3S23Vm;S4S11A1MaA2G4G5S22Ll;Lp;MbX5x2G9ScS47G0R6Vaddr;A3S25R3SaG4SbG1G1Vaddr;Vn;A4S4G4A1A3A2A2S23S2aVflags;Vm;Vlen;Vaddr;A4GaA2S22X3x2X3x2G7G8S22Ll;Lp;X5x2S10G6S22Ll;Lm0;X5x2GbX5x2G2G3S22Ll;Lp;X5x2Leff_copyins;Leff_copies;Lus;Leff_zeros;Leff_writes;Lr;Xfx1A3Feff;").
  Proof using Halign Hceil Hfresh Hlen Hno Hnot_none Hnot_rw Hpos Hshape.
    intros eff. rewrite (mmap_check i m Hno). unfold check_mmap.
    destruct (mmap_fixed_noaccess_b_gates _ _ _ Hshape) as [G1 G2].
    rewrite G1, G2, (mmap_len_gate i Hlen), Hnot_rw, Hnot_none, Hshape.
    pose proof mmap_n_pos as Hnp.
    unfold n, h, len, addr, flags, mmap_n, mmap_nZ, mmap_none_model, mmap_none_vm in *. cbv zeta.
    pose proof (alloc_top_lt (m_vmmaps m)) as Hc.
    destruct (two_pow_64 <=? bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)))%Z eqn:E1.
    { apply Z.leb_le in E1. lia. }
    rewrite (proj2 (Z.leb_le _ _) Hceil). cbn [negb].
    rewrite Halign. cbn [Z.eqb negb].
    rewrite (proj2 (Z.ltb_lt _ _) Hpos). cbn [negb].
    rewrite (region_free_app_l _ _ _ _ Hfresh). cbn [andb].
    rewrite (map_contains_false_of_free (vm_maps (m_vmmaps m)) _ _ Hnp (region_free_app_r _ _ _ _ Hfresh)).
    rewrite Hfresh. reflexivity.
  Qed.

  Lemma mmap_fixed_none_fresh_inv : ltac2:(tb__ "0|5|
S28SfA1M0S2eVi;Vm;R1A3S2S2cR2S15S14A1Vm;S4S11A1M1A4S0G0R2S27SfS12Vaddr;S4S6S1eQ40A1M2S5S1eQ8A1A1A2A1S4S6G2G2A2M3A1M4SaG3SbG2G2Vaddr;Vn;A4G4A3S4S10A1S4S6G2S9A2A1A6S2aVflags;Vm;Vlen;Vaddr;A4G1A4A3A2F_;FR;").
  Proof using Halign Hceil Hfresh Hlen Hno Hnot_none Hnot_rw Hpos Hshape.
    intros R Hs. apply spec_check in Hs. destruct R as [eff m' evs|]; cbn in Hs.
    - rewrite mmap_fixed_none_fresh_reduce in Hs.
      destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      destruct (errno_ret_in (mmap_errnos_when false) r) eqn:E.
      + destruct us; [|discriminate]. unfold mmap_errnos_when in E.
        apply errno_ret_in_true in E as (e & Hin & ->). destruct Hin as [<-|[]].
        inversion Hs; subst. left. reflexivity.
      + destruct (bv_eqb r addr && listNN_eqb us [(addr, n)]) eqn:G; [|discriminate].
        apply andb_true_iff in G as [G1 G2]. apply bv_eqb_eq in G1. apply listNN_eqb_eq in G2.
        subst. inversion Hs; subst. right. reflexivity.
    - exfalso. specialize (Hs probe_eff). rewrite mmap_fixed_none_fresh_reduce in Hs. unfold probe_eff in Hs.
      unfold mmap_errnos_when in Hs. change (errno_ret_in mmap_errnos (Z_to_bv 64 0)) with false in Hs.
      destruct (bv_eqb (Z_to_bv 64 0) addr && listNN_eqb [] [(addr, n)]); discriminate.
  Qed.

  Lemma mmap_fixed_none_fresh_intro_ok_ss : ltac2:(tb__ "0|3|
S2eVi;Vm;S27SfS12Vaddr;S4S6S1eQ40A1M0S5S1eQ8A1A1A2A1S4S6G0G0A2M1A1M2SaG1SbG0G0Vaddr;Vn;A4G2A3S4S10A1S4S6G0S9A2A1A6S2aVflags;Vm;Vlen;Vaddr;A4S4S11A1A4A3").
  Proof using Halign Hceil Hfresh Hlen Hno Hnot_none Hnot_rw Hpos Hshape.
    apply check_spec_ok. rewrite mmap_fixed_none_fresh_reduce.
    rewrite (mmap_place_not_errno_when _ _ addr (mmap_nZ len) (mmap_nZ_nonneg len) Hceil).
    rewrite bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
  Qed.

  Lemma mmap_fixed_none_fresh_intro_ok : ltac2:(tb__ "0|3|
S4bVi;Vm;S27SfS12Vaddr;S4S6S1eQ40A1M0S5S1eQ8A1A1A2A1S4S6G0G0A2M1A1M2SaG1SbG0G0Vaddr;Vn;A4G2A3S4S10A1S4S6G0S9A2A1A6S2aVflags;Vm;Vlen;Vaddr;A4S4S11A1A4A3").
  Proof using Halign Hceil Hfresh Hlen Hno Hnot_none Hnot_rw Hpos Hshape.
    intros. split; [eapply mmap_fixed_none_fresh_intro_ok_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. pose proof (mmap_place_not_errno _ addr (mmap_nZ len) (mmap_nZ_nonneg len) Hceil) as Hnot. apply ns_nonenomem_mmap; [assumption|]. cbn [eff_ret]. intro E. rewrite E in Hnot. vm_compute in Hnot. discriminate Hnot.
  Qed.
End MmapFixedNoneFresh.

Section MmapFixedRwFresh.
  Variables (i : SyscallInput) (m : Model).
  Hypothesis Hno : bv_unsigned (in_sysno i) = 222%Z.
  Let addr := in_arg i 0.
  Let len := in_arg i 1.
  Let flags := in_arg i 3.
  Let h := m_vmmaps m.
  Let n := mmap_n len.
  Hypothesis Hlen : len <> Z_to_bv 64 0.
  Hypothesis Hshape : ltac2:(tb__ "0|0|
S0S3S32SeVi;U2A2SeVi;U3A2SeVi;U5A2A3S7A3").
  Hypothesis Hnot_fn : ltac2:(tb__ "0|0|
S0S3S2fSeVi;U2A2SeVi;U3A2SeVi;U5A2A3S8A3").
  Hypothesis Hnot_none : ltac2:(tb__ "0|0|
S0S3S31SeVi;U2A2SeVi;U3A2SeVi;U5A2A3S8A3").
  Hypothesis Hnot_rw : ltac2:(tb__ "0|0|
S0S3S30SeVi;U2A2SeVi;U3A2SeVi;U5A2A3S8A3").
  Hypothesis Hceil : ltac2:(tb__ "0|0|
S42S43S1fQ40Vaddr;A2S29Vlen;A1A2S16S17Vm;A1A1A2").
  Hypothesis Halign : ltac2:(tb__ "0|0|
S0S26S44S1fQ40Vaddr;A2S18A2Z0A3").
  Hypothesis Hpos : (0 < bv_unsigned addr)%Z.
  Hypothesis Hfresh : ltac2:(tb__ "0|1|
S0S3S13SdS6S1eQ40A1M0G0A2S1aVh;A1S19Vh;A1A3Vaddr;Vn;A3S7A3").

  Lemma mmap_fixed_rw_fresh_reduce : ltac2:(tb__ "0|d|
SfS0S21S46Vi;R1Vm;A3SfS21Leff;R1S1eQ40M0A1M1S5S6G1S5S1eQ8A1A1A2M2A1M3S5S6G1G1A2M4A1M5G5S5S10A1M6S5S6G1S9A2M7A1M8G3S21Leff_writes;R5G5S21Leff_unmaps;R3G6S21Leff_copies;R2G8S21Leff_copyins;R1S3S21L_;M9S24S34S38Vflags;Vm;S29Vlen;A1MaA3A1R6A2G5S21Lzs;R4S23Vm;S4S11A1MbA2G4G5S22Ll;Lp;McX5x2G9ScScS47G0R6Vaddr;A3S25R4SaG4SbG1G1Vaddr;Vn;A4S4G4A1A3A2A2S35Vflags;Vm;GaA3A2S23S2bVflags;Vm;Vlen;Vaddr;A4GbA2S22X3x2X3x2G7G8S22Ll;Lp;X5x2S10G6S22Ll;Lm0;X5x2GcX5x2G2G3S22Ll;Lp;X5x2Leff_copyins;Leff_copies;Leff_unmaps;Lzs;Leff_writes;Lr;Xfx1A3Feff;").
  Proof using Halign Hceil Hfresh Hlen Hno Hnot_fn Hnot_none Hnot_rw Hpos Hshape.
    intros eff. rewrite (mmap_check i m Hno). unfold check_mmap.
    destruct (mmap_fixed_rw_b_gates _ _ _ Hshape) as [G1 G2].
    rewrite G1, G2, (mmap_len_gate i Hlen), Hnot_rw, Hnot_none, Hnot_fn, Hshape.
    pose proof (mmap_n_pos i m Hlen Hceil) as Hnp.
    unfold n, h, len, addr, flags, mmap_n, mmap_nZ, mmap_rw_model, mmap_rw_vm in *. cbv zeta.
    pose proof (alloc_top_lt (m_vmmaps m)) as Hc.
    destruct (two_pow_64 <=? bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)))%Z eqn:E1.
    { apply Z.leb_le in E1. lia. }
    rewrite (proj2 (Z.leb_le _ _) Hceil). cbn [negb].
    rewrite Halign. cbn [Z.eqb negb].
    rewrite (proj2 (Z.ltb_lt _ _) Hpos). cbn [negb].
    rewrite (region_free_app_l _ _ _ _ Hfresh). cbn [andb].
    rewrite (map_contains_false_of_free (vm_maps (m_vmmaps m)) _ _ Hnp (region_free_app_r _ _ _ _ Hfresh)).
    rewrite Hfresh. reflexivity.
  Qed.

  Lemma mmap_fixed_rw_fresh_inv : ltac2:(tb__ "0|5|
S28SfA1M0S2eVi;Vm;R1A3S2S2cR2S15S14A1Vm;S4S11A1M1A4S1S0S3S35Vflags;Vm;S29Vlen;A1A3S7A3S0G0R2S27SfS12Vaddr;S4S6S1eQ40A1M2S5S1eQ8A1A1A2A1SaS6G2G2A2M3SbG2G2Vaddr;Vn;A4S4G3A1M4A3G4S4S10A1S4S6G2S9A2A1A6S2bVflags;Vm;Vlen;Vaddr;A4G1A4A3A2A2F_;FR;").
  Proof using Halign Hceil Hfresh Hlen Hno Hnot_fn Hnot_none Hnot_rw Hpos Hshape.
    intros R Hs. apply spec_check in Hs. destruct R as [eff m' evs|]; cbn in Hs.
    - rewrite mmap_fixed_rw_fresh_reduce in Hs.
      destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
      destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
      destruct (errno_ret_in (mmap_errnos_when (mmap_fixed_fresh_refusable flags m (mmap_nZ len))) r) eqn:E.
      + unfold mmap_errnos_when in E.
        apply errno_ret_in_true in E as (e & Hin & ->). destruct Hin as [<-|[]].
        destruct zs; [|discriminate]. inversion Hs; subst. left. reflexivity.
      + destruct (bv_eqb r addr && listNN_eqb zs [(addr, n)] && mmap_noreserve_backed_ok flags m (mmap_nZ len)) eqn:G; [|discriminate].
        apply andb_true_iff in G as [G G3]. apply andb_true_iff in G as [G1 G2].
        apply bv_eqb_eq in G1. apply listNN_eqb_eq in G2.
        subst. inversion Hs; subst. right. split; [exact G3|reflexivity].
    - exfalso. specialize (Hs probe_eff). rewrite mmap_fixed_rw_fresh_reduce in Hs. unfold probe_eff in Hs.
      destruct (errno_ret_in (mmap_errnos_when (mmap_fixed_fresh_refusable flags m (mmap_nZ len))) (Z_to_bv 64 0)); [discriminate|].
      destruct (bv_eqb (Z_to_bv 64 0) addr && listNN_eqb [] [(addr, n)] && mmap_noreserve_backed_ok flags m (mmap_nZ len)); discriminate.
  Qed.

  Lemma mmap_fixed_rw_fresh_intro_fail_ss : ltac2:(tb__ "0|2|
S0S3S38Vflags;Vm;S29Vlen;A1A3S7A3S2eVi;Vm;S27SfS12S15S14A1S4S6S1eQ40A1M0S5S1eQ8A1A1A2A1S4S6G0G0A2A1M1G1S4S10A1S4S6G0S9A2A1A6Vm;S4S11A1A4A3F_;").
  Proof using Halign Hceil Hfresh Hlen Hno Hnot_fn Hnot_none Hnot_rw Hpos Hshape.
    intros Hrf. apply check_spec_ok. rewrite mmap_fixed_rw_fresh_reduce. rewrite Hrf. unfold mmap_errnos_when.
    rewrite (errno_ret_in_intro mmap_errnos ENOMEM ltac:(left; reflexivity)). reflexivity.
  Qed.

  Lemma mmap_fixed_rw_fresh_intro_fail : ltac2:(tb__ "0|2|
S0S3S38Vflags;Vm;S29Vlen;A1A3S7A3S4bVi;Vm;S27SfS12S15S14A1S4S6S1eQ40A1M0S5S1eQ8A1A1A2A1S4S6G0G0A2A1M1G1S4S10A1S4S6G0S9A2A1A6Vm;S4S11A1A4A3F_;").
  Proof using Halign Hceil Hfresh Hlen Hno Hnot_fn Hnot_none Hnot_rw Hpos Hshape.
    intros. split; [eapply mmap_fixed_rw_fresh_intro_fail_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. apply ns_forced_mmap; [assumption|]. intros ? ? ? Hs'. destruct (mmap_fixed_rw_fresh_inv _ Hs') as [He | (Hb & E')]; [unfold is_ret in He; inversion He; subst; reflexivity | exfalso; match goal with F : mmap_fixed_fresh_refusable _ _ _ = true |- _ => unfold mmap_fixed_fresh_refusable in F; rewrite Hb in F; discriminate F end].
  Qed.

  Lemma mmap_fixed_rw_fresh_intro_ok_ss : ltac2:(tb__ "0|3|
S0S3S35Vflags;Vm;S29Vlen;A1A3S7A3S2eVi;Vm;S27SfS12Vaddr;S4S6S1eQ40A1M0S5S1eQ8A1A1A2A1SaS6G0G0A2M1SbG0G0Vaddr;Vn;A4S4G1A1M2A3G2S4S10A1S4S6G0S9A2A1A6S2bVflags;Vm;Vlen;Vaddr;A4S4S11A1A4A3F_;").
  Proof using Halign Hceil Hfresh Hlen Hno Hnot_fn Hnot_none Hnot_rw Hpos Hshape.
    intros Hb. apply check_spec_ok. rewrite mmap_fixed_rw_fresh_reduce.
    rewrite (mmap_place_not_errno_when _ _ addr (mmap_nZ len) (mmap_nZ_nonneg len) Hceil).
    rewrite bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl), Hb. reflexivity.
  Qed.

  Lemma mmap_fixed_rw_fresh_intro_ok : ltac2:(tb__ "0|3|
S0S3S35Vflags;Vm;S29Vlen;A1A3S7A3S4bVi;Vm;S27SfS12Vaddr;S4S6S1eQ40A1M0S5S1eQ8A1A1A2A1SaS6G0G0A2M1SbG0G0Vaddr;Vn;A4S4G1A1M2A3G2S4S10A1S4S6G0S9A2A1A6S2bVflags;Vm;Vlen;Vaddr;A4S4S11A1A4A3F_;").
  Proof using Halign Hceil Hfresh Hlen Hno Hnot_fn Hnot_none Hnot_rw Hpos Hshape.
    intros. split; [eapply mmap_fixed_rw_fresh_intro_ok_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. pose proof (mmap_place_not_errno _ addr (mmap_nZ len) (mmap_nZ_nonneg len) Hceil) as Hnot. apply ns_nonenomem_mmap; [assumption|]. cbn [eff_ret]. intro E. rewrite E in Hnot. vm_compute in Hnot. discriminate Hnot.
  Qed.
End MmapFixedRwFresh.

Definition mmap_fixed_rw_ok_model (flags : word) (m : Model) (addr n : word) : Model := ltac2:(tb__ "0|0|
S41Vflags;Vaddr;Vn;S1dS3fS17Vm;A1Vaddr;Vn;A3Vm;A2A4").

Section MmapFixedRwCommit.
  Variables (i : SyscallInput) (m : Model).
  Hypothesis Hno : bv_unsigned (in_sysno i) = 222%Z.
  Let addr := in_arg i 0.
  Let len := in_arg i 1.
  Let flags := in_arg i 3.
  Let h := m_vmmaps m.
  Let n := mmap_n len.
  Hypothesis Hlen : len <> Z_to_bv 64 0.
  Hypothesis Hshape : ltac2:(tb__ "0|0|
S0S3S32SeVi;U2A2SeVi;U3A2SeVi;U5A2A3S7A3").
  Hypothesis Hnot_fn : ltac2:(tb__ "0|0|
S0S3S2fSeVi;U2A2SeVi;U3A2SeVi;U5A2A3S8A3").
  Hypothesis Hnot_none : ltac2:(tb__ "0|0|
S0S3S31SeVi;U2A2SeVi;U3A2SeVi;U5A2A3S8A3").
  Hypothesis Hnot_rw : ltac2:(tb__ "0|0|
S0S3S30SeVi;U2A2SeVi;U3A2SeVi;U5A2A3S8A3").
  Hypothesis Hceil : ltac2:(tb__ "0|0|
S42S43S1fQ40Vaddr;A2S29Vlen;A1A2S16S17Vm;A1A1A2").
  Hypothesis Halign : ltac2:(tb__ "0|0|
S0S26S44S1fQ40Vaddr;A2S18A2Z0A3").
  Hypothesis Hpos : (0 < bv_unsigned addr)%Z.

  Hypothesis Hfree : ltac2:(tb__ "0|0|
S0S3S13S1aVh;A1Vaddr;Vn;A3S7A3").
  Hypothesis Hcont : ltac2:(tb__ "0|0|
S0S3S1bS19Vh;A1Vaddr;Vn;A3S7A3").

  Lemma mmap_fixed_rw_commit_reduce : ltac2:(tb__ "0|d|
SfS0S21S46Vi;R1Vm;A3SfS21Leff;R1S1eQ40M0A1M1S5S6G1S5S1eQ8A1A1A2M2A1M3S5S6G1G1A2M4A1M5G5S5S10A1M6S5S6G1S9A2M7A1M8G3S21Leff_writes;R5G6S21Leff_copies;R2G8S21Leff_copyins;R1S3S21L_;M9ScScS24S34S3dVflags;Vm;Vaddr;Vn;A4A1R6A2S49G4R4A2MaA2S49G4R3A2A2S23Vm;S4S11A1MbA2G9ScScS24S3eR6A2GaA2S25R3SaG4SbG1G1Vaddr;Vn;A4S4G4A1A3McA2A2S23S2dVm;Vaddr;Vn;A3GbA2G5S21Lus;R3G9ScScS47G0R6Vaddr;A3S25R4GcA2A2S3bVflags;Vm;Vaddr;Vn;A4A2S23S48Vflags;Vm;Vaddr;Vn;A4GbA2S22X3x2G4G5S22Ll;Lp;X5x2X3x2X3x2G7G8S22Ll;Lp;X5x2S10G6S22Ll;Lm0;X5x2G2G3S22Ll;Lp;X5x2Leff_copyins;Leff_copies;Lus;Lzs;Leff_writes;Lr;Xfx1A3Feff;").
  Proof using Halign Hceil Hcont Hfree Hlen Hno Hnot_fn Hnot_none Hnot_rw Hpos Hshape.
    intros eff. rewrite (mmap_check i m Hno). unfold check_mmap.
    destruct (mmap_fixed_rw_b_gates _ _ _ Hshape) as [G1 G2].
    rewrite G1, G2, (mmap_len_gate i Hlen), Hnot_rw, Hnot_none, Hnot_fn, Hshape.
    pose proof (mmap_place_not_errno _ addr (mmap_nZ len) (mmap_nZ_nonneg len) Hceil) as Hna.
    unfold n, h, len, addr, flags, mmap_n, mmap_nZ, mmap_fixed_rw_ok_model, mmap_fixed_dead_model, mmap_fixed_dead_vm in *. cbv zeta.
    pose proof (alloc_top_lt (m_vmmaps m)) as Hc.
    destruct (two_pow_64 <=? bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)))%Z eqn:E1.
    { apply Z.leb_le in E1. lia. }
    rewrite (proj2 (Z.leb_le _ _) Hceil). cbn [negb].
    rewrite Halign. cbn [Z.eqb negb].
    rewrite (proj2 (Z.ltb_lt _ _) Hpos). cbn [negb].
    rewrite Hfree, Hcont. cbn [andb].
    destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity]. destruct cs; [|reflexivity].
    destruct ci; [|reflexivity].
    unfold mmap_errnos_when, mmap_destructive_errnos.
    destruct (errno_ret_in mmap_errnos r) eqn:E; cbn [andb].
    - apply errno_ret_in_true in E as (e & Hin & ->). destruct Hin as [<-|[]].
      assert (Hne : bv_eqb (errno_ret ENOMEM) (in_arg i 0) = false).
      { destruct (bv_eqb (errno_ret ENOMEM) (in_arg i 0)) eqn:B; [|reflexivity].
        apply bv_eqb_eq in B. rewrite <- B in Hna. vm_compute in Hna. discriminate Hna. }
      destruct zs as [|z zs].
      + destruct us as [|u us]; [reflexivity|].
        match goal with |- context [listNN_eqb (u :: us) ?l] => destruct (listNN_eqb (u :: us) l) end;
          reflexivity.
      + destruct us; [rewrite Hne; reflexivity | reflexivity].
    - destruct us; reflexivity.
  Qed.

  Lemma mmap_fixed_rw_commit_inv : ltac2:(tb__ "0|a|
S28SfA1M0S2eVi;Vm;R1A3S2S2cR2S15S14A1M1Vm;S4S11A1M2A4S2S1S0S3S3bVflags;Vm;Vaddr;Vn;A4S7A3S0G0R2S27SfS12Vaddr;S4S6S1eQ40A1M3S5S1eQ8A1A1A2A1M4SaS6G3G3A2M5SbG3G3Vaddr;Vn;A4S4G5A1M6A3M7G6S4S10A1M8S4S6G3S9A2A1M9A6S48Vflags;Vm;Vaddr;Vn;A4G2A4A3A2S0G0R2S27SfS12G1G4G6G7G8G9A6S2dVm;Vaddr;Vn;A3G2A4A3A2A2F_;FR;").
  Proof using Halign Hceil Hcont Hfree Hlen Hno Hnot_fn Hnot_none Hnot_rw Hpos Hshape.
    intros R Hs. apply spec_check in Hs. destruct R as [eff m' evs|]; cbn in Hs.
    - rewrite mmap_fixed_rw_commit_reduce in Hs.
      destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate].
      destruct cs; [|destruct zs, us; discriminate]. destruct ci; [|destruct zs, us; discriminate].
      destruct (errno_ret_in (mmap_errnos_when (mmap_fixed_commit_refusable flags m addr n)) r && w_nilb zs && w_nilb us) eqn:E.
      + apply andb_true_iff in E as [E Eu]. apply andb_true_iff in E as [E Ez].
        unfold mmap_errnos_when in E.
        apply errno_ret_in_true in E as (e & Hin & ->). destruct Hin as [<-|[]].
        destruct zs; [|discriminate]. destruct us; [|discriminate]. inversion Hs; subst. left. reflexivity.
      + destruct (errno_ret_in mmap_destructive_errnos r && w_nilb zs && listNN_eqb us [(addr, n)]) eqn:D.
        { apply andb_true_iff in D as [D Du]. apply andb_true_iff in D as [D Dz].
          unfold mmap_destructive_errnos in D. apply errno_ret_in_true in D as (e & Hin & ->).
          destruct Hin as [<-|[]]. destruct zs; [|discriminate]. apply listNN_eqb_eq in Du. subst us.
          inversion Hs; subst. right; right. reflexivity. }
        destruct us; [|discriminate].
        destruct (bv_eqb r addr && listNN_eqb zs [(addr, n)] && mmap_fixed_rw_budget_ok flags m addr n) eqn:G; [|discriminate].
        apply andb_true_iff in G as [G G3]. apply andb_true_iff in G as [G1 G2].
        apply bv_eqb_eq in G1. apply listNN_eqb_eq in G2.
        subst. inversion Hs; subst. right; left. split; [exact G3|reflexivity].
    - exfalso. specialize (Hs probe_eff). rewrite mmap_fixed_rw_commit_reduce in Hs. unfold probe_eff in Hs.
      unfold mmap_destructive_errnos in Hs. change (errno_ret_in mmap_errnos (Z_to_bv 64 0)) with false in Hs.
      cbn [andb] in Hs.
      destruct (errno_ret_in (mmap_errnos_when (mmap_fixed_commit_refusable flags m addr n)) (Z_to_bv 64 0) && w_nilb [] && w_nilb []); [discriminate|].
      destruct (bv_eqb (Z_to_bv 64 0) addr && listNN_eqb [] [(addr, n)] && mmap_fixed_rw_budget_ok flags m addr n); discriminate.
  Qed.

  Lemma mmap_fixed_rw_commit_intro_fail_kept_ss : ltac2:(tb__ "0|2|
S0S3S3dVflags;Vm;Vaddr;Vn;A4S7A3S2eVi;Vm;S27SfS12S15S14A1S4S6S1eQ40A1M0S5S1eQ8A1A1A2A1S4S6G0G0A2A1M1G1S4S10A1S4S6G0S9A2A1A6Vm;S4S11A1A4A3F_;").
  Proof using Halign Hceil Hcont Hfree Hlen Hno Hnot_fn Hnot_none Hnot_rw Hpos Hshape.
    intros Hrf. apply check_spec_ok. rewrite mmap_fixed_rw_commit_reduce. rewrite Hrf. unfold mmap_errnos_when.
    rewrite (errno_ret_in_intro mmap_errnos ENOMEM ltac:(left; reflexivity)). reflexivity.
  Qed.

  Lemma mmap_fixed_rw_commit_intro_fail_kept : ltac2:(tb__ "0|2|
S0S3S3dVflags;Vm;Vaddr;Vn;A4S7A3S4bVi;Vm;S27SfS12S15S14A1S4S6S1eQ40A1M0S5S1eQ8A1A1A2A1S4S6G0G0A2A1M1G1S4S10A1S4S6G0S9A2A1A6Vm;S4S11A1A4A3F_;").
  Proof using Halign Hceil Hcont Hfree Hlen Hno Hnot_fn Hnot_none Hnot_rw Hpos Hshape.
    intros. split; [eapply mmap_fixed_rw_commit_intro_fail_kept_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. apply ns_forced_mmap; [assumption|]. intros ? ? ? Hs'. destruct (mmap_fixed_rw_commit_inv _ Hs') as [He | [(Hb & E') | E']]; [unfold is_ret in He; inversion He; subst; reflexivity | exfalso; match goal with F : mmap_fixed_commit_refusable _ _ _ _ = true |- _ => unfold mmap_fixed_commit_refusable in F; rewrite Hb in F; discriminate F end | inversion E'; subst; reflexivity].
  Qed.

  Lemma mmap_fixed_rw_commit_intro_ok_ss : ltac2:(tb__ "0|3|
S0S3S3bVflags;Vm;Vaddr;Vn;A4S7A3S2eVi;Vm;S27SfS12Vaddr;S4S6S1eQ40A1M0S5S1eQ8A1A1A2A1SaS6G0G0A2M1SbG0G0Vaddr;Vn;A4S4G1A1M2A3G2S4S10A1S4S6G0S9A2A1A6S48Vflags;Vm;Vaddr;Vn;A4S4S11A1A4A3F_;").
  Proof using Halign Hceil Hcont Hfree Hlen Hno Hnot_fn Hnot_none Hnot_rw Hpos Hshape.
    intros Hb. apply check_spec_ok. rewrite mmap_fixed_rw_commit_reduce.
    unfold mmap_destructive_errnos.
    rewrite (mmap_place_not_errno _ addr (mmap_nZ len) (mmap_nZ_nonneg len) Hceil).
    rewrite (mmap_place_not_errno_when _ _ addr (mmap_nZ len) (mmap_nZ_nonneg len) Hceil). cbn [andb].
    rewrite bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl), Hb. reflexivity.
  Qed.

  Lemma mmap_fixed_rw_commit_intro_ok : ltac2:(tb__ "0|3|
S0S3S3bVflags;Vm;Vaddr;Vn;A4S7A3S4bVi;Vm;S27SfS12Vaddr;S4S6S1eQ40A1M0S5S1eQ8A1A1A2A1SaS6G0G0A2M1SbG0G0Vaddr;Vn;A4S4G1A1M2A3G2S4S10A1S4S6G0S9A2A1A6S48Vflags;Vm;Vaddr;Vn;A4S4S11A1A4A3F_;").
  Proof using Halign Hceil Hcont Hfree Hlen Hno Hnot_fn Hnot_none Hnot_rw Hpos Hshape.
    intros. split; [eapply mmap_fixed_rw_commit_intro_ok_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. pose proof (mmap_place_not_errno _ addr (mmap_nZ len) (mmap_nZ_nonneg len) Hceil) as Hnot. apply ns_nonenomem_mmap; [assumption|]. cbn [eff_ret]. intro E. rewrite E in Hnot. vm_compute in Hnot. discriminate Hnot.
  Qed.
End MmapFixedRwCommit.

Lemma mmap_flags_core_0x104022 : ltac2:(tb__ "0|1|
S1eQ40M0A1S0S26S1fG0R1A2Z104022A3S0S26S33R2A1Z100022A3F_;Fflags;").
Proof. intros flags H. unfold mmap_flags_core. rewrite H. reflexivity. Qed.
Lemma mmap_noreserve_b_0x104022 : ltac2:(tb__ "0|1|
S1eQ40M0A1S0S26S1fG0R1A2Z104022A3S0S3S3cR2A1S7A3F_;Fflags;").
Proof. intros flags H. unfold mmap_noreserve_b. rewrite H. reflexivity. Qed.

Lemma mmap_noreplace_rw_b_intro : ltac2:(tb__ "0|2|
S1eQ40M0A1M1G1G1S0S26S1fG0R3A2Z3A3S0S26S33R3A1Z100022A3S0G1R3S20G0Z0A2A3S1S0S3S39R6R5R4A3S7A3S1S0S3S36R6R5R4A3S8A3S1S0S3S32R6R5R4A3S8A3S1S0S3S2fR6R5R4A3S8A3S1S0S3S31R6R5R4A3S8A3S0S3S30R6R5R4A3S8A3A2A2A2A2A2F_;F_;F_;Foff;Fflags;Fprot;").
Proof.
  intros prot flags off Hp Hf ->.
  unfold mmap_noreplace_rw_b, mmap_noreplace_noaccess_b, mmap_noreplace_flags_b, mmap_fixed_rw_b, mmap_fixed_noaccess_b, mmap_noaccess_b, mmap_modeled_b.
  rewrite Hp, Hf. unfold PROT_READ, PROT_WRITE, PROT_NONE, MAP_PRIVATE, MAP_ANONYMOUS, MAP_FIXED, MAP_FIXED_NOREPLACE. cbn.
  repeat split; reflexivity.
Qed.

Lemma mmap_noreplace_none_b_intro : ltac2:(tb__ "0|3|
S1eQ40M0A1M1G1G1S0S26S1fG0R3A2Z0M2A3S0S26S33R3A1Z100022A3S0G1R3S20G0G2A2A3S1S0S3S36R6R5R4A3S7A3S1S0S3S39R6R5R4A3S8A3S1S0S3S32R6R5R4A3S8A3S1S0S3S2fR6R5R4A3S8A3S1S0S3S31R6R5R4A3S8A3S0S3S30R6R5R4A3S8A3A2A2A2A2A2F_;F_;F_;Foff;Fflags;Fprot;").
Proof.
  intros prot flags off Hp Hf ->.
  unfold mmap_noreplace_rw_b, mmap_noreplace_noaccess_b, mmap_noreplace_flags_b, mmap_fixed_rw_b, mmap_fixed_noaccess_b, mmap_noaccess_b, mmap_modeled_b.
  rewrite Hp, Hf. unfold PROT_READ, PROT_WRITE, PROT_NONE, MAP_PRIVATE, MAP_ANONYMOUS, MAP_FIXED, MAP_FIXED_NOREPLACE. cbn.
  repeat split; reflexivity.
Qed.

Lemma mmap_noreplace_flags_b_gates : ltac2:(tb__ "0|1|
S1eQ40A1M0G0S0S3ScS40R2A1S4aR1A1A2S7A3S1S0S3S3aR2A1S7A3S0S3S37R3A1S7A3A2F_;Foff;Fflags;").
Proof.
  intros flags off H. apply andb_true_iff in H as [H1 H2]. unfold mmap_noreplace_flags_b in H1.
  apply orb_true_iff in H1 as [H1|H1].
  - eapply (mmap_shape_gates flags off); [rewrite H1, H2; reflexivity | reflexivity].
  - eapply (mmap_shape_gates flags off); [rewrite H1, H2; reflexivity | reflexivity].
Qed.
Lemma mmap_noreplace_rw_b_gates : ltac2:(tb__ "0|1|
S1eQ40A1M0G0G0S0S3S39R3R2R1A3S7A3S1S0S3S3aR2A1S7A3S0S3S37R3A1S7A3A2F_;Foff;Fflags;Fprot;").
Proof.
  intros prot flags off H. unfold mmap_noreplace_rw_b in H. rewrite <- andb_assoc in H.
  apply andb_true_iff in H as [_ H]. exact (mmap_noreplace_flags_b_gates flags off H).
Qed.
Lemma mmap_noreplace_noaccess_b_gates : ltac2:(tb__ "0|1|
S1eQ40A1M0G0G0S0S3S36R3R2R1A3S7A3S1S0S3S3aR2A1S7A3S0S3S37R3A1S7A3A2F_;Foff;Fflags;Fprot;").
Proof.
  intros prot flags off H. unfold mmap_noreplace_noaccess_b in H. rewrite <- andb_assoc in H.
  apply andb_true_iff in H as [_ H]. exact (mmap_noreplace_flags_b_gates flags off H).
Qed.

Section MmapNoreplaceRwFresh.
  Variables (i : SyscallInput) (m : Model).
  Hypothesis Hno : bv_unsigned (in_sysno i) = 222%Z.
  Let addr := in_arg i 0.
  Let len := in_arg i 1.
  Let flags := in_arg i 3.
  Let h := m_vmmaps m.
  Let n := mmap_n len.
  Hypothesis Hlen : len <> Z_to_bv 64 0.
  Hypothesis Hshape : ltac2:(tb__ "0|0|
S0S3S39SeVi;U2A2SeVi;U3A2SeVi;U5A2A3S7A3").
  Hypothesis Hnot_nrn : ltac2:(tb__ "0|0|
S0S3S36SeVi;U2A2SeVi;U3A2SeVi;U5A2A3S8A3").
  Hypothesis Hnot_frw : ltac2:(tb__ "0|0|
S0S3S32SeVi;U2A2SeVi;U3A2SeVi;U5A2A3S8A3").
  Hypothesis Hnot_fn : ltac2:(tb__ "0|0|
S0S3S2fSeVi;U2A2SeVi;U3A2SeVi;U5A2A3S8A3").
  Hypothesis Hnot_none : ltac2:(tb__ "0|0|
S0S3S31SeVi;U2A2SeVi;U3A2SeVi;U5A2A3S8A3").
  Hypothesis Hnot_rw : ltac2:(tb__ "0|0|
S0S3S30SeVi;U2A2SeVi;U3A2SeVi;U5A2A3S8A3").
  Hypothesis Hceil : ltac2:(tb__ "0|0|
S42S43S1fQ40Vaddr;A2S29Vlen;A1A2S16S17Vm;A1A1A2").
  Hypothesis Halign : ltac2:(tb__ "0|0|
S0S26S44S1fQ40Vaddr;A2S18A2Z0A3").
  Hypothesis Hpos : (0 < bv_unsigned addr)%Z.

  Hypothesis Hfresh : ltac2:(tb__ "0|1|
S0S3S13SdS6S1eQ40A1M0G0A2S1aVh;A1S19Vh;A1A3Vaddr;Vn;A3S7A3").

  Lemma mmap_noreplace_rw_fresh_reduce : ltac2:(tb__ "0|d|
SfS0S21S46Vi;R1Vm;A3SfS21Leff;R1S1eQ40M0A1M1S5S6G1S5S1eQ8A1A1A2M2A1M3S5S6G1G1A2M4A1M5G5S5S10A1M6S5S6G1S9A2M7A1M8G3S21Leff_writes;R5G5S21Leff_unmaps;R3G6S21Leff_copies;R2G8S21Leff_copyins;R1S3S21L_;M9S24S34S38Vflags;Vm;S29Vlen;A1MaA3A1R6A2G5S21Lzs;R4S23Vm;S4S11A1MbA2G4G5S22Ll;Lp;McX5x2G9ScScS47G0R6Vaddr;A3S25R4SaG4SbG1G1Vaddr;Vn;A4S4G4A1A3A2A2S35Vflags;Vm;GaA3A2S23S2bVflags;Vm;Vlen;Vaddr;A4GbA2S22X3x2X3x2G7G8S22Ll;Lp;X5x2S10G6S22Ll;Lm0;X5x2GcX5x2G2G3S22Ll;Lp;X5x2Leff_copyins;Leff_copies;Leff_unmaps;Lzs;Leff_writes;Lr;Xfx1A3Feff;").
  Proof using Halign Hceil Hfresh Hlen Hno Hnot_fn Hnot_frw Hnot_none Hnot_nrn Hnot_rw Hpos Hshape.
    intros eff. rewrite (mmap_check i m Hno). unfold check_mmap.
    destruct (mmap_noreplace_rw_b_gates _ _ _ Hshape) as [G1 G2].
    rewrite G1, G2, (mmap_len_gate i Hlen), Hnot_rw, Hnot_none, Hnot_fn, Hnot_frw, Hnot_nrn, Hshape.
    unfold n, h, len, addr, flags, mmap_n, mmap_nZ, mmap_rw_model, mmap_rw_vm in *. cbv zeta.
    pose proof (alloc_top_lt (m_vmmaps m)) as Hc.
    destruct (two_pow_64 <=? bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)))%Z eqn:E1.
    { apply Z.leb_le in E1. lia. }
    rewrite (proj2 (Z.leb_le _ _) Hceil). cbn [negb].
    rewrite Halign. cbn [Z.eqb negb].
    rewrite (proj2 (Z.ltb_lt _ _) Hpos). cbn [negb].
    rewrite Hfresh. reflexivity.
  Qed.

  Lemma mmap_noreplace_rw_fresh_inv : ltac2:(tb__ "0|5|
S28SfA1M0S2eVi;Vm;R1A3S2S2cR2S15S14A1Vm;S4S11A1M1A4S1S0S3S35Vflags;Vm;S29Vlen;A1A3S7A3S0G0R2S27SfS12Vaddr;S4S6S1eQ40A1M2S5S1eQ8A1A1A2A1SaS6G2G2A2M3SbG2G2Vaddr;Vn;A4S4G3A1M4A3G4S4S10A1S4S6G2S9A2A1A6S2bVflags;Vm;Vlen;Vaddr;A4G1A4A3A2A2F_;FR;").
  Proof using Halign Hceil Hfresh Hlen Hno Hnot_fn Hnot_frw Hnot_none Hnot_nrn Hnot_rw Hpos Hshape.
    intros R Hs. apply spec_check in Hs. destruct R as [eff m' evs|]; cbn in Hs.
    - rewrite mmap_noreplace_rw_fresh_reduce in Hs.
      destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
      destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
      destruct (errno_ret_in (mmap_errnos_when (mmap_fixed_fresh_refusable flags m (mmap_nZ len))) r) eqn:E.
      + unfold mmap_errnos_when in E.
        apply errno_ret_in_true in E as (e & Hin & ->). destruct Hin as [<-|[]].
        destruct zs; [|discriminate]. inversion Hs; subst. left. reflexivity.
      + destruct (bv_eqb r addr && listNN_eqb zs [(addr, n)] && mmap_noreserve_backed_ok flags m (mmap_nZ len)) eqn:G; [|discriminate].
        apply andb_true_iff in G as [G G3]. apply andb_true_iff in G as [G1 G2].
        apply bv_eqb_eq in G1. apply listNN_eqb_eq in G2.
        subst. inversion Hs; subst. right. split; [exact G3|reflexivity].
    - exfalso. specialize (Hs probe_eff). rewrite mmap_noreplace_rw_fresh_reduce in Hs. unfold probe_eff in Hs.
      destruct (errno_ret_in (mmap_errnos_when (mmap_fixed_fresh_refusable flags m (mmap_nZ len))) (Z_to_bv 64 0)); [discriminate|].
      destruct (bv_eqb (Z_to_bv 64 0) addr && listNN_eqb [] [(addr, n)] && mmap_noreserve_backed_ok flags m (mmap_nZ len)); discriminate.
  Qed.

  Lemma mmap_noreplace_rw_fresh_intro_fail_ss : ltac2:(tb__ "0|2|
S0S3S38Vflags;Vm;S29Vlen;A1A3S7A3S2eVi;Vm;S27SfS12S15S14A1S4S6S1eQ40A1M0S5S1eQ8A1A1A2A1S4S6G0G0A2A1M1G1S4S10A1S4S6G0S9A2A1A6Vm;S4S11A1A4A3F_;").
  Proof using Halign Hceil Hfresh Hlen Hno Hnot_fn Hnot_frw Hnot_none Hnot_nrn Hnot_rw Hpos Hshape.
    intros Hrf. apply check_spec_ok. rewrite mmap_noreplace_rw_fresh_reduce. rewrite Hrf. unfold mmap_errnos_when.
    rewrite (errno_ret_in_intro mmap_errnos ENOMEM ltac:(left; reflexivity)). reflexivity.
  Qed.

  Lemma mmap_noreplace_rw_fresh_intro_fail : ltac2:(tb__ "0|2|
S0S3S38Vflags;Vm;S29Vlen;A1A3S7A3S4bVi;Vm;S27SfS12S15S14A1S4S6S1eQ40A1M0S5S1eQ8A1A1A2A1S4S6G0G0A2A1M1G1S4S10A1S4S6G0S9A2A1A6Vm;S4S11A1A4A3F_;").
  Proof using Halign Hceil Hfresh Hlen Hno Hnot_fn Hnot_frw Hnot_none Hnot_nrn Hnot_rw Hpos Hshape.
    intros. split; [eapply mmap_noreplace_rw_fresh_intro_fail_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. apply ns_forced_mmap; [assumption|]. intros ? ? ? Hs'. destruct (mmap_noreplace_rw_fresh_inv _ Hs') as [He | (Hb & E')]; [unfold is_ret in He; inversion He; subst; reflexivity | exfalso; match goal with F : mmap_fixed_fresh_refusable _ _ _ = true |- _ => unfold mmap_fixed_fresh_refusable in F; rewrite Hb in F; discriminate F end].
  Qed.

  Lemma mmap_noreplace_rw_fresh_intro_ok_ss : ltac2:(tb__ "0|3|
S0S3S35Vflags;Vm;S29Vlen;A1A3S7A3S2eVi;Vm;S27SfS12Vaddr;S4S6S1eQ40A1M0S5S1eQ8A1A1A2A1SaS6G0G0A2M1SbG0G0Vaddr;Vn;A4S4G1A1M2A3G2S4S10A1S4S6G0S9A2A1A6S2bVflags;Vm;Vlen;Vaddr;A4S4S11A1A4A3F_;").
  Proof using Halign Hceil Hfresh Hlen Hno Hnot_fn Hnot_frw Hnot_none Hnot_nrn Hnot_rw Hpos Hshape.
    intros Hb. apply check_spec_ok. rewrite mmap_noreplace_rw_fresh_reduce.
    rewrite (mmap_place_not_errno_when _ _ addr (mmap_nZ len) (mmap_nZ_nonneg len) Hceil).
    rewrite bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl), Hb. reflexivity.
  Qed.

  Lemma mmap_noreplace_rw_fresh_intro_ok : ltac2:(tb__ "0|3|
S0S3S35Vflags;Vm;S29Vlen;A1A3S7A3S4bVi;Vm;S27SfS12Vaddr;S4S6S1eQ40A1M0S5S1eQ8A1A1A2A1SaS6G0G0A2M1SbG0G0Vaddr;Vn;A4S4G1A1M2A3G2S4S10A1S4S6G0S9A2A1A6S2bVflags;Vm;Vlen;Vaddr;A4S4S11A1A4A3F_;").
  Proof using Halign Hceil Hfresh Hlen Hno Hnot_fn Hnot_frw Hnot_none Hnot_nrn Hnot_rw Hpos Hshape.
    intros. split; [eapply mmap_noreplace_rw_fresh_intro_ok_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. pose proof (mmap_place_not_errno _ addr (mmap_nZ len) (mmap_nZ_nonneg len) Hceil) as Hnot. apply ns_nonenomem_mmap; [assumption|]. cbn [eff_ret]. intro E. rewrite E in Hnot. vm_compute in Hnot. discriminate Hnot.
  Qed.
End MmapNoreplaceRwFresh.

Section MmapNoreplaceNoneFresh.
  Variables (i : SyscallInput) (m : Model).
  Hypothesis Hno : bv_unsigned (in_sysno i) = 222%Z.
  Let addr := in_arg i 0.
  Let len := in_arg i 1.
  Let flags := in_arg i 3.
  Let h := m_vmmaps m.
  Let n := mmap_n len.
  Hypothesis Hlen : len <> Z_to_bv 64 0.
  Hypothesis Hshape : ltac2:(tb__ "0|0|
S0S3S36SeVi;U2A2SeVi;U3A2SeVi;U5A2A3S7A3").
  Hypothesis Hnot_frw : ltac2:(tb__ "0|0|
S0S3S32SeVi;U2A2SeVi;U3A2SeVi;U5A2A3S8A3").
  Hypothesis Hnot_fn : ltac2:(tb__ "0|0|
S0S3S2fSeVi;U2A2SeVi;U3A2SeVi;U5A2A3S8A3").
  Hypothesis Hnot_none : ltac2:(tb__ "0|0|
S0S3S31SeVi;U2A2SeVi;U3A2SeVi;U5A2A3S8A3").
  Hypothesis Hnot_rw : ltac2:(tb__ "0|0|
S0S3S30SeVi;U2A2SeVi;U3A2SeVi;U5A2A3S8A3").
  Hypothesis Hceil : ltac2:(tb__ "0|0|
S42S43S1fQ40Vaddr;A2S29Vlen;A1A2S16S17Vm;A1A1A2").
  Hypothesis Halign : ltac2:(tb__ "0|0|
S0S26S44S1fQ40Vaddr;A2S18A2Z0A3").
  Hypothesis Hpos : (0 < bv_unsigned addr)%Z.
  Hypothesis Hfresh : ltac2:(tb__ "0|1|
S0S3S13SdS6S1eQ40A1M0G0A2S1aVh;A1S19Vh;A1A3Vaddr;Vn;A3S7A3").

  Lemma mmap_noreplace_none_fresh_reduce : ltac2:(tb__ "0|c|
SfS0S21S46Vi;R1Vm;A3SfS21Leff;R1S1eQ40M0A1M1S5S6G1S5S1eQ8A1A1A2M2A1M3S5S6G1G1A2M4A1M5G5S5S10A1M6S5S6G1S9A2M7A1M8G3S21Leff_writes;R5G5S21Leff_zeros;R4G6S21Leff_copies;R2G8S21Leff_copyins;R1S3S21L_;M9S24S34S8A1R6A2G5S21Lus;R3S23Vm;S4S11A1MaA2G4G5S22Ll;Lp;MbX5x2G9ScS47G0R6Vaddr;A3S25R3SaG4SbG1G1Vaddr;Vn;A4S4G4A1A3A2A2S23S2aVflags;Vm;Vlen;Vaddr;A4GaA2S22X3x2X3x2G7G8S22Ll;Lp;X5x2S10G6S22Ll;Lm0;X5x2GbX5x2G2G3S22Ll;Lp;X5x2Leff_copyins;Leff_copies;Lus;Leff_zeros;Leff_writes;Lr;Xfx1A3Feff;").
  Proof using Halign Hceil Hfresh Hlen Hno Hnot_fn Hnot_frw Hnot_none Hnot_rw Hpos Hshape.
    intros eff. rewrite (mmap_check i m Hno). unfold check_mmap.
    destruct (mmap_noreplace_noaccess_b_gates _ _ _ Hshape) as [G1 G2].
    rewrite G1, G2, (mmap_len_gate i Hlen), Hnot_rw, Hnot_none, Hnot_fn, Hnot_frw, Hshape.
    unfold n, h, len, addr, flags, mmap_n, mmap_nZ, mmap_none_model, mmap_none_vm in *. cbv zeta.
    pose proof (alloc_top_lt (m_vmmaps m)) as Hc.
    destruct (two_pow_64 <=? bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)))%Z eqn:E1.
    { apply Z.leb_le in E1. lia. }
    rewrite (proj2 (Z.leb_le _ _) Hceil). cbn [negb].
    rewrite Halign. cbn [Z.eqb negb].
    rewrite (proj2 (Z.ltb_lt _ _) Hpos). cbn [negb].
    rewrite Hfresh. reflexivity.
  Qed.

  Lemma mmap_noreplace_none_fresh_inv : ltac2:(tb__ "0|5|
S28SfA1M0S2eVi;Vm;R1A3S2S2cR2S15S14A1Vm;S4S11A1M1A4S0G0R2S27SfS12Vaddr;S4S6S1eQ40A1M2S5S1eQ8A1A1A2A1S4S6G2G2A2M3A1M4SaG3SbG2G2Vaddr;Vn;A4G4A3S4S10A1S4S6G2S9A2A1A6S2aVflags;Vm;Vlen;Vaddr;A4G1A4A3A2F_;FR;").
  Proof using Halign Hceil Hfresh Hlen Hno Hnot_fn Hnot_frw Hnot_none Hnot_rw Hpos Hshape.
    intros R Hs. apply spec_check in Hs. destruct R as [eff m' evs|]; cbn in Hs.
    - rewrite mmap_noreplace_none_fresh_reduce in Hs.
      destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      destruct (errno_ret_in (mmap_errnos_when false) r) eqn:E.
      + destruct us; [|discriminate]. unfold mmap_errnos_when in E.
        apply errno_ret_in_true in E as (e & Hin & ->). destruct Hin as [<-|[]].
        inversion Hs; subst. left. reflexivity.
      + destruct (bv_eqb r addr && listNN_eqb us [(addr, n)]) eqn:G; [|discriminate].
        apply andb_true_iff in G as [G1 G2]. apply bv_eqb_eq in G1. apply listNN_eqb_eq in G2.
        subst. inversion Hs; subst. right. reflexivity.
    - exfalso. specialize (Hs probe_eff). rewrite mmap_noreplace_none_fresh_reduce in Hs. unfold probe_eff in Hs.
      unfold mmap_errnos_when in Hs. change (errno_ret_in mmap_errnos (Z_to_bv 64 0)) with false in Hs.
      destruct (bv_eqb (Z_to_bv 64 0) addr && listNN_eqb [] [(addr, n)]); discriminate.
  Qed.

  Lemma mmap_noreplace_none_fresh_intro_ok_ss : ltac2:(tb__ "0|3|
S2eVi;Vm;S27SfS12Vaddr;S4S6S1eQ40A1M0S5S1eQ8A1A1A2A1S4S6G0G0A2M1A1M2SaG1SbG0G0Vaddr;Vn;A4G2A3S4S10A1S4S6G0S9A2A1A6S2aVflags;Vm;Vlen;Vaddr;A4S4S11A1A4A3").
  Proof using Halign Hceil Hfresh Hlen Hno Hnot_fn Hnot_frw Hnot_none Hnot_rw Hpos Hshape.
    apply check_spec_ok. rewrite mmap_noreplace_none_fresh_reduce.
    rewrite (mmap_place_not_errno_when _ _ addr (mmap_nZ len) (mmap_nZ_nonneg len) Hceil).
    rewrite bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
  Qed.

  Lemma mmap_noreplace_none_fresh_intro_ok : ltac2:(tb__ "0|3|
S4bVi;Vm;S27SfS12Vaddr;S4S6S1eQ40A1M0S5S1eQ8A1A1A2A1S4S6G0G0A2M1A1M2SaG1SbG0G0Vaddr;Vn;A4G2A3S4S10A1S4S6G0S9A2A1A6S2aVflags;Vm;Vlen;Vaddr;A4S4S11A1A4A3").
  Proof using Halign Hceil Hfresh Hlen Hno Hnot_fn Hnot_frw Hnot_none Hnot_rw Hpos Hshape.
    intros. split; [eapply mmap_noreplace_none_fresh_intro_ok_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. pose proof (mmap_place_not_errno _ addr (mmap_nZ len) (mmap_nZ_nonneg len) Hceil) as Hnot. apply ns_nonenomem_mmap; [assumption|]. cbn [eff_ret]. intro E. rewrite E in Hnot. vm_compute in Hnot. discriminate Hnot.
  Qed.
End MmapNoreplaceNoneFresh.
