(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (openat_rd_rob added, openat's robustness at a larger read-only backing for the frame obligation's new premise, LPS 75d69e00, with the read lemmas it uses; cstr_no_slash and cstr_no_slash_of_eq written as plain text, a faulting path read now False; RomBase required). *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "True"; "or"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "read_cstr"; "cstr_result"; "errno_ret"; "event"; "FdEntry"; "in_argv"; "CstrOk"; "EFAULT"; "ENAMETOOLONG"; "ENOENT"; "ProcInput"; "alloc_fd"; "fd_lookup"; "m_fds"; "m_fs"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@Corelib.Init.Datatypes"; "list"; "bool"; "false"; "option"; "pair"; "Some"; "length"; "nil"; "None"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "ms_read_byte"; "machine_state"; "ms_svc_pending"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "reg_sv"; "SLit"; "sv"; "valuation"; "ss_next"; "eval"; "agree_below"; "ss_pc"; "sstate"; "SVar"; "ss_objs"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "sys_input"; "valid_argv"; "valid_input_either"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysOpen"; "cstr_no_slash"; "openat_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "model_idle"; "world"; "wstep"; "etriple"; "triple1"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "path_eqb"; "path"; "fs_lookup"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei"; "path_has_slash"; "dotdot_path"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open"; "open_ignored_flags"; "path_is_dirref"; "openat_errnos"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall"; "fd32"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi"; "AT_FDCWD32"; "dot_path"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "ok_frameJ"; "@Stdlib.ZArith.BinInt.Z"; "ldiff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "smatch_pending"; "rho_set_rw"; "S_after"; "ok_pframeJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysOpen.WithSegs"; "AT_FDCWD_word"; "O_RD_LARGEFILE"; "S_after_open"; "@Corelib.Init.Peano"; "le"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "after_sys"; "only_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "openat_dir_model"; "openat_file_model"; "@Stdlib.Lists.List"; "In"; "@Stdlib.PArith.BinPos.Pos"; "succ"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess Uapi Syscall.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
(* LPS 75d69e00: [openat_rd_rob] below needs RomBase by name; RomBase depends on the model
   only, so there is no cycle. *)
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require RomBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundW
  SymSoundF SymSoundR SymComplete SymCall SymEntail SymExit SymFrame SymBytes Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(** LPS 75d69e00: the FAULT arm is [False], where it used to be [True].

    [ok_pframe]'s new fourth premise, [RomBase.sys_rob], says the specification is the same
    at every LARGER read-only backing, and for openat that is simply FALSE at a state whose
    pathname does not read: [rom_ext] only grows the backing ([RomBase.ms_read_byte_wrom_ext],
    RomBase.v:59-64), so an extension can turn [CstrFault] into [CstrOk] and change the check
    from EFAULT to an open.  No weaker premise rules that out, and no invariant elsewhere in
    this tree supplies it: the path is read from wherever argument 1 points.

    Strengthening THIS premise rather than adding a new one is free at every call site, which
    is the whole reason it is the right move.  All four discharges -- P/Drv_open__G1.v:389,
    U/Drv_open__G1.v:388, A/DrvM.v:403, B/DrvM.v:412 -- end in
    [destruct (length argv1 <? 4096)%nat; [exact Hnsl | exact I]], because the pathname they
    hand openat is [arg1_cstr] / [cstr1], which is [CstrOk argv1] or [CstrTooLong] by
    construction (Lib/InitArg1.v:137) and is NEVER [CstrFault].  Their text is unchanged. *)
Definition cstr_no_slash (c : cstr_result) : Prop :=
  match c with
  | CstrOk p => path_has_slash p = false
  | CstrTooLong => True
  | CstrFault => False
  end.

Lemma cstr_no_slash_not_fault : forall c, cstr_no_slash c -> c <> CstrFault.
Proof using . intros [p| |] H; [discriminate | discriminate | destruct H]. Qed.

Lemma valid_argv_arg1_plain : ltac2:(tb__ "0|3|
S18S18S15Q8A1M0A1M1A1S34R1A1S55U2S1eG1R2A2A2S1S0S19S40S56G1U1R3S1fG0A1A4M2A1S1aA3S0S19S3dG2S41A2S1aA3A2F_;F_;Fargv;").
Proof.
  intros argv (_ & _ & _ & _ & Htl) Hlen.
  destruct argv as [|a0 [|a1 r]]; cbn in Hlen; try lia. cbn.
  cbn in Htl. apply Forall_inv in Htl. exact Htl.
Qed.

Lemma valid_input_arg1_plain : ltac2:(tb__ "0|3|
S10S35R1A1S55U2S1eS18S15Q8A1M0A1M1SbR2A1A2A2S1S0S19S40S56G1U1SbR3A1S1fG0A1A4M2A1S1aA3S0S19S3dG2S41A2S1aA3A2F_;F_;Finp;").
Proof. intros inp [Hargv _] Hlen. apply valid_argv_arg1_plain; assumption. Qed.

Lemma path_is_dirref_not_dotdot : ltac2:(tb__ "0|0|
S3eS0S19S3dR1S41A2S1aA3S0S19S43R2A1S3dR2S47A2A3F_;Fp;").
Proof. intros p H. unfold path_is_dirref. rewrite H, Bool.orb_false_r. reflexivity. Qed.

(* LPS 75d69e00: restated in plain Coq with a [c <> CstrFault] premise, because
   [cstr_no_slash]'s fault arm is now [False] and the old statement is FALSE without it:
   [CstrFault] satisfies both of its hypotheses vacuously.  It has NO callers at this sha
   (`git grep -nw cstr_no_slash_of_eq` returns only this definition; must-fire control
   `path_is_dirref_not_dotdot` returns 11 hits in 5 files), so the premise costs nothing.
   This producer is in SysOpen.v itself, not in the drivers, so a sweep of the drivers
   alone does not find it. *)
Lemma cstr_no_slash_of_eq : forall (c : cstr_result) (a : path),
  path_has_slash a = false ->
  (forall p, c = CstrOk p -> p = a) ->
  c <> CstrFault ->
  cstr_no_slash c.
Proof.
  intros [p| |] a Ha He Hnf; cbn; [| exact I | exfalso; apply Hnf; reflexivity].
  rewrite (He p eq_refl). exact Ha.
Qed.

Definition openat_post (md : Model) (c : cstr_result) (r : word) (md' : Model) : Prop := ltac2:(tb__ "0|a|
S7OLc;Vc;S18S15Q8A1M0A1M1G1OLp;R1S1S0S15Q40A1M2Vr;S8SfA1A3S0S5Vmd';Vmd;A3M3A2M4G0G1S19OL_;S43R3A1S4S2S25S25S1S5cS25R1S44A3S1S0G2Vr;S8R1A1A3G3A2A2Le;A2M5S1S0S1bSaA1S12S13Vmd;A1M6S11G6A1M7A2S20SaA1A3M8S1S0G2Vr;G7A3M9S0S5Vmd';S5aVmd;A1A3A2A2A2S1bG1A1OLx;S3fS14Vmd;A1R3A2G1S4G5S1G8S1G9S0S5Vmd';S5bVmd;R4A2A3A2A2A2Ll;G4X1bx2X19x2Ll;Lb;X18x2Lp;S1S0G2Vr;S8SeA1A3G3A2S1S0G2Vr;S8SdA1A3G3A2X7x3").

Lemma openat_post_idle : ltac2:(tb__ "0|0|
S5S7S15Q40A1S5S38R4A1S37R5R4R3R2A4S38R3A1F_;F_;Fmd';Fr;Fc;Fmd;").
Proof.
  intros md c r md' Hi H. unfold openat_post in H.
  destruct c as [[|b p]| |]; try (destruct H as [_ ->]; exact Hi).
  cbn iota in H. destruct (path_is_dirref (b :: p)).
  - destruct H as [(e & _ & _ & ->)|(_ & _ & ->)]; [exact Hi | apply with_fds_idle; exact Hi].
  - destruct (fs_lookup (m_fs md) (b :: p)).
    + destruct H as [(e & _ & _ & ->)|(_ & _ & ->)]; [exact Hi | apply with_fds_idle; exact Hi].
    + destruct H as [_ ->]; exact Hi.
Qed.

Section Step.
  Variable segs : list Segment.

  Lemma wstep_openat_rd_inv : ltac2:(tb__ "0|4|
S18S9A1M0S23S5S15Q40M1A1M2S39S0S1bG2A1S24R4A1S1dG2R2A2A3S38R4A1S0S25S16G1R4A2Z38A3S0S25S4dS16G1S21R7U2A2A2S42A2Z0A3S0G2S45S21R8U0A2A1S46A3S36S6S22R9A1S21R9U1M3A2A2A1S3aVsegs;S1cG0S31RbS32RaR9A2A4R7A3S2G2G2S2S5S5S1S37RcS6S22RdA1S21RdG3A2A2R2R1A4S0S39RaS1cG0S31ReS32S57RdR2A2R1A2A4A3A2Lm';A2Lr;A2F_;F_;F_;F_;F_;F_;F_;Fw';Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 w' Hp Hi Hno Hfl Hdir Hns Hw.
    destruct (read_cstr (ms_read_byte ms) (ms_gpr ms 1)) as [[|b p]| |] eqn:Hc.
    - exists (errno_ret ENOENT), m. split; [cbn; auto|].
      exact (@wstep_openat_patherr_inv segs tr ms m x8 ENOENT w' Hp Hi Hno Hfl ltac:(rewrite Hc; reflexivity) Hw).
    - cbn [openat_post]. cbn in Hns. destruct (path_is_dirref (b :: p)) eqn:Hd.
      + destruct (@wstep_openat_dirref_inv segs tr ms m x8 (b :: p) w' Hp Hi Hno Hfl Hdir Hc Hd Hw) as [(e & Hin & ->)|(Hfree & ->)].
        * exists (errno_ret e), m. split; [left; exists e; auto | reflexivity].
        * exists (alloc_fd (m_fds m)), (openat_dir_model m). split; [right; auto | reflexivity].
      + destruct (fs_lookup (m_fs m) (b :: p)) as [data|] eqn:Hfs.
        * destruct (@wstep_openat_file_inv segs tr ms m x8 b p data w' Hp Hi Hno Hfl Hdir Hc Hd Hns Hfs Hw) as [(e & Hin & ->)|(Hfree & ->)].
          -- exists (errno_ret e), m. split; [left; exists e; auto | reflexivity].
          -- exists (alloc_fd (m_fds m)), (openat_file_model m (b :: p)). split; [right; auto | reflexivity].
        * exists (errno_ret ENOENT), m. split; [auto|].
          exact (@wstep_openat_absent_inv segs tr ms m x8 b p w' Hp Hi Hno Hfl Hdir Hc Hd Hns Hfs Hw).
    - exists (errno_ret ENAMETOOLONG), m. split; [cbn; auto|].
      exact (@wstep_openat_patherr_inv segs tr ms m x8 ENAMETOOLONG w' Hp Hi Hno Hfl ltac:(rewrite Hc; reflexivity) Hw).
    - exists (errno_ret EFAULT), m. split; [cbn; auto|].
      exact (@wstep_openat_patherr_inv segs tr ms m x8 EFAULT w' Hp Hi Hno Hfl ltac:(rewrite Hc; reflexivity) Hw).
  Qed.

  Lemma wstep_openat_rd_intro : ltac2:(tb__ "0|4|
S18S9A1M0S23S5S15Q40M1A1M2G2S5S0S1bG2A1S24R5A1S1dG2R3A2A3S38R5A1S0S25S16G1R5A2Z38A3S0S25S4dS16G1S21R8U2A2A2S42A2Z0A3S0G2S45S21R9U0A2A1S46A3S36S6S22RaA1S21RaU1M3A2A2A1S37RaS6S22RbA1S21RbG3A2A2R8R7A4S3aVsegs;S1cG0S31RdS32RcRbA2A4S1cG0S31RdS32S57RcR9A2R8A2A4A3F_;F_;F_;F_;F_;F_;F_;Fm';Fr;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 r m' Hp Hi Hno Hfl Hdir Hns H.
    destruct (read_cstr (ms_read_byte ms) (ms_gpr ms 1)) as [[|b p]| |] eqn:Hc.
    - destruct H as [-> ->]. exact (@wstep_openat_patherr_intro segs tr ms m x8 ENOENT Hp Hi Hno Hfl ltac:(rewrite Hc; reflexivity)).
    - cbn [openat_post] in H. cbn in Hns. destruct (path_is_dirref (b :: p)) eqn:Hd.
      + destruct H as [(e & Hin & -> & ->)|(Hfree & -> & ->)].
        * exact (@wstep_openat_dirref_intro_err segs tr ms m x8 (b :: p) e Hp Hi Hno Hfl Hdir Hc Hd Hin).
        * exact (@wstep_openat_dirref_intro_ok segs tr ms m x8 (b :: p) Hp Hi Hno Hfl Hdir Hc Hd Hfree).
      + destruct (fs_lookup (m_fs m) (b :: p)) as [data|] eqn:Hfs.
        * destruct H as [(e & Hin & -> & ->)|(Hfree & -> & ->)].
          -- exact (@wstep_openat_file_intro_err segs tr ms m x8 b p data e Hp Hi Hno Hfl Hdir Hc Hd Hns Hfs Hin).
          -- exact (@wstep_openat_file_intro_ok segs tr ms m x8 b p data Hp Hi Hno Hfl Hdir Hc Hd Hns Hfs Hfree).
        * destruct H as [-> ->]. exact (@wstep_openat_absent_intro segs tr ms m x8 b p Hp Hi Hno Hfl Hdir Hc Hd Hns Hfs).
    - destruct H as [-> ->]. exact (@wstep_openat_patherr_intro segs tr ms m x8 ENAMETOOLONG Hp Hi Hno Hfl ltac:(rewrite Hc; reflexivity)).
    - destruct H as [-> ->]. exact (@wstep_openat_patherr_intro segs tr ms m x8 EFAULT Hp Hi Hno Hfl ltac:(rewrite Hc; reflexivity)).
  Qed.

  Lemma openat_rd_only_ok : ltac2:(tb__ "0|2|
S23S5S15Q40M0A1M1S38R2A1S0S25S16G0R2A2Z38A3S0S25S4dS16G0S21R5U2A2A2S42A2Z0A3S0G1S45S21R6U0A2A1S46A3S36S6S22R7A1S21R7U1A2A2A1S58S33Vsegs;R8R6A3R7A2F_;F_;F_;F_;F_;Fx8;Fm;Fms;").
  Proof using .
    intros ms m x8 Hi Hno Hfl Hdir Hns.
    destruct (read_cstr (ms_read_byte ms) (ms_gpr ms 1)) as [[|b p]| |] eqn:Hc.
    - exact (@openat_patherr_only_ok segs ms m x8 ENOENT Hi Hno Hfl ltac:(rewrite Hc; reflexivity)).
    - cbn in Hns. destruct (path_is_dirref (b :: p)) eqn:Hd.
      + exact (@openat_dirref_only_ok segs ms m x8 (b :: p) Hi Hno Hfl Hdir Hc Hd).
      + destruct (fs_lookup (m_fs m) (b :: p)) as [data|] eqn:Hfs.
        * exact (@openat_file_only_ok segs ms m x8 b p data Hi Hno Hfl Hdir Hc Hd Hns Hfs).
        * exact (@openat_absent_only_ok segs ms m x8 b p Hi Hno Hfl Hdir Hc Hd Hns Hfs).
    - exact (@openat_patherr_only_ok segs ms m x8 ENAMETOOLONG Hi Hno Hfl ltac:(rewrite Hc; reflexivity)).
    - exact (@openat_patherr_only_ok segs ms m x8 EFAULT Hi Hno Hfl ltac:(rewrite Hc; reflexivity)).
  Qed.

  (** ** [RomBase.sys_rob] for openat (56)

      56 is not in [RomBase.memfree_lit] and must not be: [memfree 56] is FALSE, because
      [Open.check_openat_body] reads the pathname out of [in_mem].  [RomBase.sys_rob] asks
      only that the check agree at a LARGER backing, and it does -- but ONLY when the path
      read succeeds, which is what [cstr_no_slash]'s [CstrFault] arm now gives.

      [RomBase.with_mem] changes the memory field alone, so these two hold by conversion. *)
  Lemma in_arg_with_mem : forall i mp k, in_arg (RomBase.with_mem i mp) k = in_arg i k.
  Proof using . reflexivity. Qed.

  Lemma in_mem_with_mem : forall i mp, in_mem (RomBase.with_mem i mp) = mp.
  Proof using . reflexivity. Qed.

  (** A lemma ABOUT a model definition, written in this tree's proof library: nothing under
      [theories/] changes.  [Open.check_openat_body] (75d69e00
      theories/LinuxProcessSem/Checks/Sys/Fs/Open.v:482-493) reads [in_mem] in exactly one
      place, [read_cstr (in_mem i) pathp]; every arm below that is a function of the decoded
      path, the flags, the effect and the model.  So it is constant on memories that answer
      that read the same way, which by [RomBase.read_cstr_ext] (RomBase.v:169) is every
      larger one -- PROVIDED the read does not fault.  Without that proviso the statement is
      FALSE, not merely unprovable: a larger backing can map a byte the smaller one did not
      and turn EFAULT into an open. *)
  Lemma check_openat_body_with_mem : forall i mp dirfd pathp flags eff m,
    RomBase.mem_ext (in_mem i) mp ->
    read_cstr (in_mem i) pathp <> CstrFault ->
    Open.check_openat_body (RomBase.with_mem i mp) dirfd pathp flags eff m
      = Open.check_openat_body i dirfd pathp flags eff m.
  Proof using .
    intros i mp dirfd pathp flags eff m Hx Hnf.
    unfold Open.check_openat_body. rewrite in_mem_with_mem.
    rewrite (RomBase.read_cstr_ext (in_mem i) mp pathp Hx Hnf). reflexivity.
  Qed.

  (** The copy-in record openat claims is the same prefix, by [cstr_access_len_aux_ext]
      (RomBase.v:159) under the same proviso. *)
  Lemma openat_reads_with_mem : forall i mp,
    RomBase.mem_ext (in_mem i) mp ->
    read_cstr (in_mem i) (in_arg i 1) <> CstrFault ->
    openat_reads (RomBase.with_mem i mp) = openat_reads i.
  Proof using .
    intros i mp Hx Hnf. unfold openat_reads. cbv zeta.
    rewrite !in_arg_with_mem, in_mem_with_mem.
    rewrite (RomBase.cstr_access_len_aux_ext path_max (in_mem i) mp (in_arg i 1) Hx Hnf).
    reflexivity.
  Qed.

  Lemma openat_rd_rob : forall ms m x8,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 56%Z ->
    Z.ldiff (bv_unsigned (ms_gpr ms 2)) open_ignored_flags = 0%Z ->
    cstr_no_slash (read_cstr (ms_read_byte ms) (ms_gpr ms 1)) ->
    RomBase.sys_rob segs (mkCfg ms m).
  Proof using .
    intros ms m x8 Hp Hno Hfl Hns.
    pose proof (cstr_no_slash_not_fault _ Hns) as Hnf.
    eapply RomBase.sys_rob_of_mem_ext; [exact Hp|]. intros mp Hx eff.
    rewrite (@openat_check (RomBase.with_mem (sys_input segs ms x8) mp) m Hno Hfl eff),
            (@openat_check (sys_input segs ms x8) m Hno Hfl eff).
    (* the section's [dirfd]/[pathp] may survive discharge as let-ins in the statement *)
    cbv zeta.
    rewrite !in_arg_with_mem.
    rewrite (openat_reads_with_mem (sys_input segs ms x8) mp Hx Hnf).
    rewrite (check_openat_body_with_mem (sys_input segs ms x8) mp
               (fd32 (in_arg (sys_input segs ms x8) 0)) (in_arg (sys_input segs ms x8) 1)
               (in_arg (sys_input segs ms x8) 2) (clear_copyins eff) m Hx Hnf).
    reflexivity.
  Qed.
End Step.

Section WithSegs.
Variable segs : list Segment.

Definition AT_FDCWD_word : Z := 2 ^ 64 - 100.

Definition O_RD_LARGEFILE : Z := 32768.

Lemma ldiff_rd_largefile : ltac2:(tb__ "0|1|
S0S25S4dS16Q40M0S17G0S53A2A2S42A2Z0A3").
Proof using . vm_compute. reflexivity. Qed.

Lemma fd32_at_fdcwd_word : ltac2:(tb__ "0|1|
S0S15Q40M0A1S45S17G0S52A2A1S46A3").
Proof using . apply fd32_AT_FDCWD. vm_compute. reflexivity. Qed.

Definition S_after_open (S : sstate) : sstate := ltac2:(tb__ "0|1|
S50VS;S2fS2aVS;A1M0A1S30VS;A1S5dG0A1A4").

Lemma triple1_openatJ : ltac2:(tb__ "0|2|
S39OF_;S4bS4bS2eS29S4cVsegs;R5R4A3S51Vsegs;R6R5A3S0S1bS48A1S59Vsegs;S2dR4A1A2S1dS48S49A2A3S0S28S26R5Z11A2S27Z38A1A3S0S28S26R6ZaA2S27S52A1A3S0S28S26R7ZcA2S27S53A1A3S18S9A1M0S23S5S4eVsegs;RaRbS1cG0S31R3S32R2R1A2A4A4ReRbR4R2A3S36S6S22R4A1S2bRcS26RdZbM1A2A2A2A1F_;F_;Fmd;Fms;Ftr;G0S23S5S15Q40A1S5S4eVsegs;RdReS1cG0S31R5S32R4R3A2A4A4R11ReR6R4A3S37R5S6S22R6A1S2bRfS26R10G1A2A2A2R4R3A4R12S4fR10S2aR11A1R5A3R8R4A3F_;F_;F_;Fmd';Fr;Fmd;Fms;Ftr;S3cVsegs;RdS4aVsegs;RcRaR9A4S39S2S29S29S1S2cS2aRcA1RbR1A3S4aVsegs;RdS54RcA1R1R2A5A2Lrho';A2Lw;A4F_;F_;F_;F_;F_;F_;F_;F_;Frho;FS;FJ';FJ;Fok;").
Proof using .
  intros ok J J' S rho Hokf Hokp Hi H17 H10 H12 HNS HK.
  apply triple1_ecall_detJ; [exact Hokf | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 0 Hsp ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite H10 in G0. cbn [eval] in G0.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 1 Hsp ltac:(lia)) as G1. change (10 + Z.of_nat 1) with 11 in G1.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 2 Hsp ltac:(lia)) as G2. change (10 + Z.of_nat 2) with 12 in G2. rewrite H12 in G2. cbn [eval] in G2.
  assert (H56 : bv_unsigned (Z_to_bv 64 56) = 56%Z) by reflexivity.
  assert (Hfl : Z.ldiff (bv_unsigned (ms_gpr ms 2)) open_ignored_flags = 0%Z) by (rewrite G2; apply ldiff_rd_largefile).
  assert (Hdir : fd32 (ms_gpr ms 0) = AT_FDCWD32) by (rewrite G0; apply fd32_at_fdcwd_word).
  split.
  (* LPS 75d69e00: [ok_pframe]'s fourth premise.  openat is 56 and 56 is NOT in
     [RomBase.memfree_lit] -- [memfree 56] is FALSE, the path is read out of [in_mem] -- so
     [RomBase.rob_auto] cannot close it.  [openat_rd_rob] does, and it is the reason
     [cstr_no_slash]'s fault arm is [False]: at a faulting path the premise is not merely
     hard, it is false. *)
  - eapply Hokp;
      first
        [ solve [ exact Hk ]
        | solve [ exact Hp ]
        | solve [ eapply openat_rd_only_ok; [exact Hh | exact H56 | exact Hfl | exact Hdir | rewrite G1; exact (HNS tr ms md Hsp Hk)] ]
        | solve [ eapply openat_rd_rob; [exact Hp | exact H56 | exact Hfl | rewrite G1; exact (HNS tr ms md Hsp Hk)] ] ].
  - intros w' Hw.
    destruct (wstep_openat_rd_inv segs tr ms md _ w' Hp Hh H56 Hfl Hdir ltac:(rewrite G1; exact (HNS tr ms md Hsp Hk)) Hw) as (r & md' & Hpost & ->).
    assert (Hag : agree_below (ss_next S) rho (rho_set_rw rho (ss_next S) r)) by (apply agree_below_set_rw; lia).
    exists (rho_set_rw rho (ss_next S) r). split; [exact Hag|].
    split.
    + unfold S_after_open. eapply smatch_after_ret; [exact Hsp | exact (openat_post_idle _ _ _ _ Hh Hpost)].
    + eapply HK; [exact Hsp | exact Hk |]. rewrite <- G1. exact Hpost.
Qed.

Lemma etriple_openatJ : ltac2:(tb__ "0|3|
S4bS4bS2eS29S0S1bS48A1S59Vsegs;S2dR2A1A2S1dS48S49A2A3S0S28S26R3Z11A2S27Z38A1A3S0S28S26R4ZaA2S27S52A1A3S0S28S26R5ZcA2S27S53A1A3S18S9A1M0S23S5S4eVsegs;R8R9S1cG0S31R3S32R2R1A2A4A4RcR9R4R2A3S1S36S6S22R4A1S2bRaS26RbZbM1A2A2A2A1S2S15Q40A1M2G2S2S5S5S1S37R5S6S22R6A1S2bRcS26RdG1A2A2A2R2R1A4ReS4fRcS2aRdA1R2A3R7R1A3A2Lmd';A2Lr;A2A2F_;F_;Fmd;Fms;Ftr;S3bVsegs;S4aVsegs;R9R7R6A4S39S2S29S29S1S2cS2aR9A1R8R1A3S4aVsegs;RaS54R9A1R1R2A5A2Lrho';A2Lw;A3F_;F_;F_;F_;F_;Frho;FS;FJ';FJ;").
Proof using .
  intros J J' S rho Hi H17 H10 H12 HK.
  apply etriple_ecall_detJ; [exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 0 Hsp ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite H10 in G0. cbn [eval] in G0.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 1 Hsp ltac:(lia)) as G1. change (10 + Z.of_nat 1) with 11 in G1.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 2 Hsp ltac:(lia)) as G2. change (10 + Z.of_nat 2) with 12 in G2. rewrite H12 in G2. cbn [eval] in G2.
  assert (H56 : bv_unsigned (Z_to_bv 64 56) = 56%Z) by reflexivity.
  assert (Hfl : Z.ldiff (bv_unsigned (ms_gpr ms 2)) open_ignored_flags = 0%Z) by (rewrite G2; apply ldiff_rd_largefile).
  assert (Hdir : fd32 (ms_gpr ms 0) = AT_FDCWD32) by (rewrite G0; apply fd32_at_fdcwd_word).
  destruct (HK tr ms md Hsp Hk) as (Hns & r & md' & Hpost & Hk').
  rewrite <- G1 in Hpost, Hns.
  eexists. split; [exact (wstep_openat_rd_intro segs tr ms md _ r md' Hp Hh H56 Hfl Hdir Hns Hpost)|].
  assert (Hag : agree_below (ss_next S) rho (rho_set_rw rho (ss_next S) r)) by (apply agree_below_set_rw; lia).
  exists (rho_set_rw rho (ss_next S) r). split; [exact Hag|].
  split; [|exact Hk'].
  unfold S_after_open. eapply smatch_after_ret; [exact Hsp | exact (openat_post_idle _ _ _ _ Hh Hpost)].
Qed.

End WithSegs.
