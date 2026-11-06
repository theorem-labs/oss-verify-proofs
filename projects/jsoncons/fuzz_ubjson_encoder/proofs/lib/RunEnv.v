(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Run.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_RunEnv () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes6option00K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00I4ELinuxProcessSemantics?LinuxProcessSem5State;InputStream00C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsK47Corelib4Init9Datatypes4list01C4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6RunEnv8re_credsC13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Creds00c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6RunEnv6re_netC13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State8NetQueue00c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6RunEnv9re_nofileC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6RunEnv:re_sigmaskC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6RunEnv8re_abortC13~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes6option02K47Corelib4Init9Datatypes4bool02C45stdpp9bitvector;definitions7Z_to_bvK47Corelib7Numbers7BinNums1Z01c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6RunEnv8mkModelEC13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00K47Corelib4Init9Datatypes6option01c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6RunEnv:run_env_ofC13~~~K4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps01C4ELinuxProcessSemantics?LinuxProcessSem5State8in_stdinC4ELinuxProcessSemantics?LinuxProcessSem5State5in_fsI47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6RunEnv8fds_initC13~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


Class RunEnv := mkRunEnv {
  re_creds   : Creds;
  re_net     : NetQueue;
  re_urandom : InputStream;   (* [comment removed for export] *)
  re_nofile  : word;
  re_sigmask : word;
  re_abort   : bool
}.

(* [comment removed for export] *)
Definition run_env_of (inp : ProcInput) : RunEnv :=
  {| re_creds := mkCreds (in_uid inp) (in_uid inp) (in_uid inp)
                         (in_gid inp) (in_gid inp) (in_gid inp) (in_groups inp);
     re_net := in_net inp;
     re_urandom := in_urandom inp;
     re_nofile := in_nofile inp;
     re_sigmask := in_sigmask inp;
     re_abort := in_abort_terminal inp |}.

Section WithEnv.
  Context {RE : RunEnv}.

  Definition mkModelE (fds : list (word * FdEntry)) (vm : VmMaps)
      (stdin : InputStream) (fs : Fs.Fs) (halted : option word)
      (tid : option word) (rlim : option (list byte)) : Model :=
    with_abort_terminal re_abort
     (with_sigmask re_sigmask
     (with_nofile re_nofile
      (with_net re_net (with_urandom re_urandom (with_creds re_creds (mkModel fds vm stdin fs halted tid rlim)))))).

  Lemma m_fds_mkModelE : forall fds vm stdin fs halted tid rlim,
    m_fds (mkModelE fds vm stdin fs halted tid rlim) = fds.
Proof.
ltac2:(KReplay.run1 (kr_t_RunEnv ()) ["FPX_1"; "WithEnv"] "h03fdsh12fsh26haltedh34rlimh45stdinh53tidh62vmp;1p;2g0000j10Tg000Uj11Tg0013j12Tg001Vj25Tg0026j14Tg002Vj13Tg0038j26Tg003R#0#0#0R0#0#0#0#1#2R1g0047'5#4R2g004og005fg006b%31R1%10#2#4#3f6,62W3X51W2W1W4W6W0o"). Qed.
  Lemma m_vmmaps_mkModelE : forall fds vm stdin fs halted tid rlim,
    m_vmmaps (mkModelE fds vm stdin fs halted tid rlim) = vm.
Proof.
ltac2:(KReplay.run1 (kr_t_RunEnv ()) ["FPX_1"; "WithEnv"] "h03fdsh12fsh26haltedh34rlimh45stdinh53tidh62vmp;1p;2g0000j10Tg000Uj11Tg0013j12Tg001Vj25Tg0026j14Tg002Vj13Tg0038j26Tg003R#0#0#0R0#0#0#0#1#2R1g0047'5#4g004oR2g005fg006b%31R1%10#2#4#3f5,62W3X51W2W1W4W6W0o"). Qed.
  Lemma m_stdin_mkModelE : forall fds vm stdin fs halted tid rlim,
    m_stdin (mkModelE fds vm stdin fs halted tid rlim) = stdin.
Proof.
ltac2:(KReplay.run1 (kr_t_RunEnv ()) ["FPX_1"; "WithEnv"] "h03fdsh12fsh26haltedh34rlimh45stdinh53tidh62vmp;1p;2g0000j10Tg000Uj11Tg0013j12Tg001Vj25Tg0026j14Tg002Vj13Tg0038j26Tg003R#0#0#0R0#0#0#0#1#2R1g0047'5#4g004og005fR2g006b%31R1%10#2#4#3f4,62W3X51W2W1W4W6W0o"). Qed.
  Lemma m_fs_mkModelE : forall fds vm stdin fs halted tid rlim,
    m_fs (mkModelE fds vm stdin fs halted tid rlim) = fs.
Proof.
ltac2:(KReplay.run1 (kr_t_RunEnv ()) ["FPX_1"; "WithEnv"] "h03fdsh12fsh26haltedh34rlimh45stdinh53tidh62vmp;1p;2g0000j10Tg000Uj11Tg0013j12Tg001Vj25Tg0026j14Tg002Vj13Tg0038j26Tg003R#0#0#0R0#0#0#0#1#2R1g0047'5#4g004og005fg006bR2%31R1%10#2#4#3f3,62W3X51W2W1W4W6W0o"). Qed.
  Lemma m_halted_mkModelE : forall fds vm stdin fs halted tid rlim,
    m_halted (mkModelE fds vm stdin fs halted tid rlim) = halted.
Proof.
ltac2:(KReplay.run1 (kr_t_RunEnv ()) ["FPX_1"; "WithEnv"] "h03fdsh12fsh26haltedh34rlimh45stdinh53tidh62vmp;1p;2g0000j10Tg000Uj11Tg0013j12Tg001Vj25Tg0026j14Tg002Vj13Tg0038j26Tg003R#0#0#0R0#0#0#0#1#2R1g0047'5#4g004og005fg006b%31R1%10#2#4#3f2,61W3X51W2W1W4W6W0o"). Qed.
  Lemma m_tid_mkModelE : forall fds vm stdin fs halted tid rlim,
    m_tid (mkModelE fds vm stdin fs halted tid rlim) = tid.
Proof.
ltac2:(KReplay.run1 (kr_t_RunEnv ()) ["FPX_1"; "WithEnv"] "h03fdsh12fsh26haltedh34rlimh45stdinh53tidh62vmp;1p;2g0000j10Tg000Uj11Tg0013j12Tg001Vj25Tg0026j14Tg002Vj13Tg0038j26Tg003R#0#0#0R0#0#0#0#1#2R1g0047'5#4g004og005fg006b%31R1%10#2#4#3f1,61W3X51W2W1W4W6W0o"). Qed.
  Lemma m_rlimit_core_mkModelE : forall fds vm stdin fs halted tid rlim,
    m_rlimit_core (mkModelE fds vm stdin fs halted tid rlim) = rlim.
Proof.
ltac2:(KReplay.run1 (kr_t_RunEnv ()) ["FPX_1"; "WithEnv"] "h03fdsh12fsh26haltedh34rlimh45stdinh53tidh62vmp;1p;2g0000j10Tg000Uj11Tg0013j12Tg001Vj25Tg0026j14Tg002Vj13Tg0038j26Tg003R#0#0#0R0#0#0#0#1#2R1g0047'5#4g004og005fg006b%31R1%10#2#4#3R0f0,60W3X51W2W1W4W6W0o"). Qed.
  Lemma m_vm_lazy_mkModelE : forall fds vm stdin fs halted tid rlim,
    m_vm_lazy (mkModelE fds vm stdin fs halted tid rlim) = [].
Proof.
ltac2:(KReplay.run1 (kr_t_RunEnv ()) ["FPX_1"; "WithEnv"] "h03fdsh12fsh26haltedh34rlimh45stdinh53tidh62vmp;1p;2g0000j10Tg000Uj14Tg0013j13Tg001Vj22Tg0026j11Tg002Vj15Tg007Pj17Tg0038j26Tg003R#0#0#0R0#0#0#0#4#3R1g0047'2#1g004og005fg006b%51R2%40#3#1#51211R1#1%71'6W3X52W2W1W4W6W0o"). Qed.
  Lemma m_vm_materialized_mkModelE : forall fds vm stdin fs halted tid rlim,
    m_vm_materialized (mkModelE fds vm stdin fs halted tid rlim) = [].
Proof.
ltac2:(KReplay.run1 (kr_t_RunEnv ()) ["FPX_1"; "WithEnv"] "h03fdsh12fsh26haltedh34rlimh45stdinh53tidh62vmp;1p;2g0000j10Tg000Uj12Tg0013j13Tg001Vj25Tg0026j11Tg002Vj14Tg007Pj17Tg0038j26Tg003R#0#0#0R0#0#0#0#2#3R1g0047'5#1g004og005fg006b%41R2%20#3#1#4%11%71'6W3X52W2W1W4W6W0o"). Qed.
  Lemma m_pipes_mkModelE : forall fds vm stdin fs halted tid rlim,
    m_pipes (mkModelE fds vm stdin fs halted tid rlim) = [].
Proof.
ltac2:(KReplay.run1 (kr_t_RunEnv ()) ["FPX_1"; "WithEnv"] "h03fdsh12fsh26haltedh34rlimh45stdinh53tidh62vmp;1p;2g0000j10Tg000Uj14Tg0013j13Tg001Vj22Tg0026j11Tg002Vj15Tg007Pj17Tg0038j26Tg003R#0#0#0R0#0#0#0#4#3R1g0047'2#1g004og005fg006b%51R2%40#3#1#5g0080,21R1#1%71'6W3X52W2W1W4W6W0o"). Qed.
  Lemma m_creds_mkModelE : forall fds vm stdin fs halted tid rlim,
    m_creds (mkModelE fds vm stdin fs halted tid rlim) = re_creds.
Proof.
ltac2:(KReplay.run1 (kr_t_RunEnv ()) ["FPX_1"; "WithEnv"] "h03fdsh12fsh26haltedh34rlimh45stdinh53tidh62vmp;1p;2g0000j10Tg000Uj11Tg0013j12Tg001Vj25Tg0026j14Tg002Vj13Tg008fj17Tg0038j26Tg003R#0#0#0R0#0#0#0#1#2R1g0047'5#4g004og005fg006b%31R1%10#2#4#3g00:0p,2RE#7'6W3X51W2W1W4W6W0o"). Qed.
  Lemma m_net_mkModelE : forall fds vm stdin fs halted tid rlim,
    m_net (mkModelE fds vm stdin fs halted tid rlim) = re_net.
Proof.
ltac2:(KReplay.run1 (kr_t_RunEnv ()) ["FPX_1"; "WithEnv"] "h03fdsh12fsh26haltedh34rlimh45stdinh53tidh62vmp;1p;2g0000j10Tg000Uj11Tg0013j12Tg001Vj25Tg0026j14Tg002Vj13Tg00:fj17Tg0038j26Tg003R#0#0#0R0#0#0#0#1#2R1g0047'5#4g004og005fg006b%31R1%10#2#4#3g00;np,2RE#7'6W3X51W2W1W4W6W0o"). Qed.
  Lemma m_nofile_mkModelE : forall fds vm stdin fs halted tid rlim,
    m_nofile (mkModelE fds vm stdin fs halted tid rlim) = re_nofile.
Proof.
ltac2:(KReplay.run1 (kr_t_RunEnv ()) ["FPX_1"; "WithEnv"] "h03fdsh12fsh26haltedh34rlimh45stdinh53tidh62vmp;1p;2g0000j10Tg000Uj11Tg0013j12Tg001Vj25Tg0026j14Tg002Vj13Tg00<gj17Tg0038j26Tg003R#0#0#0R0#0#0#0#1#2R1g0047'5#4g004og005fg006b%31R2%10#2#4#3p,2RE#7,61W3X52W2W1W4W6W0o"). Qed.
  Lemma m_sigmask_mkModelE : forall fds vm stdin fs halted tid rlim,
    m_sigmask (mkModelE fds vm stdin fs halted tid rlim) = re_sigmask.
Proof.
ltac2:(KReplay.run1 (kr_t_RunEnv ()) ["FPX_1"; "WithEnv"] "h03fdsh12fsh26haltedh34rlimh45stdinh53tidh62vmp;1p;2g0000j10Tg000Uj11Tg0013j12Tg001Vj25Tg0026j14Tg002Vj13Tg00>2j17Tg0038j26Tg003R#0#0#0R0#0#0#0#1#2R1g0047'5#4g004og005fg006b%31R2%10#2#4#3p,2RE#7,61W3X52W2W1W4W6W0o"). Qed.
  Lemma m_abort_terminal_mkModelE : forall fds vm stdin fs halted tid rlim,
    m_abort_terminal (mkModelE fds vm stdin fs halted tid rlim) = re_abort.
Proof.
ltac2:(KReplay.run1 (kr_t_RunEnv ()) ["FPX_1"; "WithEnv"] "h03fdsh12fsh26haltedh34rlimh45stdinh53tidh62vmp;1p;2g0000j10Tg000Uj11Tg0013j12Tg001Vj25Tg0026j14Tg002Vj13Tg00?>j17Tg0038j26Tg003R#0#0#0R0#0#0#0#1#2R1g0047'5#4g004og005fg006b%31R1%10#2#4#3g00@Hp,2RE#7'6W3X51W2W1W4W6W0o"). Qed.
  Lemma m_killed_mkModelE : forall fds vm stdin fs halted tid rlim,
    m_killed (mkModelE fds vm stdin fs halted tid rlim) = None.
Proof.
ltac2:(KReplay.run1 (kr_t_RunEnv ()) ["FPX_1"; "WithEnv"] "h03fdsh12fsh26haltedh34rlimh45stdinh53tidh62vmp;1p;2g0000j10Tg000Uj11Tg0013j12Tg001Vj25Tg0026j14Tg002Vj13Tg00@hj17Tg0038j26Tg003R#0#0#0R0#0#0#0#1#2R1g0047'5#4g004og005fg006b%31R2%10#2#4#3%71,62W3X52W2W1W4W6W0o"). Qed.
  Lemma m_sigabrt_pending_mkModelE : forall fds vm stdin fs halted tid rlim,
    m_sigabrt_pending (mkModelE fds vm stdin fs halted tid rlim) = false.
Proof.
ltac2:(KReplay.run1 (kr_t_RunEnv ()) ["FPX_1"; "WithEnv"] "h03fdsh12fsh26haltedh34rlimh45stdinh53tidh62vmp;1p;2g0000j10Tg000Uj11Tg0013j12Tg001Vj25Tg0026j14Tg002Vj13Tg0038j26Tg003R#0#0#0R0#0#0#0#1#2R1g0047'5#4g004og005fg006b%31R1%10#2#4#3g00@Hg00AJ'6W3X51W2W1W4W6W0o"). Qed.
  Lemma m_conn_ix_mkModelE : forall fds vm stdin fs halted tid rlim,
    m_conn_ix (mkModelE fds vm stdin fs halted tid rlim) = Z_to_bv 64 0.
Proof.
ltac2:(KReplay.run1 (kr_t_RunEnv ()) ["FPX_1"; "WithEnv"] "h03fdsh12fsh26haltedh34rlimh45stdinh53tidh62vmp;1p;2g0000j10Tg000Uj11Tg0013j12Tg001Vj25Tg0026j14Tg002Vj13Tg00Ajj27Tg0038j26Tg003R#0#0#0R0#0#0#0#1R1#2R2g0047'5#4g004og005fg006b%32R3%10#2#4#3g00BP,71,62W3X53W2W1W4W6W0o"). Qed.

  (* [comment removed for export] *)
  Lemma with_fds_mkModelE : forall fds' fds vm stdin fs halted tid rlim,
    with_fds fds' (mkModelE fds vm stdin fs halted tid rlim) = mkModelE fds' vm stdin fs halted tid rlim.
Proof.
ltac2:(KReplay.run1 (kr_t_RunEnv ()) ["FPX_1"; "WithEnv"] "h03fdsh14fds'h22fsh36haltedh44rlimh55stdinh63tidh72vmp;1p;2p;7g0000j10Tg000Uj11Tg0013j12Tg001Vj25Tg0026j14Tg002Vj13Tg00Bnj77Tg0038j26Tg003R#0#0#0R0#0#0#0#1#2R1g0047'5#4R2g004og005fg006b%31R1%10#2#4#3g00D8f7f5f4f3f2f1f0F7'6W4X61W3W2W5W7X02W1o"). Qed.
  Lemma with_vmmaps_mkModelE : forall vm' fds vm stdin fs halted tid rlim,
    with_vmmaps vm' (mkModelE fds vm stdin fs halted tid rlim) = mkModelE fds vm' stdin fs halted tid rlim.
Proof.
ltac2:(KReplay.run1 (kr_t_RunEnv ()) ["FPX_1"; "WithEnv"] "h03fdsh12fsh26haltedh34rlimh45stdinh53tidh62vmh73vm'p;1p;2p;7g0000j10Tg000Uj11Tg0013j12Tg001Vj25Tg0026j14Tg002Vj13Tg00Bnj77Tg0038j26Tg004oR0g003R#0#0#0R1#0#0#0#1#2R2g0047'5#4g005fg006b%32R2%11#2#4#3g00D8f6f7f4f3f2f1f0F7'6W3X52W2W1W4X60W0W7o"). Qed.
  Lemma with_tid_mkModelE : forall t fds vm stdin fs halted tid rlim,
    with_tid t (mkModelE fds vm stdin fs halted tid rlim) = mkModelE fds vm stdin fs halted (Some t) rlim.
Proof.
ltac2:(KReplay.run1 (kr_t_RunEnv ()) ["FPX_1"; "WithEnv"] "h03fdsh12fsh26haltedh34rlimh45stdinh51th63tidh72vmp;1p;2p;7g0000j10Tg000Uj11Tg0013j12Tg001Vj25Tg0026j14Tg002Vj13Tg00Dnj28Tg00Bnj77Tg0038j26Tg003R#0#0#0R0#0#0#0#1#2R1g0047,51#4g004og005fg006b%31R2%10#2#4#3g00D8f6f5f4f3f2f7,81f0F7'6W3X62W2W1W4W7W0W5o"). Qed.
  Lemma with_halted_mkModelE : forall c fds vm stdin fs halted tid rlim,
    with_halted c (mkModelE fds vm stdin fs halted tid rlim) = mkModelE fds vm stdin fs (Some c) tid rlim.
Proof.
ltac2:(KReplay.run1 (kr_t_RunEnv ()) ["FPX_1"; "WithEnv"] "h01ch13fdsh22fsh36haltedh44rlimh55stdinh63tidh72vmp;1p;2p;7g0000j10Tg000Uj11Tg0013j12Tg001Vj25Tg0026j14Tg002Vj13Tg00Dnj28Tg00Bnj77Tg0038j26Tg003R#0#0#0R0#0#0#0#1#2R1g0047,51#4g004og005fg006b%31R2%10#2#4#3g00D8f6f5f4f3f7,81f1f0F7'6W4X62W3W2W5W7W1W0o"). Qed.
  Lemma with_fs_mkModelE : forall fs' fds vm stdin fs halted tid rlim,
    with_fs fs' (mkModelE fds vm stdin fs halted tid rlim) = mkModelE fds vm stdin fs' halted tid rlim.
Proof.
ltac2:(KReplay.run1 (kr_t_RunEnv ()) ["FPX_1"; "WithEnv"] "h03fdsh12fsh23fs'h36haltedh44rlimh55stdinh63tidh72vmp;1p;2p;7g0000j10Tg000Uj11Tg0013j12Tg001Vj25Tg0026j14Tg002Vj13Tg00Bnj77Tg0038j26Tg006bR0g003R#0#0#0R1#0#0#0#1#2R2g0047'5#4g004og005f%32R2%11#2#4#3g00D8f6f5f4f7f2f1f0F7'6W4X62W3X10W5W7W0W2o"). Qed.
  Lemma with_stdin_mkModelE : forall s fds vm stdin fs halted tid rlim,
    with_stdin s (mkModelE fds vm stdin fs halted tid rlim) = mkModelE fds vm s fs halted tid rlim.
Proof.
ltac2:(KReplay.run1 (kr_t_RunEnv ()) ["FPX_1"; "WithEnv"] "h03fdsh12fsh26haltedh34rlimh41sh55stdinh63tidh72vmp;1p;2p;7g0000j10Tg000Uj11Tg0013j12Tg001Vj25Tg0026j14Tg002Vj13Tg00Bnj77Tg0038j26Tg005fR0g003R#0#0#0R1#0#0#0#1#2R2g0047'5#4g004og006b%32R2%11#2#4#3g00D8f6f5f7f3f2f1f0F7'6W3X62W2W1X50W7W0W4o"). Qed.
End WithEnv.
End FPX_1.


#[export] Hint Rewrite @m_fds_mkModelE @m_vmmaps_mkModelE @m_stdin_mkModelE @m_fs_mkModelE
  @m_halted_mkModelE @m_tid_mkModelE @m_rlimit_core_mkModelE @m_vm_lazy_mkModelE
  @m_vm_materialized_mkModelE @m_pipes_mkModelE @m_creds_mkModelE @m_net_mkModelE
  @m_nofile_mkModelE @m_sigmask_mkModelE @m_abort_terminal_mkModelE @m_killed_mkModelE
  @m_sigabrt_pending_mkModelE @m_conn_ix_mkModelE
  @with_fds_mkModelE @with_vmmaps_mkModelE @with_tid_mkModelE @with_halted_mkModelE
  @with_fs_mkModelE @with_stdin_mkModelE : model.
Section FPX_2. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
Definition fds_init : list (word * FdEntry) :=
  [ (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0));
    (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
    (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2)) ].

(* [comment removed for export] *)
Lemma init_model_E : forall reserved brk0 mbase sp lim inp,
  init_model reserved brk0 mbase sp lim inp
  = @mkModelE (run_env_of inp) fds_init (mkVmMapsFull reserved [] [] brk0 brk0 lim mbase sp)
              (in_stdin inp) (in_fs inp) None None None.
Proof.
ltac2:(KReplay.run1 (kr_t_RunEnv ()) ["FPX_2"] "h04brk0h13inph23limh35mbaseh48reservedh52spp;1p;2p;8g0000j10Tg000Uj12Tg0013j11Tg001Vj25Tg0026j14Tg00EPj1<Tg007Pj1;Tg00F\j88Tg00GSj17Tg00HJj16Tg00@hj13Tg00Bnj89Tg0038j2:Tg003R#0#0#0R0#0#0#0#2#1R1/51R2#4g00I>g00I\g00D8f0R3#<g00JVf5%;2R2P2f4R2P2f1f3f2G8%73%63%31R3P3%20#1#4#3G9':W1W2X51X31X01W4o"). Qed.

Lemma with_tid_init_model_E : forall tid reserved brk0 mbase sp lim inp,
  with_tid tid (init_model reserved brk0 mbase sp lim inp)
  = @mkModelE (run_env_of inp) fds_init (mkVmMapsFull reserved [] [] brk0 brk0 lim mbase sp)
              (in_stdin inp) (in_fs inp) None (Some tid) None.
Proof.
ltac2:(KReplay.run1 (kr_t_RunEnv ()) ["FPX_2"] "h04brk0h13inph23limh35mbaseh48reservedh52sph63tidp;1p;2p;8g0000j10Tg000Uj14Tg0013j12Tg001Vj25Tg0026j11Tg00EPj1<Tg007Pj1;Tg00F\j88Tg00GSj17Tg00HJj16Tg00@hj13Tg00Dnj29Tg00Bnj8:Tg0038j2=Tg003R#0#0#0R0#0#0#0#4#2R11511R2#1g00I>g00I\g00D8f0R3#<g00JVf5%;2R2P2f4R2P2f1f3f2G8%73%63%31f6,91%40#2#1#3G:'=W1W2X51X31X01W4W6o"). Qed.

End FPX_2.
