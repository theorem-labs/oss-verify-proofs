(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the run's channel-reader bit as a new last field of the input record). *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs Vdso State Run.
Import ListNotations.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Class Amb : Type := mkAmb {
  a_uid : word;
  a_gid : word;
  a_groups : list word;
  a_net : NetQueue;
  a_nofile : word;
  a_sigmask : word;
  a_hwcap : word;
  a_abort_terminal : bool;
  a_va_size : VaSize;
  a_urandom : InputStream;
  a_kernel : KernelBuild;
  a_execfn : list byte;
  a_channel_reader : bool;
  a_sigpipe_default : bool;
  a_sigpipe_terminal : bool
}.

Definition amb_creds {AMB : Amb} : Creds :=
  mkCreds a_uid a_uid a_uid a_gid a_gid a_gid a_groups.

Definition mkModelC {AMB : Amb} (fds : list (word * FdEntry)) (vm : VmMaps)
    (stdin : InputStream) (fs : Fs.Fs) (halted : option word)
    (tid : option word) (rlim : option (list byte)) : Model :=
  mkModelOf (mkFdState fds []) (mkVmState vm [] [] a_kernel (vdso_run_init vdso_draw_keep))
            (mkIoState stdin a_urandom a_net (Z_to_bv 64 0)) (mkFsState fs)
            (mkProcState halted tid amb_creds false a_sigmask false None
                         false false false a_abort_terminal [] false a_channel_reader (sigpipe_action_at_exec a_sigpipe_default) a_sigpipe_terminal)
            (mkLimState rlim a_nofile)
            (mkTimeState (Z_to_bv 64 0)).

Definition mkProcInputC {AMB : Amb} (argv envp : list (list byte)) (fs : Fs.Fs)
    (stdin : InputStream) : ProcInput :=
  mkProcInput_full argv envp fs stdin a_uid a_gid a_groups a_net
              a_nofile a_sigmask a_hwcap a_abort_terminal a_va_size a_urandom []
              a_kernel a_execfn a_channel_reader a_sigpipe_default a_sigpipe_terminal.

Definition amb_of (inp : ProcInput) : Amb :=
  mkAmb (in_uid inp) (in_gid inp) (in_groups inp) (in_net inp)
        (in_nofile inp) (in_sigmask inp) (in_hwcap inp) (in_abort_terminal inp) (in_va_size inp) (in_urandom inp)
        (in_kernel inp) (in_execfn inp) (in_channel_reader inp)
        (in_sigpipe_default inp) (in_sigpipe_terminal inp).

Section Proj.
  Context {AMB : Amb}.

End Proj.
