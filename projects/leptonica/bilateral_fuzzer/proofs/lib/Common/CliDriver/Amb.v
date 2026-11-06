(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State StackLayout Run.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_Amb () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00K47Corelib4Init5Logic2eq01i69OSSVerify5KrLib6Common9CliDriver3Amb3Amb00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsI4ELinuxProcessSemantics?LinuxProcessSem5State;InputStream00I47Corelib4Init9Datatypes4prod00c69OSSVerify5KrLib6Common9CliDriver3Amb6amb_ofC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7in_argvC4ELinuxProcessSemantics?LinuxProcessSem5State7in_envpC4ELinuxProcessSemantics?LinuxProcessSem5State5in_fsC4ELinuxProcessSemantics?LinuxProcessSem5State8in_stdinc69OSSVerify5KrLib6Common9CliDriver3Amb<mkProcInputCC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:init_modelI4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00I47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C4ELinuxProcessSemantics?LinuxProcessSem3Run;init_configI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib7Numbers7BinNums1N00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8PhdrInfo00I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C45stdpp9bitvector;definitions7Z_to_bvK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01K47Corelib4Init9Datatypes4prod01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps01K47Corelib4Init9Datatypes6option02c69OSSVerify5KrLib6Common9CliDriver3Amb8mkModelCC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes6option01I47Corelib4Init9Datatypes6option00I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00".
Import ListNotations.

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
  a_draw : EntryDraw;
  a_urandom : InputStream
}.

(* [comment removed for export] *)
Definition amb_creds {AMB : Amb} : Creds :=
  mkCreds a_uid a_uid a_uid a_gid a_gid a_gid a_groups.

(* [comment removed for export] *)
Definition mkModelC {AMB : Amb} (fds : list (word * FdEntry)) (vm : VmMaps)
    (stdin : InputStream) (fs : Fs.Fs) (halted : option word)
    (tid : option word) (rlim : option (list byte)) : Model :=
  with_abort_terminal a_abort_terminal
  (with_sigmask a_sigmask
  (with_nofile a_nofile
   (with_net a_net
   (with_urandom a_urandom
   (with_creds amb_creds
    (mkModel fds vm stdin fs halted tid rlim)))))).

(* [comment removed for export] *)
Definition mkProcInputC {AMB : Amb} (argv envp : list (list byte)) (fs : Fs.Fs)
    (stdin : InputStream) : ProcInput :=
  mkProcInput_full argv envp fs stdin a_uid a_gid a_groups a_net a_nofile a_sigmask a_hwcap a_abort_terminal a_va_size
                   a_urandom [].

(* [comment removed for export] *)
Definition amb_of (inp : ProcInput) (draw : EntryDraw) : Amb :=
  mkAmb (in_uid inp) (in_gid inp) (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_hwcap inp)
        (in_abort_terminal inp) (in_va_size inp) draw (in_urandom inp).

Lemma in_fs_C : forall {AMB : Amb} av ev fs si, in_fs (mkProcInputC av ev fs si) = fs.
Proof.
ltac2:(KReplay.run1 (kr_t_Amb ()) [] "h03AMBh12avh22evh32fsh42sip;1p;2g0000j10Tg000Uj14Tg0013j12Tg001Vj11Tg0026j23Tg002Pg003O#0#0#0#4#2#1#1R0g0044R1g004bf1,31W4W3X20W1W0o"). Qed.

(* [comment removed for export] *)
Lemma init_model_C_of : forall inp draw reserved brk0 mbase sp lim,
  init_model reserved brk0 mbase sp lim inp
  = init_model reserved brk0 mbase sp lim
      (@mkProcInputC (amb_of inp draw) (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp)).
Proof.
ltac2:(KReplay.run1 (kr_t_Amb ()) [] "h04brk0h14drawh23inph33limh45mbaseh58reservedh62spp;1p;2p;5p;6g0000j10Tg000Uj1<Tg0013j12Tg005^j21Tg001Vj1;Tg006>j2:Tg007>j13Tg0084j14Tg008jj15Tg009^j16Tg00:Uj57Tg00;[j68Tg0026j29Tg00<Tg00=Ng003O#0#0#0#0#0#0#<#2R0/10#;g00>Ng00>lf4f3f2f1f0f6R1f5':%31%41%51%61D7E8'9W3X60X40X00W5W1W2o"). Qed.

(* [comment removed for export] *)
Lemma init_config_C_of : forall segs pc ph sp brk mbase draw lim inp,
  init_config segs pc ph sp brk mbase draw lim inp
  = init_config segs pc ph sp brk mbase draw lim
      (@mkProcInputC (amb_of inp draw) (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp)).
Proof.
ltac2:(KReplay.run1 (kr_t_Amb ()) [] "h03brkh14drawh23inph33limh45mbaseh52pch62phh74segsh82spp;1p;2p;5p;9g001Vj1;Tg0000j10Tg000Uj12Tg0013j11Tg006>j2:Tg007>j19Tg0084j13Tg008jj14Tg009^j15Tg00:Uj56Tg00?bl97Tg0026j28Tg00@Z#;g00AYg00B7g003O#0#0#0#0#0#0#2#1R0g00=Ng00>Ng00<Tg00C7f8f7f6f5f4f3f2R1f1f0R2/:1%92%32%42%52D6M97'8W2W3W1X40X00W8W6W5W7o"). Qed.

Lemma init_model_C : forall {AMB : Amb} reserved brk0 mbase sp lim av ev fs stdin,
  init_model reserved brk0 mbase sp lim (mkProcInputC av ev fs stdin)
  = mkModelC [ (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0));
               (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
               (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2)) ]
             (mkVmMapsFull reserved [] [] brk0 brk0 lim mbase sp) stdin fs None None None.
Proof.
ltac2:(KReplay.run1 (kr_t_Amb ()) [] "h03AMBh12avh24brk0h32evh42fsh53limh65mbaseh78reservedh82sph95stdinp;1p;2p;4p;3p;8g0000j10Tg000Uj1;Tg0013j19Tg005^j26Tg001Vj15Tg00Clj24Tg00DRj13Tg00EJj42Tg00Ejj18Tg00FHj17Tg00Fhj31Tg00GHj8<Tg00H?j1:Tg00Haj8>Tg0026j2=Tg002Pg003OR0#0R1#0#0R2#0#0#0#;R3#9R4/64R5#5g00>N%;2#9#5R2#5R6g0044g004bg00>lf9g00IcR7,64R8P4P7g00J[,43R9%39C2P4P7%80,43R0%30C2P4P7%81,43R3%33C2%7851851831f8%75R5P5f7R5P5f4f6f5G<f0f1%:4R5P5%:2G>'=W9W4X36W1W5X84X64X24W7W0o"). Qed.

(* [comment removed for export] *)
Lemma with_tid_init_model_C : forall {AMB : Amb} reserved brk0 mbase sp lim av ev fs stdin tid,
  with_tid tid (init_model reserved brk0 mbase sp lim (mkProcInputC av ev fs stdin))
  = mkModelC [ (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0));
               (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
               (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2)) ]
             (mkVmMapsFull reserved [] [] brk0 brk0 lim mbase sp) stdin fs None (Some tid) None.
Proof.
ltac2:(KReplay.run1 (kr_t_Amb ()) [] "h03AMBh12avh24brk0h32evh42fsh53limh65mbaseh78reservedh82sph95stdinh:3tidp;1p;2p;4p;3p;8g0000j10Tg000Uj1;Tg0013j19Tg005^j26Tg001Vj15Tg00Clj24Tg00DRj13Tg00EJj42Tg00Ejj18Tg00FHj17Tg00Fhj31Tg00GHj8<Tg00H?j1:Tg00K9j2?Tg00Haj8>Tg0026j2=Tg002Pg003OR0#0R1#0#0R2#0#0#0#;R3#9R4/64R5#5g00>N%;2#9#5R2#5R6g0044g004bg00>lf:g00IcR7,64R8P4P7g00J[,43R9%39C2P4P7%80,43R0%30C2P4P7%81,43R3%33C2%7851851831f9%75R5P5f8R5P5f5f7f6G<f1f2%:4f0,?4%:2G>'=X:4W9W4X36W1W5X84X64X24W7W0o"). Qed.

(* [comment removed for export] *)
Section Proj.
  Context {AMB : Amb}.
  Lemma m_fds_C : forall fds vm si fs h t r, m_fds (mkModelC fds vm si fs h t r) = fds.
Proof.
ltac2:(KReplay.run1 (kr_t_Amb ()) ["Proj"] "h03fdsh12fsh21hh31rh42sih51th62vmp;1p;2g0000j10Tg000Uj11Tg0013j12Tg005^j25Tg001Vj14Tg00K[j13Tg0026j26Tg003O#0#0#0R0#0#0#0#1#2R1g00Ic'5#4R2g00L=g004bg0044%31R1%10#2#4#3f6,62W3X51W2W1W4W6W0o"). Qed.
  Lemma m_vmmaps_C : forall fds vm si fs h t r, m_vmmaps (mkModelC fds vm si fs h t r) = vm.
Proof.
ltac2:(KReplay.run1 (kr_t_Amb ()) ["Proj"] "h03fdsh12fsh21hh31rh42sih51th62vmp;1p;2g0000j10Tg000Uj11Tg0013j12Tg005^j25Tg001Vj14Tg00K[j13Tg0026j26Tg003O#0#0#0R0#0#0#0#1#2R1g00Ic'5#4g00L=R2g004bg0044%31R1%10#2#4#3f5,62W3X51W2W1W4W6W0o"). Qed.
  Lemma m_stdin_C : forall fds vm si fs h t r, m_stdin (mkModelC fds vm si fs h t r) = si.
Proof.
ltac2:(KReplay.run1 (kr_t_Amb ()) ["Proj"] "h03fdsh12fsh21hh31rh42sih51th62vmp;1p;2g0000j10Tg000Uj11Tg0013j12Tg005^j25Tg001Vj14Tg00K[j13Tg0026j26Tg003O#0#0#0R0#0#0#0#1#2R1g00Ic'5#4g00L=g004bR2g0044%31R1%10#2#4#3f4,62W3X51W2W1W4W6W0o"). Qed.
  Lemma m_fs_C : forall fds vm si fs h t r, m_fs (mkModelC fds vm si fs h t r) = fs.
Proof.
ltac2:(KReplay.run1 (kr_t_Amb ()) ["Proj"] "h03fdsh12fsh21hh31rh42sih51th62vmp;1p;2g0000j10Tg000Uj11Tg0013j12Tg005^j25Tg001Vj14Tg00K[j13Tg0026j26Tg003O#0#0#0R0#0#0#0#1#2R1g00Ic'5#4g00L=g004bg0044R2%31R1%10#2#4#3f3,62W3X51W2W1W4W6W0o"). Qed.
  Lemma m_halted_C : forall fds vm si fs h t r, m_halted (mkModelC fds vm si fs h t r) = h.
Proof.
ltac2:(KReplay.run1 (kr_t_Amb ()) ["Proj"] "h03fdsh12fsh21hh31rh42sih51th62vmp;1p;2g0000j10Tg000Uj11Tg0013j12Tg005^j25Tg001Vj14Tg00K[j13Tg0026j26Tg003O#0#0#0R0#0#0#0#1#2R1g00Ic'5#4g00L=g004bg0044%31R1%10#2#4#3f2,61W3X51W2W1W4W6W0o"). Qed.
  Lemma m_tid_C : forall fds vm si fs h t r, m_tid (mkModelC fds vm si fs h t r) = t.
Proof.
ltac2:(KReplay.run1 (kr_t_Amb ()) ["Proj"] "h03fdsh12fsh21hh31rh42sih51th62vmp;1p;2g0000j10Tg000Uj11Tg0013j12Tg005^j25Tg001Vj14Tg00K[j13Tg0026j26Tg003O#0#0#0R0#0#0#0#1#2R1g00Ic'5#4g00L=g004bg0044%31R1%10#2#4#3f1,61W3X51W2W1W4W6W0o"). Qed.
  Lemma m_vm_lazy_C : forall fds vm si fs h t r, m_vm_lazy (mkModelC fds vm si fs h t r) = [].
Proof.
ltac2:(KReplay.run1 (kr_t_Amb ()) ["Proj"] "h03fdsh12fsh21hh31rh42sih51th62vmp;1p;2g0000j10Tg000Uj14Tg0013j13Tg005^j22Tg001Vj11Tg00K[j15Tg00FHj17Tg0026j26Tg003O#0#0#0R0#0#0#0#4#3R1g00Ic'2#1g00L=g004bg0044%51R2%40#3#1#51211R1#1%71'6W3X52W2W1W4W6W0o"). Qed.
  Lemma m_vm_materialized_C : forall fds vm si fs h t r, m_vm_materialized (mkModelC fds vm si fs h t r) = [].
Proof.
ltac2:(KReplay.run1 (kr_t_Amb ()) ["Proj"] "h03fdsh12fsh21hh31rh42sih51th62vmp;1p;2g0000j10Tg000Uj12Tg0013j13Tg005^j25Tg001Vj11Tg00K[j14Tg00FHj17Tg0026j26Tg003O#0#0#0R0#0#0#0#2#3R1g00Ic'5#1g00L=g004bg0044%41R2%20#3#1#4%11%71'6W3X52W2W1W4W6W0o"). Qed.
  Lemma with_fds_C : forall fds' fds vm si fs h t r,
    with_fds fds' (mkModelC fds vm si fs h t r) = mkModelC fds' vm si fs h t r.
Proof.
ltac2:(KReplay.run1 (kr_t_Amb ()) ["Proj"] "h03fdsh14fds'h22fsh31hh41rh52sih61th72vmp;1p;2p;8g0000j10Tg000Uj11Tg0013j12Tg005^j25Tg001Vj14Tg00K[j13Tg00Haj87Tg0026j26Tg003O#0#0#0R0#0#0#0#1#2R1g00Ic'5#4R2g00L=g004bg0044%31R1%10#2#4#3g00>lp,3AMBf7f5f4f3f2f1f0G7'6W4X61W3W2W5W7X02W1o"). Qed.
  Lemma with_vmmaps_C : forall vm' fds vm si fs h t r,
    with_vmmaps vm' (mkModelC fds vm si fs h t r) = mkModelC fds vm' si fs h t r.
Proof.
ltac2:(KReplay.run1 (kr_t_Amb ()) ["Proj"] "h03fdsh12fsh21hh31rh42sih51th62vmh73vm'p;1p;2p;8g0000j10Tg000Uj11Tg0013j12Tg005^j25Tg001Vj14Tg00K[j13Tg00Haj87Tg0026j26Tg00L=R0g003O#0#0#0R1#0#0#0#1#2R2g00Ic'5#4g004bg0044%32R2%11#2#4#3g00>lp,3AMBf6f7f4f3f2f1f0G7'6W3X52W2W1W4X60W0W7o"). Qed.
  Lemma with_stdin_C : forall si' fds vm si fs h t r,
    with_stdin si' (mkModelC fds vm si fs h t r) = mkModelC fds vm si' fs h t r.
Proof.
ltac2:(KReplay.run1 (kr_t_Amb ()) ["Proj"] "h03fdsh12fsh21hh31rh42sih53si'h61th72vmp;1p;2p;8g0000j10Tg000Uj11Tg0013j12Tg005^j25Tg001Vj14Tg00K[j13Tg00Haj87Tg0026j26Tg004bR0g003O#0#0#0R1#0#0#0#1#2R2g00Ic'5#4g00L=g0044%32R2%11#2#4#3g00>lp,3AMBf6f5f7f3f2f1f0G7'6W3X62W2W1X40W7W0W5o"). Qed.
  Lemma with_halted_C : forall c fds vm si fs h t r,
    with_halted c (mkModelC fds vm si fs h t r) = mkModelC fds vm si fs (Some c) t r.
Proof.
ltac2:(KReplay.run1 (kr_t_Amb ()) ["Proj"] "h01ch13fdsh22fsh31hh41rh52sih61th72vmp;1p;2p;8g0000j10Tg000Uj11Tg0013j12Tg005^j25Tg001Vj14Tg00K[j13Tg00K9j28Tg00Haj87Tg0026j26Tg003O#0#0#0R0#0#0#0#1#2R1g00Ic,51#4g00L=g004bg0044%31R2%10#2#4#3g00>lp,3AMBf6f5f4f3f7,81f1f0G7'6W4X62W3W2W5W7W1W0o"). Qed.
  Lemma with_tid_C : forall t' fds vm si fs h t r,
    with_tid t' (mkModelC fds vm si fs h t r) = mkModelC fds vm si fs h (Some t') r.
Proof.
ltac2:(KReplay.run1 (kr_t_Amb ()) ["Proj"] "h03fdsh12fsh21hh31rh42sih51th62t'h72vmp;1p;2p;8g0000j10Tg000Uj11Tg0013j12Tg005^j25Tg001Vj14Tg00K[j13Tg00K9j28Tg00Haj87Tg0026j26Tg003O#0#0#0R0#0#0#0#1#2R1g00Ic,51#4g00L=g004bg0044%31R2%10#2#4#3g00>lp,3AMBf6f5f4f3f2f7,81f0G7'6W3X52W2W1W4W7W0W6o"). Qed.
End Proj.
