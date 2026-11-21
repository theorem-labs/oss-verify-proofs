(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start state per CONFIG_RSEQ, taken at the launch's flag; the stack-pointer and head facts from the new entry-stack layout's numbers and the launch conjunct; the argument layout from those numbers and the exec file name's address, launch variable 13; the launch's mmap base in the initial valuation's invariant; the launch model's channel reader from the valid input, LPS 08b1429; the reserved ledger is the image's entries then the vDSO/vvar pair, the pair's facts and the ledger's apartness proved from the launch's stack pointer and mmap base, M1_fields written as plain text; the pair's top as the launch writes it at LPS c0dd863a, equal to vdso_top by the model's page_round_down_Z_min_r). *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "modulo"; "pow"; "divide"; "@Corelib.Init.Datatypes"; "list"; "nil"; "prod"; "None"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "agree_below"; "@Corelib.Numbers.BinNums"; "Z"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "m_fds"; "m_fs"; "m_stdin"; "FdEntry"; "InputStream"; "m_halted"; "m_tid"; "m_vm_lazy"; "m_vm_materialized"; "m_vmmaps"; "sp_window_hi"; "sp_window_lo"; "vm_backing_used"; "vm_brk"; "vm_init_sp"; "vm_limit"; "vm_maps"; "vm_noaccess"; "vm_reserved"; "vm_start_brk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Init"; "pcA"; "phA"; "S0_A"; "c0A"; "imgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState"; "Jinit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start0"; "K0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartLib"; "K_nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartMain.Main"; "M1"; "QMain"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "ok_frame"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "jpredA"; "ok_frameA"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "Fs"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "cfg_model"; "mkEntry"; "segments_reserved"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Fork"; "PID_MAX_ENVELOPE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.StartArgF"; "arg_layout"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartMain"; "B0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartTop"; "PostMain"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "ok_pframe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout"; "valid_entry48"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall SymSummary Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA CompleteA GlueA GlueA2 SysCallA
  MmapA MmapFixedA MmapFixedA2 MmapBrkA MmapNodesA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv InitState InitLayout.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Init Code StartLib KxA Placement PlacementA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartStates Start0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start6 Start7States Start7 Start8States0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start8M.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartTop.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.PlacementA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.StartArgF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e0.Start1States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.Start1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start7States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start8States0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g2.Start8CallDefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fz.Start8CallA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fz.Start8CallB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start8M OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g2.Start8Out OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g4.Start8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartTop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition B0 : Z := 0.

Section Main.
Variable sp brk mb : word.
Variable draw : EntryDraw.
Variable lim : Z.
Variable inp : ProcInput.
Hypothesis Hent : ltac2:(tb__ "0|0|
S47S30S3cVsp;Vbrk;Vmb;Vdraw;A4Vinp;A3").
Hypothesis Hinp : valid_input_either inp.
Hypothesis Hlim : 2 ^ 25 <= lim.
(* LPS 727298f3: the start-up chain's states are made per CONFIG_RSEQ (StartStates.v, Init.v's
   [S0_A]); this run's value is the launch's kernel build's. *)
Let rq : bool := kb_rseq (in_kernel inp).
Variable rhoI : valuation.
Hypothesis HJ : ltac2:(tb__ "0|0|
S31S3S2cS2dVsp;Vmb;Vdraw;Vinp;VrhoI;A8").

Let m0 : Model := ltac2:(tb__ "0|0|
S3bS2fVsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;A6A1").

Definition M1 (tid : word) : Model := with_tid tid m0.
(* LPS 08b1429: [init_model] copies [in_channel_reader]; [valid_input_either]'s thirteenth conjunct pins it. *)
Lemma M1_rdr : forall tid, m_channel_reader (M1 tid) = true.
Proof using Hinp. intros tid. destruct Hinp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
(* LPS 727298f3: the launch reserves the vDSO/vvar pair (State.v [vm_reserved_init_model]); no setter
   on the way to [M1] writes the kernel build or the reserved ledger (as P/Drv_spine.v's [vdso_ok_md0]). *)
Lemma vdso_M1 : forall tid e, In e (vdso_reserved (m_kernel (M1 tid)) (vdso_top (m_vmmaps (M1 tid)))) -> In e (vm_reserved (m_vmmaps (M1 tid))).
Proof using .
  intros tid e He. unfold M1, m0, c0A, init_config, with_tid in *. cbn [cfg_model] in *.
  autorewrite with model in *.
  try rewrite vm_reserved_init_model.
  autorewrite with model in *.
  (* LPS c0dd863a: the launch writes the pair's top as [page_round_down_Z (Z.min mb (sp - stack_max_size))];
     [vdso_top] rounds [sp - stack_max_size] first (State.v [page_round_down_Z_min_r]: the same value). *)
  apply in_or_app. right. rewrite <- page_round_down_Z_min_r. exact He.
Qed.

(* LPS 727298f3: the launch's reserved ledger is the image's entries then the vDSO/vvar pair ending at
   [vdso_top] (State.v [vm_reserved_init_model]); no setter on the way to [M1] writes it. *)
Lemma resv_M1 : forall tid, vm_reserved (m_vmmaps (M1 tid)) = segments_reserved segsA ++ vdso_reserved (m_kernel (M1 tid)) (vdso_top (m_vmmaps (M1 tid))).
Proof using .
  intros tid. unfold M1, m0, c0A, init_config. cbn [cfg_model].
  rewrite ?m_vmmaps_with_tid, ?m_kernel_with_tid, ?m_vmmaps_with_vdso, ?m_kernel_with_vdso, ?m_kernel_init_model.
  exact (vm_reserved_init_model _ _ _ _ _ _).
Qed.

(* LPS 727298f3: the pair's facts (Fw/SysSpec.v [vdso_pair_ok_of]) from the launch's mmap base and stack
   pointer: [M1]'s are [mb] and [sp], and [Hent] gives [valid_mmap_base mb] and [valid_sp sp]. *)
Lemma pair_ok_M1 : forall tid, vdso_pair_ok (vdso_reserved (m_kernel (M1 tid)) (vdso_top (m_vmmaps (M1 tid)))).
Proof using Hent.
  intros tid. destruct Hent as (Hsp & _ & Hmb & _ & _).
  assert (HMB : vm_mmap_base (m_vmmaps (M1 tid)) = mb).
  { unfold M1, m0, c0A, init_config. cbn [cfg_model]. rewrite ?m_vmmaps_with_tid, ?m_vmmaps_with_vdso. reflexivity. }
  assert (HSP : vm_init_sp (m_vmmaps (M1 tid)) = sp).
  { unfold M1, m0, c0A, init_config. cbn [cfg_model]. rewrite ?m_vmmaps_with_tid, ?m_vmmaps_with_vdso. reflexivity. }
  apply vdso_pair_ok_of.
  - rewrite HMB. destruct Hmb as (H1 & H2 & _). split; assumption.
  - rewrite HSP. destruct Hsp as (H1 & _). exact H1.
Qed.

(* The pair ends at or below the mmap base, a word. *)
Lemma vdso_top_lt : forall h : VmMaps, vdso_top h < two_pow_64.
Proof using .
  intros h. pose proof (bv_unsigned_in_range _ (vm_mmap_base h)) as Rm. change (bv_modulus 64) with (2 ^ 64) in Rm.
  assert (Hvt : vdso_top h = page_round_down_Z (Z.min (bv_unsigned (vm_mmap_base h)) (page_round_down_Z (bv_unsigned (vm_init_sp h) - stack_max_size)))) by reflexivity.
  assert (PR : forall z, page_round_down_Z z <= z).
  { intros z. unfold page_round_down_Z, page_size. pose proof (Z.mod_pos_bound z 4096 ltac:(lia)). pose proof (Z.div_mod z 4096 ltac:(lia)). lia. }
  rewrite Hvt. pose proof (PR (Z.min (bv_unsigned (vm_mmap_base h)) (page_round_down_Z (bv_unsigned (vm_init_sp h) - stack_max_size)))) as P1.
  pose proof (Z.le_min_l (bv_unsigned (vm_mmap_base h)) (page_round_down_Z (bv_unsigned (vm_init_sp h) - stack_max_size))) as P2.
  unfold two_pow_64. lia.
Qed.

(* LPS 727298f3: the launch's reserved ledger is apart within itself, the pair's two entries included
   (Start8M.v [resv_apart_of], [vdso_reserved_apart]); StartTop's [Hrap]. *)
Lemma resv_apart_M1 : forall tid, ranges_apart (vm_reserved (m_vmmaps (M1 tid))).
Proof using Hent.
  intros tid. apply (resv_apart_of (m_vmmaps (M1 tid)) (vdso_reserved (m_kernel (M1 tid)) (vdso_top (m_vmmaps (M1 tid))))).
  - exact (resv_M1 tid).
  - exact (pair_ok_M1 tid).
  - apply vdso_reserved_apart. exact (vdso_top_lt (m_vmmaps (M1 tid))).
Qed.

Variable ok : assn.
Hypothesis OKF : ltac2:(tb__ "0|0|
SaS16A1S17OF_;F_;S33R1A1S37S3Vok;R2A3F_;FK;").
Hypothesis OKP : ltac2:(tb__ "0|0|
SaS16A1S17OF_;F_;S33R1A1S45S3Vok;R2A3F_;FK;").
Hypothesis OKFA : ltac2:(tb__ "0|1|
S38S10SaS15Q40A1A1SaS16A1M0S17R5R4R3R2R1A4S1G0R3SbS16A1A3F_;Fmd;Ftr;Ftp;Frho;S39S3Vok;R2A3F_;FJ;").
Hypothesis OKPA : ltac2:(tb__ "0|1|
S38S10SaS15Q40A1A1SaS16A1M0S17R5R4R3R2R1A4S1G0R3SbS16A1A3F_;Fmd;Ftr;Ftp;Frho;S46S3Vok;R2A3F_;FJ;").

Lemma K0_nil : K_nil (K0 m0). Proof. intros tr md [H _]; exact H. Qed.
Lemma K1_nil : K_nil (K1 m0). Proof. intros tr md [H _]; exact H. Qed.

(* LPS 727298f3: the reserved ledger's conjunct is the image's entries then the vDSO/vvar pair (Fw/SysSpec.v
   [vdso_pair_ok]), proved from the launch ([resv_M1], [pair_ok_M1]).  Statement written as plain text. *)
Lemma M1_fields : forall tid : word,
  m_halted (M1 tid) = None /\ m_vm_lazy (M1 tid) = [] /\ m_vm_materialized (M1 tid) = [] /\
  (exists V, vm_reserved (m_vmmaps (M1 tid)) = segments_reserved segsA ++ V /\ vdso_pair_ok V) /\
  vm_maps (m_vmmaps (M1 tid)) = [] /\ vm_noaccess (m_vmmaps (M1 tid)) = [] /\ vm_limit (m_vmmaps (M1 tid)) = lim /\
  vm_start_brk (m_vmmaps (M1 tid)) = brk /\ vm_brk (m_vmmaps (M1 tid)) = brk /\ vm_init_sp (m_vmmaps (M1 tid)) = sp /\
  vm_backing_used (M1 tid) = 0 /\ m_tid (M1 tid) = Some tid /\
  m_fds (M1 tid) = m_fds m0 /\ m_fs (M1 tid) = m_fs m0 /\ m_stdin (M1 tid) = m_stdin m0.
Proof using Hent.
  intros tid. pose proof (resv_M1 tid) as EV. pose proof (pair_ok_M1 tid) as HV.
  split; [|split; [|split; [|split; [exists (vdso_reserved (m_kernel (M1 tid)) (vdso_top (m_vmmaps (M1 tid)))); split; assumption|]]]].
  all: unfold M1, m0, c0A, init_config, init_model, with_tid; cbn -[segments_reserved]; repeat split; reflexivity.
Qed.

Lemma brk_facts : ltac2:(tb__ "0|1|
S0S0S4Z646000S14Q40Vbrk;A2M0A2S4G0Z80646000A2A2S9Z1000G0A2A2").
Proof.
  clear - Hent. destruct Hent as (_ & Hbrk & _ & _). unfold valid_brk in Hbrk. rewrite reserved_top_A in Hbrk.
  unfold IMG_BAND_HI, brk_aslr_max, page_size in Hbrk. split; [lia|]. apply Z.mod_divide; lia.
Qed.
Lemma sp_facts : ltac2:(tb__ "0|1|
S0S0S4S23S14Q40Vsp;A2M0A2S4G0S22A2A2S0S0S4Z7fff80000000G0A2S4G0S8Z2Z2fA2A2A2S1S13S7G0Z10A2Z0A3A2A2").
Proof.
  clear - Hent Hinp. destruct Hent as (Hsp & _ & _ & _ & Hlau).
  pose proof (nums pcA phA sp brk mb draw inp Hsp Hinp Hlau) as N. cbv zeta in N. destruct N as (Nsp & N16 & _).
  pose proof Hsp as (S1 & S2 & S3). repeat split; try assumption; lia.
Qed.

Lemma layout_facts : ltac2:(tb__ "0|0|
S10S31S3S2cS2dVsp;Vmb;Vdraw;Vinp;R1A8S14Q40S11R2P1A2A2S13S14Q40S11R3P6A2A2S13S0S0S4Z7fff80000000R2A2S4R2S8Z2Z2fA2A2A2S0S1S13S7R2Z10A2Z0A3S0S4S5R2Z50A2R1A2S0S4S5R1Z10A2S8Z2Z2fA2A2S0S4S5R1Z10A2S5R2Z2228cfA2A2S0S4R2S14Q40S11R4P4A2A2A2S0S4R2R1A2S1S13R2S14Q40Vsp;A2A3A2A2A2A2A2A2A2Tr6;Tx;F_;Frho;").
Proof.
  (* LPS 727298f3: the head is [RND + 16] bytes (InitState's [nums]), the strings above it. *)
  clear - Hent Hinp. intros rho HJr. destruct Hent as (Hsp & _ & _ & _ & Hlau).
  pose proof (nums pcA phA sp brk mb draw inp Hsp Hinp Hlau) as N. cbv zeta in N.
  destruct N as (Nsp & N16 & Nargc & Nenvc & Nstr & _ & _ & Nrnd & Npad & Ntab1 & Ntab2 & Nlen & _ & _).
  pose proof (LEN_fit pcA phA sp brk mb draw inp Hlau) as LF. cbv zeta in LF. rewrite sp_hi_val in LF.
  pose proof (auxv_size_le (kb_rseq (in_kernel inp))). pose proof (auxv_size_ge (kb_rseq (in_kernel inp))).
  pose proof (Nat.mod_upper_bound (block_items (in_argv inp) (in_envp inp)) 2 ltac:(lia)).
  rewrite (ji_sp _ _ _ _ _ _ _ _ HJr), (ji_rand _ _ _ _ _ _ _ _ HJr), (ji_argv0 _ _ _ _ _ _ _ _ HJr). cbv zeta.
  pose proof (Zle_0_nat (pad_len inp sp draw)). pose proof (Zle_0_nat (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp))).
  rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite !(Z.mod_small (bv_unsigned sp + _) (2 ^ 64)) by lia.
  repeat split; lia.
Qed.

Lemma arg_layout_of_Jinit : ltac2:(tb__ "0|0|
S10S31S3S2cS2dVsp;Vmb;Vdraw;Vinp;R1A8S3fR2A1F_;Frho;").
Proof.
  (* LPS 727298f3: the new argument layout from the launch's numbers (InitState's [nums]) and the
     exec file name's address (InitState's [execfn_nums], Jinit's [ji_execfn]). *)
  clear - Hent Hinp. intros rho HJr. destruct Hent as (Hsp & _ & _ & _ & Hlau).
  pose proof (nums pcA phA sp brk mb draw inp Hsp Hinp Hlau) as N. cbv zeta in N.
  destruct N as (Nsp & N16 & Nargc & Nenvc & Nstr & Nlen0t & Nlen0 & Nrnd & Npad & Ntab1 & Ntab2 & Nlen & _ & _).
  pose proof (execfn_nums pcA phA sp brk mb draw inp Hsp Hinp Hlau) as (EX & EXb). cbv zeta in EX, EXb.
  pose proof (LEN_fit pcA phA sp brk mb draw inp Hlau) as LF. cbv zeta in LF. rewrite sp_hi_val in LF.
  pose proof (auxv_size_ge (kb_rseq (in_kernel inp))).
  unfold arg_layout.
  rewrite (ji_sp _ _ _ _ _ _ _ _ HJr), (ji_argc _ _ _ _ _ _ _ _ HJr), (ji_envc _ _ _ _ _ _ _ _ HJr), (ji_argv0 _ _ _ _ _ _ _ _ HJr), (ji_len0 _ _ _ _ _ _ _ _ HJr),
          (ji_rand _ _ _ _ _ _ _ _ HJr), (ji_execfn _ _ _ _ _ _ _ _ HJr), EX.
  pose proof (Zle_0_nat (pad_len inp sp draw)). pose proof (Zle_0_nat (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp))).
  pose proof (Zle_0_nat (tab (in_argv inp))). pose proof (Zle_0_nat (tab (in_envp inp))).
  rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite !Z.mod_small by lia. repeat split; lia.
Qed.

Lemma Jinit_agree : ltac2:(tb__ "0|0|
S10S10S31S3S2cS2dVsp;Vmb;Vdraw;Vinp;R2A8S12P14R3R2A3S31S3S2cS2dVsp;Vmb;Vdraw;Vinp;R3A8F_;F_;Frho';Frho;").
Proof.
  clear. intros rho rho' HJr (Hw & Hl & Hm). destruct HJr; constructor; try (rewrite <- Hw by (cbv; reflexivity); assumption); try (rewrite <- Hl; assumption).
  intros a. rewrite <- Hm. auto.
Qed.

Definition QMain : assn := ltac2:(tb__ "0|0|
S44S2S15Q40A1S15Q40A1S2S10S10S0S0S6Z0S14Q40R2A2A2S6S14Q40R2A2S3eA2A2S0S31S3S2cS2dVsp;Vmb;Vdraw;Vinp;R1A8S41S34R2A1S40R1R3A4A2A2Lrho;A2Ltid;A2Lw;").

Theorem start_main_A : ltac2:(tb__ "0|0|
S43S3Vok;S36S3S32Vm0;A1S2eVrq;A1VrhoI;A4S35A4").
Proof.

  eapply triple_seq; [exact (start0_sum_A sp brk mb draw lim inp Hent Hinp rhoI HJ ok (OKF _ K0_nil) (OKP _ K0_nil) (OKF _ K1_nil))|].
  apply triple_ex; intros L. apply triple_ex; intros rho1. apply triple_pure; intros [<-|[]]. apply triple_pure; intros Hag1. cbn [lf_state].
  eapply triple_conseq with (P := fun w => exists tid, 0 < bv_unsigned tid < PID_MAX_ENVELOPE /\ SP segsA (Kx (M1 tid)) (S_ctor rq) rho1 w); [| intros w Hw; exact Hw |].
  { intros w [Hsm [Htr (tid & Htid & Hmd)]]. exists tid. split; [exact Htid|]. split; [exact Hsm|]. split; [exact Htr | exact Hmd]. }
  apply triple_ex; intros tid. apply triple_pure; intros Htid.
  pose proof (Jinit_agree rhoI rho1 HJ Hag1) as HJ1.
  pose proof (M1_fields tid) as (Fh & Flz & Fmt & Fres & Fmaps & Fna & Flim & Fsb & Fbrk & Fisp & Fused & _).
  pose proof brk_facts as [Hbrk Hbal]. pose proof sp_facts as (Hwin & Hspr & Hsp16).
  pose proof (layout_facts rho1 HJ1) as LF. cbv zeta in LF. destruct LF as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8).
  assert (Htop : init_sp_ok (m_vmmaps (M1 tid))) by (unfold init_sp_ok; rewrite Fisp; exact Hwin).
  eapply triple_conseq; [intros w Hw; exact Hw | |].
  2:{ apply (startA_main (M1 tid) B0 rq Fh Flz Fmt Fres Fmaps Fna ltac:(rewrite Fused; unfold B0; lia) ltac:(rewrite Flim; unfold B0; lia) Htop (M1_rdr tid)
               ltac:(rewrite Fsb, Fbrk; reflexivity) ltac:(rewrite Fbrk; exact Hbrk) ltac:(rewrite Fbrk; exact Hbal) (vdso_M1 tid) (resv_apart_M1 tid) ok (OKF _ (Kx_nil _)) OKFA OKPA rho1).
      - rewrite Fisp. exact X8.
      - exact X6.
      - exact X7.
      - exact X1.
      - exact X2.
      - exact X3.
      - exact X4.
      - exact X5.
      - exact (arg_layout_of_Jinit rho1 HJ1). }
  intros w Hw. exists tid, rho1. split; [exact Htid|]. split; [exact HJ1 | exact Hw].
Qed.

Theorem start_main_ex_A : ltac2:(tb__ "0|0|
S42S3S36S3S32Vm0;A1S2eVrq;A1VrhoI;A4S35A3").
Proof.
  eapply etriple_seq; [exact (start0_sum_ex_A sp brk mb draw lim inp Hent Hinp rhoI HJ)|].
  apply etriple_ex; intros L. apply etriple_ex; intros rho1. apply etriple_pure; intros [<-|[]]. apply etriple_pure; intros Hag1. cbn [lf_state].
  eapply etriple_conseq with (P := fun w => exists tid, 0 < bv_unsigned tid < PID_MAX_ENVELOPE /\ SP segsA (Kx (M1 tid)) (S_ctor rq) rho1 w); [| intros w Hw; exact Hw |].
  { intros w [Hsm [Htr (tid & Htid & Hmd)]]. exists tid. split; [exact Htid|]. split; [exact Hsm|]. split; [exact Htr | exact Hmd]. }
  apply etriple_ex; intros tid. apply etriple_pure; intros Htid.
  pose proof (Jinit_agree rhoI rho1 HJ Hag1) as HJ1.
  pose proof (M1_fields tid) as (Fh & Flz & Fmt & Fres & Fmaps & Fna & Flim & Fsb & Fbrk & Fisp & Fused & _).
  pose proof brk_facts as [Hbrk Hbal]. pose proof sp_facts as (Hwin & Hspr & Hsp16).
  pose proof (layout_facts rho1 HJ1) as LF. cbv zeta in LF. destruct LF as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8).
  assert (Htop : init_sp_ok (m_vmmaps (M1 tid))) by (unfold init_sp_ok; rewrite Fisp; exact Hwin).
  eapply etriple_conseq; [intros w Hw; exact Hw | |].
  2:{ apply (startA_main_ex (M1 tid) B0 rq Flz Fmt Fres Fmaps Fna ltac:(rewrite Fused; unfold B0; lia) ltac:(rewrite Flim; unfold B0; lia) Htop (M1_rdr tid)
               ltac:(rewrite Fsb, Fbrk; reflexivity) ltac:(rewrite Fbrk; exact Hbrk) ltac:(rewrite Fbrk; exact Hbal) (vdso_M1 tid) (resv_apart_M1 tid) ok OKFA OKPA rho1).
      - rewrite Fisp. exact X8.
      - exact X6.
      - exact X7.
      - exact X1.
      - exact X2.
      - exact X3.
      - exact X4.
      - exact X5.
      - exact (arg_layout_of_Jinit rho1 HJ1). }
  intros w Hw. exists tid, rho1. split; [exact Htid|]. split; [exact HJ1 | exact Hw].
Qed.

End Main.
