(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanPlan AxSymExec3F.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require EntryKn.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require EntryGlue.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Img.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require KnKeepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBlock__Lib.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3L.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module BootKn1.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanPlan AxSymExec3F. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3F.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require Import EntryKn.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require Import EntryGlue.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Img. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require Import KnKeepF.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition V_TLS : nat := 7.
Definition V_TID : nat := 8.
Definition V_CANARY : nat := 9.

(* [comment removed for export] *)
Definition FUEL : nat := 3000.
Definition noscr : scripts := SCR [] [] [].

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition r_ss (r : sym_state * list sidecond * scripts) : sym_state := fst (fst r).
Definition r_scs (r : sym_state * list sidecond * scripts) : list sidecond := snd (fst r).
Definition c_kn (c : list kentry * list sidecond * list bool) : list kentry := fst (fst c).
Definition c_scs (c : list kentry * list sidecond * list bool) : list sidecond := snd (fst c).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kx : list kentry := [].  (* [comment removed for export] *)

Definition KN0 : list kentry := kn0 PH A_img_lo A_img_hi A_rw_lo A_rw_len kx.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition run1 := Eval vm_compute in (AX2F.sym_execF SEGS KN0 FUEL true [A_envloop] noscr (SS A_start sr_init [] KN0 7) []).
Definition SS1 : sym_state := Eval vm_compute in (r_ss run1).
Definition car1 := Eval vm_compute in (AX2F.carryF (s_log SS1) KN0 []).
Definition KN1 : list kentry := Eval vm_compute in (c_kn car1).
Definition SR1 : list expr := Eval vm_compute in (s_regs SS1).

(* [comment removed for export] *)
Definition SR2 : list expr := 
  sr_upd (sr_upd SR1 9 e_auxv) 10 (ELit 0).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition run2 := Eval vm_compute in (AX2F.sym_execF SEGS KN1 FUEL true [A_pnloop] noscr (SS A_envloop_exit SR2 [] KN1 7) []).
Definition SS2 : sym_state := Eval vm_compute in (r_ss run2).
Definition car2 := Eval vm_compute in (AX2F.carryF (s_log SS2) KN1 []).
Definition KN2 : list kentry := Eval vm_compute in (c_kn car2).
Definition SR2e : list expr := Eval vm_compute in (s_regs SS2).

(* [comment removed for export] *)
Definition SR3 : list expr := 
  sr_upd (sr_upd SR2e 11 e_str1) 13 (ELit 0).
Definition KN3 : list kentry := 
  List.filter (keep_b KN2 (ELit 0) A_progname (ELit 8)) KN2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition run3 := Eval vm_compute in (AX2F.sym_execF SEGS KN3 FUEL true [] noscr (SS A_pnloop_exit SR3 [] KN3 7) []).
Definition SS3 : sym_state := Eval vm_compute in (r_ss run3).
Definition car3 := Eval vm_compute in (AX2F.carryF (s_log SS3) KN3 []).
Definition KN3e : list kentry := Eval vm_compute in (c_kn car3).
Definition SR3e : list expr := Eval vm_compute in (s_regs SS3).

(* static_init_tls takes the builtin_tls path (the TLS block is in .bss, no mmap): run3 ends at the
   set_tid_address ecall, which is where the state at the next phase starts. *)
Definition KN4e : list kentry := KN3e.
Definition SR4e : list expr := SR3e.

Definition KN5 : list kentry := 
  KN4e ++ [KRange (EVar V_TID) 1 4194303].
Definition SR5 : list expr := 
  sr_upd SR4e 10 (EVar V_TID).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition run5 := Eval vm_compute in (AX2F.sym_execF SEGS KN5 FUEL true [A_ssp_sb] noscr (SS A_set_tid_ret SR5 [] KN5 9) []).
Definition SS5 : sym_state := Eval vm_compute in (r_ss run5).
Definition car5 := Eval vm_compute in (AX2F.carryF (s_log SS5) KN5 []).
Definition KN5e : list kentry := Eval vm_compute in (c_kn car5).
Definition SR5e : list expr := Eval vm_compute in (s_regs SS5).

(* [comment removed for export] *)
Definition KN6 : list kentry := 
  KWord (SA (ELit 0) A_stack_chk_guard) 8 (EVar V_CANARY)
     :: List.filter (keep_b KN5e (ELit 0) A_stack_chk_guard (ELit 8)) KN5e.
Definition SR6 : list expr := 
  sr_upd SR5e 10 (EVar V_CANARY).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition run6 := Eval vm_compute in (AX2F.sym_execF SEGS KN6 FUEL true [A_maxva_smeared] noscr (SS A_ssp_after_ld SR6 [] KN6 10) []).
Definition SS6 : sym_state := Eval vm_compute in (r_ss run6).
Definition car6 := Eval vm_compute in (AX2F.carryF (s_log SS6) KN6 []).
Definition KN6e : list kentry := Eval vm_compute in (c_kn car6).
Definition SR6e : list expr := Eval vm_compute in (s_regs SS6).

Definition MAXVA : Z := 2 ^ 47 - 1.
Definition SR7 : list expr := sr_upd SR6e 10 (ELit MAXVA).

(* [comment removed for export] *)
Definition run7 := Eval vm_compute in (AX2F.sym_execF SEGS KN6e FUEL true [A_internal_mmap_ecall] noscr (SS A_maxva_smeared SR7 [] KN6e 10) []).
Definition SS7 : sym_state := Eval vm_compute in (r_ss run7).
Definition car7 := Eval vm_compute in (AX2F.carryF (s_log SS7) KN6e []).
Definition KN_E3 : list kentry := Eval vm_compute in (c_kn car7).
Definition SR_E3 : list expr := Eval vm_compute in (s_regs SS7).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma itinerary_ok :
  (s_pc SS1, r_scs run1, c_scs car1) = (A_envloop, [], [])
  /\ (s_pc SS2, r_scs run2, c_scs car2) = (A_pnloop, [], [])
  /\ (s_pc SS3, r_scs run3, c_scs car3) = (A_set_tid_ecall, [], [])
  /\ (s_pc SS5, r_scs run5, c_scs car5) = (A_ssp_sb, [], [])
  /\ (s_pc SS6, r_scs run6, c_scs car6) = (A_maxva_smeared, [], [])
  /\ (s_pc SS7, r_scs run7, c_scs car7) = (A_internal_mmap_ecall, [], []).
Proof. vmeq_conj. Qed.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.TwB.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition V_TLS : nat := 7.
Definition V_TID : nat := 8.
Definition V_CANARY : nat := 9.

(* [comment removed for export] *)
Definition FUEL : nat := 3000.
Definition noscr : scripts := SCR [] [] [].

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition r_ss (r : sym_state * list sidecond * scripts) : sym_state := fst (fst r).
Definition r_scs (r : sym_state * list sidecond * scripts) : list sidecond := snd (fst r).
Definition c_kn (c : list kentry * list sidecond * list bool) : list kentry := fst (fst c).
Definition c_scs (c : list kentry * list sidecond * list bool) : list sidecond := snd (fst c).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kx : list kentry := [].  (* [comment removed for export] *)

Definition KN0 : list kentry := kn0 PH A_img_lo A_img_hi A_rw_lo A_rw_len kx.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition run1 := Eval vm_compute in (AX2F.sym_execF SEGS KN0 FUEL true [A_envloop] noscr (SS A_start sr_init [] KN0 7) []).
Definition SS1 : sym_state := Eval vm_compute in (r_ss run1).
Definition car1 := Eval vm_compute in (AX2F.carryF (s_log SS1) KN0 []).
Definition KN1 : list kentry := Eval vm_compute in (c_kn car1).
Definition SR1 : list expr := Eval vm_compute in (s_regs SS1).

(* [comment removed for export] *)
Definition SR2 : list expr := 
  sr_upd (sr_upd SR1 9 e_auxv) 10 (ELit 0).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition run2 := Eval vm_compute in (AX2F.sym_execF SEGS KN1 FUEL true [A_pnloop] noscr (SS A_envloop_exit SR2 [] KN1 7) []).
Definition SS2 : sym_state := Eval vm_compute in (r_ss run2).
Definition car2 := Eval vm_compute in (AX2F.carryF (s_log SS2) KN1 []).
Definition KN2 : list kentry := Eval vm_compute in (c_kn car2).
Definition SR2e : list expr := Eval vm_compute in (s_regs SS2).

(* [comment removed for export] *)
Definition SR3 : list expr := 
  sr_upd (sr_upd SR2e 11 e_str1) 13 (ELit 0).
Definition KN3 : list kentry := 
  List.filter (keep_b KN2 (ELit 0) A_progname (ELit 8)) KN2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition run3 := Eval vm_compute in (AX2F.sym_execF SEGS KN3 FUEL true [] noscr (SS A_pnloop_exit SR3 [] KN3 7) []).
Definition SS3 : sym_state := Eval vm_compute in (r_ss run3).
Definition car3 := Eval vm_compute in (AX2F.carryF (s_log SS3) KN3 []).
Definition KN3e : list kentry := Eval vm_compute in (c_kn car3).
Definition SR3e : list expr := Eval vm_compute in (s_regs SS3).

(* static_init_tls takes the builtin_tls path (the TLS block is in .bss, no mmap): run3 ends at the
   set_tid_address ecall, which is where the state at the next phase starts. *)
Definition KN4e : list kentry := KN3e.
Definition SR4e : list expr := SR3e.

Definition KN5 : list kentry := 
  KN4e ++ [KRange (EVar V_TID) 1 4194303].
Definition SR5 : list expr := 
  sr_upd SR4e 10 (EVar V_TID).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition run5 := Eval vm_compute in (AX2F.sym_execF SEGS KN5 FUEL true [A_ssp_sb] noscr (SS A_set_tid_ret SR5 [] KN5 9) []).
Definition SS5 : sym_state := Eval vm_compute in (r_ss run5).
Definition car5 := Eval vm_compute in (AX2F.carryF (s_log SS5) KN5 []).
Definition KN5e : list kentry := Eval vm_compute in (c_kn car5).
Definition SR5e : list expr := Eval vm_compute in (s_regs SS5).

(* [comment removed for export] *)
Definition KN6 : list kentry := 
  KWord (SA (ELit 0) A_stack_chk_guard) 8 (EVar V_CANARY)
     :: List.filter (keep_b KN5e (ELit 0) A_stack_chk_guard (ELit 8)) KN5e.
Definition SR6 : list expr := 
  sr_upd SR5e 10 (EVar V_CANARY).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition run6 := Eval vm_compute in (AX2F.sym_execF SEGS KN6 FUEL true [A_maxva_smeared] noscr (SS A_ssp_after_ld SR6 [] KN6 10) []).
Definition SS6 : sym_state := Eval vm_compute in (r_ss run6).
Definition car6 := Eval vm_compute in (AX2F.carryF (s_log SS6) KN6 []).
Definition KN6e : list kentry := Eval vm_compute in (c_kn car6).
Definition SR6e : list expr := Eval vm_compute in (s_regs SS6).

Definition MAXVA : Z := 2 ^ 47 - 1.
Definition SR7 : list expr := sr_upd SR6e 10 (ELit MAXVA).

(* [comment removed for export] *)
Definition run7 := Eval vm_compute in (AX2F.sym_execF SEGS KN6e FUEL true [A_internal_mmap_ecall] noscr (SS A_maxva_smeared SR7 [] KN6e 10) []).
Definition SS7 : sym_state := Eval vm_compute in (r_ss run7).
Definition car7 := Eval vm_compute in (AX2F.carryF (s_log SS7) KN6e []).
Definition KN_E3 : list kentry := Eval vm_compute in (c_kn car7).
Definition SR_E3 : list expr := Eval vm_compute in (s_regs SS7).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma itinerary_ok :
  (s_pc SS1, r_scs run1, c_scs car1) = (A_envloop, [], [])
  /\ (s_pc SS2, r_scs run2, c_scs car2) = (A_pnloop, [], [])
  /\ (s_pc SS3, r_scs run3, c_scs car3) = (A_set_tid_ecall, [], [])
  /\ (s_pc SS5, r_scs run5, c_scs car5) = (A_ssp_sb, [], [])
  /\ (s_pc SS6, r_scs run6, c_scs car6) = (A_maxva_smeared, [], [])
  /\ (s_pc SS7, r_scs run7, c_scs car7) = (A_internal_mmap_ecall, [], []).
Proof. vmeq_conj. Qed.
End TwB.
End BootKn1.

(* [comment removed for export] *)
Module BootKn2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanPlan AxSymExec3F. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3F.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require Import EntryKn EntryGlue.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Img. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require Import AsanBootKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require Import KnKeepF.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition SHADOW_STOPS : list Z := [A_internal_mmap_ecall; A_istrncpy].

(* [comment removed for export] *)
Definition SHB_LO : Z := 0x7fff7000.        (* [comment removed for export] *)
Definition SHB_HI : Z := 0x10007fff8000.    (* [comment removed for export] *)
Definition KDJ_TLS : kentry := KDisj (SA (EVar V_TLS) 0) (ELit 4096) (SA (ELit 0) SHB_LO) (ELit (SHB_HI - SHB_LO)).
Definition KN_E3d : list kentry := KDJ_TLS :: KN_E3.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition SR8 : list expr := sr_upd SR_E3 10 (ELit 0x7fff7000).
Definition run8 := Eval vm_compute in (AX2F.sym_execF SEGS KN_E3d FUEL true SHADOW_STOPS noscr (SS A_internal_mmap_ret SR8 [] KN_E3d 10) []).
Definition SS8 : sym_state := Eval vm_compute in (r_ss run8).
Definition car8 := Eval vm_compute in (AX2F.carryF (s_log SS8) KN_E3d []).
Definition KN8e : list kentry := Eval vm_compute in (c_kn car8).
Definition SR8e : list expr := Eval vm_compute in (s_regs SS8).
(* [comment removed for export] *)
Definition run8n := Eval vm_compute in (AX2F.sym_execF SEGS KN_E3d FUEL true [A_spin_shadow0] noscr (SS A_internal_mmap_ret (sr_upd SR_E3 10 (ELit (2 ^ 64 - 12))) [] KN_E3d 10) []).
Definition run8x := Eval vm_compute in (AX2F.sym_execF SEGS KN_E3d FUEL true [A_spin_shadow0] noscr (SS A_internal_mmap_ret (sr_upd SR_E3 10 (ELit (2 ^ 64 - 17))) [] KN_E3d 10) []).

(* [comment removed for export] *)
Definition SR9 : list expr := sr_upd SR8e 10 (ELit 0x8fff7000).
Definition run9 := Eval vm_compute in (AX2F.sym_execF SEGS KN8e FUEL true SHADOW_STOPS noscr (SS A_internal_mmap_ret SR9 [] KN8e 10) []).
Definition SS9 : sym_state := Eval vm_compute in (r_ss run9).
Definition car9 := Eval vm_compute in (AX2F.carryF (s_log SS9) KN8e []).
Definition KN9e : list kentry := Eval vm_compute in (c_kn car9).
Definition SR9e : list expr := Eval vm_compute in (s_regs SS9).
Definition run9n := Eval vm_compute in (AX2F.sym_execF SEGS KN8e FUEL true [A_spin_shadow1] noscr (SS A_internal_mmap_ret (sr_upd SR8e 10 (ELit (2 ^ 64 - 12))) [] KN8e 10) []).
Definition run9x := Eval vm_compute in (AX2F.sym_execF SEGS KN8e FUEL true [A_spin_shadow1] noscr (SS A_internal_mmap_ret (sr_upd SR8e 10 (ELit (2 ^ 64 - 17))) [] KN8e 10) []).

(* [comment removed for export] *)
Definition SR10 : list expr := sr_upd SR9e 10 (ELit 0x2008fff7000).
Definition run10 := Eval vm_compute in (AX2F.sym_execF SEGS KN9e FUEL true SHADOW_STOPS noscr (SS A_internal_mmap_ret SR10 [] KN9e 10) []).
Definition SS10 : sym_state := Eval vm_compute in (r_ss run10).
Definition car10 := Eval vm_compute in (AX2F.carryF (s_log SS10) KN9e []).
Definition KN10e : list kentry := Eval vm_compute in (c_kn car10).
Definition SR10e : list expr := Eval vm_compute in (s_regs SS10).
Definition run10n := Eval vm_compute in (AX2F.sym_execF SEGS KN9e FUEL true [A_spin_shadow2] noscr (SS A_internal_mmap_ret (sr_upd SR9e 10 (ELit (2 ^ 64 - 12))) [] KN9e 10) []).
Definition run10x := Eval vm_compute in (AX2F.sym_execF SEGS KN9e FUEL true [A_spin_shadow2] noscr (SS A_internal_mmap_ret (sr_upd SR9e 10 (ELit (2 ^ 64 - 17))) [] KN9e 10) []).

(* [comment removed for export] *)
Definition junk5 (sr : list expr) (v : nat) : list expr :=
  sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr 11 (EVar v)) 12 (EVar (S v))) 13 (EVar (S (S v)))) 14 (EVar (3 + v))) 15 (EVar (4 + v)).
Definition sealed_kn (dst : Z) (kn : list kentry) : list kentry :=
  [KWord (SA (ELit 0) dst) 8 (ELit SEALED_U64); KZero (SA (ELit 0) (dst + 8)) (ELit 4087)] ++ kimg_cut dst (dst + 4095) kn.
Definition SR11 : list expr := junk5 SR10e 16.
Definition KN11 : list kentry := sealed_kn A_binary_name_cache KN10e.

(* [comment removed for export] *)
Definition run11 := Eval vm_compute in (AX2F.sym_execF SEGS KN11 FUEL true SHADOW_STOPS noscr (SS A_cbn_mid SR11 [] KN11 21) []).
Definition SS11 : sym_state := Eval vm_compute in (r_ss run11).
Definition car11 := Eval vm_compute in (AX2F.carryF (s_log SS11) KN11 []).
Definition KN11e : list kentry := Eval vm_compute in (c_kn car11).
Definition SR11e : list expr := Eval vm_compute in (s_regs SS11).

Definition SR12 : list expr := junk5 SR11e 21.
Definition KN12 : list kentry := sealed_kn A_process_name_cache KN11e.

(* [comment removed for export] *)
Definition run12 := Eval vm_compute in (AX2F.sym_execF SEGS KN12 FUEL true SHADOW_STOPS noscr (SS A_init_after_cbn SR12 [] KN12 26) []).
Definition SS12 : sym_state := Eval vm_compute in (r_ss run12).
Definition car12 := Eval vm_compute in (AX2F.carryF (s_log SS12) KN12 []).
Definition KN_E6 : list kentry := Eval vm_compute in (c_kn car12).
Definition SR_E6 : list expr := Eval vm_compute in (s_regs SS12).

(* [comment removed for export] *)
Lemma itinerary2_ok :
  (s_pc SS8, r_scs run8, c_scs car8) = (A_internal_mmap_ecall, [], []) /\ KN8e = KN_E3d /\ KN9e = KN_E3d
  /\ map (fun r => sr_get SR8e (Z_to_bv 5 r)) [10; 11; 12; 13; 15; 17] = [ELit 0x8fff7000; ELit (2 ^ 41); ELit 0; ELit 0x104022; ELit 0; ELit 222]
  /\ (s_pc (r_ss run8n), r_scs run8n, s_log (r_ss run8n)) = (A_spin_shadow0, [], [])
  /\ (s_pc (r_ss run8x), r_scs run8x, s_log (r_ss run8x)) = (A_spin_shadow0, [], [])
  /\ (s_pc SS9, r_scs run9, c_scs car9) = (A_internal_mmap_ecall, [], [])
  /\ map (fun r => sr_get SR9e (Z_to_bv 5 r)) [10; 11; 12; 13; 15; 17] = [ELit 0x2008fff7000; ELit 0xdfff0001000; ELit 3; ELit 0x104022; ELit 0; ELit 222]
  /\ (s_pc (r_ss run9n), r_scs run9n, s_log (r_ss run9n)) = (A_spin_shadow1, [], [])
  /\ (s_pc (r_ss run9x), r_scs run9x, s_log (r_ss run9x)) = (A_spin_shadow1, [], [])
  /\ (s_pc SS10, r_scs run10, c_scs car10) = (A_istrncpy, [], [])
  /\ map (fun r => sr_get SR10e (Z_to_bv 5 r)) [1; 10; 11; 12] = [ELit A_cbn_mid; ELit A_binary_name_cache; ELit A_sealed_str; ELit 4095]
  /\ (s_pc (r_ss run10n), r_scs run10n, s_log (r_ss run10n)) = (A_spin_shadow2, [], [])
  /\ (s_pc (r_ss run10x), r_scs run10x, s_log (r_ss run10x)) = (A_spin_shadow2, [], [])
  /\ (s_pc SS11, r_scs run11, c_scs car11) = (A_istrncpy, [], [])
  /\ map (fun r => sr_get SR11e (Z_to_bv 5 r)) [1; 10; 11; 12] = [ELit A_init_after_cbn; ELit A_process_name_cache; ELit A_sealed_str; ELit 4095]
  /\ (s_pc SS12, r_scs run12, c_scs car12) = (A_internal_mmap_ecall, [], [])
  /\ map (fun r => sr_get SR_E6 (Z_to_bv 5 r)) [10; 11; 12; 13; 14; 15; 17] = [ELit 0; ELit 65536; ELit 3; ELit 34; ELit (2 ^ 64 - 1); ELit 0; ELit 222].
Proof. vmeq_conj. Qed.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1.TwB.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition SHADOW_STOPS : list Z := [A_internal_mmap_ecall; A_istrncpy].

(* [comment removed for export] *)
Definition SHB_LO : Z := 0x7fff7000.        (* [comment removed for export] *)
Definition SHB_HI : Z := 0x10007fff8000.    (* [comment removed for export] *)
Definition KDJ_TLS : kentry := KDisj (SA (EVar V_TLS) 0) (ELit 4096) (SA (ELit 0) SHB_LO) (ELit (SHB_HI - SHB_LO)).
Definition KN_E3d : list kentry := KDJ_TLS :: KN_E3.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition SR8 : list expr := sr_upd SR_E3 10 (ELit 0x7fff7000).
Definition run8 := Eval vm_compute in (AX2F.sym_execF SEGS KN_E3d FUEL true SHADOW_STOPS noscr (SS A_internal_mmap_ret SR8 [] KN_E3d 10) []).
Definition SS8 : sym_state := Eval vm_compute in (r_ss run8).
Definition car8 := Eval vm_compute in (AX2F.carryF (s_log SS8) KN_E3d []).
Definition KN8e : list kentry := Eval vm_compute in (c_kn car8).
Definition SR8e : list expr := Eval vm_compute in (s_regs SS8).
(* [comment removed for export] *)
Definition run8n := Eval vm_compute in (AX2F.sym_execF SEGS KN_E3d FUEL true [A_spin_shadow0] noscr (SS A_internal_mmap_ret (sr_upd SR_E3 10 (ELit (2 ^ 64 - 12))) [] KN_E3d 10) []).
Definition run8x := Eval vm_compute in (AX2F.sym_execF SEGS KN_E3d FUEL true [A_spin_shadow0] noscr (SS A_internal_mmap_ret (sr_upd SR_E3 10 (ELit (2 ^ 64 - 17))) [] KN_E3d 10) []).

(* [comment removed for export] *)
Definition SR9 : list expr := sr_upd SR8e 10 (ELit 0x8fff7000).
Definition run9 := Eval vm_compute in (AX2F.sym_execF SEGS KN8e FUEL true SHADOW_STOPS noscr (SS A_internal_mmap_ret SR9 [] KN8e 10) []).
Definition SS9 : sym_state := Eval vm_compute in (r_ss run9).
Definition car9 := Eval vm_compute in (AX2F.carryF (s_log SS9) KN8e []).
Definition KN9e : list kentry := Eval vm_compute in (c_kn car9).
Definition SR9e : list expr := Eval vm_compute in (s_regs SS9).
Definition run9n := Eval vm_compute in (AX2F.sym_execF SEGS KN8e FUEL true [A_spin_shadow1] noscr (SS A_internal_mmap_ret (sr_upd SR8e 10 (ELit (2 ^ 64 - 12))) [] KN8e 10) []).
Definition run9x := Eval vm_compute in (AX2F.sym_execF SEGS KN8e FUEL true [A_spin_shadow1] noscr (SS A_internal_mmap_ret (sr_upd SR8e 10 (ELit (2 ^ 64 - 17))) [] KN8e 10) []).

(* [comment removed for export] *)
Definition SR10 : list expr := sr_upd SR9e 10 (ELit 0x2008fff7000).
Definition run10 := Eval vm_compute in (AX2F.sym_execF SEGS KN9e FUEL true SHADOW_STOPS noscr (SS A_internal_mmap_ret SR10 [] KN9e 10) []).
Definition SS10 : sym_state := Eval vm_compute in (r_ss run10).
Definition car10 := Eval vm_compute in (AX2F.carryF (s_log SS10) KN9e []).
Definition KN10e : list kentry := Eval vm_compute in (c_kn car10).
Definition SR10e : list expr := Eval vm_compute in (s_regs SS10).
Definition run10n := Eval vm_compute in (AX2F.sym_execF SEGS KN9e FUEL true [A_spin_shadow2] noscr (SS A_internal_mmap_ret (sr_upd SR9e 10 (ELit (2 ^ 64 - 12))) [] KN9e 10) []).
Definition run10x := Eval vm_compute in (AX2F.sym_execF SEGS KN9e FUEL true [A_spin_shadow2] noscr (SS A_internal_mmap_ret (sr_upd SR9e 10 (ELit (2 ^ 64 - 17))) [] KN9e 10) []).

(* [comment removed for export] *)
Definition junk5 (sr : list expr) (v : nat) : list expr :=
  sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr 11 (EVar v)) 12 (EVar (S v))) 13 (EVar (S (S v)))) 14 (EVar (3 + v))) 15 (EVar (4 + v)).
Definition sealed_kn (dst : Z) (kn : list kentry) : list kentry :=
  [KWord (SA (ELit 0) dst) 8 (ELit SEALED_U64); KZero (SA (ELit 0) (dst + 8)) (ELit 4087)] ++ kimg_cut dst (dst + 4095) kn.
Definition SR11 : list expr := junk5 SR10e 16.
Definition KN11 : list kentry := sealed_kn A_binary_name_cache KN10e.

(* [comment removed for export] *)
Definition run11 := Eval vm_compute in (AX2F.sym_execF SEGS KN11 FUEL true SHADOW_STOPS noscr (SS A_cbn_mid SR11 [] KN11 21) []).
Definition SS11 : sym_state := Eval vm_compute in (r_ss run11).
Definition car11 := Eval vm_compute in (AX2F.carryF (s_log SS11) KN11 []).
Definition KN11e : list kentry := Eval vm_compute in (c_kn car11).
Definition SR11e : list expr := Eval vm_compute in (s_regs SS11).

Definition SR12 : list expr := junk5 SR11e 21.
Definition KN12 : list kentry := sealed_kn A_process_name_cache KN11e.

(* [comment removed for export] *)
Definition run12 := Eval vm_compute in (AX2F.sym_execF SEGS KN12 FUEL true SHADOW_STOPS noscr (SS A_init_after_cbn SR12 [] KN12 26) []).
Definition SS12 : sym_state := Eval vm_compute in (r_ss run12).
Definition car12 := Eval vm_compute in (AX2F.carryF (s_log SS12) KN12 []).
Definition KN_E6 : list kentry := Eval vm_compute in (c_kn car12).
Definition SR_E6 : list expr := Eval vm_compute in (s_regs SS12).

(* [comment removed for export] *)
Lemma itinerary2_ok :
  (s_pc SS8, r_scs run8, c_scs car8) = (A_internal_mmap_ecall, [], []) /\ KN8e = KN_E3d /\ KN9e = KN_E3d
  /\ map (fun r => sr_get SR8e (Z_to_bv 5 r)) [10; 11; 12; 13; 15; 17] = [ELit 0x8fff7000; ELit (2 ^ 41); ELit 0; ELit 0x104022; ELit 0; ELit 222]
  /\ (s_pc (r_ss run8n), r_scs run8n, s_log (r_ss run8n)) = (A_spin_shadow0, [], [])
  /\ (s_pc (r_ss run8x), r_scs run8x, s_log (r_ss run8x)) = (A_spin_shadow0, [], [])
  /\ (s_pc SS9, r_scs run9, c_scs car9) = (A_internal_mmap_ecall, [], [])
  /\ map (fun r => sr_get SR9e (Z_to_bv 5 r)) [10; 11; 12; 13; 15; 17] = [ELit 0x2008fff7000; ELit 0xdfff0001000; ELit 3; ELit 0x104022; ELit 0; ELit 222]
  /\ (s_pc (r_ss run9n), r_scs run9n, s_log (r_ss run9n)) = (A_spin_shadow1, [], [])
  /\ (s_pc (r_ss run9x), r_scs run9x, s_log (r_ss run9x)) = (A_spin_shadow1, [], [])
  /\ (s_pc SS10, r_scs run10, c_scs car10) = (A_istrncpy, [], [])
  /\ map (fun r => sr_get SR10e (Z_to_bv 5 r)) [1; 10; 11; 12] = [ELit A_cbn_mid; ELit A_binary_name_cache; ELit A_sealed_str; ELit 4095]
  /\ (s_pc (r_ss run10n), r_scs run10n, s_log (r_ss run10n)) = (A_spin_shadow2, [], [])
  /\ (s_pc (r_ss run10x), r_scs run10x, s_log (r_ss run10x)) = (A_spin_shadow2, [], [])
  /\ (s_pc SS11, r_scs run11, c_scs car11) = (A_istrncpy, [], [])
  /\ map (fun r => sr_get SR11e (Z_to_bv 5 r)) [1; 10; 11; 12] = [ELit A_init_after_cbn; ELit A_process_name_cache; ELit A_sealed_str; ELit 4095]
  /\ (s_pc SS12, r_scs run12, c_scs car12) = (A_internal_mmap_ecall, [], [])
  /\ map (fun r => sr_get SR_E6 (Z_to_bv 5 r)) [10; 11; 12; 13; 14; 15; 17] = [ELit 0; ELit 65536; ELit 3; ELit 34; ELit (2 ^ 64 - 1); ELit 0; ELit 222].
Proof. vmeq_conj. Qed.
End TwB.
End BootKn2.

(* [comment removed for export] *)
Module BootKn3a.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AxNfCodec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanPlan AxSymExec3F. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3F.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require EntryKn EntryGlue. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBlock__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.NodesMmDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.MallocSymAux.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Img. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require Import KnKeepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require Import AxSymExec3L.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Definition IT_Kn3a : itab := AX2F.mk_itab_rs SEGS [
  (260316, 762%nat); (402140, 22%nat); (402304, 6%nat); (402344, 10%nat); (408292, 12%nat); (409980, 4%nat); (410020, 1%nat); (414704, 83%nat); (415876, 1193%nat); (423644, 15%nat); (423740, 16%nat); (424476, 9%nat); (424600, 10%nat); (424692, 1%nat); (426616, 8%nat); (426656, 1%nat); (427360, 21%nat); (432632, 20%nat); (432728, 7%nat); (516196, 261%nat)] PTLeaf.
Lemma IT_Kn3a_ok : itab_sound SEGS IT_Kn3a.
Proof. apply AX2F.mk_itab_rs_sound. apply AX2F.itab_leaf_sound. Qed.

Definition F8 : nat := 8000.
Definition STOPS3 : list Z := [A_internal_mmap_ecall; A_maxva_smeared; A_spin_mmapordie; A_spin_noreserve].

(* [comment removed for export] *)
Definition DS_E6 : list (saddr * expr) :=
  [(SA (EVar 0) (- 0x800000), ELit 0x1800000); (SA (ELit 0) A_img_lo, ELit (A_img_hi - A_img_lo));
   (SA (ELit 0) SHB_LO, ELit (SHB_HI - SHB_LO));
   (SA (ELit 0x2008fff7000) 0, ELit 0xdfff0001000); (SA (ELit 0x8fff7000) 0, ELit (2 ^ 41)); (SA (ELit 0x7fff7000) 0, ELit (2 ^ 28))].

(* [comment removed for export] *)
Definition SR13 : list expr := sr_upd SR_E6 10 (EVar 26).
Definition KCa3a_1 : list kentry := Eval vm_compute in (NFC.d_kl "$011$:00,$-.061$:00,$-.041$:'%,051$:'%,0',%###-#/,#&&$,'/'071$:00,$-.010,+,.@#?0$.+/'.&071$:00,$-.000,$-.00'.$,#&071$:00,$-.000$%.+.%#.'00--.,,-&&%./.071$:00,$-.00@,-.#/,/@&,000,.%#$&@'+@&,071$:00,$-.00$'++$##$&000@,,&,'+/@%&071$:00,$-.00$%.+.%#.'000$-@&.@&@071$:00,$-.01700'%,0010$$'?800010$$&?80&#+###'-@#&/@$+,-$4010$$%?80$#$&.&0010$$$?80,$-.0010$$#?80/+/@<").
Definition KCa3a_2 : list kentry := Eval vm_compute in (NFC.d_kl "$0010$#@?800010$#/?80&-,/+8010$#.740'4010$#-?80,$'%.0010$#,?80'@,0010$#+?80,$-.0010$#'?80@-$+@0010$#&?80&'.,%0000$#$&.&080'%,0010$#%?802010$#$?80+.'@#0010$##?820100,@?010@@?80&,..&0010,-?800010,.?800010,/?400").
Definition KCa3a_3 : list kentry := Eval vm_compute in (NFC.d_kl "$0010@/?80,$'%.0010@.?80%%'/-8010,/740$-'#'##+#4010,@?80&#+###'-@#&/@$+,-$4010&&?800010&%?800010&$?800010&#?800010%@?800010%/?800010%.?800010%-?800010%,?80,$'%.0010%+?802010%'?80+.'@#0010%&?80,$'%.0").
Definition KCa3a_4 : list kentry := Eval vm_compute in (NFC.d_kl "$0010%%?80&%/+-8000$#$&.-080$$%+/+.$/%$$%$@.'+8100$#$&..00'%'>000$#$.#%080$$%+/+.$/%$$%$@.'+8100$#$.#&00'%'>000,$'&$010271700'%,000$%.+.%#.'00--.,,-&&%./.0000,$#/&080$%.+.%'@@0000,$'%/080+,-%./&'&.'%'>000$#$&.$0820100$.?010$.?80&#+###'-@#&/@$+,-$4000+/&,+080$$'.&2010$-?8202010400$0110%0010$,?80',../0010$+?80+.'@#0010$'?80,$'%.0").
Definition KCa3a_5 : list kentry := Eval vm_compute in (NFC.d_kl "$0010$&?80&%@/%0000,$'%.040,$-.0010$%?80+.'@'0010$$?80'-#-$8010@?80+$@%'0010.?811010-?820100$0010,?80+$@''0010'?800010&?800010%?800010$?800010?800017%$0819000'.-#@.0819010+.?800").
Definition KCa3a_6 : list kentry := Eval vm_compute in (NFC.d_kl "$0010+-?800010+,?800010++?800010+'?800010+&?800010+%?80'.-$,+0010+$?820201020400$011400$0120%$0010+#?820201020400$011400$0120%$0010'@?80+%#''0010'.?80+$//-8017&0800017%0817017$0817017$'0820170$'0017$.080'.-$-$0017'0418").
Definition KCa3a_7 : list kentry := Eval vm_compute in (NFC.d_kl "$0017+0404000'.-$,+01020170817017%%0820170+,0017+,0802010,&?800010,%?800010,$?800010,#?820170+-0010+@?80'.-#,'0010+/?820170+,0017+-0820170%&,0000'.-$,/080$0000'.-$,.080+.0000'.-#,/0800000'.-#,-080&%0").
Definition KCa3a_8 : list kentry := Eval vm_compute in (NFC.d_kl "$0000'.-$,@0802000'.-$,-080'.-#,'0000'.-#,.080$0000'.-#,,0800000'.-#,+080+.#-+0010'/?820201020400$011400$0120%$0000'.-$,'0820201020400$011400$0120%$0000'.-$-#080'%,0000'.-$--0816010$/?820201020400$01120400$012400$0140%$0010%#?800010&,?80'%,0010&-?80$6010&.?80-0010&/?80,$.+0000'.-$,,0820201020400$011400$0120&0").
Definition KCa3a_9 : list kentry := Eval vm_compute in (NFC.d_kl "$0000'.-#,%08202010400$0110%0010/?800010$#?800010$@?800010%$?800010&'?800010&+?800010&@?800010'#?800010'$?800010+?820100$0510+,-%-,+/,%/'%0+,-%./&'&.'#&0410%0520201020400$01120400$012400$0140%&0+,-%-,+/,%/,'0+,-%./&'&.'%+05112$#-05120%@0").
Definition KCa3a_10 : list kentry := Eval vm_compute in (NFC.d_kl "$05130$$&''>5140%'&%/05150%+,#,##-+<610,+,.@#?0,+,.@$0110,+,.@#?0,+,-.-0110$#.?08110@-?0&.0110,,?0&0110'-?0,00100811010$0820201020400$011400$0120%$0010%084024021120201020400$01120400$012130%$20201020400$011400$012&08060201020400$011400$012'080,$.+00201020400$011400$012+08080201020400$011400$012,080-0").
Definition KCa3a_11 : list kentry := Eval vm_compute in (NFC.d_kl "$00201020400$011400$012-080:0201020400$011400$012.080$60201020400$011400$012/080%00201020400$011400$012@08160201020400$011400$012$#080<0201020400$011400$012$$080'%,00201020400$011400$012$%080$60201020400$011400$012$&08150201020400$011400$012$'080$80201020400$011400$012$+08150201020400$011400$012$,080%>0201020400$011400$012$-08000201020400$011400$012$.080&20201020400$011400$012$/0820201020400$01120400$012400$0140%$00201020400$011400$012$@08000201020400$011400$012%#0800").
Definition KCa3a_12 : list kentry := Eval vm_compute in (NFC.d_kl "$02201020400$01120400$012400$014%$00%0$92201020400$011400$012%$020130213,$-.0+/&,+03+/&,,0,$#/&03,$#/'0,$'%.03,$'%.8,$'%/03,$'%@0,$'&$03,$'&$2$#$&.$03$#$&.%0$#$&.&03$#$&.'0$#$&.-03$#$.#$>$#$.#%03$#%$%->'.-#,%03'.-#,&0'.-#,+03'.-#,@0'.-#@.03'.-#@/0'.-$,&03'.-$,+2'.-$,,0").
Definition KCa3a_13 : list kentry := Eval vm_compute in (NFC.d_kl "?3'.-$-$0'.-$--03'.-$-.0'.--.#0600+.#@+00'%@,.,0417'%,0517'%,0+,-%./%./$%#/071700'%,000,$-.00'.$,#&071700'%,010,+,.@#?0/.'-/-0117'808117+80/8117$+00&0117$/00&0117%&00&&0117+.00&-/061700'%,05182&%./@+>").
Definition KN13 : list kentry := ltac:(nf_rope (KCa3a_1 ++ KCa3a_2 ++ KCa3a_3 ++ KCa3a_4 ++ KCa3a_5 ++ KCa3a_6 ++ KCa3a_7 ++ KCa3a_8 ++ KCa3a_9 ++ KCa3a_10 ++ KCa3a_11 ++ KCa3a_12 ++ KCa3a_13) ((kn_grant_d DS_E6 26 65536 KN_E6))).
Lemma KN13_eq : kn_grant_d DS_E6 26 65536 KN_E6 = KN13. Proof. kn_fast. Qed.


(* [comment removed for export] *)
Definition run13a := ltac:(nf_run KN13 ((AX2L.sym_execFS6 SEGS IT_Kn3a KN13 F8 true STOPS3 noscr (SS A_internal_mmap_ret SR13 [] KN13 27) []))).
Definition PC13a : Z := Eval lazy in (s_pc (fst (fst run13a))).
Definition SR13a : list expr := Eval lazy in (s_regs (fst (fst run13a))).
Definition LG13a : list sentry := s_log (fst (fst run13a)).
Definition SK13a : list kentry := s_know (fst (fst run13a)).
Definition NX13a : nat := Eval lazy in (s_next (fst (fst run13a))).
Definition SC13a : list sidecond := Eval lazy in (snd (fst run13a)).
Definition SP13a : scripts := Eval lazy in (snd run13a).
Lemma run13a_eq : sym_exec SEGS F8 true STOPS3 noscr (SS A_internal_mmap_ret SR13 [] KN13 27) [] = (SSR PC13a SR13a LG13a SK13a NX13a None, SC13a, SP13a).
Proof. apply (AX2L.sym_exec_viaFS6 SEGS IT_Kn3a KN13); [exact IT_Kn3a_ok | reflexivity | vm_cast_no_check (eq_refl run13a)]. Qed.
Definition KCa3a_14 : list kentry := Eval vm_compute in (NFC.d_kl "$0010,/?40.201$:$,-08201$:0,#%001$:$,,080-.,&>01$:$,+080$#&-&601$:,#&080$#%$'.:01$:,#%080+.+#%0000@-$,#08201$:0,#'0010$#.?80+.+#%0010$#-?80$#%$&@0010$#,?820100,@?010$#+?80&,$-,001$:$,'08201$:0,##001$:$,&080,@-+:01$:$,%080./,#801$:,#$080$#%$'.801$:,##080+.+#%0").
Definition KCa3a_15 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$,$08201$:0+@/001$:$,#080-.',001$:$+@080.#&$>01$:+@@080$#%$'.601$:+@/080+.+#%001$:$+/08201$:0+@-001$:$+.080/$+'201$:$+-080/$+%801$:+@.080$#%$'.401$:+@-080+.+#%001$:$+,08201$:0+@+001$:$++080-$-%:01$:$+'080-.'&801$:+@,080$#%$'.201$:+@+080+.+#%001$:$+&08201$:0+@&0").
Definition KCa3a_16 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$+%080-$+.:01$:$+$080/--@>01$:+@'080$#%$'.001$:+@&080+.+#%001$:$+#08201$:0+@$001$:$'@080$#-+$401$:$'/080,-&-801$:+@%080$#%$'-801$:+@$080+.'@/001$:$'.08201$:0+/@001$:$'-080/$''001$:$',080,,#,001$:+@#080$#%$'-001$:+/@080+.+#%001$:$'+08201$:0+/.001$:$''080/&/&2").
Definition KCa3a_17 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$'&080.%''<01$:+//080$#%$',001$:+/.080+.+#,001$:$'%08201$:0+/,001$:$'$080/&-@:01$:$'#080$#$'#201$:+/-080$#%$'+001$:+/,080+.+#%001$:$&@08201$:0+/'001$:$&/080@+.,>01$:$&.080/--/<01$:+/+080$#%$''001$:+/'080+.+#,001$:$&-08201$:0+/%001$:$&,080@+-/:01$:$&+080./,&<").
Definition KCa3a_18 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:+/&080$#%$'&801$:+/%080+.'@/001$:$&'08201$:0+/#001$:$&&080$#+#'>01$:$&%080/,#+601$:+/$080$#%$'&601$:+/#080+.+#%001$:$&$08201$:0+./001$:$&#080/$&,001$:$%@080,@-%>01$:+.@080$#%$'&401$:+./080+.+#%001$:$%/08201$:0+.-001$:$%.080@&%@<01$:$%-080,'%,:01$:+..080$#%$'&2").
Definition KCa3a_19 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:+.-080+.+#%001$:$%,08201$:0+.+001$:$%+080@&%#401$:$%'080$$#/$:01$:+.,080$#%$'&001$:+.+080+.+#%001$:$%&08201$:0+.&001$:$%%080/+@/<01$:$%$080/---801$:+.'080$#%$'%001$:+.&080+.+#,001$:$%#08201$:0+.$001$:$$@080$#&+,201$:$$/080-,'+>01$:+.%080$#%$'$001$:+.$080+.+#%0").
Definition KCa3a_20 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$$.08201$:0+-@001$:$$-080..+'801$:$$,080@&$.201$:+.#080$#%$'#001$:+-@080+.+#,001$:$$+08201$:0+-.001$:$$'080$#-&/001$:$$&080,.$-401$:+-/080$#%$&@001$:+-.080+.+#%0010$#'?80,#$%@8010$#&?80,#$&%:010$#%?80&#+###'-@#&/@$+,-$4010$#$?80,#$%@0010$##?80+.+#%0010@@?80,#$&%8").
Definition KCa3a_21 : list kentry := Eval vm_compute in (NFC.d_kl "$0010@/?80$#%$&@0010@.?80%%-@%801$:$$%08201$:0+-,001$:$$$080.$-&>01$:$$#080/+&@<01$:+--080,#$'%601$:+-,080+.+#%001$:$#@08201$:0+-'001$:$#/080--.%201$:$#.080@-,#601$:+-+080,#$'%401$:+-'080+.+#%001$:$#-08201$:0+-%001$:$#,080$$#$+801$:$#+080,@$'201$:+-&080,#$'%2").
Definition KCa3a_22 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:+-%080+.+#%001$:$#'08201$:0+-#001$:$#&080,@#'001$:$#%080--.#601$:+-$080,#$'%001$:+-#080+.+#%001$:$#$08201$:0+,/001$:$##080./@/801$:@@080@-+/<01$:+,@080,#$'$001$:+,/080+.+#,001$:@/08201$:0+,-001$:@.080-&,+001$:@-080./@,>01$:+,.080,#$'#801$:+,-080+.'@/0").
Definition KCa3a_23 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:@,08201$:0+,+001$:@+080-+@,001$:@'080$#/%-:01$:+,,080,#$'#001$:+,+080+.+#%001$:@&08201$:0+,&001$:@%080@-&,>01$:@$080$#,'':01$:+,'080,#$&@801$:+,&080+.'@/001$:@#08201$:0+,$001$:/@080,/.%001$://080@%,/>01$:+,%080,#$&@401$:+,$080+.+#%001$:/.08201$:0++@0").
Definition KCa3a_24 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:/-080--,,001$:/,080,/-@<01$:+,#080,#$&@201$:++@080+.+#%001$:/+08201$:0++.001$:/'080@/.%401$:/&080$#$#-801$:++/080,#$&@001$:++.080+.+#%001$:/%08201$:0++,001$:/$080-+//601$:/#080,&%-:01$:++-080,#$&/>01$:++,080+.+#%001$:.@08201$:0++'001$:./080,/-&>").
Definition KCa3a_25 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:..080-&,%801$:+++080,#$&/<01$:++'080+.+#%001$:.-08201$:0++%001$:.,080/&%#401$:.+080,&-#201$:++&080,#$&/:01$:++%080+.+#%001$:.'08201$:0++#001$:.&080-@&,001$:.%080-#,+601$:++$080,#$&/801$:++#080+.+#%001$:.$08201$:0+'/001$:.#080.$+@>01$:-@080@/-@0").
Definition KCa3a_26 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:+'@080,#$&/601$:+'/080+.+#%001$:-/08201$:0+'-001$:-.080.+.+601$:--080,-,&:01$:+'.080,#$&/401$:+'-080+.+#%001$:-,08201$:0+'+001$:-+080/&$,201$:-'080/#/@801$:+',080,#$&/201$:+'+080+.+#%001$:-&08201$:0+'&001$:-%080$#'+'001$:-$080/-#-:01$:+''080,#$&/0").
Definition KCa3a_27 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:+'&080+.+#%001$:-#08201$:0+'$001$:,@080$$%..401$:,/080/-#,201$:+'%080,#$&.>01$:+'$080+.+#%001$:,.08201$:0+&@001$:,-080$$#$$801$:,,080.-/%<01$:+'#080,#$&.<01$:+&@080+.+#%001$:,+08201$:0+&.001$:,'080$#''.601$:,&080./@'401$:+&/080,#$&.:01$:+&.080+.+#%0").
Definition KCa3a_28 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:,%08201$:0+&,001$:,$080/,@->01$:,#080/,@'<01$:+&-080,#$&.801$:+&,080+.+#%001$:+@08201$:0+&'001$:+/080@/,&:01$:+.080./@%001$:+&+080,#$&.001$:+&'080+.'@/001$:+-08201$:0+&%001$:+,080.+,@<01$:++080@-&'<01$:+&&080,#$&-801$:+&%080+.'@/001$:+'08201$:0+&#0").
Definition KCa3a_29 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:+&080@'@.<01$:+%080,/-$801$:+&$080,#$&-001$:+&#080+.'@/001$:+$08201$:0+%/001$:+#080$#/$/801$:'@080//+'>01$:+%@080,#$&,801$:+%/080+.+#%001$:'/08201$:0+%-001$:'.080$$'+.:01$:'-080$#%@+201$:+%.080,#$&,001$:+%-080+.'@/001$:',08201$:0+%+001$:'+080,-+.<").
Definition KCa3a_30 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:''080$#$#+601$:+%,080,#$&+801$:+%+080+.'@/001$:'&08201$:0+%&001$:'%080/#.,001$:'$080/,@%601$:+%'080,#$&+001$:+%&080+.'@/001$:'#08201$:0+%$001$:&@080.--/001$:&/080/+&.201$:+%%080,#$&'801$:+%$080+.'@/001$:&.08201$:0+$@001$:&-080-&+,:01$:&,080@-&&0").
Definition KCa3a_31 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:+%#080,#$&'001$:+$@080+.+#%001$:&+08201$:0+$.001$:&'080//+$401$:&&080/,/@801$:+$/080,#$&&801$:+$.080+.'@/001$:&%08201$:0+$,001$:&$080@/,#001$:&#080,-++>01$:+$-080,#$&&001$:+$,080+.'@/001$:%@08201$:0+$'001$:%/080@'@%201$:%.080@/+-401$:+$+080,#$&%>").
Definition KCa3a_32 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:+$'080+.+#%001$:%-08201$:0+$%001$:%,080-&'/401$:%+080@%,.001$:+$&080,#$&%<01$:+$%080+.+#%001$:%'08201$:0+$#001$:%&080$$%--:01$:%%080,+,-801$:+$$080,#$&%:01$:+$#080+.+#%001$:%$08201$:0+#/001$:%#080-&'%601$:$@080@%,':01$:+#@080,#$&%801$:+#/080+.+#%0").
Definition KCa3a_33 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$/08201$:0+#-001$:$.080/,.%:01$:$-080,/,@:01$:+#.080,#$&%001$:+#-080+.'@/001$:$,08201$:0+#+001$:$+080$##@-:01$:$'080,-++201$:+#,080,#$&$801$:+#+080+.+#%001$:$&08201$:0+#&001$:$%080$$%-#801$:$$080.&-.001$:+#'080,#$&$001$:+#&080+.'@/001$:$#08201$:0+#$0").
Definition KCa3a_34 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:@080,&+/201$:/080$#'&@:01$:+#%080,#$&#801$:+#$080+.'@/001$:.08201$:0'@@001$:-080@'-#<01$:,080//%+<01$:+##080,#$&#001$:'@@080+.'@/001$:+08201$:0'@.001$:'080/+%$001$:&080/#+-601$:'@/080,#$%@801$:'@.080+.'@/001$:%08201$:0'@,001$:$080@#&@>").
Definition KCa3a_35 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:080.$+.>01$:'@-080,#$%@001$:'@,080+.'@/0010-+?80,#$'%6010-,?80,#$'%4010--?80,#$'%2010-.?80,#$'%0010-/?80,#$'$0010-@?80,#$'#8010.#?80,#$'#0010.$?80,#$&@8010.%?80,#$&@4010.&?80,#$&@2010.'?80,#$&@0010.+?80,#$&/>010.,?80,#$&/<").
Definition KCa3a_36 : list kentry := Eval vm_compute in (NFC.d_kl "$0010.-?80,#$&/:010..?80,#$&/8010./?80,#$&/6010.@?80,#$&/4010/#?80,#$&/2000,#$&@4100000,#$&$8100000,#$'$080--+%4010/$?80,#$&/0000,#$'#8404010/%?80,#$&.>000,#$'#0102000,#$&@8400000,#$&@0202010/&?80,#$&.<000,#$&/080%$.@%+&/-#/$'@/#2").
Definition KCa3a_37 : list kentry := Eval vm_compute in (NFC.d_kl "$0010/'?80,#$&.:000,#$&.080$#%&+/%$/%+/$+0010/+?80,#$&.8000,#$&'840'%,0000,#$&'0100010/,?80,#$&.0000,#$&&080',#@@@$%.$0010/-?80,#$&-8000,#$&%080%$.@%+&-$',,%&&&2010/.?80,#$&-0000,#$&$040%$&0000,#$&-0800000,#$&,8102010//?80,#$&,8000,#$&,040@:010/@?80,#$&,0").
Definition KCa3a_38 : list kentry := Eval vm_compute in (NFC.d_kl "$0000,#$&+080&@%/+'.#/&-0010@#?80,#$&+8000,#$&#080&/,&/&$#-%>010@$?80,#$&+0000,#$%@080',%###-#/,#&/-.'+$>010@%?80,#$&'8000,#$'%040,$@-2010@&?80,#$&'0010@'?80,#$&&8010@+?80,#$&&0010@,?80,#$&%>010@-?80,#$&%<010-'?80--+%4000$#%$-$>100000$#%$-$<102000$#%$-$:100").
Definition KCa3a_39 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$-$8100000$#%$-$6100000$#%$-$4100000$#%$-$2102000$#%$-$0100000$#%$-#>100000$#%$-#<100000$#%$-#:100000$#%$-#8100000$#%$-#6100000$#%$-#4102000$#%$-#210$,8000$#%$-#010%+4000$#%$,@>100000$#%$,@<100000$#%$,@:102").
Definition KCa3a_40 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$,@8100000$#%$,@6100000$#%$,@4100000$#%$,@2100000$#%$,@0102000$#%$,/>100000$#%$,/<100000$#%$,/:100000$#%$,/8100000$#%$,/6102000$#%$,/4102000$#%$,/2102000$#%$,/0102000$#%$,.>102000$#%$,.<102000$#%$,.:102").
Definition KCa3a_41 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$,.8102000$#%$,.6102000$#%$,.4102000$#%$,.2102000$#%$,.0102000$#%$,->102000$#%$,-<102000$#%$,-:100000$#%$,-8102000$#%$,-6100000$#%$,-4100000$#%$,-2100000$#%$,-0100000$#%$,,>100000$#%$,,<100000$#%$,,:100").
Definition KCa3a_42 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$,,8100000$#%$,,6100000$#%$,,4102000$#%$,,210%+8000$#%$,,010$#4000$#%$,+>100000$#%$,+<100000$#%$,+:100000$#%$,+8100000$#%$,+6100000$#%$,+4100000$#%$,+2100000$#%$,+0100000$#%$,'>100000$#%$,'<100000$#%$,':102").
Definition KCa3a_43 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$,'8102000$#%$,'6102000$#%$,'4102000$#%$,'2102000$#%$,'0100000$#%$,&>100000$#%$,&<100000$#%$,&:100000$#%$,&8100000$#%$,&6100000$#%$,&4102000$#%$,&210->000$#%$,&010$%4000$#%$,%>100000$#%$,%<100000$#%$,%:100").
Definition KCa3a_44 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$,%8100000$#%$,%6100000$#%$,%4102000$#%$,%210->000$#%$,%010$%4000$#%$,$>100000$#%$,$<100000$#%$,$:100000$#%$,$8100000$#%$,$6100000$#%$,$4102000$#%$,$210.4000$#%$,$010%,4000$#%$,#>100000$#%$,#<100000$#%$,#:100").
Definition KCa3a_45 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$,#8100000$#%$,#6100000$#%$,#4100000$#%$,#2100000$#%$,#0102000$#%$+@>100000$#%$+@<100000$#%$+@:10%6000$#%$+@810$,0000$#%$+@6100000$#%$+@4100000$#%$+@2100000$#%$+@0100000$#%$+/>100000$#%$+/<100000$#%$+/:100").
Definition KCa3a_46 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$+/8100000$#%$+/6100000$#%$+/4100000$#%$+/2100000$#%$+/0100000$#%$+.>100000$#%$+.<100000$#%$+.:100000$#%$+.8100000$#%$+.6100000$#%$+.4100000$#%$+.2100000$#%$+.0100000$#%$+->100000$#%$+-<100000$#%$+-:100").
Definition KCa3a_47 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$+-8100000$#%$+-6100000$#%$+-4100000$#%$+-2100000$#%$+-0100000$#%$+,>100000$#%$+,<100000$#%$+,:100000$#%$+,8100000$#%$+,6100000$#%$+,4100000$#%$+,2100000$#%$+,0100000$#%$++>100000$#%$++<100000$#%$++:100").
Definition KCa3a_48 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$++8100000$#%$++6100000$#%$++4100000$#%$++2102000$#%$++0100000$#%$+'>100000$#%$+'<100000$#%$+':100000$#%$+'8100000$#%$+'6100000$#%$+'4102000$#%$+'210&0000$#%$+'010$#:000$#%$+&>100000$#%$+&<100000$#%$+&:100").
Definition KCa3a_49 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$+&8100000$#%$+&6100000$#%$+&4102000$#%$+&2100000$#%$+&0100000$#%$+%>100000$#%$+%<100000$#%$+%:100000$#%$+%8100000$#%$+%6100000$#%$+%4102000$#%$+%2102000$#%$+%0102000$#%$+$>100000$#%$+$<100000$#%$+$:100").
Definition KCa3a_50 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$+$8102000$#%$+$6100000$#%$+$4100000$#%$+$2100000$#%$+$0100000$#%$+#>100000$#%$+#<100000$#%$+#:100000$#%$+#8100000$#%$+#6100000$#%$+#4100000$#%$+#2100000$#%$+#0100000$#%$'@>100000$#%$'@<100000$#%$'@:100").
Definition KCa3a_51 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$'@8102000$#%$'@6100000$#%$'@4100000$#%$'@2100000$#%$'@0102000$#%$'/>100000$#%$'/<100000$#%$'/:100000$#%$'/8102000$#%$'/6100000$#%$'/4100000$#%$'/2100000$#%$'/0100000$#%$'.>100000$#%$'.<100000$#%$'.:102").
Definition KCa3a_52 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$'.8100000$#%$'.6102000$#%$'.4102000$#%$'.2102000$#%$'.0102000$#%$'->100000$#%$'-<100000$#%$'-:100000$#%$'-8100000$#%$'-6100000$#%$'-4100000$#%$'-2100000$#%$'-0100000$#%$',>100000$#%$',<100000$#%$',:100").
Definition KCa3a_53 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$',8100000$#%$',6100000$#%$',4100000$#%$',2100000$#%$',0100000$#%$'+>100000$#%$'+<100000$#%$'+:100000$#%$'+8100000$#%$'+6100000$#%$'+4100000$#%$'+2100000$#%$'+0100000$#%$''>100000$#%$''<100000$#%$'':100").
Definition KCa3a_54 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$''8100000$#%$''6100000$#%$''4100000$#%$''2100000$#%$''0100000$#%$'&>100000$#%$'&<100000$#%$'&:100000$#%$'&810&<000$#%$'&6100000$#%$'&4102000$#%$'&2100000$#%$'&0100000$#%$'%>100000$#%$'%<100000$#%$'%:100").
Definition KCa3a_55 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$'%8100000$#%$'%6100000$#%$'%4102000$#%$'%210->000$#%$'%010$%4000$#%$'$>100000$#%$'$<100000$#%$'$:100000$#%$'$8100000$#%$'$6100000$#%$'$4100000$#%$'$2100000$#%$'$0100000$#%$'#>100000$#%$'#<100000$#%$'#:100").
Definition KCa3a_56 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$'#8100000$#%$'#6100000$#%$'#4100000$#%$'#2100000$#%$'#0100000$#%$&@>100000$#%$&@<100000$#%$&@:100000$#%$&@8100000$#%$&@6100000$#%$&@4100000$#%$&@2100000$#%$&@0102010&,?402010+#=102010,%740&<").
Definition KCa3a_57 : list kentry := Eval vm_compute in (NFC.d_kl "$0010,+?800010&'1100010&'3102010&'5100010&'7100010&'9100010&';100010&'=102010&'?100010&+1100010&+3100010&+5100010&+7100010&+9100010&+;102010&+=10$,8").
Definition KCa3a_58 : list kentry := Eval vm_compute in (NFC.d_kl "$0010&+?10%+4010&,1100010&,3100010&,5102010&,7100010&-1100010&-3100010&-5100010&-7100010&-9102010&-;102010&-=102010&-?102010&.1102010&.3102010&.5102").
Definition KCa3a_59 : list kentry := Eval vm_compute in (NFC.d_kl "$0010&.7102010&.9102010&.;102010&.=102010&.?102010&/1102010&/3102010&/5100010&/7102010&/9100010&/;100010&/=100010&/?100010&@1100010&@3100010&@5100").
Definition KCa3a_60 : list kentry := Eval vm_compute in (NFC.d_kl "$0010&@7100010&@9100010&@;102010&@=10%+8010&@?10$#4010'#1100010'#3100010'#5100010'#7100010'#9100010'#;100010'#=100010'#?100010'$1100010'$3100010'$5102").
Definition KCa3a_61 : list kentry := Eval vm_compute in (NFC.d_kl "$0010'$7102010'$9102010'$;102010'$=102010'$?100010'%1100010'%3100010'%5100010'%7100010'%9100010'%;102010'%=10->010'%?10$%4010'&1100010'&3100010'&5100").
Definition KCa3a_62 : list kentry := Eval vm_compute in (NFC.d_kl "$0010'&7100010'&9100010'&;102010'&=10->010'&?10$%4010''1100010''3100010''5100010''7100010''9100010'';102010''=10.4010''?10%,4010'+1100010'+3100010'+5100").
Definition KCa3a_63 : list kentry := Eval vm_compute in (NFC.d_kl "$0010'+7100010'+9100010'+;100010'+=100010'+?102010',1100010',3100010',510%6010',710$,0010',9100010',;100010',=100010',?100010'-1100010'-3100010'-5100").
Definition KCa3a_64 : list kentry := Eval vm_compute in (NFC.d_kl "$0010'-7100010'-9100010'-;100010'-=100010'-?100010'.1100010'.3100010'.5100010'.7100010'.9100010'.;100010'.=100010'.?100010'/1100010'/3100010'/5100").
Definition KCa3a_65 : list kentry := Eval vm_compute in (NFC.d_kl "$0010'/7100010'/9100010'/;100010'/=100010'/?100010'@1100010'@3100010'@5100010'@7100010'@9100010'@;100010'@=100010'@?100010+#1100010+#3100010+#5100").
Definition KCa3a_66 : list kentry := Eval vm_compute in (NFC.d_kl "$0010+#7100010+#9100010+#;100010+#?100010+$1100010+$3100010+$5100010+$7100010+$9100010+$;102010+$=10&0010+$?10$#:010+%1100010+%3100010+%5100010+%7100").
Definition KCa3a_67 : list kentry := Eval vm_compute in (NFC.d_kl "$0010+%9100010+%;102010+%=100010+%?100010+&1100010+&3100010+&5100010+&7100010+&9100010+&;102010+&=102010+&?102010+'1100010+'3100010+'5100010+'7102").
Definition KCa3a_68 : list kentry := Eval vm_compute in (NFC.d_kl "$0010+'9100010+';100010+'=100010+'?100010++1100010++3100010++5100010++7100010++9100010++;100010++=100010++?100010+,1100010+,3100010+,5100010+,7102").
Definition KCa3a_69 : list kentry := Eval vm_compute in (NFC.d_kl "$0010+,9100010+,;100010+,=100010+,?102010+-1100010+-3100010+-5100010+-7102010+-9100010+-;100010+-=100010+-?100010+.1100010+.3100010+.5102010+.7100").
Definition KCa3a_70 : list kentry := Eval vm_compute in (NFC.d_kl "$0010+.9102010+.;102010+.=102010+.?102010+/1100010+/3100010+/5100010+/7100010+/9100010+/;100010+/=100010+/?100010+@1100010+@3100010+@5100010+@7100").
Definition KCa3a_71 : list kentry := Eval vm_compute in (NFC.d_kl "$0010+@9100010+@;100010+@=100010+@?100010,#1100010,#3100010,#5100010,#7100010,#9100010,#;100010,#=100010,#?100010,$1100010,$3100010,$5100010,$7100").
Definition KCa3a_72 : list kentry := Eval vm_compute in (NFC.d_kl "$0010,$9100010,$;100010,$=100010,$?100010,%9100010,%;102010,%=100010,%?100010,&1100010,&3100010,&5100010,&7100010,&9100010,&;102010,&=10->010,&?10$%4").
Definition KCa3a_73 : list kentry := Eval vm_compute in (NFC.d_kl "$0010,'1100010,'3100010,'5100010,'7100010,'9100010,';100010,'=100010,'?100010,,1100010,,3100010,,5100010,,7100010,,9100010,,;100010,,=100010,,?102").
Definition KCa3a_74 : list kentry := Eval vm_compute in (NFC.d_kl "$0010,@?81$:000@-$+@08201$:0,$-.011$:$,.00&&/011$:,#'00+,-'061$:00,$-.041$:'%,051$:'%,0',%###-#/,#&&$,'/'071$:00,$-.010,+,.@#?0$.+/'.&071$:00,$-.000,$-.00'.$,#&071$:00,$-.000$%.+.%#.'00--.,,-&&%./.071$:00,$-.00@,-.#/,/@&,000,.%#$&@'+@&,071$:00,$-.00$'++$##$&000@,,&,'+/@%&071$:00,$-.00$%.+.%#.'000$-@&.@&@071$:00,$-.01700'%,0010$$'?800010$$&?80&#+###'-@#&/@$+,-$4").
Definition KCa3a_75 : list kentry := Eval vm_compute in (NFC.d_kl "$0010$$%?80$#$&.&0010$$$?80,$-.0010$$#?80/+/@<010$#@?800010$#/?80&-,/+8000$#$&.&080'%,0010,-?800010,.?800010,/740$-'#'##+#4010&&?800010&%?800010&$?800010&#?800010%@?800010%/?800010%.?800").
Definition KCa3a_76 : list kentry := Eval vm_compute in (NFC.d_kl "5010%-?800010%,?80,$'%.0010%+?802010%'?80+.'@#0010%&?80,$'%.0").
Definition KCa3a_77 : list kentry := Eval vm_compute in (NFC.d_kl "$0010$&?80&%@/%0000,$'%.040,$-.0010$%?80+.'@'0010$$?80'-#-$8010@?80+$@%'0010.?811010-?820100$0010,?80+$@''0010'?800010&?800010%?800010$?800010?800017%$0819000'.-#@.0819017&0800").
Definition KCa3a_78 : list kentry := Eval vm_compute in (NFC.d_kl "$0017%0817017$0817017$'0820170$'0017$.080'.-$-$0017'0418017+0404000'.-$,+01020170817017%%0820170+,0017+,0802017+-0820170%&,0000'.-$,/080$0000'.-$,.080+.0000'.-#,/0800000'.-#,-080&%0000'.-$,@0802").
Definition KCa3a_79 : list kentry := Eval vm_compute in (NFC.d_kl "$0000'.-$,-080'.-#,'0000'.-#,.080$0000'.-#,,0800000'.-#,+080+.#-+0000'.-$,'0820201020400$011400$0120%$0000'.-$-#080'%,0000'.-$--0816010$/?820201020400$01120400$012400$0140%$0010%#?800000'.-$,,0820201020400$011400$0120&0000'.-#,%08202010400$0110%0010/?800010$#?800010$@?800010%$?800010+?820100$0").
Definition KCa3a_80 : list kentry := Eval vm_compute in (NFC.d_kl "$0510+,-%-,+/,%/'%0+,-%./&'&.'#&0410%0520201020400$01120400$012400$0140%&0+,-%-,+/,%/,'0+,-%./&'&.'%+05112$#-05120%@05130$$&''>5140%'&%/05150%+,#,##-+<610,+,.@#?0,+,.@$0110,+,.@#?0,+,-.-0110-&?0'00100811010$0820201020400$011400$0120%$0010%084024021120201020400$01120400$012130%$20201020400$011400$012&08060201020400$011400$012'080,$.+0").
Definition KCa3a_81 : list kentry := Eval vm_compute in (NFC.d_kl "20201020400$011400$012+08080201020400$011400$012,080-0").
Definition KCa3a_82 : list kentry := Eval vm_compute in (NFC.d_kl "$02201020400$01120400$012400$014%$00%0$92201020400$011400$012%$020130213,$-.0+/&,+03+/&,,0,#$%@03,#$&$:,#$&%03,#$&'2,#$&'83,#$&,:,#$&-03,#$&@6,#$&@83,#$'#2,#$'#83,#$'%8,$#/&03,$#/'0,$'%.03,$'%.8,$'%/03,$'%@0,$'&$03,$'&$2@-$+@03@-$,$0$#$&.$03$#$&.%0$#$&.&0").
Definition KCa3a_83 : list kentry := Eval vm_compute in (NFC.d_kl "83$#$&.'0$#$&.-03$#$.#$>$#$.#%03$#%$%->$#%$&@03$#%$-%0'.-#,%03'.-#,&0'.-#,+03'.-#,@0'.-#@.03'.-#@/0'.-$,&03'.-$,+2'.-$,,0").
Definition car13a := ltac:(nf_car (KCa3a_14 ++ KCa3a_15 ++ KCa3a_16 ++ KCa3a_17 ++ KCa3a_18 ++ KCa3a_19 ++ KCa3a_20 ++ KCa3a_21 ++ KCa3a_22 ++ KCa3a_23 ++ KCa3a_24 ++ KCa3a_25 ++ KCa3a_26 ++ KCa3a_27 ++ KCa3a_28 ++ KCa3a_29 ++ KCa3a_30 ++ KCa3a_31 ++ KCa3a_32 ++ KCa3a_33 ++ KCa3a_34 ++ KCa3a_35 ++ KCa3a_36 ++ KCa3a_37 ++ KCa3a_38 ++ KCa3a_39 ++ KCa3a_40 ++ KCa3a_41 ++ KCa3a_42 ++ KCa3a_43 ++ KCa3a_44 ++ KCa3a_45 ++ KCa3a_46 ++ KCa3a_47 ++ KCa3a_48 ++ KCa3a_49 ++ KCa3a_50 ++ KCa3a_51 ++ KCa3a_52 ++ KCa3a_53 ++ KCa3a_54 ++ KCa3a_55 ++ KCa3a_56 ++ KCa3a_57 ++ KCa3a_58 ++ KCa3a_59 ++ KCa3a_60 ++ KCa3a_61 ++ KCa3a_62 ++ KCa3a_63 ++ KCa3a_64 ++ KCa3a_65 ++ KCa3a_66 ++ KCa3a_67 ++ KCa3a_68 ++ KCa3a_69 ++ KCa3a_70 ++ KCa3a_71 ++ KCa3a_72 ++ KCa3a_73 ++ KCa3a_74 ++ KCa3a_75 ++ KCa3a_76 ++ KCa3a_4 ++ KCa3a_77 ++ KCa3a_78 ++ KCa3a_79 ++ KCa3a_80 ++ KCa3a_81 ++ KCa3a_11 ++ KCa3a_82 ++ KCa3a_83 ++ KCa3a_13) ((AX2L.carryF3 LG13a KN13 []))).
Definition KN13a : list kentry := fst (fst car13a).
Definition CS13a : list sidecond := Eval lazy in (snd (fst car13a)).
Definition HS13a : list bool := Eval lazy in (snd car13a).
Lemma car13a_eq : carry LG13a KN13 [] = (KN13a, CS13a, HS13a).
Proof. apply AX2L.carry_viaF3. vm_cast_no_check (eq_refl car13a). Qed.


(* [comment removed for export] *)
Definition run13b := ltac:(nf_run KN13a ((AX2L.sym_execFS6 SEGS IT_Kn3a KN13a F8 true STOPS3 noscr (SS PC13a SR13a [] KN13a 27) []))).
Definition PC13b : Z := Eval lazy in (s_pc (fst (fst run13b))).
Definition SR13b : list expr := Eval lazy in (s_regs (fst (fst run13b))).
Definition LG13b : list sentry := s_log (fst (fst run13b)).
Definition SK13b : list kentry := s_know (fst (fst run13b)).
Definition NX13b : nat := Eval lazy in (s_next (fst (fst run13b))).
Definition SC13b : list sidecond := Eval lazy in (snd (fst run13b)).
Definition SP13b : scripts := Eval lazy in (snd run13b).
Lemma run13b_eq : sym_exec SEGS F8 true STOPS3 noscr (SS PC13a SR13a [] KN13a 27) [] = (SSR PC13b SR13b LG13b SK13b NX13b None, SC13b, SP13b).
Proof. apply (AX2L.sym_exec_viaFS6 SEGS IT_Kn3a KN13a); [exact IT_Kn3a_ok | reflexivity | vm_cast_no_check (eq_refl run13b)]. Qed.
Definition KCa3a_84 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:.-@080,&%@801$:$%%#080$#%$,$001$:$%$@080+.+#,0000@-$,#08201$:0$%%$0010$#.?80+.+#%0010$#-?80$#%$&@0010$#,?820100,,?010$#+?80&,&#+8010,+?40-:01$:.-/08201$:0$%$.001$:.-.080@.$-001$:.--080/#+/<01$:$%$/080$#%$,#201$:$%$.080+.+#%001$:.-,08201$:0$%$,001$:.-+080-'+%6").
Definition KCa3a_85 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:.-'080-.-,>01$:$%$-080$#%$,#001$:$%$,080+.+#%001$:.-&08201$:0$%$'001$:.-%080/.#%201$:.-$080$#./%401$:$%$+080$#%$+@801$:$%$'080+.'@/001$:.-#08201$:0$%$%001$:.,@080,,#@<01$:.,/080/&//201$:$%$&080$#%$+@001$:$%$%080+.+#%001$:.,.08201$:0$%$#001$:.,-080/-//401$:.,,080$#-,#8").
Definition KCa3a_86 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$%$$080$#%$+/001$:$%$#080+.+%.001$:.,+08201$:0$%#/001$:.,'080@+/@201$:.,&080$$&&.801$:$%#@080$#%$+.001$:$%#/080+.+%.001$:.,%08201$:0$%#-001$:.,$080/-.$201$:.,#080-'+#201$:$%#.080$#%$+-001$:$%#-080+.+%.001$:.+@08201$:0$%#+001$:.+/080-$@%201$:.+.080..-$001$:$%#,080$#%$+,0").
Definition KCa3a_87 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$%#+080+.+%.001$:.+-08201$:0$%#&001$:.+,080$#$''<01$:.++080@'',401$:$%#'080$#%$++401$:$%#&080+.+#%001$:.+'08201$:0$%#$001$:.+&080-''->01$:.+%080,'%/401$:$%#%080$#%$++201$:$%#$080+.+#%001$:.+$08201$:0$$@@001$:.+#080@#.-401$:.'@080$$&&,001$:$%##080$#%$++001$:$$@@080+.+#%0").
Definition KCa3a_88 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:.'/08201$:0$$@.001$:.'.080$#+#/801$:.'-080/@#,601$:$$@/080$#%$+'001$:$$@.080+.+#,001$:.',08201$:0$$@,001$:.'+080@.#&601$:.''080/@#%>01$:$$@-080$#%$+&001$:$$@,080+.+%.001$:.'&08201$:0$$@'001$:.'%080-.-%001$:.'$080,.&/>01$:$$@+080$#%$+%401$:$$@'080+.+#%001$:.'#08201$:0$$@%0").
Definition KCa3a_89 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:.&@080..,+<01$:.&/080.,+'401$:$$@&080$#%$+%201$:$$@%080+.+#%001$:.&.08201$:0$$@#001$:.&-080$#@$@401$:.&,080,,#-<01$:$$@$080$#%$+%001$:$$@#080+.+#%001$:.&+08201$:0$$//001$:.&'080.'',401$:.&&080$$&&'401$:$$/@080$#%$+$801$:$$//080+.+%'001$:.&%08201$:0$$/-001$:.&$080,.$.8").
Definition KCa3a_90 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:.&#080@.#$801$:$$/.080$#%$+$001$:$$/-080+.+%'001$:.%@08201$:0$$/+001$:.%/080@&&.>01$:.%.080$$$#+:01$:$$/,080$#%$+#801$:$$/+080+.+%'001$:.%-08201$:0$$/&001$:.%,080$$#/'401$:.%+080.''':01$:$$/'080$#%$+#001$:$$/&080+.+%'001$:.%'08201$:0$$/$001$:.%&080-$.#>01$:.%%080@@+@6").
Definition KCa3a_91 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$$/%080$#%$'@801$:$$/$080+.+%'001$:.%$08201$:0$$.@001$:.%#080$#/@.>01$:.$@080..,'401$:$$/#080$#%$'@001$:$$.@080+.+%'001$:.$/08201$:0$$..001$:.$.080$#$'$<01$:.$-080$#-+/>01$:$$./080$#%$'/801$:$$..080+.+#%001$:.$,08201$:0$$.,001$:.$+080@@''801$:.$'080-,'->01$:$$.-080$#%$'/0").
Definition KCa3a_92 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$$.,080+.'@/001$:.$&08201$:0$$.'001$:.$%080-.,&>01$:.$$080$#&-&601$:$$.+080$#%$'.:01$:$$.'080+.+#%001$:.$#08201$:0$$.%001$:.#@080,@-+:01$:.#/080./,#801$:$$.&080$#%$'.801$:$$.%080+.+#%001$:.#.08201$:0$$.#001$:.#-080-.',001$:.#,080.#&$>01$:$$.$080$#%$'.601$:$$.#080+.+#%0").
Definition KCa3a_93 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:.#+08201$:0$$-/001$:.#'080/$+'201$:.#&080/$+%801$:$$-@080$#%$'.401$:$$-/080+.+#%001$:.#%08201$:0$$--001$:.#$080-$-%:01$:.##080-.'&801$:$$-.080$#%$'.201$:$$--080+.+#%001$:-@@08201$:0$$-+001$:-@/080-$+.:01$:-@.080/--@>01$:$$-,080$#%$'.001$:$$-+080+.+#%001$:-@-08201$:0$$-&0").
Definition KCa3a_94 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:-@,080$#-+$401$:-@+080,-&-801$:$$-'080$#%$'-801$:$$-&080+.'@/001$:-@'08201$:0$$-$001$:-@&080/$''001$:-@%080,,#,001$:$$-%080$#%$'-001$:$$-$080+.+#%001$:-@$08201$:0$$,@001$:-@#080/&/&201$:-/@080.%''<01$:$$-#080$#%$',001$:$$,@080+.+#,001$:-//08201$:0$$,.001$:-/.080/&-@:").
Definition KCa3a_95 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:-/-080$#$'#201$:$$,/080$#%$'+001$:$$,.080+.+#%001$:-/,08201$:0$$,,001$:-/+080@+.,>01$:-/'080/--/<01$:$$,-080$#%$''001$:$$,,080+.+#,001$:-/&08201$:0$$,'001$:-/%080@+-/:01$:-/$080./,&<01$:$$,+080$#%$'&801$:$$,'080+.'@/001$:-/#08201$:0$$,%001$:-.@080$#+#'>01$:-./080/,#+6").
Definition KCa3a_96 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$$,&080$#%$'&601$:$$,%080+.+#%001$:-..08201$:0$$,#001$:-.-080/$&,001$:-.,080,@-%>01$:$$,$080$#%$'&401$:$$,#080+.+#%001$:-.+08201$:0$$+/001$:-.'080@&%@<01$:-.&080,'%,:01$:$$+@080$#%$'&201$:$$+/080+.+#%001$:-.%08201$:0$$+-001$:-.$080@&%#401$:-.#080$$#/$:01$:$$+.080$#%$'&0").
Definition KCa3a_97 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$$+-080+.+#%001$:--@08201$:0$$++001$:--/080/+@/<01$:--.080/---801$:$$+,080$#%$'%001$:$$++080+.+#,001$:---08201$:0$$+&001$:--,080$#&+,201$:--+080-,'+>01$:$$+'080$#%$'$001$:$$+&080+.+#%001$:--'08201$:0$$+$001$:--&080..+'801$:--%080@&$.201$:$$+%080$#%$'#001$:$$+$080+.+#,0").
Definition KCa3a_98 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:--$08201$:0$$'@001$:--#080$#-&/001$:-,@080,.$-401$:$$+#080$#%$&@001$:$$'@080+.+#%0010$#'?80,#$%@8010$#&?80$@4010$#%?80&#+###'-@#&/@$+,-$4010$#$?80,#$%@0010$##?80'.#,@#0010@@?80',%###-#/+%$/+.'%-4010@/?80$#%$&@0010@.?80%%.#&801$:-,/08201$:0$$'.001$:-,.080-/-$>01$:-,-080$$$/':").
Definition KCa3a_99 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$$'/080'.#,@+001$:$$'.080+.'@/001$:-,,08201$:0$$',001$:-,+080./@/801$:-,'080@-+/<01$:$$'-080'.#,@'001$:$$',080+.+#,001$:-,&08201$:0$$''001$:-,%080.+#&001$:-,$080/,&#601$:$$'+080'.#,@&001$:$$''080+.'@/001$:-,#08201$:0$$'%001$:-+@080$#&@.:01$:-+/080$$+&+<01$:$$'&080'.#,@%<").
Definition KCa3a_100 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$$'%080+.+#%001$:-+.08201$:0$$'#001$:-+-080$#&@.:01$:-+,080@...>01$:$$'$080'.#,@%:01$:$$'#080+.+#%001$:-++08201$:0$$&/001$:-+'080-##'>01$:-+&080@..-401$:$$&@080'.#,@%801$:$$&/080+.+#%001$:-+%08201$:0$$&-001$:-+$080.@/#<01$:-+#080@..+:01$:$$&.080'.#,@%601$:$$&-080+.+#%0").
Definition KCa3a_101 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:-'@08201$:0$$&+001$:-'/080$$$/#401$:-'.080@..&>01$:$$&,080'.#,@%401$:$$&+080+.+#%001$:-'-08201$:0$$&&001$:-',080-/+&:01$:-'+080.#.,601$:$$&'080'.#,@%201$:$$&&080+.+#%001$:-''08201$:0$$&$001$:-'&080$##'#:01$:-'%080$#%$-801$:$$&%080'.#,@%001$:$$&$080+.+#%001$:-'$08201$:0$$%@0").
Definition KCa3a_102 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:-'#080-+%&>01$:-&@080,,,+401$:$$&#080'.#,@$>01$:$$%@080+.+#%001$:-&/08201$:0$$%.001$:-&.080$#+-'201$:-&-080/'-+>01$:$$%/080'.#,@$<01$:$$%.080+.+#%001$:-&,08201$:0$$%,001$:-&+080.#.%601$:-&'080.#.$001$:$$%-080'.#,@$:01$:$$%,080+.+#%001$:-&&08201$:0$$%'001$:-&%080@$+'>").
Definition KCa3a_103 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:-&$080@,.'201$:$$%+080'.#,@$801$:$$%'080+.+#%001$:-&#08201$:0$$%%001$:-%@080.'@@401$:-%/080$##&@601$:$$%&080'.#,@$001$:$$%%080+.'@/001$:-%.08201$:0$$%#001$:-%-080$#+,$001$:-%,080-##&801$:$$%$080'.#,@#801$:$$%#080+.'@/001$:-%+08201$:0$$$/001$:-%'080$$+%/801$:-%&080@$+&0").
Definition KCa3a_104 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$$$@080'.#,@#001$:$$$/080+.+#%0010,,?8201$:0-%&0010,&?800010,'?800010,+110$@4010,+310$@4010,+510$@4010,+710$@4000'.#,@+0402000'.#,@%040%@2000'.#,@$080%$.@%+&/,@-$%&@/0000'.#,@#8400000'.#,@#0100000'.#,@'080--+%4000'.#,@&0402").
Definition KCa3a_105 : list kentry := Eval vm_compute in (NFC.d_kl "$0000'.#,@%<100000'.#,@%8200010,/?40$+<01$:&&+08201$:0-$@001$:&&'080$#'@/401$:&&&080.#%@:01$:-%%080--+%401$:-%$010201$:-%#0820100,@?01$:-$@080+.+%#001$:&&%08201$:0-$,001$:&&$080@@&@<01$:&&#080@@&/<01$:-$/080--+%401$:-$.010001$:-$-0820100,@?").
Definition KCa3a_106 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:-$,080+.+%#001$:&%@08201$:0-$'001$:&%/080.@'-001$:&%.080$#-/@:01$:-$+080$#%$-$<01$:-$'080+.+#%001$:&%-08201$:0-$%001$:&%,080-.@+601$:&%+080$$$'+<01$:-$&080$#%$-$:01$:-$%080+.+#%001$:&%'08201$:0-$#001$:&%&080.@&@201$:&%%080,@.-<01$:-$$080$#%$-$801$:-$#080+.+#%0").
Definition KCa3a_107 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:&%$08201$:0-#/001$:&%#080@@-&<01$:&$@080.@&,401$:-#@080$#%$-$601$:-#/080+.+#%001$:&$/08201$:0-#-001$:&$.080@#//601$:&$-080@#/-201$:-#.080$#%$-$401$:-#-080+.+#%001$:&$,08201$:0-#+001$:&$+080/.+&201$:&$'080.#+':01$:-#,080$#%$-$201$:-#+080+.+#%001$:&$&08201$:0-#&0").
Definition KCa3a_108 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:&$%080-%%.<01$:&$$080-,+%201$:-#'080$#%$-$001$:-#&080+.+#%001$:&$#08201$:0-#$001$:&#@080-.@%:01$:&#/080,@.,401$:-#%080$#%$-#001$:-#$080+.+#,001$:&#.08201$:0,@@001$:&#-080/$+->01$:&#,080.%,#201$:-##080$#%$,@>01$:,@@080+.+#%001$:&#+08201$:0,@.001$:&#'080$$$'#:").
Definition KCa3a_109 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:&#&080$#+%&801$:,@/080$#%$,@<01$:,@.080+.+#%001$:&#%08201$:0,@,001$:&#$080-%$-:01$:&##080-%$+401$:,@-080$#%$,@:01$:,@,080+.+#%001$:%@@08201$:0,@'001$:%@/080/.'&<01$:%@.080@.&':01$:,@+080$#%$,@801$:,@'080+.+#%001$:%@-08201$:0,@%001$:%@,080$#-/&201$:%@+080@.&&8").
Definition KCa3a_110 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:,@&080$#%$,@001$:,@%080+.'@/001$:%@'08201$:0,@#001$:%@&080..-%<01$:%@%080$#-/#<01$:,@$080$#%$,/801$:,@#080+.+#%001$:%@$08201$:0,//001$:%@#080@@,,001$:%/@080.%+/401$:,/@080$#%$,/601$:,//080+.+#%001$:%//08201$:0,/-001$:%/.080$#+$+<01$:%/-080.',@401$:,/.080$#%$,/4").
Definition KCa3a_111 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:,/-080+.+#%001$:%/,08201$:0,/+001$:%/+080-'.,201$:%/'080$$&,$601$:,/,080$#%$,/201$:,/+080+.+#%001$:%/&08201$:0,/&001$:%/%080/@#@401$:%/$080,@.'201$:,/'080$#%$,/001$:,/&080+.+#%001$:%/#08201$:0,/$001$:%.@080.#'':01$:%./080/'#$<01$:,/%080$#%$,.>01$:,/$080+.+#%0").
Definition KCa3a_112 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:%..08201$:0,.@001$:%.-080/.&,001$:%.,080$#$'.601$:,/#080$#%$,.<01$:,.@080+.+#%001$:%.+08201$:0,..001$:%.'080.%'.601$:%.&080,,%,<01$:,./080$#%$,.:01$:,..080+.+#%001$:%.%08201$:0,.,001$:%.$080$#-.%<01$:%.#080@@,&<01$:,.-080$#%$,.801$:,.,080+.+#%001$:%-@08201$:0,.'0").
Definition KCa3a_113 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:%-/080-%#+>01$:%-.080$#&-+201$:,.+080$#%$,.601$:,.'080+.+#%001$:%--08201$:0,.%001$:%-,080@,&$601$:%-+080.#'%801$:,.&080$#%$,.401$:,.%080+.+#%001$:%-'08201$:0,.#001$:%-&080$$$&%<01$:%-%080@,%@201$:,.$080$#%$,.201$:,.#080+.+#%001$:%-$08201$:0,-/001$:%-#080,,$.6").
Definition KCa3a_114 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:%,@080$#-.#:01$:,-@080$#%$,.001$:,-/080+.+#%001$:%,/08201$:0,--001$:%,.080$$&+%201$:%,-080.@&'201$:,-.080$#%$,->01$:,--080+.+#%001$:%,,08201$:0,-+001$:%,+080$#--#>01$:%,'080/.&&>01$:,-,080$#%$,-<01$:,-+080+.+#%001$:%,&08201$:0,-&001$:%,%080/,#-001$:%,$080@.&#>").
Definition KCa3a_115 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:,-'080$#%$,-:01$:,-&080+.+#%001$:%,#08201$:0,-$001$:%+@080/&@+>01$:%+/080/@#-201$:,-%080$#%$,-801$:,-$080+.+#%001$:%+.08201$:0,,@001$:%+-080$$&'.801$:%+,080@@,$201$:,-#080$#%$,-001$:,,@080+.'@/001$:%++08201$:0,,.001$:%+'080-',@801$:%+&080,.'$001$:,,/080$#%$,,0").
Definition KCa3a_116 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:,,.080+.+#,001$:%+%08201$:0,,,001$:%+$080-.-/>01$:%+#080,,$,001$:,,-080$#%$,+001$:,,,080+.'@/001$:%'@08201$:0,,'001$:%'/080$#-,&601$:%'.080$#+$&601$:,,+080$#%$,'<01$:,,'080+.+#%001$:%'-08201$:0,,%001$:%',080-,'@001$:%'+080-',/601$:,,&080$#%$,':01$:,,%080+.+#%0").
Definition KCa3a_117 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:%''08201$:0,,#001$:%'&080-',%801$:%'%080.@&$201$:,,$080$#%$,'801$:,,#080+.+#%001$:%'$08201$:0,+/001$:%'#080$$&&@<01$:%&@080.%',201$:,+@080$#%$,'601$:,+/080+.+#%001$:%&/08201$:0,+-001$:%&.080$$$#/<01$:%&-080.#'#601$:,+.080$#%$,'401$:,+-080+.+#%001$:%&,08201$:0,++0").
Definition KCa3a_118 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:%&+080$$'/'601$:%&'080$$$#-601$:,+,080$#%$,'201$:,++080+.+#%001$:%&&08201$:0,+&001$:%&%080@&+@201$:%&$080@#/'<01$:,+'080$#%$,'001$:,+&080+.+#%001$:%&#08201$:0,+$001$:%%@080.#&'401$:%%/080,,$'801$:,+%080$#%$,&001$:,+$080+.+#,001$:%%.08201$:0,'@001$:%%-080/&/@<").
Definition KCa3a_119 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:%%,080.',-801$:,+#080$#%$,%001$:,'@080+.+#,001$:%%+08201$:0,'.001$:%%'080/.%+>01$:%%&080,&%@801$:,'/080$#%$,$001$:,'.080+.+#,001$:%%%08201$:0,',001$:%%$080@.$-001$:%%#080/#+/<01$:,'-080$#%$,#201$:,',080+.+#%001$:%$@08201$:0,''001$:%$/080-'+%601$:%$.080-.-,>").
Definition KCa3a_120 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:,'+080$#%$,#001$:,''080+.+#%001$:%$-08201$:0,'%001$:%$,080/.#%201$:%$+080$#./%401$:,'&080$#%$+@801$:,'%080+.'@/001$:%$'08201$:0,'#001$:%$&080,,#@<01$:%$%080/&//201$:,'$080$#%$+@001$:,'#080+.+#%001$:%$$08201$:0,&/001$:%$#080/-//401$:%#@080$#-,#801$:,&@080$#%$+/0").
Definition KCa3a_121 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:,&/080+.+%.001$:%#/08201$:0,&-001$:%#.080@+/@201$:%#-080$$&&.801$:,&.080$#%$+.001$:,&-080+.+%.001$:%#,08201$:0,&+001$:%#+080/-.$201$:%#'080-'+#201$:,&,080$#%$+-001$:,&+080+.+%.001$:%#&08201$:0,&&001$:%#%080-$@%201$:%#$080..-$001$:,&'080$#%$+,001$:,&&080+.+%.0").
Definition KCa3a_122 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:%##08201$:0,&$001$:$@@080$#$''<01$:$@/080@'',401$:,&%080$#%$++401$:,&$080+.+#%001$:$@.08201$:0,%@001$:$@-080-''->01$:$@,080,'%/401$:,&#080$#%$++201$:,%@080+.+#%001$:$@+08201$:0,%.001$:$@'080@#.-401$:$@&080$$&&,001$:,%/080$#%$++001$:,%.080+.+#%001$:$@%08201$:0,%,0").
Definition KCa3a_123 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$@$080$#+#/801$:$@#080/@#,601$:,%-080$#%$+'001$:,%,080+.+#,001$:$/@08201$:0,%'001$:$//080@.#&601$:$/.080/@#%>01$:,%+080$#%$+&001$:,%'080+.+%.001$:$/-08201$:0,%%001$:$/,080-.-%001$:$/+080,.&/>01$:,%&080$#%$+%401$:,%%080+.+#%001$:$/'08201$:0,%#001$:$/&080..,+<").
Definition KCa3a_124 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$/%080.,+'401$:,%$080$#%$+%201$:,%#080+.+#%001$:$/$08201$:0,$/001$:$/#080$#@$@401$:$.@080,,#-<01$:,$@080$#%$+%001$:,$/080+.+#%001$:$./08201$:0,$-001$:$..080.'',401$:$.-080$$&&'401$:,$.080$#%$+$801$:,$-080+.+%'001$:$.,08201$:0,$+001$:$.+080,.$.801$:$.'080@.#$8").
Definition KCa3a_125 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:,$,080$#%$+$001$:,$+080+.+%'001$:$.&08201$:0,$&001$:$.%080@&&.>01$:$.$080$$$#+:01$:,$'080$#%$+#801$:,$&080+.+%'001$:$.#08201$:0,$$001$:$-@080$$#/'401$:$-/080.''':01$:,$%080$#%$+#001$:,$$080+.+%'001$:$-.08201$:0,#@001$:$--080-$.#>01$:$-,080@@+@601$:,$#080$#%$'@8").
Definition KCa3a_126 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:,#@080+.+%'001$:$-+08201$:0,#.001$:$-'080$#/@.>01$:$-&080..,'401$:,#/080$#%$'@001$:,#.080+.+%'001$:$-%08201$:0,#,001$:$-$080$#$'$<01$:$-#080$#-+/>01$:,#-080$#%$'/801$:,#,080+.+#%001$:$,@08201$:0,#'001$:$,/080@@''801$:$,.080-,'->01$:,#+080$#%$'/001$:,#'080+.'@/0").
Definition KCa3a_127 : list kentry := Eval vm_compute in (NFC.d_kl ":01$:$,-08201$:0,#%001$:$,,080-.,&>01$:$,+080$#&-&601$:,#&080$#%$'.:01$:,#%080+.+#%001$:$,'08201$:0,##001$:$,&080,@-+:01$:$,%080./,#801$:,#$080$#%$'.801$:,##080+.+#%0").
Definition KCa3a_128 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$$.08201$:0+-@001$:$$-080..+'801$:$$,080@&$.201$:+.#080$#%$'#001$:+-@080+.+#,001$:$$+08201$:0+-.001$:$$'080$#-&/001$:$$&080,.$-401$:+-/080$#%$&@001$:+-.080+.+#%001$:$$%08201$:0+-,001$:$$$080.$-&>01$:$$#080/+&@<01$:+--080,#$'%601$:+-,080+.+#%001$:$#@08201$:0+-'0").
Definition KCa3a_129 : list kentry := Eval vm_compute in (NFC.d_kl "801$:$#/080--.%201$:$#.080@-,#601$:+-+080,#$'%401$:+-'080+.+#%001$:$#-08201$:0+-%001$:$#,080$$#$+801$:$#+080,@$'201$:+-&080,#$'%2").
Definition KCa3a_130 : list kentry := Eval vm_compute in (NFC.d_kl "?010&'1100010&'3102010&'5100010&'7100010&'9100010&';100010&'=102010&'?100010&+1100010&+3100010&+5100010&+7100010&+9100010&+;102010&+=10$,8").
Definition KCa3a_131 : list kentry := Eval vm_compute in (NFC.d_kl "$0010,$9100010,$;100010,$=100010,$?100010,%9100010,%;102010,%=100010,%?100010,@?81$:000@-$+@08201$:0,$-.011$:&&,00$-#011$:-$.20>11$:-%$20>11$:..#00&'/011$:$%%$00'@+-061$:00,$-.0").
Definition KCa3a_132 : list kentry := Eval vm_compute in (NFC.d_kl ";41$:'%,051$:'%,0',%###-#/,#&&$,'/'071$:00,$-.010,+,.@#?0$.+/'.&071$:00,$-.000,$-.00'.$,#&071$:00,$-.000$%.+.%#.'00--.,,-&&%./.071$:00,$-.00@,-.#/,/@&,000,.%#$&@'+@&,071$:00,$-.00$'++$##$&000@,,&,'+/@%&071$:00,$-.00$%.+.%#.'000$-@&.@&@071$:00,$-.01700'%,0010$$'?800010$$&?80&#+###'-@#&/@$+,-$4").
Definition KCa3a_133 : list kentry := Eval vm_compute in (NFC.d_kl "<3$#$&.'0$#$&.-03$#$.#$>$#$.#%03$#%$%->$#%$&@03$#%$-%0'.#,@#03'.#,@#2'.#,@#83'.#,@%>'.#,@&03'.#,@&8'.#,@'03'.#,@+8'.-#,%03'.-#,&0'.-#,+03'.-#,@0'.-#@.03'.-#@/0'.-$,&03'.-$,+2'.-$,,0").
Definition car13b := ltac:(nf_car (KCa3a_84 ++ KCa3a_85 ++ KCa3a_86 ++ KCa3a_87 ++ KCa3a_88 ++ KCa3a_89 ++ KCa3a_90 ++ KCa3a_91 ++ KCa3a_92 ++ KCa3a_93 ++ KCa3a_94 ++ KCa3a_95 ++ KCa3a_96 ++ KCa3a_97 ++ KCa3a_98 ++ KCa3a_99 ++ KCa3a_100 ++ KCa3a_101 ++ KCa3a_102 ++ KCa3a_103 ++ KCa3a_104 ++ KCa3a_105 ++ KCa3a_106 ++ KCa3a_107 ++ KCa3a_108 ++ KCa3a_109 ++ KCa3a_110 ++ KCa3a_111 ++ KCa3a_112 ++ KCa3a_113 ++ KCa3a_114 ++ KCa3a_115 ++ KCa3a_116 ++ KCa3a_117 ++ KCa3a_118 ++ KCa3a_119 ++ KCa3a_120 ++ KCa3a_121 ++ KCa3a_122 ++ KCa3a_123 ++ KCa3a_124 ++ KCa3a_125 ++ KCa3a_126 ++ KCa3a_127 ++ KCa3a_15 ++ KCa3a_16 ++ KCa3a_17 ++ KCa3a_18 ++ KCa3a_19 ++ KCa3a_128 ++ KCa3a_129 ++ KCa3a_22 ++ KCa3a_23 ++ KCa3a_24 ++ KCa3a_25 ++ KCa3a_26 ++ KCa3a_27 ++ KCa3a_28 ++ KCa3a_29 ++ KCa3a_30 ++ KCa3a_31 ++ KCa3a_32 ++ KCa3a_33 ++ KCa3a_34 ++ KCa3a_35 ++ KCa3a_36 ++ KCa3a_37 ++ KCa3a_38 ++ KCa3a_39 ++ KCa3a_40 ++ KCa3a_41 ++ KCa3a_42 ++ KCa3a_43 ++ KCa3a_44 ++ KCa3a_45 ++ KCa3a_46 ++ KCa3a_47 ++ KCa3a_48 ++ KCa3a_49 ++ KCa3a_50 ++ KCa3a_51 ++ KCa3a_52 ++ KCa3a_53 ++ KCa3a_54 ++ KCa3a_55 ++ KCa3a_56 ++ KCa3a_130 ++ KCa3a_58 ++ KCa3a_59 ++ KCa3a_60 ++ KCa3a_61 ++ KCa3a_62 ++ KCa3a_63 ++ KCa3a_64 ++ KCa3a_65 ++ KCa3a_66 ++ KCa3a_67 ++ KCa3a_68 ++ KCa3a_69 ++ KCa3a_70 ++ KCa3a_71 ++ KCa3a_131 ++ KCa3a_132 ++ KCa3a_75 ++ KCa3a_76 ++ KCa3a_4 ++ KCa3a_77 ++ KCa3a_78 ++ KCa3a_79 ++ KCa3a_80 ++ KCa3a_81 ++ KCa3a_11 ++ KCa3a_82 ++ KCa3a_133 ++ KCa3a_13) ((AX2L.carryF3 LG13b KN13a []))).
Definition KN13b : list kentry := fst (fst car13b).
Definition CS13b : list sidecond := Eval lazy in (snd (fst car13b)).
Definition HS13b : list bool := Eval lazy in (snd car13b).
Lemma car13b_eq : carry LG13b KN13a [] = (KN13b, CS13b, HS13b).
Proof. apply AX2L.carry_viaF3. vm_cast_no_check (eq_refl car13b). Qed.


(* [comment removed for export] *)
Definition SR13r : list expr := sr_upd SR_E6 10 (ELit (2 ^ 64 - 12)).

(* [comment removed for export] *)
Definition run13n := ltac:(nf_run KN_E6 ((AX2L.sym_execFS6 SEGS IT_Kn3a KN_E6 F8 true STOPS3 noscr (SS A_internal_mmap_ret SR13r [] KN_E6 26) []))).
Definition PC13n : Z := Eval lazy in (s_pc (fst (fst run13n))).
Definition SR13n : list expr := Eval lazy in (s_regs (fst (fst run13n))).
Definition LG13n : list sentry := s_log (fst (fst run13n)).
Definition SK13n : list kentry := s_know (fst (fst run13n)).
Definition NX13n : nat := Eval lazy in (s_next (fst (fst run13n))).
Definition SC13n : list sidecond := Eval lazy in (snd (fst run13n)).
Definition SP13n : scripts := Eval lazy in (snd run13n).
Lemma run13n_eq : sym_exec SEGS F8 true STOPS3 noscr (SS A_internal_mmap_ret SR13r [] KN_E6 26) [] = (SSR PC13n SR13n LG13n SK13n NX13n None, SC13n, SP13n).
Proof. apply (AX2L.sym_exec_viaFS6 SEGS IT_Kn3a KN_E6); [exact IT_Kn3a_ok | reflexivity | vm_cast_no_check (eq_refl run13n)]. Qed.
Definition KCa3a_134 : list kentry := Eval vm_compute in (NFC.d_kl "$0010$$%?80',%###-#/,#&/-.'+#8010$$$?80,$-.0010$$#?80/+/@<010$#@?800010$#/?80&--#%8010$#.?40$8010$$'?800010$$&?80&#+###'-@#&/@$+,-$4010$#.740'4010$#-?80,$'%.0010$#,?80'@,0010$#+?80,$-.0010$#'?80@-$+@0010$#&?80&'.,%0000$#$&.&080'%,0010$#%?802").
Definition KCa3a_135 : list kentry := Eval vm_compute in (NFC.d_kl "$0010$#$?80+.'@#0010$##?820100,@?010@@?80&,..&0010,-?800010,.?800010,/?400010@/?80,$'%.0010@.?80%%'/-8010,/740$-'#'##+#4010,@?80&#+###'-@#&/@$+,-$4010&&?800010&%?800010&$?800010&#?800010%@?800010%/?800").
Definition KCa3a_136 : list kentry := Eval vm_compute in (NFC.d_kl "$0010%.?800010%-?800010%,?80,$'%.0010%+?802010%'?80+.'@#0010%&?80,$'%.0010%%?80&%/+-8000$#$&.-080$$%+/+.$/%$$%$@.'+8100$#$&..00'%'>000$#$.#%080$$%+/+.$/%$$%$@.'+8100$#$.#&00'%'>000,$'&$010271700'%,000$%.+.%#.'00--.,,-&&%./.0000,$#/&080$%.+.%'@@0000,$'%/080+,-%./&'&.'%'>000$#$&.$0820100$.?").
Definition KCa3a_137 : list kentry := Eval vm_compute in (NFC.d_kl "$0010$.?80&#+###'-@#&/@$+,-$4000+/&,+080$$'.&2010$-?8202010400$0110%0010$,?80',../0010$+?80+.'@#0010$'?80,$'%.0010$&?80&%@/%0000,$'%.040,$-.0010$%?80+.'@'0010$$?80'-#-$8010@?80+$@%'0010.?811010-?820100$0010,?80+$@''0010'?800010&?800").
Definition KCa3a_138 : list kentry := Eval vm_compute in (NFC.d_kl "$0010%?800010$?800010?800017%$0819000'.-#@.0819010+.?800010+-?800010+,?800010++?800010+'?800010+&?800010+%?80'.-$,+0010+$?820201020400$011400$0120%$0010+#?820201020400$011400$0120%$0010'@?80+%#''0010'.?80+$//-8").
Definition KCa3a_139 : list kentry := Eval vm_compute in (NFC.d_kl "$0017&0800017%0817017$0817017$'0820170$'0017$.080'.-$-$0017'0418017+0404000'.-$,+01020170817017%%0820170+,0017+,0802010,&?800010,%?800010,$?800010,#?820170+-0010+@?80'.-#,'0").
Definition KCa3a_140 : list kentry := Eval vm_compute in (NFC.d_kl "$0010+/?820170+,0017+-0820170%&,0000'.-$,/080$0000'.-$,.080+.0000'.-#,/0800000'.-#,-080&%0000'.-$,@0802000'.-$,-080'.-#,'0000'.-#,.080$0000'.-#,,0800000'.-#,+080+.#-+0010'/?820201020400$011400$0120%$0000'.-$,'0820201020400$011400$0120%$0000'.-$-#080'%,0000'.-$--0816010$/?820201020400$01120400$012400$0140%$0").
Definition KCa3a_141 : list kentry := Eval vm_compute in (NFC.d_kl "$0010%#?800010&,?80'%,0010&-?80$6010&.?80-0010&/?80,$.+0000'.-$,,0820201020400$011400$0120&0000'.-#,%08202010400$0110%0010/?800010$#?800010$@?800010%$?800010&'?800010&+?800010&@?800010'#?800010'$?800").
Definition KCa3a_142 : list kentry := Eval vm_compute in (NFC.d_kl "$0010+?820100$0510+,-%-,+/,%/'%0+,-%./&'&.'#&0410%0520201020400$01120400$012400$0140%&0+,-%-,+/,%/,'0+,-%./&'&.'%+05112$#-05120%@05130$$&''>5140%'&%/05150%+,#,##-+<610,+,.@#?0,+,.@$0110,+,.@#?0,+,-.-0110@-?0&.0110,,?0&0110'-?0,00100811010$0820201020400$011400$0120%$0").
Definition KCa3a_143 : list kentry := Eval vm_compute in (NFC.d_kl "$0010%084024021120201020400$01120400$012130%$20201020400$011400$012&08060201020400$011400$012'080,$.+00201020400$011400$012+08080201020400$011400$012,080-00201020400$011400$012-080:0201020400$011400$012.080$60201020400$011400$012/080%00201020400$011400$012@08160201020400$011400$012$#080<0201020400$011400$012$$080'%,00201020400$011400$012$%080$60201020400$011400$012$&08150201020400$011400$012$'080$80201020400$011400$012$+08150201020400$011400$012$,080%>").
Definition KCa3a_144 : list kentry := Eval vm_compute in (NFC.d_kl "$00201020400$011400$012$-08000201020400$011400$012$.080&20201020400$011400$012$/0820201020400$01120400$012400$0140%$00201020400$011400$012$@08000201020400$011400$012%#08002201020400$01120400$012400$014%$00%0$92201020400$011400$012%$020130213,$-.0+/&,+03+/&,,0,$#/&03,$#/'0,$'%.03,$'%.8,$'%/03,$'%@0,$'&$03,$'&$2$#$&.$03$#$&.%0$#$&.&03$#$&.'0$#$&.-03$#$.#$>$#$.#%0").
Definition KCa3a_145 : list kentry := Eval vm_compute in (NFC.d_kl "$03$#%$%->'.-#,%03'.-#,&0'.-#,+03'.-#,@0'.-#@.03'.-#@/0'.-$,&03'.-$,+2'.-$,,03'.-$-$0'.-$--03'.-$-.0'.--.#0600+.#@+00'%@,.,0417'%,0517'%,0+,-%./%./$%#/071700'%,000,$-.00'.$,#&071700'%,010,+,.@#?0/.'-/-0117'808117+80/8117$+00&0117$/00&0").
Definition KCa3a_146 : list kentry := Eval vm_compute in (NFC.d_kl "4117%&00&&0117+.00&-/061700'%,05182&%./@+>").
Definition car13n := ltac:(nf_car (KCa3a_134 ++ KCa3a_135 ++ KCa3a_136 ++ KCa3a_137 ++ KCa3a_138 ++ KCa3a_139 ++ KCa3a_140 ++ KCa3a_141 ++ KCa3a_142 ++ KCa3a_143 ++ KCa3a_144 ++ KCa3a_145 ++ KCa3a_146) ((AX2L.carryF3 LG13n KN_E6 []))).
Definition KN13n : list kentry := fst (fst car13n).
Definition CS13n : list sidecond := Eval lazy in (snd (fst car13n)).
Definition HS13n : list bool := Eval lazy in (snd car13n).
Lemma car13n_eq : carry LG13n KN_E6 [] = (KN13n, CS13n, HS13n).
Proof. apply AX2L.carry_viaF3. vm_cast_no_check (eq_refl car13n). Qed.


Lemma itinerary3a_ok :
  (PC13a =? A_internal_mmap_ecall, SC13a, CS13a) = (false, [], [])
  /\ (PC13b =? A_internal_mmap_ecall, SC13b, CS13b) = (false, [], [])
  /\ (PC13n, SC13n) = (A_spin_mmapordie, []).
Proof. vmeq_conj. Qed.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.NodesMmDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.MallocSymAux.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2.TwB.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Definition IT_Kn3a : itab := AX2F.mk_itab_rs SEGS [
  (260420, 762%nat); (402244, 22%nat); (402408, 6%nat); (402448, 10%nat); (408396, 12%nat); (410084, 4%nat); (410124, 1%nat); (414808, 83%nat); (415980, 1193%nat); (423748, 15%nat); (423844, 16%nat); (424580, 9%nat); (424704, 10%nat); (424796, 1%nat); (426720, 8%nat); (426760, 1%nat); (427464, 21%nat); (432736, 20%nat); (432832, 7%nat); (516300, 261%nat)] PTLeaf.
Lemma IT_Kn3a_ok : itab_sound SEGS IT_Kn3a.
Proof. apply AX2F.mk_itab_rs_sound. apply AX2F.itab_leaf_sound. Qed.

Definition F8 : nat := 8000.
Definition STOPS3 : list Z := [A_internal_mmap_ecall; A_maxva_smeared; A_spin_mmapordie; A_spin_noreserve].

(* [comment removed for export] *)
Definition DS_E6 : list (saddr * expr) :=
  [(SA (EVar 0) (- 0x800000), ELit 0x1800000); (SA (ELit 0) A_img_lo, ELit (A_img_hi - A_img_lo));
   (SA (ELit 0) SHB_LO, ELit (SHB_HI - SHB_LO));
   (SA (ELit 0x2008fff7000) 0, ELit 0xdfff0001000); (SA (ELit 0x8fff7000) 0, ELit (2 ^ 41)); (SA (ELit 0x7fff7000) 0, ELit (2 ^ 28))].

(* [comment removed for export] *)
Definition SR13 : list expr := sr_upd SR_E6 10 (EVar 26).
Definition KCb3a_147 : list kentry := Eval vm_compute in (NFC.d_kl "$011$:00,$-.061$:00,$-.041$:'%,051$:'%,0',%###-#/,#&&$,'/'071$:00,$-.010,+,.@#?0$.+/'.&071$:00,$-.000,$-.00'.$@%/071$:00,$-.000$%.+.%#.'00--.,,-&&%./.071$:00,$-.00@,-.#/,/@&,000,.%#$&@'+@&,071$:00,$-.00$'++$##$&000@,,&,'+/@%&071$:00,$-.00$%.+.%#.'000$-@&.@&@071$:00,$-.01700'%,0010$$'?800010$$&?80&#+###'-@#&/@$+,-$4010$$%?80$#$'.@0010$$$?80,$-.0010$$#?80/+/@<").
Definition KCb3a_148 : list kentry := Eval vm_compute in (NFC.d_kl "$0010$#@?800010$#/?80&--#$8010$#.740'4010$#-?80,$+&'0010$#,?80'@,0010$#+?80,$-.0010$#'?80@-%,,0010$#&?80&'.-/0000$#$'.@080'%,0010$#%?802010$#$?80+.+@.0010$##?820100,@?010@@?80&,./@0010,-?800010,.?800010,/?400").
Definition KCb3a_149 : list kentry := Eval vm_compute in (NFC.d_kl "$0010@/?80,$+&'0010@.?80%%+#&8010,/740$-'#'##+#4010,@?80&#+###'-@#&/@$+,-$4010&&?800010&%?800010&$?800010&#?800010%@?800010%/?800010%.?800010%-?800010%,?80,$+&'0010%+?802010%'?80+.+@.0010%&?80,$+&'0").
Definition KCb3a_150 : list kentry := Eval vm_compute in (NFC.d_kl "$0010%%?80&%/-&8000$#$'/&080$$%+/+.$/%$$%$@.'+8100$#$'/'00'%'>000$#$/#/080$$%+/+.$/%$$%$@.'+8100$#$/#@00'%'>000,$+&.010271700'%,000$%.+.%#.'00--.,,-&&%./.0000,$$/@080$%.+.%'@@0000,$+&+080+,-%./&'&.'%'>000$#$'..0820100$.?010$.?80&#+###'-@#&/@$+,-$4000+/'-%080$$'.&2010$-?8202010400$0110%0010$,?80',.@+0010$+?80+.+@.0010$'?80,$+&'0").
Definition KCb3a_151 : list kentry := Eval vm_compute in (NFC.d_kl "$0010$&?80&%@@/0000,$+&'040,$-.0010$%?80+.,#$0010$$?80'-#/%0010@?80+%#&$8010.?811010-?820100$0010,?80+%#+$8010'?800010&?800010%?800010$?800010?800017%$0819000'.-%#'0819010+.?800").
Definition KCb3a_152 : list kentry := Eval vm_compute in (NFC.d_kl "$0010+-?800010+,?800010++?800010+'?800010+&?800010+%?80'.-%-$0010+$?820201020400$011400$0120%$0010+#?820201020400$011400$0120%$0010'@?80+%$+$8010'.?80+$@@+0017&0800017%0817017$0817017$'0820170$'0017$.080'.-%-.0017'0418").
Definition KCb3a_153 : list kentry := Eval vm_compute in (NFC.d_kl "$0017+0404000'.-%-$01020170817017%%0820170+,0017+,0802010,&?800010,%?800010,$?800010,#?820170+-0010+@?80'.-$-#0010+/?820170+,0017+-0820170%&,0000'.-%-+080$0000'.-%-'080+.0000'.-$-+0800000'.-$-&080&%0").
Definition KCb3a_154 : list kentry := Eval vm_compute in (NFC.d_kl "$0000'.-%-,0802000'.-%-&080'.-$-#0000'.-$-'080$0000'.-$-%0800000'.-$-$080+.$.%0010'/?820201020400$011400$0120%$0000'.-%-#0820201020400$011400$0120%$0000'.-%--080'%,0000'.-%.&0816010$/?820201020400$01120400$012400$0140%$0010%#?800010&,?80'%,0010&-?80$6010&.?80-0010&/?80,$.+0000'.-%-%0820201020400$011400$0120&0").
Definition KCb3a_155 : list kentry := Eval vm_compute in (NFC.d_kl "$0000'.-$,/08202010400$0110%0010/?800010$#?800010$@?800010%$?800010&'?800010&+?800010&@?800010'#?800010'$?800010+?820100$0510+,-%-,+/,%/'%0+,-%./&'&.'#&0410%0520201020400$01120400$012400$0140%&0+,-%-,+/,%/,'0+,-%./&'&.'%+05112$#-05120%@0").
Definition KCb3a_156 : list kentry := Eval vm_compute in (NFC.d_kl "$05130$$&''>5140%'&%/05150%+,#,##-+<610,+,.@#?0,+,.@$0110,+,.@#?0,+,-.-0110$#.?08110@-?0&.0110,,?0&0110'-?0,00100811010$0820201020400$011400$0120%$0010%084024021120201020400$01120400$012130%$20201020400$011400$012&08060201020400$011400$012'080,$.+00201020400$011400$012+08080201020400$011400$012,080-0").
Definition KCb3a_157 : list kentry := Eval vm_compute in (NFC.d_kl "$00201020400$011400$012-080:0201020400$011400$012.080$60201020400$011400$012/080%00201020400$011400$012@08160201020400$011400$012$#080<0201020400$011400$012$$080'%,00201020400$011400$012$%080$60201020400$011400$012$&08150201020400$011400$012$'080$80201020400$011400$012$+08150201020400$011400$012$,080%>0201020400$011400$012$-08000201020400$011400$012$.080&20201020400$011400$012$/0820201020400$01120400$012400$0140%$00201020400$011400$012$@08000201020400$011400$012%#0800").
Definition KCb3a_158 : list kentry := Eval vm_compute in (NFC.d_kl "$02201020400$01120400$012400$014%$00%0$92201020400$011400$012%$020130213,$-.0+/'-%03+/'-&0,$$/@03,$$@#0,$+&'03,$+&'8,$+&+03,$+&,0,$+&.03,$+&.2$#$'..03$#$'./0$#$'.@03$#$'/#0$#$'/&03$#$/#.>$#$/#/03$#%%&&>'.-$,/03'.-$,@0'.-$-$03'.-$-,0'.-%#'03'.-%#+0'.-%,@03'.-%-$2'.-%-%0").
Definition KCb3a_159 : list kentry := Eval vm_compute in (NFC.d_kl "?3'.-%-.0'.-%.&03'.-%.'0'..#@,0600+.+%#00'%@,.,0417'%,0517'%,0+,-%./%./$%#/071700'%,000,$-.00'.$@%/071700'%,010,+,.@#?0/.'-/-0117'808117+80/8117$+00&0117$/00&0117%&00&&0117+.00&-/061700'%,05182&%./@+>").
Definition KN13 : list kentry := ltac:(nf_rope (KCb3a_147 ++ KCb3a_148 ++ KCb3a_149 ++ KCb3a_150 ++ KCb3a_151 ++ KCb3a_152 ++ KCb3a_153 ++ KCb3a_154 ++ KCb3a_155 ++ KCb3a_156 ++ KCb3a_157 ++ KCb3a_158 ++ KCb3a_159) ((kn_grant_d DS_E6 26 65536 KN_E6))).
Lemma KN13_eq : kn_grant_d DS_E6 26 65536 KN_E6 = KN13. Proof. kn_fast. Qed.


(* [comment removed for export] *)
Definition run13a := ltac:(nf_run KN13 ((AX2L.sym_execFS6 SEGS IT_Kn3a KN13 F8 true STOPS3 noscr (SS A_internal_mmap_ret SR13 [] KN13 27) []))).
Definition PC13a : Z := Eval lazy in (s_pc (fst (fst run13a))).
Definition SR13a : list expr := Eval lazy in (s_regs (fst (fst run13a))).
Definition LG13a : list sentry := s_log (fst (fst run13a)).
Definition SK13a : list kentry := s_know (fst (fst run13a)).
Definition NX13a : nat := Eval lazy in (s_next (fst (fst run13a))).
Definition SC13a : list sidecond := Eval lazy in (snd (fst run13a)).
Definition SP13a : scripts := Eval lazy in (snd run13a).
Lemma run13a_eq : sym_exec SEGS F8 true STOPS3 noscr (SS A_internal_mmap_ret SR13 [] KN13 27) [] = (SSR PC13a SR13a LG13a SK13a NX13a None, SC13a, SP13a).
Proof. apply (AX2L.sym_exec_viaFS6 SEGS IT_Kn3a KN13); [exact IT_Kn3a_ok | reflexivity | vm_cast_no_check (eq_refl run13a)]. Qed.
Definition KCb3a_160 : list kentry := Eval vm_compute in (NFC.d_kl "$0010,/?40.201$:$,-08201$:0,#%001$:$,,080-.,&>01$:$,+080$#&-&601$:,#&080$#%%+':01$:,#%080+.,#@0000@-%,-08201$:0,#'0010$#.?80+.,#@0010$#-?80$#%%',0010$#,?820100,@?010$#+?80&,$/%001$:$,'08201$:0,##001$:$,&080,@-+:01$:$,%080./,#801$:,#$080$#%%+'801$:,##080+.,#@0").
Definition KCb3a_161 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$,$08201$:0+@/001$:$,#080-.',001$:$+@080.#&$>01$:+@@080$#%%+'601$:+@/080+.,#@001$:$+/08201$:0+@-001$:$+.080/$+'201$:$+-080/$+%801$:+@.080$#%%+'401$:+@-080+.,#@001$:$+,08201$:0+@+001$:$++080-$-%:01$:$+'080-.'&801$:+@,080$#%%+'201$:+@+080+.,#@001$:$+&08201$:0+@&0").
Definition KCb3a_162 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$+%080-$+.:01$:$+$080/--@>01$:+@'080$#%%+'001$:+@&080+.,#@001$:$+#08201$:0+@$001$:$'@080$#-+$401$:$'/080,-&-801$:+@%080$#%%+&801$:+@$080+.,#,001$:$'.08201$:0+/@001$:$'-080/$''001$:$',080,,#,001$:+@#080$#%%+&001$:+/@080+.,#@001$:$'+08201$:0+/.001$:$''080/&/&2").
Definition KCb3a_163 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$'&080.%''<01$:+//080$#%%+%001$:+/.080+.,$&001$:$'%08201$:0+/,001$:$'$080/&-@:01$:$'#080$#$'#201$:+/-080$#%%+$001$:+/,080+.,#@001$:$&@08201$:0+/'001$:$&/080@+.+>01$:$&.080/--/<01$:+/+080$#%%+#001$:+/'080+.,$&001$:$&-08201$:0+/%001$:$&,080@+-.:01$:$&+080./,&<").
Definition KCb3a_164 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:+/&080$#%%'@801$:+/%080+.,#,001$:$&'08201$:0+/#001$:$&&080$#+#'>01$:$&%080/,#+601$:+/$080$#%%'@601$:+/#080+.,#@001$:$&$08201$:0+./001$:$&#080/$&,001$:$%@080,@-%>01$:+.@080$#%%'@401$:+./080+.,#@001$:$%/08201$:0+.-001$:$%.080@&%/<01$:$%-080,'%,:01$:+..080$#%%'@2").
Definition KCb3a_165 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:+.-080+.,#@001$:$%,08201$:0+.+001$:$%+080@&$@401$:$%'080$$#/$:01$:+.,080$#%%'@001$:+.+080+.,#@001$:$%&08201$:0+.&001$:$%%080/+@/<01$:$%$080/---801$:+.'080$#%%'/001$:+.&080+.,$&001$:$%#08201$:0+.$001$:$$@080$#&+,201$:$$/080-,'+>01$:+.%080$#%%'.001$:+.$080+.,#@0").
Definition KCb3a_166 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$$.08201$:0+-@001$:$$-080..+'801$:$$,080@&$-201$:+.#080$#%%'-001$:+-@080+.,$&001$:$$+08201$:0+-.001$:$$'080$#-&/001$:$$&080,.$-401$:+-/080$#%%',001$:+-.080+.,#@0010$#'?80,#%&,8010$#&?80,#%&/:010$#%?80&#+###'-@#&/@$+,-$4010$#$?80,#%&,0010$##?80+.,#@0010@@?80,#%&/8").
Definition KCb3a_167 : list kentry := Eval vm_compute in (NFC.d_kl "$0010@/?80$#%%',0010@.?80%%.#/801$:$$%08201$:0+-,001$:$$$080.$-&>01$:$$#080/+&@<01$:+--080,#%'/601$:+-,080+.,#@001$:$#@08201$:0+-'001$:$#/080--.%201$:$#.080@-+@601$:+-+080,#%'/401$:+-'080+.,#@001$:$#-08201$:0+-%001$:$#,080$$#$+801$:$#+080,@$'201$:+-&080,#%'/2").
Definition KCb3a_168 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:+-%080+.,#@001$:$#'08201$:0+-#001$:$#&080,@#'001$:$#%080--.#601$:+-$080,#%'/001$:+-#080+.,#@001$:$#$08201$:0+,/001$:$##080./@/801$:@@080@-+.<01$:+,@080,#%'.001$:+,/080+.,$&001$:@/08201$:0+,-001$:@.080-&,+001$:@-080./@,>01$:+,.080,#%'-801$:+,-080+.,#,0").
Definition KCb3a_169 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:@,08201$:0+,+001$:@+080-+@,001$:@'080$#/%-:01$:+,,080,#%'-001$:+,+080+.,#@001$:@&08201$:0+,&001$:@%080@-&+>01$:@$080$#,'':01$:+,'080,#%',801$:+,&080+.,#,001$:@#08201$:0+,$001$:/@080,/.%001$://080@%,.>01$:+,%080,#%',401$:+,$080+.,#@001$:/.08201$:0++@0").
Definition KCb3a_170 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:/-080--,,001$:/,080,/-@<01$:+,#080,#%',201$:++@080+.,#@001$:/+08201$:0++.001$:/'080@/.$401$:/&080$#$#-801$:++/080,#%',001$:++.080+.,#@001$:/%08201$:0++,001$:/$080-+//601$:/#080,&%-:01$:++-080,#%'+>01$:++,080+.,#@001$:.@08201$:0++'001$:./080,/-&>").
Definition KCb3a_171 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:..080-&,%801$:+++080,#%'+<01$:++'080+.,#@001$:.-08201$:0++%001$:.,080/&%#401$:.+080,&-#201$:++&080,#%'+:01$:++%080+.,#@001$:.'08201$:0++#001$:.&080-@&,001$:.%080-#,+601$:++$080,#%'+801$:++#080+.,#@001$:.$08201$:0+'/001$:.#080.$+@>01$:-@080@/-/0").
Definition KCb3a_172 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:+'@080,#%'+601$:+'/080+.,#@001$:-/08201$:0+'-001$:-.080.+.+601$:--080,-,&:01$:+'.080,#%'+401$:+'-080+.,#@001$:-,08201$:0+'+001$:-+080/&$,201$:-'080/#/@801$:+',080,#%'+201$:+'+080+.,#@001$:-&08201$:0+'&001$:-%080$#'+'001$:-$080/-#-:01$:+''080,#%'+0").
Definition KCb3a_173 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:+'&080+.,#@001$:-#08201$:0+'$001$:,@080$$%..401$:,/080/-#,201$:+'%080,#%''>01$:+'$080+.,#@001$:,.08201$:0+&@001$:,-080$$#$$801$:,,080.-/%<01$:+'#080,#%''<01$:+&@080+.,#@001$:,+08201$:0+&.001$:,'080$#''.601$:,&080./@'401$:+&/080,#%'':01$:+&.080+.,#@0").
Definition KCb3a_174 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:,%08201$:0+&,001$:,$080/,@->01$:,#080/,@'<01$:+&-080,#%''801$:+&,080+.,#@001$:+@08201$:0+&'001$:+/080@/,%:01$:+.080./@%001$:+&+080,#%''001$:+&'080+.,#,001$:+-08201$:0+&%001$:+,080.+,@<01$:++080@-&&<01$:+&&080,#%'&801$:+&%080+.,#,001$:+'08201$:0+&#0").
Definition KCb3a_175 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:+&080@'@-<01$:+%080,/-$801$:+&$080,#%'&001$:+&#080+.,#,001$:+$08201$:0+%/001$:+#080$#/$/801$:'@080//+&>01$:+%@080,#%'%801$:+%/080+.,#@001$:'/08201$:0+%-001$:'.080$$'+.:01$:'-080$#%@+201$:+%.080,#%'%001$:+%-080+.,#,001$:',08201$:0+%+001$:'+080,-+.<").
Definition KCb3a_176 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:''080$#$#+601$:+%,080,#%'$801$:+%+080+.,#,001$:'&08201$:0+%&001$:'%080/#.,001$:'$080/,@%601$:+%'080,#%'$001$:+%&080+.,#,001$:'#08201$:0+%$001$:&@080.--/001$:&/080/+&.201$:+%%080,#%'#801$:+%$080+.,#,001$:&.08201$:0+$@001$:&-080-&+,:01$:&,080@-&%0").
Definition KCb3a_177 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:+%#080,#%'#001$:+$@080+.,#@001$:&+08201$:0+$.001$:&'080//+#401$:&&080/,/@801$:+$/080,#%&@801$:+$.080+.,#,001$:&%08201$:0+$,001$:&$080@/+@001$:&#080,-++>01$:+$-080,#%&@001$:+$,080+.,#,001$:%@08201$:0+$'001$:%/080@'@$201$:%.080@/+,401$:+$+080,#%&/>").
Definition KCb3a_178 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:+$'080+.,#@001$:%-08201$:0+$%001$:%,080-&'/401$:%+080@%,-001$:+$&080,#%&/<01$:+$%080+.,#@001$:%'08201$:0+$#001$:%&080$$%--:01$:%%080,+,-801$:+$$080,#%&/:01$:+$#080+.,#@001$:%$08201$:0+#/001$:%#080-&'%601$:$@080@%,&:01$:+#@080,#%&/801$:+#/080+.,#@0").
Definition KCb3a_179 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$/08201$:0+#-001$:$.080/,.%:01$:$-080,/,@:01$:+#.080,#%&/001$:+#-080+.,#,001$:$,08201$:0+#+001$:$+080$##@-:01$:$'080,-++201$:+#,080,#%&.801$:+#+080+.,#@001$:$&08201$:0+#&001$:$%080$$%-#801$:$$080.&-.001$:+#'080,#%&.001$:+#&080+.,#,001$:$#08201$:0+#$0").
Definition KCb3a_180 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:@080,&+/201$:/080$#'&@:01$:+#%080,#%&-801$:+#$080+.,#,001$:.08201$:0'@@001$:-080@',@<01$:,080//%'<01$:+##080,#%&-001$:'@@080+.,#,001$:+08201$:0'@.001$:'080/+%$001$:&080/#+-601$:'@/080,#%&,801$:'@.080+.,#,001$:%08201$:0'@,001$:$080@#&/>").
Definition KCb3a_181 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:080.$+.>01$:'@-080,#%&,001$:'@,080+.,#,0010-+?80,#%'/6010-,?80,#%'/4010--?80,#%'/2010-.?80,#%'/0010-/?80,#%'.0010-@?80,#%'-8010.#?80,#%'-0010.$?80,#%',8010.%?80,#%',4010.&?80,#%',2010.'?80,#%',0010.+?80,#%'+>010.,?80,#%'+<").
Definition KCb3a_182 : list kentry := Eval vm_compute in (NFC.d_kl "$0010.-?80,#%'+:010..?80,#%'+8010./?80,#%'+6010.@?80,#%'+4010/#?80,#%'+2000,#%',4100000,#%&.8100000,#%'.080--+%4010/$?80,#%'+0000,#%'-8404010/%?80,#%''>000,#%'-0102000,#%',8400000,#%',0202010/&?80,#%''<000,#%'+080%$.@%+&/-#/$'@/#2").
Definition KCb3a_183 : list kentry := Eval vm_compute in (NFC.d_kl "$0010/'?80,#%'':000,#%''080$#%&+/%$/%+/$+0010/+?80,#%''8000,#%'#840'%,0000,#%'#0100010/,?80,#%''0000,#%&@080',#@@@$%.$0010/-?80,#%'&8000,#%&/080%$.@%+&-$',,%&&&2010/.?80,#%'&0000,#%&.040%$&0000,#%'&0800000,#%'%8102010//?80,#%'%8000,#%'%040@:010/@?80,#%'%0").
Definition KCb3a_184 : list kentry := Eval vm_compute in (NFC.d_kl "$0000,#%'$080&@%/+'.#/&-0010@#?80,#%'$8000,#%&-080&/,&/&$#-%>010@$?80,#%'$0000,#%&,080',%###-#/,#&/-.'+$>010@%?80,#%'#8000,#%'/040,$@-2010@&?80,#%'#0010@'?80,#%&@8010@+?80,#%&@0010@,?80,#%&/>010@-?80,#%&/<010-'?80--+%4000$#%%-.>100000$#%%-.<102000$#%%-.:100").
Definition KCb3a_185 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%%-.8100000$#%%-.6100000$#%%-.4100000$#%%-.2102000$#%%-.0100000$#%%-->100000$#%%--<100000$#%%--:100000$#%%--8100000$#%%--6100000$#%%--4102000$#%%--210$,8000$#%%--010%+4000$#%%-,>100000$#%%-,<100000$#%%-,:102").
Definition KCb3a_186 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%%-,8100000$#%%-,6100000$#%%-,4100000$#%%-,2100000$#%%-,0102000$#%%-+>100000$#%%-+<100000$#%%-+:100000$#%%-+8100000$#%%-+6102000$#%%-+4102000$#%%-+2102000$#%%-+0102000$#%%-'>102000$#%%-'<102000$#%%-':102").
Definition KCb3a_187 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%%-'8102000$#%%-'6102000$#%%-'4102000$#%%-'2102000$#%%-'0102000$#%%-&>102000$#%%-&<102000$#%%-&:100000$#%%-&8102000$#%%-&6100000$#%%-&4100000$#%%-&2100000$#%%-&0100000$#%%-%>100000$#%%-%<100000$#%%-%:100").
Definition KCb3a_188 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%%-%8100000$#%%-%6100000$#%%-%4102000$#%%-%210%+8000$#%%-%010$#4000$#%%-$>100000$#%%-$<100000$#%%-$:100000$#%%-$8100000$#%%-$6100000$#%%-$4100000$#%%-$2100000$#%%-$0100000$#%%-#>100000$#%%-#<100000$#%%-#:102").
Definition KCb3a_189 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%%-#8102000$#%%-#6102000$#%%-#4102000$#%%-#2102000$#%%-#0100000$#%%,@>100000$#%%,@<100000$#%%,@:100000$#%%,@8100000$#%%,@6100000$#%%,@4102000$#%%,@210->000$#%%,@010$%4000$#%%,/>100000$#%%,/<100000$#%%,/:100").
Definition KCb3a_190 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%%,/8100000$#%%,/6100000$#%%,/4102000$#%%,/210->000$#%%,/010$%4000$#%%,.>100000$#%%,.<100000$#%%,.:100000$#%%,.8100000$#%%,.6100000$#%%,.4102000$#%%,.210.4000$#%%,.010%,4000$#%%,->100000$#%%,-<100000$#%%,-:100").
Definition KCb3a_191 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%%,-8100000$#%%,-6100000$#%%,-4100000$#%%,-2100000$#%%,-0102000$#%%,,>100000$#%%,,<100000$#%%,,:10%6000$#%%,,810$,0000$#%%,,6100000$#%%,,4100000$#%%,,2100000$#%%,,0100000$#%%,+>100000$#%%,+<100000$#%%,+:100").
Definition KCb3a_192 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%%,+8100000$#%%,+6100000$#%%,+4100000$#%%,+2100000$#%%,+0100000$#%%,'>100000$#%%,'<100000$#%%,':100000$#%%,'8100000$#%%,'6100000$#%%,'4100000$#%%,'2100000$#%%,'0100000$#%%,&>100000$#%%,&<100000$#%%,&:100").
Definition KCb3a_193 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%%,&8100000$#%%,&6100000$#%%,&4100000$#%%,&2100000$#%%,&0100000$#%%,%>100000$#%%,%<100000$#%%,%:100000$#%%,%8100000$#%%,%6100000$#%%,%4100000$#%%,%2100000$#%%,%0100000$#%%,$>100000$#%%,$<100000$#%%,$:100").
Definition KCb3a_194 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%%,$8100000$#%%,$6100000$#%%,$4100000$#%%,$2102000$#%%,$0100000$#%%,#>100000$#%%,#<100000$#%%,#:100000$#%%,#8100000$#%%,#6100000$#%%,#4102000$#%%,#210&0000$#%%,#010$#:000$#%%+@>100000$#%%+@<100000$#%%+@:100").
Definition KCb3a_195 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%%+@8100000$#%%+@6100000$#%%+@4102000$#%%+@2100000$#%%+@0100000$#%%+/>100000$#%%+/<100000$#%%+/:100000$#%%+/8100000$#%%+/6100000$#%%+/4102000$#%%+/2102000$#%%+/0102000$#%%+.>100000$#%%+.<100000$#%%+.:100").
Definition KCb3a_196 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%%+.8102000$#%%+.6100000$#%%+.4100000$#%%+.2100000$#%%+.0100000$#%%+->100000$#%%+-<100000$#%%+-:100000$#%%+-8100000$#%%+-6100000$#%%+-4100000$#%%+-2100000$#%%+-0100000$#%%+,>100000$#%%+,<100000$#%%+,:100").
Definition KCb3a_197 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%%+,8102000$#%%+,6100000$#%%+,4100000$#%%+,2100000$#%%+,0102000$#%%++>100000$#%%++<100000$#%%++:100000$#%%++8102000$#%%++6100000$#%%++4100000$#%%++2100000$#%%++0100000$#%%+'>100000$#%%+'<100000$#%%+':102").
Definition KCb3a_198 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%%+'8100000$#%%+'6102000$#%%+'4102000$#%%+'2102000$#%%+'0102000$#%%+&>100000$#%%+&<100000$#%%+&:100000$#%%+&8100000$#%%+&6100000$#%%+&4100000$#%%+&2100000$#%%+&0100000$#%%+%>100000$#%%+%<100000$#%%+%:100").
Definition KCb3a_199 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%%+%8100000$#%%+%6100000$#%%+%4100000$#%%+%2100000$#%%+%0100000$#%%+$>100000$#%%+$<100000$#%%+$:100000$#%%+$8100000$#%%+$6100000$#%%+$4100000$#%%+$2100000$#%%+$0100000$#%%+#>100000$#%%+#<100000$#%%+#:100").
Definition KCb3a_200 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%%+#8100000$#%%+#6100000$#%%+#4100000$#%%+#2100000$#%%+#0100000$#%%'@>100000$#%%'@<100000$#%%'@:100000$#%%'@810&<000$#%%'@6100000$#%%'@4102000$#%%'@2100000$#%%'@0100000$#%%'/>100000$#%%'/<100000$#%%'/:100").
Definition KCb3a_201 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%%'/8100000$#%%'/6100000$#%%'/4102000$#%%'/210->000$#%%'/010$%4000$#%%'.>100000$#%%'.<100000$#%%'.:100000$#%%'.8100000$#%%'.6100000$#%%'.4100000$#%%'.2100000$#%%'.0100000$#%%'->100000$#%%'-<100000$#%%'-:100").
Definition KCb3a_202 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%%'-8100000$#%%'-6100000$#%%'-4100000$#%%'-2100000$#%%'-0100000$#%%',>100000$#%%',<100000$#%%',:100000$#%%',8100000$#%%',6100000$#%%',4100000$#%%',2100000$#%%',0102010&,?402010+#=102010,%740&<").
Definition KCb3a_203 : list kentry := Eval vm_compute in (NFC.d_kl "$0010,+?800010&'1100010&'3102010&'5100010&'7100010&'9100010&';100010&'=102010&'?100010&+1100010&+3100010&+5100010&+7100010&+9100010&+;102010&+=10$,8").
Definition KCb3a_204 : list kentry := Eval vm_compute in (NFC.d_kl "$0010&+?10%+4010&,1100010&,3100010&,5102010&,7100010&-1100010&-3100010&-5100010&-7100010&-9102010&-;102010&-=102010&-?102010&.1102010&.3102010&.5102").
Definition KCb3a_205 : list kentry := Eval vm_compute in (NFC.d_kl "$0010&.7102010&.9102010&.;102010&.=102010&.?102010&/1102010&/3102010&/5100010&/7102010&/9100010&/;100010&/=100010&/?100010&@1100010&@3100010&@5100").
Definition KCb3a_206 : list kentry := Eval vm_compute in (NFC.d_kl "$0010&@7100010&@9100010&@;102010&@=10%+8010&@?10$#4010'#1100010'#3100010'#5100010'#7100010'#9100010'#;100010'#=100010'#?100010'$1100010'$3100010'$5102").
Definition KCb3a_207 : list kentry := Eval vm_compute in (NFC.d_kl "$0010'$7102010'$9102010'$;102010'$=102010'$?100010'%1100010'%3100010'%5100010'%7100010'%9100010'%;102010'%=10->010'%?10$%4010'&1100010'&3100010'&5100").
Definition KCb3a_208 : list kentry := Eval vm_compute in (NFC.d_kl "$0010'&7100010'&9100010'&;102010'&=10->010'&?10$%4010''1100010''3100010''5100010''7100010''9100010'';102010''=10.4010''?10%,4010'+1100010'+3100010'+5100").
Definition KCb3a_209 : list kentry := Eval vm_compute in (NFC.d_kl "$0010'+7100010'+9100010'+;100010'+=100010'+?102010',1100010',3100010',510%6010',710$,0010',9100010',;100010',=100010',?100010'-1100010'-3100010'-5100").
Definition KCb3a_210 : list kentry := Eval vm_compute in (NFC.d_kl "$0010'-7100010'-9100010'-;100010'-=100010'-?100010'.1100010'.3100010'.5100010'.7100010'.9100010'.;100010'.=100010'.?100010'/1100010'/3100010'/5100").
Definition KCb3a_211 : list kentry := Eval vm_compute in (NFC.d_kl "$0010'/7100010'/9100010'/;100010'/=100010'/?100010'@1100010'@3100010'@5100010'@7100010'@9100010'@;100010'@=100010'@?100010+#1100010+#3100010+#5100").
Definition KCb3a_212 : list kentry := Eval vm_compute in (NFC.d_kl "$0010+#7100010+#9100010+#;100010+#?100010+$1100010+$3100010+$5100010+$7100010+$9100010+$;102010+$=10&0010+$?10$#:010+%1100010+%3100010+%5100010+%7100").
Definition KCb3a_213 : list kentry := Eval vm_compute in (NFC.d_kl "$0010+%9100010+%;102010+%=100010+%?100010+&1100010+&3100010+&5100010+&7100010+&9100010+&;102010+&=102010+&?102010+'1100010+'3100010+'5100010+'7102").
Definition KCb3a_214 : list kentry := Eval vm_compute in (NFC.d_kl "$0010+'9100010+';100010+'=100010+'?100010++1100010++3100010++5100010++7100010++9100010++;100010++=100010++?100010+,1100010+,3100010+,5100010+,7102").
Definition KCb3a_215 : list kentry := Eval vm_compute in (NFC.d_kl "$0010+,9100010+,;100010+,=100010+,?102010+-1100010+-3100010+-5100010+-7102010+-9100010+-;100010+-=100010+-?100010+.1100010+.3100010+.5102010+.7100").
Definition KCb3a_216 : list kentry := Eval vm_compute in (NFC.d_kl "$0010+.9102010+.;102010+.=102010+.?102010+/1100010+/3100010+/5100010+/7100010+/9100010+/;100010+/=100010+/?100010+@1100010+@3100010+@5100010+@7100").
Definition KCb3a_217 : list kentry := Eval vm_compute in (NFC.d_kl "$0010+@9100010+@;100010+@=100010+@?100010,#1100010,#3100010,#5100010,#7100010,#9100010,#;100010,#=100010,#?100010,$1100010,$3100010,$5100010,$7100").
Definition KCb3a_218 : list kentry := Eval vm_compute in (NFC.d_kl "$0010,$9100010,$;100010,$=100010,$?100010,%9100010,%;102010,%=100010,%?100010,&1100010,&3100010,&5100010,&7100010,&9100010,&;102010,&=10->010,&?10$%4").
Definition KCb3a_219 : list kentry := Eval vm_compute in (NFC.d_kl "$0010,'1100010,'3100010,'5100010,'7100010,'9100010,';100010,'=100010,'?100010,,1100010,,3100010,,5100010,,7100010,,9100010,,;100010,,=100010,,?102").
Definition KCb3a_220 : list kentry := Eval vm_compute in (NFC.d_kl "$0010,@?81$:000@-%,,08201$:0,$-.011$:$,.00&&/011$:,#'00+,-'061$:00,$-.041$:'%,051$:'%,0',%###-#/,#&&$,'/'071$:00,$-.010,+,.@#?0$.+/'.&071$:00,$-.000,$-.00'.$@%/071$:00,$-.000$%.+.%#.'00--.,,-&&%./.071$:00,$-.00@,-.#/,/@&,000,.%#$&@'+@&,071$:00,$-.00$'++$##$&000@,,&,'+/@%&071$:00,$-.00$%.+.%#.'000$-@&.@&@071$:00,$-.01700'%,0010$$'?800010$$&?80&#+###'-@#&/@$+,-$4").
Definition KCb3a_221 : list kentry := Eval vm_compute in (NFC.d_kl "$0010$$%?80$#$'.@0010$$$?80,$-.0010$$#?80/+/@<010$#@?800010$#/?80&--#$8000$#$'.@080'%,0010,-?800010,.?800010,/740$-'#'##+#4010&&?800010&%?800010&$?800010&#?800010%@?800010%/?800010%.?800").
Definition KCb3a_222 : list kentry := Eval vm_compute in (NFC.d_kl "5010%-?800010%,?80,$+&'0010%+?802010%'?80+.+@.0010%&?80,$+&'0").
Definition KCb3a_223 : list kentry := Eval vm_compute in (NFC.d_kl "$0010$&?80&%@@/0000,$+&'040,$-.0010$%?80+.,#$0010$$?80'-#/%0010@?80+%#&$8010.?811010-?820100$0010,?80+%#+$8010'?800010&?800010%?800010$?800010?800017%$0819000'.-%#'0819017&0800").
Definition KCb3a_224 : list kentry := Eval vm_compute in (NFC.d_kl "$0017%0817017$0817017$'0820170$'0017$.080'.-%-.0017'0418017+0404000'.-%-$01020170817017%%0820170+,0017+,0802017+-0820170%&,0000'.-%-+080$0000'.-%-'080+.0000'.-$-+0800000'.-$-&080&%0000'.-%-,0802").
Definition KCb3a_225 : list kentry := Eval vm_compute in (NFC.d_kl "$0000'.-%-&080'.-$-#0000'.-$-'080$0000'.-$-%0800000'.-$-$080+.$.%0000'.-%-#0820201020400$011400$0120%$0000'.-%--080'%,0000'.-%.&0816010$/?820201020400$01120400$012400$0140%$0010%#?800000'.-%-%0820201020400$011400$0120&0000'.-$,/08202010400$0110%0010/?800010$#?800010$@?800010%$?800010+?820100$0").
Definition KCb3a_226 : list kentry := Eval vm_compute in (NFC.d_kl "$0510+,-%-,+/,%/'%0+,-%./&'&.'#&0410%0520201020400$01120400$012400$0140%&0+,-%-,+/,%/,'0+,-%./&'&.'%+05112$#-05120%@05130$$&''>5140%'&%/05150%+,#,##-+<610,+,.@#?0,+,.@$0110,+,.@#?0,+,-.-0110-&?0'00100811010$0820201020400$011400$0120%$0010%084024021120201020400$01120400$012130%$20201020400$011400$012&08060201020400$011400$012'080,$.+0").
Definition KCb3a_227 : list kentry := Eval vm_compute in (NFC.d_kl "20201020400$011400$012+08080201020400$011400$012,080-0").
Definition KCb3a_228 : list kentry := Eval vm_compute in (NFC.d_kl "$02201020400$01120400$012400$014%$00%0$92201020400$011400$012%$020130213,$-.0+/'-%03+/'-&0,#%&,03,#%&.:,#%&/03,#%'#2,#%'#83,#%'%:,#%'&03,#%',6,#%',83,#%'-2,#%'-83,#%'/8,$$/@03,$$@#0,$+&'03,$+&'8,$+&+03,$+&,0,$+&.03,$+&.2@-%,,03@-%,.0$#$'..03$#$'./0$#$'.@0").
Definition KCb3a_229 : list kentry := Eval vm_compute in (NFC.d_kl "83$#$'/#0$#$'/&03$#$/#.>$#$/#/03$#%%&&>$#%%',03$#%%-/0'.-$,/03'.-$,@0'.-$-$03'.-$-,0'.-%#'03'.-%#+0'.-%,@03'.-%-$2'.-%-%0").
Definition car13a := ltac:(nf_car (KCb3a_160 ++ KCb3a_161 ++ KCb3a_162 ++ KCb3a_163 ++ KCb3a_164 ++ KCb3a_165 ++ KCb3a_166 ++ KCb3a_167 ++ KCb3a_168 ++ KCb3a_169 ++ KCb3a_170 ++ KCb3a_171 ++ KCb3a_172 ++ KCb3a_173 ++ KCb3a_174 ++ KCb3a_175 ++ KCb3a_176 ++ KCb3a_177 ++ KCb3a_178 ++ KCb3a_179 ++ KCb3a_180 ++ KCb3a_181 ++ KCb3a_182 ++ KCb3a_183 ++ KCb3a_184 ++ KCb3a_185 ++ KCb3a_186 ++ KCb3a_187 ++ KCb3a_188 ++ KCb3a_189 ++ KCb3a_190 ++ KCb3a_191 ++ KCb3a_192 ++ KCb3a_193 ++ KCb3a_194 ++ KCb3a_195 ++ KCb3a_196 ++ KCb3a_197 ++ KCb3a_198 ++ KCb3a_199 ++ KCb3a_200 ++ KCb3a_201 ++ KCb3a_202 ++ KCb3a_203 ++ KCb3a_204 ++ KCb3a_205 ++ KCb3a_206 ++ KCb3a_207 ++ KCb3a_208 ++ KCb3a_209 ++ KCb3a_210 ++ KCb3a_211 ++ KCb3a_212 ++ KCb3a_213 ++ KCb3a_214 ++ KCb3a_215 ++ KCb3a_216 ++ KCb3a_217 ++ KCb3a_218 ++ KCb3a_219 ++ KCb3a_220 ++ KCb3a_221 ++ KCb3a_222 ++ KCb3a_150 ++ KCb3a_223 ++ KCb3a_224 ++ KCb3a_225 ++ KCb3a_226 ++ KCb3a_227 ++ KCb3a_157 ++ KCb3a_228 ++ KCb3a_229 ++ KCb3a_159) ((AX2L.carryF3 LG13a KN13 []))).
Definition KN13a : list kentry := fst (fst car13a).
Definition CS13a : list sidecond := Eval lazy in (snd (fst car13a)).
Definition HS13a : list bool := Eval lazy in (snd car13a).
Lemma car13a_eq : carry LG13a KN13 [] = (KN13a, CS13a, HS13a).
Proof. apply AX2L.carry_viaF3. vm_cast_no_check (eq_refl car13a). Qed.


(* [comment removed for export] *)
Definition run13b := ltac:(nf_run KN13a ((AX2L.sym_execFS6 SEGS IT_Kn3a KN13a F8 true STOPS3 noscr (SS PC13a SR13a [] KN13a 27) []))).
Definition PC13b : Z := Eval lazy in (s_pc (fst (fst run13b))).
Definition SR13b : list expr := Eval lazy in (s_regs (fst (fst run13b))).
Definition LG13b : list sentry := s_log (fst (fst run13b)).
Definition SK13b : list kentry := s_know (fst (fst run13b)).
Definition NX13b : nat := Eval lazy in (s_next (fst (fst run13b))).
Definition SC13b : list sidecond := Eval lazy in (snd (fst run13b)).
Definition SP13b : scripts := Eval lazy in (snd run13b).
Lemma run13b_eq : sym_exec SEGS F8 true STOPS3 noscr (SS PC13a SR13a [] KN13a 27) [] = (SSR PC13b SR13b LG13b SK13b NX13b None, SC13b, SP13b).
Proof. apply (AX2L.sym_exec_viaFS6 SEGS IT_Kn3a KN13a); [exact IT_Kn3a_ok | reflexivity | vm_cast_no_check (eq_refl run13b)]. Qed.
Definition KCb3a_230 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:.-@080,&%@801$:$%%#080$#%%,.001$:$%$@080+.,$&0000@-%,-08201$:0$%%$0010$#.?80+.,#@0010$#-?80$#%%',0010$#,?820100,,?010$#+?80&,&%$8010,+?40-:01$:.-/08201$:0$%$.001$:.-.080@.$,001$:.--080/#+/<01$:$%$/080$#%%,-201$:$%$.080+.,#@001$:.-,08201$:0$%$,001$:.-+080-'+%6").
Definition KCb3a_231 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:.-'080-.-,>01$:$%$-080$#%%,-001$:$%$,080+.,#@001$:.-&08201$:0$%$'001$:.-%080/.#%201$:.-$080$#./%401$:$%$+080$#%%,,801$:$%$'080+.,#,001$:.-#08201$:0$%$%001$:.,@080,,#@<01$:.,/080/&//201$:$%$&080$#%%,,001$:$%$%080+.,#@001$:.,.08201$:0$%$#001$:.,-080/-//401$:.,,080$#-,#8").
Definition KCb3a_232 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$%$$080$#%%,+001$:$%$#080+.,&+001$:.,+08201$:0$%#/001$:.,'080@+//201$:.,&080$$&&.801$:$%#@080$#%%,'001$:$%#/080+.,&+001$:.,%08201$:0$%#-001$:.,$080/-.$201$:.,#080-'+#201$:$%#.080$#%%,&001$:$%#-080+.,&+001$:.+@08201$:0$%#+001$:.+/080-$@%201$:.+.080..-$001$:$%#,080$#%%,%0").
Definition KCb3a_233 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$%#+080+.,&+001$:.+-08201$:0$%#&001$:.+,080$#$''<01$:.++080@''+401$:$%#'080$#%%,$401$:$%#&080+.,#@001$:.+'08201$:0$%#$001$:.+&080-''->01$:.+%080,'%/401$:$%#%080$#%%,$201$:$%#$080+.,#@001$:.+$08201$:0$$@@001$:.+#080@#.,401$:.'@080$$&&,001$:$%##080$#%%,$001$:$$@@080+.,#@0").
Definition KCb3a_234 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:.'/08201$:0$$@.001$:.'.080$#+#/801$:.'-080/@#+601$:$$@/080$#%%,#001$:$$@.080+.,$&001$:.',08201$:0$$@,001$:.'+080@.#%601$:.''080/@#$>01$:$$@-080$#%%+@001$:$$@,080+.,&+001$:.'&08201$:0$$@'001$:.'%080-.-%001$:.'$080,.&/>01$:$$@+080$#%%+/401$:$$@'080+.,#@001$:.'#08201$:0$$@%0").
Definition KCb3a_235 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:.&@080..,+<01$:.&/080.,+'401$:$$@&080$#%%+/201$:$$@%080+.,#@001$:.&.08201$:0$$@#001$:.&-080$#@$@401$:.&,080,,#-<01$:$$@$080$#%%+/001$:$$@#080+.,#@001$:.&+08201$:0$$//001$:.&'080.'',401$:.&&080$$&&'401$:$$/@080$#%%+.801$:$$//080+.,&$001$:.&%08201$:0$$/-001$:.&$080,.$.8").
Definition KCb3a_236 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:.&#080@.##801$:$$/.080$#%%+.001$:$$/-080+.,&$001$:.%@08201$:0$$/+001$:.%/080@&&->01$:.%.080$$$#+:01$:$$/,080$#%%+-801$:$$/+080+.,&$001$:.%-08201$:0$$/&001$:.%,080$$#/'401$:.%+080.''':01$:$$/'080$#%%+-001$:$$/&080+.,&$001$:.%'08201$:0$$/$001$:.%&080-$.#>01$:.%%080@@+/6").
Definition KCb3a_237 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$$/%080$#%%+,801$:$$/$080+.,&$001$:.%$08201$:0$$.@001$:.%#080$#/@.>01$:.$@080..,'401$:$$/#080$#%%+,001$:$$.@080+.,&$001$:.$/08201$:0$$..001$:.$.080$#$'$<01$:.$-080$#-+/>01$:$$./080$#%%++801$:$$..080+.,#@001$:.$,08201$:0$$.,001$:.$+080@@'&801$:.$'080-,'->01$:$$.-080$#%%++0").
Definition KCb3a_238 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$$.,080+.,#,001$:.$&08201$:0$$.'001$:.$%080-.,&>01$:.$$080$#&-&601$:$$.+080$#%%+':01$:$$.'080+.,#@001$:.$#08201$:0$$.%001$:.#@080,@-+:01$:.#/080./,#801$:$$.&080$#%%+'801$:$$.%080+.,#@001$:.#.08201$:0$$.#001$:.#-080-.',001$:.#,080.#&$>01$:$$.$080$#%%+'601$:$$.#080+.,#@0").
Definition KCb3a_239 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:.#+08201$:0$$-/001$:.#'080/$+'201$:.#&080/$+%801$:$$-@080$#%%+'401$:$$-/080+.,#@001$:.#%08201$:0$$--001$:.#$080-$-%:01$:.##080-.'&801$:$$-.080$#%%+'201$:$$--080+.,#@001$:-@@08201$:0$$-+001$:-@/080-$+.:01$:-@.080/--@>01$:$$-,080$#%%+'001$:$$-+080+.,#@001$:-@-08201$:0$$-&0").
Definition KCb3a_240 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:-@,080$#-+$401$:-@+080,-&-801$:$$-'080$#%%+&801$:$$-&080+.,#,001$:-@'08201$:0$$-$001$:-@&080/$''001$:-@%080,,#,001$:$$-%080$#%%+&001$:$$-$080+.,#@001$:-@$08201$:0$$,@001$:-@#080/&/&201$:-/@080.%''<01$:$$-#080$#%%+%001$:$$,@080+.,$&001$:-//08201$:0$$,.001$:-/.080/&-@:").
Definition KCb3a_241 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:-/-080$#$'#201$:$$,/080$#%%+$001$:$$,.080+.,#@001$:-/,08201$:0$$,,001$:-/+080@+.+>01$:-/'080/--/<01$:$$,-080$#%%+#001$:$$,,080+.,$&001$:-/&08201$:0$$,'001$:-/%080@+-.:01$:-/$080./,&<01$:$$,+080$#%%'@801$:$$,'080+.,#,001$:-/#08201$:0$$,%001$:-.@080$#+#'>01$:-./080/,#+6").
Definition KCb3a_242 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$$,&080$#%%'@601$:$$,%080+.,#@001$:-..08201$:0$$,#001$:-.-080/$&,001$:-.,080,@-%>01$:$$,$080$#%%'@401$:$$,#080+.,#@001$:-.+08201$:0$$+/001$:-.'080@&%/<01$:-.&080,'%,:01$:$$+@080$#%%'@201$:$$+/080+.,#@001$:-.%08201$:0$$+-001$:-.$080@&$@401$:-.#080$$#/$:01$:$$+.080$#%%'@0").
Definition KCb3a_243 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$$+-080+.,#@001$:--@08201$:0$$++001$:--/080/+@/<01$:--.080/---801$:$$+,080$#%%'/001$:$$++080+.,$&001$:---08201$:0$$+&001$:--,080$#&+,201$:--+080-,'+>01$:$$+'080$#%%'.001$:$$+&080+.,#@001$:--'08201$:0$$+$001$:--&080..+'801$:--%080@&$-201$:$$+%080$#%%'-001$:$$+$080+.,$&0").
Definition KCb3a_244 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:--$08201$:0$$'@001$:--#080$#-&/001$:-,@080,.$-401$:$$+#080$#%%',001$:$$'@080+.,#@0010$#'?80,#%&,8010$#&?80$@4010$#%?80&#+###'-@#&/@$+,-$4010$#$?80,#%&,0010$##?80'.#-@-0010@@?80',%###-#/+%$/+.'%-4010@/?80$#%%',0010@.?80%%.$@801$:-,/08201$:0$$'.001$:-,.080-/-$>01$:-,-080$$$/':").
Definition KCb3a_245 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$$'/080'.#.#$001$:$$'.080+.,#,001$:-,,08201$:0$$',001$:-,+080./@/801$:-,'080@-+.<01$:$$'-080'.#.##001$:$$',080+.,$&001$:-,&08201$:0$$''001$:-,%080.+#&001$:-,$080/,&#601$:$$'+080'.#-@@001$:$$''080+.,#,001$:-,#08201$:0$$'%001$:-+@080$#&@.:01$:-+/080$$+&+<01$:$$'&080'.#-@/<").
Definition KCb3a_246 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$$'%080+.,#@001$:-+.08201$:0$$'#001$:-+-080$#&@.:01$:-+,080@..->01$:$$'$080'.#-@/:01$:$$'#080+.,#@001$:-++08201$:0$$&/001$:-+'080-##'>01$:-+&080@..,401$:$$&@080'.#-@/801$:$$&/080+.,#@001$:-+%08201$:0$$&-001$:-+$080.@/#<01$:-+#080@..':01$:$$&.080'.#-@/601$:$$&-080+.,#@0").
Definition KCb3a_247 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:-'@08201$:0$$&+001$:-'/080$$$/#401$:-'.080@..%>01$:$$&,080'.#-@/401$:$$&+080+.,#@001$:-'-08201$:0$$&&001$:-',080-/+&:01$:-'+080.#.,601$:$$&'080'.#-@/201$:$$&&080+.,#@001$:-''08201$:0$$&$001$:-'&080$##&@:01$:-'%080$#%$-801$:$$&%080'.#-@/001$:$$&$080+.,#@001$:-'$08201$:0$$%@0").
Definition KCb3a_248 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:-'#080-+%&>01$:-&@080,,,+401$:$$&#080'.#-@.>01$:$$%@080+.,#@001$:-&/08201$:0$$%.001$:-&.080$#+-'201$:-&-080/'-+>01$:$$%/080'.#-@.<01$:$$%.080+.,#@001$:-&,08201$:0$$%,001$:-&+080.#.%601$:-&'080.#.$001$:$$%-080'.#-@.:01$:$$%,080+.,#@001$:-&&08201$:0$$%'001$:-&%080@$+&>").
Definition KCb3a_249 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:-&$080@,.&201$:$$%+080'.#-@.801$:$$%'080+.,#@001$:-&#08201$:0$$%%001$:-%@080.'@@401$:-%/080$##&/601$:$$%&080'.#-@.001$:$$%%080+.,#,001$:-%.08201$:0$$%#001$:-%-080$#+,$001$:-%,080-##&801$:$$%$080'.#-@-801$:$$%#080+.,#,001$:-%+08201$:0$$$/001$:-%'080$$+%/801$:-%&080@$+%0").
Definition KCb3a_250 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$$$@080'.#-@-001$:$$$/080+.,#@0010,,?8201$:0-%&0010,&?800010,'?800010,+110$@4010,+310$@4010,+510$@4010,+710$@4000'.#.#$0402000'.#-@/040%@2000'.#-@.080%$.@%+&/,@-$%&@/0000'.#-@-8400000'.#-@-0100000'.#.##080--+%4000'.#-@@0402").
Definition KCb3a_251 : list kentry := Eval vm_compute in (NFC.d_kl "$0000'.#-@/<100000'.#-@/8200010,/?40$+<01$:&&+08201$:0-$@001$:&&'080$#'@/401$:&&&080.#%@:01$:-%%080--+%401$:-%$010201$:-%#0820100,@?01$:-$@080+.,%.001$:&&%08201$:0-$,001$:&&$080@@&/<01$:&&#080@@&.<01$:-$/080--+%401$:-$.010001$:-$-0820100,@?").
Definition KCb3a_252 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:-$,080+.,%.001$:&%@08201$:0-$'001$:&%/080.@'-001$:&%.080$#-/@:01$:-$+080$#%%-.<01$:-$'080+.,#@001$:&%-08201$:0-$%001$:&%,080-.@+601$:&%+080$$$'+<01$:-$&080$#%%-.:01$:-$%080+.,#@001$:&%'08201$:0-$#001$:&%&080.@&@201$:&%%080,@.-<01$:-$$080$#%%-.801$:-$#080+.,#@0").
Definition KCb3a_253 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:&%$08201$:0-#/001$:&%#080@@-%<01$:&$@080.@&,401$:-#@080$#%%-.601$:-#/080+.,#@001$:&$/08201$:0-#-001$:&$.080@#/.601$:&$-080@#/,201$:-#.080$#%%-.401$:-#-080+.,#@001$:&$,08201$:0-#+001$:&$+080/.+&201$:&$'080.#+':01$:-#,080$#%%-.201$:-#+080+.,#@001$:&$&08201$:0-#&0").
Definition KCb3a_254 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:&$%080-%%.<01$:&$$080-,+%201$:-#'080$#%%-.001$:-#&080+.,#@001$:&$#08201$:0-#$001$:&#@080-.@%:01$:&#/080,@.,401$:-#%080$#%%--001$:-#$080+.,$&001$:&#.08201$:0,@@001$:&#-080/$+->01$:&#,080.%,#201$:-##080$#%%-,>01$:,@@080+.,#@001$:&#+08201$:0,@.001$:&#'080$$$'#:").
Definition KCb3a_255 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:&#&080$#+%&801$:,@/080$#%%-,<01$:,@.080+.,#@001$:&#%08201$:0,@,001$:&#$080-%$-:01$:&##080-%$+401$:,@-080$#%%-,:01$:,@,080+.,#@001$:%@@08201$:0,@'001$:%@/080/.'&<01$:%@.080@.&&:01$:,@+080$#%%-,801$:,@'080+.,#@001$:%@-08201$:0,@%001$:%@,080$#-/&201$:%@+080@.&%8").
Definition KCb3a_256 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:,@&080$#%%-,001$:,@%080+.,#,001$:%@'08201$:0,@#001$:%@&080..-%<01$:%@%080$#-/#<01$:,@$080$#%%-+801$:,@#080+.,#@001$:%@$08201$:0,//001$:%@#080@@,+001$:%/@080.%+/401$:,/@080$#%%-+601$:,//080+.,#@001$:%//08201$:0,/-001$:%/.080$#+$+<01$:%/-080.',@401$:,/.080$#%%-+4").
Definition KCb3a_257 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:,/-080+.,#@001$:%/,08201$:0,/+001$:%/+080-'.,201$:%/'080$$&,$601$:,/,080$#%%-+201$:,/+080+.,#@001$:%/&08201$:0,/&001$:%/%080/@#/401$:%/$080,@.'201$:,/'080$#%%-+001$:,/&080+.,#@001$:%/#08201$:0,/$001$:%.@080.#'':01$:%./080/'#$<01$:,/%080$#%%-'>01$:,/$080+.,#@0").
Definition KCb3a_258 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:%..08201$:0,.@001$:%.-080/.&,001$:%.,080$#$'.601$:,/#080$#%%-'<01$:,.@080+.,#@001$:%.+08201$:0,..001$:%.'080.%'.601$:%.&080,,%,<01$:,./080$#%%-':01$:,..080+.,#@001$:%.%08201$:0,.,001$:%.$080$#-.%<01$:%.#080@@,%<01$:,.-080$#%%-'801$:,.,080+.,#@001$:%-@08201$:0,.'0").
Definition KCb3a_259 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:%-/080-%#+>01$:%-.080$#&-+201$:,.+080$#%%-'601$:,.'080+.,#@001$:%--08201$:0,.%001$:%-,080@,&#601$:%-+080.#'%801$:,.&080$#%%-'401$:,.%080+.,#@001$:%-'08201$:0,.#001$:%-&080$$$&%<01$:%-%080@,%/201$:,.$080$#%%-'201$:,.#080+.,#@001$:%-$08201$:0,-/001$:%-#080,,$.6").
Definition KCb3a_260 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:%,@080$#-.#:01$:,-@080$#%%-'001$:,-/080+.,#@001$:%,/08201$:0,--001$:%,.080$$&+%201$:%,-080.@&'201$:,-.080$#%%-&>01$:,--080+.,#@001$:%,,08201$:0,-+001$:%,+080$#--#>01$:%,'080/.&&>01$:,-,080$#%%-&<01$:,-+080+.,#@001$:%,&08201$:0,-&001$:%,%080/,#-001$:%,$080@.%@>").
Definition KCb3a_261 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:,-'080$#%%-&:01$:,-&080+.,#@001$:%,#08201$:0,-$001$:%+@080/&@+>01$:%+/080/@#,201$:,-%080$#%%-&801$:,-$080+.,#@001$:%+.08201$:0,,@001$:%+-080$$&'.801$:%+,080@@,#201$:,-#080$#%%-&001$:,,@080+.,#,001$:%++08201$:0,,.001$:%+'080-',@801$:%+&080,.'$001$:,,/080$#%%-%0").
Definition KCb3a_262 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:,,.080+.,$&001$:%+%08201$:0,,,001$:%+$080-.-/>01$:%+#080,,$,001$:,,-080$#%%-$001$:,,,080+.,#,001$:%'@08201$:0,,'001$:%'/080$#-,&601$:%'.080$#+$&601$:,,+080$#%%-#<01$:,,'080+.,#@001$:%'-08201$:0,,%001$:%',080-,'@001$:%'+080-',/601$:,,&080$#%%-#:01$:,,%080+.,#@0").
Definition KCb3a_263 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:%''08201$:0,,#001$:%'&080-',%801$:%'%080.@&$201$:,,$080$#%%-#801$:,,#080+.,#@001$:%'$08201$:0,+/001$:%'#080$$&&@<01$:%&@080.%',201$:,+@080$#%%-#601$:,+/080+.,#@001$:%&/08201$:0,+-001$:%&.080$$$#/<01$:%&-080.#'#601$:,+.080$#%%-#401$:,+-080+.,#@001$:%&,08201$:0,++0").
Definition KCb3a_264 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:%&+080$$'/'601$:%&'080$$$#-601$:,+,080$#%%-#201$:,++080+.,#@001$:%&&08201$:0,+&001$:%&%080@&+/201$:%&$080@#/&<01$:,+'080$#%%-#001$:,+&080+.,#@001$:%&#08201$:0,+$001$:%%@080.#&'401$:%%/080,,$'801$:,+%080$#%%,@001$:,+$080+.,$&001$:%%.08201$:0,'@001$:%%-080/&/@<").
Definition KCb3a_265 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:%%,080.',-801$:,+#080$#%%,/001$:,'@080+.,$&001$:%%+08201$:0,'.001$:%%'080/.%+>01$:%%&080,&%@801$:,'/080$#%%,.001$:,'.080+.,$&001$:%%%08201$:0,',001$:%%$080@.$,001$:%%#080/#+/<01$:,'-080$#%%,-201$:,',080+.,#@001$:%$@08201$:0,''001$:%$/080-'+%601$:%$.080-.-,>").
Definition KCb3a_266 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:,'+080$#%%,-001$:,''080+.,#@001$:%$-08201$:0,'%001$:%$,080/.#%201$:%$+080$#./%401$:,'&080$#%%,,801$:,'%080+.,#,001$:%$'08201$:0,'#001$:%$&080,,#@<01$:%$%080/&//201$:,'$080$#%%,,001$:,'#080+.,#@001$:%$$08201$:0,&/001$:%$#080/-//401$:%#@080$#-,#801$:,&@080$#%%,+0").
Definition KCb3a_267 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:,&/080+.,&+001$:%#/08201$:0,&-001$:%#.080@+//201$:%#-080$$&&.801$:,&.080$#%%,'001$:,&-080+.,&+001$:%#,08201$:0,&+001$:%#+080/-.$201$:%#'080-'+#201$:,&,080$#%%,&001$:,&+080+.,&+001$:%#&08201$:0,&&001$:%#%080-$@%201$:%#$080..-$001$:,&'080$#%%,%001$:,&&080+.,&+0").
Definition KCb3a_268 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:%##08201$:0,&$001$:$@@080$#$''<01$:$@/080@''+401$:,&%080$#%%,$401$:,&$080+.,#@001$:$@.08201$:0,%@001$:$@-080-''->01$:$@,080,'%/401$:,&#080$#%%,$201$:,%@080+.,#@001$:$@+08201$:0,%.001$:$@'080@#.,401$:$@&080$$&&,001$:,%/080$#%%,$001$:,%.080+.,#@001$:$@%08201$:0,%,0").
Definition KCb3a_269 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$@$080$#+#/801$:$@#080/@#+601$:,%-080$#%%,#001$:,%,080+.,$&001$:$/@08201$:0,%'001$:$//080@.#%601$:$/.080/@#$>01$:,%+080$#%%+@001$:,%'080+.,&+001$:$/-08201$:0,%%001$:$/,080-.-%001$:$/+080,.&/>01$:,%&080$#%%+/401$:,%%080+.,#@001$:$/'08201$:0,%#001$:$/&080..,+<").
Definition KCb3a_270 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$/%080.,+'401$:,%$080$#%%+/201$:,%#080+.,#@001$:$/$08201$:0,$/001$:$/#080$#@$@401$:$.@080,,#-<01$:,$@080$#%%+/001$:,$/080+.,#@001$:$./08201$:0,$-001$:$..080.'',401$:$.-080$$&&'401$:,$.080$#%%+.801$:,$-080+.,&$001$:$.,08201$:0,$+001$:$.+080,.$.801$:$.'080@.##8").
Definition KCb3a_271 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:,$,080$#%%+.001$:,$+080+.,&$001$:$.&08201$:0,$&001$:$.%080@&&->01$:$.$080$$$#+:01$:,$'080$#%%+-801$:,$&080+.,&$001$:$.#08201$:0,$$001$:$-@080$$#/'401$:$-/080.''':01$:,$%080$#%%+-001$:,$$080+.,&$001$:$-.08201$:0,#@001$:$--080-$.#>01$:$-,080@@+/601$:,$#080$#%%+,8").
Definition KCb3a_272 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:,#@080+.,&$001$:$-+08201$:0,#.001$:$-'080$#/@.>01$:$-&080..,'401$:,#/080$#%%+,001$:,#.080+.,&$001$:$-%08201$:0,#,001$:$-$080$#$'$<01$:$-#080$#-+/>01$:,#-080$#%%++801$:,#,080+.,#@001$:$,@08201$:0,#'001$:$,/080@@'&801$:$,.080-,'->01$:,#+080$#%%++001$:,#'080+.,#,0").
Definition KCb3a_273 : list kentry := Eval vm_compute in (NFC.d_kl ":01$:$,-08201$:0,#%001$:$,,080-.,&>01$:$,+080$#&-&601$:,#&080$#%%+':01$:,#%080+.,#@001$:$,'08201$:0,##001$:$,&080,@-+:01$:$,%080./,#801$:,#$080$#%%+'801$:,##080+.,#@0").
Definition KCb3a_274 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$$.08201$:0+-@001$:$$-080..+'801$:$$,080@&$-201$:+.#080$#%%'-001$:+-@080+.,$&001$:$$+08201$:0+-.001$:$$'080$#-&/001$:$$&080,.$-401$:+-/080$#%%',001$:+-.080+.,#@001$:$$%08201$:0+-,001$:$$$080.$-&>01$:$$#080/+&@<01$:+--080,#%'/601$:+-,080+.,#@001$:$#@08201$:0+-'0").
Definition KCb3a_275 : list kentry := Eval vm_compute in (NFC.d_kl "801$:$#/080--.%201$:$#.080@-+@601$:+-+080,#%'/401$:+-'080+.,#@001$:$#-08201$:0+-%001$:$#,080$$#$+801$:$#+080,@$'201$:+-&080,#%'/2").
Definition KCb3a_276 : list kentry := Eval vm_compute in (NFC.d_kl "?010&'1100010&'3102010&'5100010&'7100010&'9100010&';100010&'=102010&'?100010&+1100010&+3100010&+5100010&+7100010&+9100010&+;102010&+=10$,8").
Definition KCb3a_277 : list kentry := Eval vm_compute in (NFC.d_kl "$0010,$9100010,$;100010,$=100010,$?100010,%9100010,%;102010,%=100010,%?100010,@?81$:000@-%,,08201$:0,$-.011$:&&,00$-#011$:-$.20>11$:-%$20>11$:..#00&'/011$:$%%$00'@+-061$:00,$-.0").
Definition KCb3a_278 : list kentry := Eval vm_compute in (NFC.d_kl ";41$:'%,051$:'%,0',%###-#/,#&&$,'/'071$:00,$-.010,+,.@#?0$.+/'.&071$:00,$-.000,$-.00'.$@%/071$:00,$-.000$%.+.%#.'00--.,,-&&%./.071$:00,$-.00@,-.#/,/@&,000,.%#$&@'+@&,071$:00,$-.00$'++$##$&000@,,&,'+/@%&071$:00,$-.00$%.+.%#.'000$-@&.@&@071$:00,$-.01700'%,0010$$'?800010$$&?80&#+###'-@#&/@$+,-$4").
Definition KCb3a_279 : list kentry := Eval vm_compute in (NFC.d_kl "<3$#$'/#0$#$'/&03$#$/#.>$#$/#/03$#%%&&>$#%%',03$#%%-/0'.#-@-03'.#-@-2'.#-@-83'.#-@/>'.#-@@03'.#-@@8'.#.##03'.#.#$8'.-$,/03'.-$,@0'.-$-$03'.-$-,0'.-%#'03'.-%#+0'.-%,@03'.-%-$2'.-%-%0").
Definition car13b := ltac:(nf_car (KCb3a_230 ++ KCb3a_231 ++ KCb3a_232 ++ KCb3a_233 ++ KCb3a_234 ++ KCb3a_235 ++ KCb3a_236 ++ KCb3a_237 ++ KCb3a_238 ++ KCb3a_239 ++ KCb3a_240 ++ KCb3a_241 ++ KCb3a_242 ++ KCb3a_243 ++ KCb3a_244 ++ KCb3a_245 ++ KCb3a_246 ++ KCb3a_247 ++ KCb3a_248 ++ KCb3a_249 ++ KCb3a_250 ++ KCb3a_251 ++ KCb3a_252 ++ KCb3a_253 ++ KCb3a_254 ++ KCb3a_255 ++ KCb3a_256 ++ KCb3a_257 ++ KCb3a_258 ++ KCb3a_259 ++ KCb3a_260 ++ KCb3a_261 ++ KCb3a_262 ++ KCb3a_263 ++ KCb3a_264 ++ KCb3a_265 ++ KCb3a_266 ++ KCb3a_267 ++ KCb3a_268 ++ KCb3a_269 ++ KCb3a_270 ++ KCb3a_271 ++ KCb3a_272 ++ KCb3a_273 ++ KCb3a_161 ++ KCb3a_162 ++ KCb3a_163 ++ KCb3a_164 ++ KCb3a_165 ++ KCb3a_274 ++ KCb3a_275 ++ KCb3a_168 ++ KCb3a_169 ++ KCb3a_170 ++ KCb3a_171 ++ KCb3a_172 ++ KCb3a_173 ++ KCb3a_174 ++ KCb3a_175 ++ KCb3a_176 ++ KCb3a_177 ++ KCb3a_178 ++ KCb3a_179 ++ KCb3a_180 ++ KCb3a_181 ++ KCb3a_182 ++ KCb3a_183 ++ KCb3a_184 ++ KCb3a_185 ++ KCb3a_186 ++ KCb3a_187 ++ KCb3a_188 ++ KCb3a_189 ++ KCb3a_190 ++ KCb3a_191 ++ KCb3a_192 ++ KCb3a_193 ++ KCb3a_194 ++ KCb3a_195 ++ KCb3a_196 ++ KCb3a_197 ++ KCb3a_198 ++ KCb3a_199 ++ KCb3a_200 ++ KCb3a_201 ++ KCb3a_202 ++ KCb3a_276 ++ KCb3a_204 ++ KCb3a_205 ++ KCb3a_206 ++ KCb3a_207 ++ KCb3a_208 ++ KCb3a_209 ++ KCb3a_210 ++ KCb3a_211 ++ KCb3a_212 ++ KCb3a_213 ++ KCb3a_214 ++ KCb3a_215 ++ KCb3a_216 ++ KCb3a_217 ++ KCb3a_277 ++ KCb3a_278 ++ KCb3a_221 ++ KCb3a_222 ++ KCb3a_150 ++ KCb3a_223 ++ KCb3a_224 ++ KCb3a_225 ++ KCb3a_226 ++ KCb3a_227 ++ KCb3a_157 ++ KCb3a_228 ++ KCb3a_279 ++ KCb3a_159) ((AX2L.carryF3 LG13b KN13a []))).
Definition KN13b : list kentry := fst (fst car13b).
Definition CS13b : list sidecond := Eval lazy in (snd (fst car13b)).
Definition HS13b : list bool := Eval lazy in (snd car13b).
Lemma car13b_eq : carry LG13b KN13a [] = (KN13b, CS13b, HS13b).
Proof. apply AX2L.carry_viaF3. vm_cast_no_check (eq_refl car13b). Qed.


(* [comment removed for export] *)
Definition SR13r : list expr := sr_upd SR_E6 10 (ELit (2 ^ 64 - 12)).

(* [comment removed for export] *)
Definition run13n := ltac:(nf_run KN_E6 ((AX2L.sym_execFS6 SEGS IT_Kn3a KN_E6 F8 true STOPS3 noscr (SS A_internal_mmap_ret SR13r [] KN_E6 26) []))).
Definition PC13n : Z := Eval lazy in (s_pc (fst (fst run13n))).
Definition SR13n : list expr := Eval lazy in (s_regs (fst (fst run13n))).
Definition LG13n : list sentry := s_log (fst (fst run13n)).
Definition SK13n : list kentry := s_know (fst (fst run13n)).
Definition NX13n : nat := Eval lazy in (s_next (fst (fst run13n))).
Definition SC13n : list sidecond := Eval lazy in (snd (fst run13n)).
Definition SP13n : scripts := Eval lazy in (snd run13n).
Lemma run13n_eq : sym_exec SEGS F8 true STOPS3 noscr (SS A_internal_mmap_ret SR13r [] KN_E6 26) [] = (SSR PC13n SR13n LG13n SK13n NX13n None, SC13n, SP13n).
Proof. apply (AX2L.sym_exec_viaFS6 SEGS IT_Kn3a KN_E6); [exact IT_Kn3a_ok | reflexivity | vm_cast_no_check (eq_refl run13n)]. Qed.
Definition KCb3a_280 : list kentry := Eval vm_compute in (NFC.d_kl "$0010$$%?80',%###-#/,#&/-.'+#8010$$$?80,$-.0010$$#?80/+/@<010$#@?800010$#/?80&--$/8010$#.?40$8010$$'?800010$$&?80&#+###'-@#&/@$+,-$4010$#.740'4010$#-?80,$+&'0010$#,?80'@,0010$#+?80,$-.0010$#'?80@-%,,0010$#&?80&'.-/0000$#$'.@080'%,0010$#%?802").
Definition KCb3a_281 : list kentry := Eval vm_compute in (NFC.d_kl "$0010$#$?80+.+@.0010$##?820100,@?010@@?80&,./@0010,-?800010,.?800010,/?400010@/?80,$+&'0010@.?80%%+#&8010,/740$-'#'##+#4010,@?80&#+###'-@#&/@$+,-$4010&&?800010&%?800010&$?800010&#?800010%@?800010%/?800").
Definition KCb3a_282 : list kentry := Eval vm_compute in (NFC.d_kl "$0010%.?800010%-?800010%,?80,$+&'0010%+?802010%'?80+.+@.0010%&?80,$+&'0010%%?80&%/-&8000$#$'/&080$$%+/+.$/%$$%$@.'+8100$#$'/'00'%'>000$#$/#/080$$%+/+.$/%$$%$@.'+8100$#$/#@00'%'>000,$+&.010271700'%,000$%.+.%#.'00--.,,-&&%./.0000,$$/@080$%.+.%'@@0000,$+&+080+,-%./&'&.'%'>000$#$'..0820100$.?").
Definition KCb3a_283 : list kentry := Eval vm_compute in (NFC.d_kl "$0010$.?80&#+###'-@#&/@$+,-$4000+/'-%080$$'.&2010$-?8202010400$0110%0010$,?80',.@+0010$+?80+.+@.0010$'?80,$+&'0010$&?80&%@@/0000,$+&'040,$-.0010$%?80+.,#$0010$$?80'-#/%0010@?80+%#&$8010.?811010-?820100$0010,?80+%#+$8010'?800010&?800").
Definition KCb3a_284 : list kentry := Eval vm_compute in (NFC.d_kl "$0010%?800010$?800010?800017%$0819000'.-%#'0819010+.?800010+-?800010+,?800010++?800010+'?800010+&?800010+%?80'.-%-$0010+$?820201020400$011400$0120%$0010+#?820201020400$011400$0120%$0010'@?80+%$+$8010'.?80+$@@+0").
Definition KCb3a_285 : list kentry := Eval vm_compute in (NFC.d_kl "$0017&0800017%0817017$0817017$'0820170$'0017$.080'.-%-.0017'0418017+0404000'.-%-$01020170817017%%0820170+,0017+,0802010,&?800010,%?800010,$?800010,#?820170+-0010+@?80'.-$-#0").
Definition KCb3a_286 : list kentry := Eval vm_compute in (NFC.d_kl "$0010+/?820170+,0017+-0820170%&,0000'.-%-+080$0000'.-%-'080+.0000'.-$-+0800000'.-$-&080&%0000'.-%-,0802000'.-%-&080'.-$-#0000'.-$-'080$0000'.-$-%0800000'.-$-$080+.$.%0010'/?820201020400$011400$0120%$0000'.-%-#0820201020400$011400$0120%$0000'.-%--080'%,0000'.-%.&0816010$/?820201020400$01120400$012400$0140%$0").
Definition KCb3a_287 : list kentry := Eval vm_compute in (NFC.d_kl "$0010%#?800010&,?80'%,0010&-?80$6010&.?80-0010&/?80,$.+0000'.-%-%0820201020400$011400$0120&0000'.-$,/08202010400$0110%0010/?800010$#?800010$@?800010%$?800010&'?800010&+?800010&@?800010'#?800010'$?800").
Definition KCb3a_288 : list kentry := Eval vm_compute in (NFC.d_kl "$0010+?820100$0510+,-%-,+/,%/'%0+,-%./&'&.'#&0410%0520201020400$01120400$012400$0140%&0+,-%-,+/,%/,'0+,-%./&'&.'%+05112$#-05120%@05130$$&''>5140%'&%/05150%+,#,##-+<610,+,.@#?0,+,.@$0110,+,.@#?0,+,-.-0110@-?0&.0110,,?0&0110'-?0,00100811010$0820201020400$011400$0120%$0").
Definition KCb3a_289 : list kentry := Eval vm_compute in (NFC.d_kl "$0010%084024021120201020400$01120400$012130%$20201020400$011400$012&08060201020400$011400$012'080,$.+00201020400$011400$012+08080201020400$011400$012,080-00201020400$011400$012-080:0201020400$011400$012.080$60201020400$011400$012/080%00201020400$011400$012@08160201020400$011400$012$#080<0201020400$011400$012$$080'%,00201020400$011400$012$%080$60201020400$011400$012$&08150201020400$011400$012$'080$80201020400$011400$012$+08150201020400$011400$012$,080%>").
Definition KCb3a_290 : list kentry := Eval vm_compute in (NFC.d_kl "$00201020400$011400$012$-08000201020400$011400$012$.080&20201020400$011400$012$/0820201020400$01120400$012400$0140%$00201020400$011400$012$@08000201020400$011400$012%#08002201020400$01120400$012400$014%$00%0$92201020400$011400$012%$020130213,$-.0+/'-%03+/'-&0,$$/@03,$$@#0,$+&'03,$+&'8,$+&+03,$+&,0,$+&.03,$+&.2$#$'..03$#$'./0$#$'.@03$#$'/#0$#$'/&03$#$/#.>$#$/#/0").
Definition KCb3a_291 : list kentry := Eval vm_compute in (NFC.d_kl "$03$#%%&&>'.-$,/03'.-$,@0'.-$-$03'.-$-,0'.-%#'03'.-%#+0'.-%,@03'.-%-$2'.-%-%03'.-%-.0'.-%.&03'.-%.'0'..#@,0600+.+%#00'%@,.,0417'%,0517'%,0+,-%./%./$%#/071700'%,000,$-.00'.$@%/071700'%,010,+,.@#?0/.'-/-0117'808117+80/8117$+00&0117$/00&0").
Definition KCb3a_292 : list kentry := Eval vm_compute in (NFC.d_kl "4117%&00&&0117+.00&-/061700'%,05182&%./@+>").
Definition car13n := ltac:(nf_car (KCb3a_280 ++ KCb3a_281 ++ KCb3a_282 ++ KCb3a_283 ++ KCb3a_284 ++ KCb3a_285 ++ KCb3a_286 ++ KCb3a_287 ++ KCb3a_288 ++ KCb3a_289 ++ KCb3a_290 ++ KCb3a_291 ++ KCb3a_292) ((AX2L.carryF3 LG13n KN_E6 []))).
Definition KN13n : list kentry := fst (fst car13n).
Definition CS13n : list sidecond := Eval lazy in (snd (fst car13n)).
Definition HS13n : list bool := Eval lazy in (snd car13n).
Lemma car13n_eq : carry LG13n KN_E6 [] = (KN13n, CS13n, HS13n).
Proof. apply AX2L.carry_viaF3. vm_cast_no_check (eq_refl car13n). Qed.


Lemma itinerary3a_ok :
  (PC13a =? A_internal_mmap_ecall, SC13a, CS13a) = (false, [], [])
  /\ (PC13b =? A_internal_mmap_ecall, SC13b, CS13b) = (false, [], [])
  /\ (PC13n, SC13n) = (A_spin_mmapordie, []).
Proof. vmeq_conj. Qed.
End TwB.
End BootKn3a.

(* [comment removed for export] *)
Module BootKn3b.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AxNfCodec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanPlan AxSymExec3F. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3F.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require EntryKn EntryGlue. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBlock__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.NodesMmDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.MallocSymAux.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Img. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require Import KnKeepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require Import AxSymExec3L.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Definition IT_Kn3b : itab := AX2F.mk_itab_rs SEGS [
  (263364, 20%nat); (402140, 22%nat); (402344, 10%nat); (415876, 1193%nat); (423644, 15%nat); (423740, 16%nat); (540584, 88%nat)] PTLeaf.
Lemma IT_Kn3b_ok : itab_sound SEGS IT_Kn3b.
Proof. apply AX2F.mk_itab_rs_sound. apply AX2F.itab_leaf_sound. Qed.


(* [comment removed for export] *)
Definition run13c := ltac:(nf_run KN13b ((AX2L.sym_execFS6 SEGS IT_Kn3b KN13b F8 true STOPS3 noscr (SS PC13b SR13b [] KN13b 27) []))).
Definition PC13c : Z := Eval lazy in (s_pc (fst (fst run13c))).
Definition SR13c : list expr := Eval lazy in (s_regs (fst (fst run13c))).
Definition LG13c : list sentry := s_log (fst (fst run13c)).
Definition SK13c : list kentry := s_know (fst (fst run13c)).
Definition NX13c : nat := Eval lazy in (s_next (fst (fst run13c))).
Definition SC13c : list sidecond := Eval lazy in (snd (fst run13c)).
Definition SP13c : scripts := Eval lazy in (snd run13c).
Lemma run13c_eq : sym_exec SEGS F8 true STOPS3 noscr (SS PC13b SR13b [] KN13b 27) [] = (SSR PC13c SR13c LG13c SK13c NX13c None, SC13c, SP13c).
Proof. apply (AX2L.sym_exec_viaFS6 SEGS IT_Kn3b KN13b); [exact IT_Kn3b_ok | reflexivity | vm_cast_no_check (eq_refl run13c)]. Qed.
Definition KCa3b_1 : list kentry := Eval vm_compute in (NFC.d_kl "$0010$#+?80&,+#@8010-%?40@>01$:$+$$08201$:0$/&-001$:$+$#080/.+&201$:$+#@080.#+':01$:$/&.080$#%$-$201$:$/&-080+.+#%0000@-$,#08201$:0$/&/0010$#.?80+.+#%0010$#-?80$#%$&@0010$#,?820100-&?01$:$+#/08201$:0$/&+001$:$+#.080-%%.<01$:$+#-080-,+%201$:$/&,080$#%$-$001$:$/&+080+.+#%0").
Definition KCa3b_2 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$+#,08201$:0$/&&001$:$+#+080-.@%:01$:$+#'080,@.,401$:$/&'080$#%$-#001$:$/&&080+.+#,001$:$+#&08201$:0$/&$001$:$+#%080/$+->01$:$+#$080.%,#201$:$/&%080$#%$,@>01$:$/&$080+.+#%001$:$+##08201$:0$/%@001$:$'@@080$$$'#:01$:$'@/080$#+%&801$:$/&#080$#%$,@<01$:$/%@080+.+#%001$:$'@.08201$:0$/%.0").
Definition KCa3b_3 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$'@-080-%$-:01$:$'@,080-%$+401$:$/%/080$#%$,@:01$:$/%.080+.+#%001$:$'@+08201$:0$/%,001$:$'@'080/.'&<01$:$'@&080@.&':01$:$/%-080$#%$,@801$:$/%,080+.+#%001$:$'@%08201$:0$/%'001$:$'@$080$#-/&201$:$'@#080@.&&801$:$/%+080$#%$,@001$:$/%'080+.'@/001$:$'/@08201$:0$/%%001$:$'//080..-%<").
Definition KCa3b_4 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$'/.080$#-/#<01$:$/%&080$#%$,/801$:$/%%080+.+#%001$:$'/-08201$:0$/%#001$:$'/,080@@,,001$:$'/+080.%+/401$:$/%$080$#%$,/601$:$/%#080+.+#%001$:$'/'08201$:0$/$/001$:$'/&080$#+$+<01$:$'/%080.',@401$:$/$@080$#%$,/401$:$/$/080+.+#%001$:$'/$08201$:0$/$-001$:$'/#080-'.,201$:$'.@080$$&,$6").
Definition KCa3b_5 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$/$.080$#%$,/201$:$/$-080+.+#%001$:$'./08201$:0$/$+001$:$'..080/@#@401$:$'.-080,@.'201$:$/$,080$#%$,/001$:$/$+080+.+#%001$:$'.,08201$:0$/$&001$:$'.+080.#'':01$:$'.'080/'#$<01$:$/$'080$#%$,.>01$:$/$&080+.+#%001$:$'.&08201$:0$/$$001$:$'.%080/.&,001$:$'.$080$#$'.601$:$/$%080$#%$,.<").
Definition KCa3b_6 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$/$$080+.+#%001$:$'.#08201$:0$/#@001$:$'-@080.%'.601$:$'-/080,,%,<01$:$/$#080$#%$,.:01$:$/#@080+.+#%001$:$'-.08201$:0$/#.001$:$'--080$#-.%<01$:$'-,080@@,&<01$:$/#/080$#%$,.801$:$/#.080+.+#%001$:$'-+08201$:0$/#,001$:$'-'080-%#+>01$:$'-&080$#&-+201$:$/#-080$#%$,.601$:$/#,080+.+#%0").
Definition KCa3b_7 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$'-%08201$:0$/#'001$:$'-$080@,&$601$:$'-#080.#'%801$:$/#+080$#%$,.401$:$/#'080+.+#%001$:$',@08201$:0$/#%001$:$',/080$$$&%<01$:$',.080@,%@201$:$/#&080$#%$,.201$:$/#%080+.+#%001$:$',-08201$:0$/##001$:$',,080,,$.601$:$',+080$#-.#:01$:$/#$080$#%$,.001$:$/##080+.+#%001$:$','08201$:0$.@/0").
Definition KCa3b_8 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$',&080$$&+%201$:$',%080.@&'201$:$.@@080$#%$,->01$:$.@/080+.+#%001$:$',$08201$:0$.@-001$:$',#080$#--#>01$:$'+@080/.&&>01$:$.@.080$#%$,-<01$:$.@-080+.+#%001$:$'+/08201$:0$.@+001$:$'+.080/,#-001$:$'+-080@.&#>01$:$.@,080$#%$,-:01$:$.@+080+.+#%001$:$'+,08201$:0$.@&001$:$'++080/&@+>").
Definition KCa3b_9 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$'+'080/@#-201$:$.@'080$#%$,-801$:$.@&080+.+#%001$:$'+&08201$:0$.@$001$:$'+%080$$&'.801$:$'+$080@@,$201$:$.@%080$#%$,-001$:$.@$080+.'@/001$:$'+#08201$:0$./@001$:$''@080-',@801$:$''/080,.'$001$:$.@#080$#%$,,001$:$./@080+.+#,001$:$''.08201$:0$./.001$:$''-080-.-/>01$:$'',080,,$,0").
Definition KCa3b_10 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$.//080$#%$,+001$:$./.080+.'@/001$:$''+08201$:0$./,001$:$'''080$#-,&601$:$''&080$#+$&601$:$./-080$#%$,'<01$:$./,080+.+#%001$:$''%08201$:0$./'001$:$''$080-,'@001$:$''#080-',/601$:$./+080$#%$,':01$:$./'080+.+#%001$:$'&@08201$:0$./%001$:$'&/080-',%801$:$'&.080.@&$201$:$./&080$#%$,'8").
Definition KCa3b_11 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$./%080+.+#%001$:$'&-08201$:0$./#001$:$'&,080$$&&@<01$:$'&+080.%',201$:$./$080$#%$,'601$:$./#080+.+#%001$:$'&'08201$:0$../001$:$'&&080$$$#/<01$:$'&%080.#'#601$:$..@080$#%$,'401$:$../080+.+#%001$:$'&$08201$:0$..-001$:$'&#080$$'/'601$:$'%@080$$$#-601$:$...080$#%$,'201$:$..-080+.+#%0").
Definition KCa3b_12 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$'%/08201$:0$..+001$:$'%.080@&+@201$:$'%-080@#/'<01$:$..,080$#%$,'001$:$..+080+.+#%001$:$'%,08201$:0$..&001$:$'%+080.#&'401$:$'%'080,,$'801$:$..'080$#%$,&001$:$..&080+.+#,001$:$'%&08201$:0$..$001$:$'%%080/&/@<01$:$'%$080.',-801$:$..%080$#%$,%001$:$..$080+.+#,001$:$'%#08201$:0$.-@0").
Definition KCa3b_13 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$'$@080/.%+>01$:$'$/080,&%@801$:$..#080$#%$,$001$:$.-@080+.+#,001$:$'$.08201$:0$.-.001$:$'$-080@.$-001$:$'$,080/#+/<01$:$.-/080$#%$,#201$:$.-.080+.+#%001$:$'$+08201$:0$.-,001$:$'$'080-'+%601$:$'$&080-.-,>01$:$.--080$#%$,#001$:$.-,080+.+#%001$:$'$%08201$:0$.-'001$:$'$$080/.#%2").
Definition KCa3b_14 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$'$#080$#./%401$:$.-+080$#%$+@801$:$.-'080+.'@/001$:$'#@08201$:0$.-%001$:$'#/080,,#@<01$:$'#.080/&//201$:$.-&080$#%$+@001$:$.-%080+.+#%001$:$'#-08201$:0$.-#001$:$'#,080/-//401$:$'#+080$#-,#801$:$.-$080$#%$+/001$:$.-#080+.+%.001$:$'#'08201$:0$.,/001$:$'#&080@+/@201$:$'#%080$$&&.8").
Definition KCa3b_15 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$.,@080$#%$+.001$:$.,/080+.+%.001$:$'#$08201$:0$.,-001$:$'##080/-.$201$:$&@@080-'+#201$:$.,.080$#%$+-001$:$.,-080+.+%.001$:$&@/08201$:0$.,+001$:$&@.080-$@%201$:$&@-080..-$001$:$.,,080$#%$+,001$:$.,+080+.+%.001$:$&@,08201$:0$.,&001$:$&@+080$#$''<01$:$&@'080@'',401$:$.,'080$#%$++4").
Definition KCa3b_16 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$.,&080+.+#%001$:$&@&08201$:0$.,$001$:$&@%080-''->01$:$&@$080,'%/401$:$.,%080$#%$++201$:$.,$080+.+#%001$:$&@#08201$:0$.+@001$:$&/@080@#.-401$:$&//080$$&&,001$:$.,#080$#%$++001$:$.+@080+.+#%001$:$&/.08201$:0$.+.001$:$&/-080$#+#/801$:$&/,080/@#,601$:$.+/080$#%$+'001$:$.+.080+.+#,0").
Definition KCa3b_17 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$&/+08201$:0$.+,001$:$&/'080@.#&601$:$&/&080/@#%>01$:$.+-080$#%$+&001$:$.+,080+.+%.001$:$&/%08201$:0$.+'001$:$&/$080-.-%001$:$&/#080,.&/>01$:$.++080$#%$+%401$:$.+'080+.+#%001$:$&.@08201$:0$.+%001$:$&./080..,+<01$:$&..080.,+'401$:$.+&080$#%$+%201$:$.+%080+.+#%001$:$&.-08201$:0$.+#0").
Definition KCa3b_18 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$&.,080$#@$@401$:$&.+080,,#-<01$:$.+$080$#%$+%001$:$.+#080+.+#%001$:$&.'08201$:0$.'/001$:$&.&080.'',401$:$&.%080$$&&'401$:$.'@080$#%$+$801$:$.'/080+.+%'001$:$&.$08201$:0$.'-001$:$&.#080,.$.801$:$&-@080@.#$801$:$.'.080$#%$+$001$:$.'-080+.+%'001$:$&-/08201$:0$.'+001$:$&-.080@&&.>").
Definition KCa3b_19 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$&--080$$$#+:01$:$.',080$#%$+#801$:$.'+080+.+%'001$:$&-,08201$:0$.'&001$:$&-+080$$#/'401$:$&-'080.''':01$:$.''080$#%$+#001$:$.'&080+.+%'001$:$&-&08201$:0$.'$001$:$&-%080-$.#>01$:$&-$080@@+@601$:$.'%080$#%$'@801$:$.'$080+.+%'001$:$&-#08201$:0$.&@001$:$&,@080$#/@.>01$:$&,/080..,'4").
Definition KCa3b_20 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$.'#080$#%$'@001$:$.&@080+.+%'001$:$&,.08201$:0$.&.001$:$&,-080$#$'$<01$:$&,,080$#-+/>01$:$.&/080$#%$'/801$:$.&.080+.+#%001$:$&,+08201$:0$.&,001$:$&,'080@@''801$:$&,&080-,'->01$:$.&-080$#%$'/001$:$.&,080+.'@/001$:$&,%08201$:0$.&'001$:$&,$080-.,&>01$:$&,#080$#&-&601$:$.&+080$#%$'.:").
Definition KCa3b_21 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$.&'080+.+#%001$:$&+@08201$:0$.&%001$:$&+/080,@-+:01$:$&+.080./,#801$:$.&&080$#%$'.801$:$.&%080+.+#%001$:$&+-08201$:0$.&#001$:$&+,080-.',001$:$&++080.#&$>01$:$.&$080$#%$'.601$:$.&#080+.+#%001$:$&+'08201$:0$.%/001$:$&+&080/$+'201$:$&+%080/$+%801$:$.%@080$#%$'.401$:$.%/080+.+#%0").
Definition KCa3b_22 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$&+$08201$:0$.%-001$:$&+#080-$-%:01$:$&'@080-.'&801$:$.%.080$#%$'.201$:$.%-080+.+#%001$:$&'/08201$:0$.%+001$:$&'.080-$+.:01$:$&'-080/--@>01$:$.%,080$#%$'.001$:$.%+080+.+#%001$:$&',08201$:0$.%&001$:$&'+080$#-+$401$:$&''080,-&-801$:$.%'080$#%$'-801$:$.%&080+.'@/001$:$&'&08201$:0$.%$0").
Definition KCa3b_23 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$&'%080/$''001$:$&'$080,,#,001$:$.%%080$#%$'-001$:$.%$080+.+#%001$:$&'#08201$:0$.$@001$:$&&@080/&/&201$:$&&/080.%''<01$:$.%#080$#%$',001$:$.$@080+.+#,001$:$&&.08201$:0$.$.001$:$&&-080/&-@:01$:$&&,080$#$'#201$:$.$/080$#%$'+001$:$.$.080+.+#%001$:$&&+08201$:0$.$,001$:$&&'080@+.,>").
Definition KCa3b_24 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$&&&080/--/<01$:$.$-080$#%$''001$:$.$,080+.+#,001$:$&&%08201$:0$.$'001$:$&&$080@+-/:01$:$&&#080./,&<01$:$.$+080$#%$'&801$:$.$'080+.'@/001$:$&%@08201$:0$.$%001$:$&%/080$#+#'>01$:$&%.080/,#+601$:$.$&080$#%$'&601$:$.$%080+.+#%001$:$&%-08201$:0$.$#001$:$&%,080/$&,001$:$&%+080,@-%>").
Definition KCa3b_25 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$.$$080$#%$'&401$:$.$#080+.+#%001$:$&%'08201$:0$.#/001$:$&%&080@&%@<01$:$&%%080,'%,:01$:$.#@080$#%$'&201$:$.#/080+.+#%001$:$&%$08201$:0$.#-001$:$&%#080@&%#401$:$&$@080$$#/$:01$:$.#.080$#%$'&001$:$.#-080+.+#%001$:$&$/08201$:0$.#+001$:$&$.080/+@/<01$:$&$-080/---801$:$.#,080$#%$'%0").
Definition KCa3b_26 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$.#+080+.+#,001$:$&$,08201$:0$.#&001$:$&$+080$#&+,201$:$&$'080-,'+>01$:$.#'080$#%$'$001$:$.#&080+.+#%001$:$&$&08201$:0$.#$001$:$&$%080..+'801$:$&$$080@&$.201$:$.#%080$#%$'#001$:$.#$080+.+#,001$:$&$#08201$:0$-@@001$:$&#@080$#-&/001$:$&#/080,.$-401$:$.##080$#%$&@001$:$-@@080+.+#%0").
Definition KCa3b_27 : list kentry := Eval vm_compute in (NFC.d_kl "$0010$#'?80,#$%@8010$#&?80$@4010$#%?80&#+###'-@#&/@$+,-$4010$#$?80,#$%@0010$##?80'.#-,%0010@@?80',%###-#/+%$/+.'%-4010@/?80$#%$&@0010@.?80%%.$%801$:$&#.08201$:0$-@.001$:$&#-080/'.&001$:$&#,080-#$,801$:$-@/080'.#-,'201$:$-@.080+.+#%001$:$&#+08201$:0$-@,001$:$&#'080.&$@:01$:$&#&080@.@$2").
Definition KCa3b_28 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$-@-080'.#-,'001$:$-@,080+.+#%001$:$&#%08201$:0$-@'001$:$&#$080./@/801$:$&##080@-+/<01$:$-@+080'.#-,&001$:$-@'080+.+#,001$:$%@@08201$:0$-@%001$:$%@/080$#%%.:01$:$%@.080$#'#/201$:$-@&080'.#-,%201$:$-@%080+.+#%001$:$%@-08201$:0$-@#001$:$%@,080$#@-+401$:$%@+080--.#601$:$-@$080'.#-,%0").
Definition KCa3b_29 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$-@#080+.+#%0010-&?8201$:0$%@+0010-#?800010-$?800010-%110$@4010-%310$@4010-%510$@4010-%710$@4000'.#-,'0200000'.#-,&080--+%4000'.#-,%0200010,+?40$%401$://$08201$:0$%@$001$://#080$#'@/401$:/.@080.#%@:01$:$%@'080--+%4").
Definition KCa3b_30 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$%@&010201$:$%@%0820100,,?01$:$%@$080+.+%#001$:/./08201$:0$%/.001$:/..080@@&@<01$:/.-080@@&/<01$:$%@#080--+%401$:$%/@010001$:$%//0820100,,?01$:$%/.080+.+%#001$:/.,08201$:0$%/,001$:/.+080.@'-001$:/.'080$#-/@:01$:$%/-080$#%$-$<01$:$%/,080+.+#%001$:/.&08201$:0$%/'0").
Definition KCa3b_31 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:/.%080-.@+601$:/.$080$$$'+<01$:$%/+080$#%$-$:01$:$%/'080+.+#%001$:/.#08201$:0$%/%001$:/-@080.@&@201$:/-/080,@.-<01$:$%/&080$#%$-$801$:$%/%080+.+#%001$:/-.08201$:0$%/#001$:/--080@@-&<01$:/-,080.@&,401$:$%/$080$#%$-$601$:$%/#080+.+#%001$:/-+08201$:0$%./001$:/-'080@#//6").
Definition KCa3b_32 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:/-&080@#/-201$:$%.@080$#%$-$401$:$%./080+.+#%001$:/-%08201$:0$%.-001$:/-$080/.+&201$:/-#080.#+':01$:$%..080$#%$-$201$:$%.-080+.+#%001$:/,@08201$:0$%.+001$:/,/080-%%.<01$:/,.080-,+%201$:$%.,080$#%$-$001$:$%.+080+.+#%001$:/,-08201$:0$%.&001$:/,,080-.@%:01$:/,+080,@.,4").
Definition KCa3b_33 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$%.'080$#%$-#001$:$%.&080+.+#,001$:/,'08201$:0$%.$001$:/,&080/$+->01$:/,%080.%,#201$:$%.%080$#%$,@>01$:$%.$080+.+#%001$:/,$08201$:0$%-@001$:/,#080$$$'#:01$:/+@080$#+%&801$:$%.#080$#%$,@<01$:$%-@080+.+#%001$:/+/08201$:0$%-.001$:/+.080-%$-:01$:/+-080-%$+401$:$%-/080$#%$,@:").
Definition KCa3b_34 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$%-.080+.+#%001$:/+,08201$:0$%-,001$:/++080/.'&<01$:/+'080@.&':01$:$%--080$#%$,@801$:$%-,080+.+#%001$:/+&08201$:0$%-'001$:/+%080$#-/&201$:/+$080@.&&801$:$%-+080$#%$,@001$:$%-'080+.'@/001$:/+#08201$:0$%-%001$:/'@080..-%<01$:/'/080$#-/#<01$:$%-&080$#%$,/801$:$%-%080+.+#%0").
Definition KCa3b_35 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:/'.08201$:0$%-#001$:/'-080@@,,001$:/',080.%+/401$:$%-$080$#%$,/601$:$%-#080+.+#%001$:/'+08201$:0$%,/001$:/''080$#+$+<01$:/'&080.',@401$:$%,@080$#%$,/401$:$%,/080+.+#%001$:/'%08201$:0$%,-001$:/'$080-'.,201$:/'#080$$&,$601$:$%,.080$#%$,/201$:$%,-080+.+#%001$:/&@08201$:0$%,+0").
Definition KCa3b_36 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:/&/080/@#@401$:/&.080,@.'201$:$%,,080$#%$,/001$:$%,+080+.+#%001$:/&-08201$:0$%,&001$:/&,080.#'':01$:/&+080/'#$<01$:$%,'080$#%$,.>01$:$%,&080+.+#%001$:/&'08201$:0$%,$001$:/&&080/.&,001$:/&%080$#$'.601$:$%,%080$#%$,.<01$:$%,$080+.+#%001$:/&$08201$:0$%+@001$:/&#080.%'.6").
Definition KCa3b_37 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:/%@080,,%,<01$:$%,#080$#%$,.:01$:$%+@080+.+#%001$:/%/08201$:0$%+.001$:/%.080$#-.%<01$:/%-080@@,&<01$:$%+/080$#%$,.801$:$%+.080+.+#%001$:/%,08201$:0$%+,001$:/%+080-%#+>01$:/%'080$#&-+201$:$%+-080$#%$,.601$:$%+,080+.+#%001$:/%&08201$:0$%+'001$:/%%080@,&$601$:/%$080.#'%8").
Definition KCa3b_38 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$%++080$#%$,.401$:$%+'080+.+#%001$:/%#08201$:0$%+%001$:/$@080$$$&%<01$:/$/080@,%@201$:$%+&080$#%$,.201$:$%+%080+.+#%001$:/$.08201$:0$%+#001$:/$-080,,$.601$:/$,080$#-.#:01$:$%+$080$#%$,.001$:$%+#080+.+#%001$:/$+08201$:0$%'/001$:/$'080$$&+%201$:/$&080.@&'201$:$%'@080$#%$,->").
Definition KCa3b_39 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$%'/080+.+#%001$:/$%08201$:0$%'-001$:/$$080$#--#>01$:/$#080/.&&>01$:$%'.080$#%$,-<01$:$%'-080+.+#%001$:/#@08201$:0$%'+001$:/#/080/,#-001$:/#.080@.&#>01$:$%',080$#%$,-:01$:$%'+080+.+#%001$:/#-08201$:0$%'&001$:/#,080/&@+>01$:/#+080/@#-201$:$%''080$#%$,-801$:$%'&080+.+#%0").
Definition KCa3b_40 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:/#'08201$:0$%'$001$:/#&080$$&'.801$:/#%080@@,$201$:$%'%080$#%$,-001$:$%'$080+.'@/001$:/#$08201$:0$%&@001$:/##080-',@801$:.@@080,.'$001$:$%'#080$#%$,,001$:$%&@080+.+#,001$:.@/08201$:0$%&.001$:.@.080-.-/>01$:.@-080,,$,001$:$%&/080$#%$,+001$:$%&.080+.'@/001$:.@,08201$:0$%&,0").
Definition KCa3b_41 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:.@+080$#-,&601$:.@'080$#+$&601$:$%&-080$#%$,'<01$:$%&,080+.+#%001$:.@&08201$:0$%&'001$:.@%080-,'@001$:.@$080-',/601$:$%&+080$#%$,':01$:$%&'080+.+#%001$:.@#08201$:0$%&%001$:./@080-',%801$:.//080.@&$201$:$%&&080$#%$,'801$:$%&%080+.+#%001$:./.08201$:0$%&#001$:./-080$$&&@<").
Definition KCa3b_42 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:./,080.%',201$:$%&$080$#%$,'601$:$%&#080+.+#%001$:./+08201$:0$%%/001$:./'080$$$#/<01$:./&080.#'#601$:$%%@080$#%$,'401$:$%%/080+.+#%001$:./%08201$:0$%%-001$:./$080$$'/'601$:./#080$$$#-601$:$%%.080$#%$,'201$:$%%-080+.+#%001$:..@08201$:0$%%+001$:../080@&+@201$:...080@#/'<").
Definition KCa3b_43 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$%%,080$#%$,'001$:$%%+080+.+#%001$:..-08201$:0$%%&001$:..,080.#&'401$:..+080,,$'801$:$%%'080$#%$,&001$:$%%&080+.+#,001$:..'08201$:0$%%$001$:..&080/&/@<01$:..%080.',-801$:$%%%080$#%$,%001$:$%%$080+.+#,001$:..$08201$:0$%$@001$:..#080/.%+>01$:.-@080,&%@801$:$%%#080$#%$,$0").
Definition KCa3b_44 : list kentry := Eval vm_compute in (NFC.d_kl "801$:$%$@080+.+#,001$:.-/08201$:0$%$.001$:.-.080@.$-001$:.--080/#+/<01$:$%$/080$#%$,#201$:$%$.080+.+#%001$:.-,08201$:0$%$,001$:.-+080-'+%6").
Definition KCa3b_45 : list kentry := Eval vm_compute in (NFC.d_kl "801$:--$08201$:0$$'@001$:--#080$#-&/001$:-,@080,.$-401$:$$+#080$#%$&@001$:$$'@080+.+#%001$:-,/08201$:0$$'.001$:-,.080-/-$>01$:-,-080$$$/':").
Definition KCa3b_46 : list kentry := Eval vm_compute in (NFC.d_kl "$0010,$9100010,$;100010,$=100010,$?100010,%9100010,%;102010,%=100010,%?100010,@?81$:000@-$+@08201$:0,$-.011$:&&,00$-#011$:-$.20>11$:-%$20>11$://%00%&-011$:$%/@20>11$:$%@&20>").
Definition KCa3b_47 : list kentry := Eval vm_compute in (NFC.d_kl "311$:$+$%00%./011$:$/&/00'&&@061$:00,$-.0").
Definition KCa3b_48 : list kentry := Eval vm_compute in (NFC.d_kl "?510+,-%-,+/,%/'%0+,-%./&'&.'#&0410%0520201020400$01120400$012400$0140%&0+,-%-,+/,%/,'0+,-%./&'&.'%+05112$#-05120%@05130$$&''>5140%'&%/05150%+,#,##-+<610,+,.@#?0,+,.@$0110,+,.@#?0,+,-.-00100811010$0820201020400$011400$0120%$0010%084024021120201020400$01120400$012130%$20201020400$011400$012&08060201020400$011400$012'080,$.+0").
Definition KCa3b_49 : list kentry := Eval vm_compute in (NFC.d_kl ">3$#$&.'0$#$&.-03$#$.#$>$#$.#%03$#%$%->$#%$&@03$#%$-%0'.#,@#03'.#,@#2'.#,@#83'.#,@%>'.#,@&03'.#,@&8'.#,@'03'.#,@+8'.#-,%03'.#-,%4'.#-,&03'.#-,'4'.-#,%03'.-#,&0'.-#,+03'.-#,@0'.-#@.03'.-#@/0'.-$,&03'.-$,+2'.-$,,0").
Definition car13c := ltac:(nf_car (KCa3b_1 ++ KCa3b_2 ++ KCa3b_3 ++ KCa3b_4 ++ KCa3b_5 ++ KCa3b_6 ++ KCa3b_7 ++ KCa3b_8 ++ KCa3b_9 ++ KCa3b_10 ++ KCa3b_11 ++ KCa3b_12 ++ KCa3b_13 ++ KCa3b_14 ++ KCa3b_15 ++ KCa3b_16 ++ KCa3b_17 ++ KCa3b_18 ++ KCa3b_19 ++ KCa3b_20 ++ KCa3b_21 ++ KCa3b_22 ++ KCa3b_23 ++ KCa3b_24 ++ KCa3b_25 ++ KCa3b_26 ++ KCa3b_27 ++ KCa3b_28 ++ KCa3b_29 ++ KCa3b_30 ++ KCa3b_31 ++ KCa3b_32 ++ KCa3b_33 ++ KCa3b_34 ++ KCa3b_35 ++ KCa3b_36 ++ KCa3b_37 ++ KCa3b_38 ++ KCa3b_39 ++ KCa3b_40 ++ KCa3b_41 ++ KCa3b_42 ++ KCa3b_43 ++ KCa3b_44 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_85 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_86 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_87 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_88 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_89 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_90 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_91 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_92 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_93 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_94 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_95 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_96 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_97 ++ KCa3b_45 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_99 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_100 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_101 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_102 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_103 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_104 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_105 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_106 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_107 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_108 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_109 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_110 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_111 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_112 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_113 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_114 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_115 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_116 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_117 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_118 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_119 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_120 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_121 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_122 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_123 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_124 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_125 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_126 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_127 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_15 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_16 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_17 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_18 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_19 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_128 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_129 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_22 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_23 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_24 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_25 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_26 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_27 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_28 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_29 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_30 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_31 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_32 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_33 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_34 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_35 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_36 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_37 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_38 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_39 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_40 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_41 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_42 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_43 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_44 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_45 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_46 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_47 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_48 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_49 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_50 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_51 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_52 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_53 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_54 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_55 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_56 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_130 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_58 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_59 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_60 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_61 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_62 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_63 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_64 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_65 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_66 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_67 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_68 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_69 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_70 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_71 ++ KCa3b_46 ++ KCa3b_47 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_132 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_75 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_76 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_4 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_77 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_78 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_79 ++ KCa3b_48 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_81 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_11 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_82 ++ KCa3b_49 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_13) ((AX2L.carryF3 LG13c KN13b []))).
Definition KN13c : list kentry := fst (fst car13c).
Definition CS13c : list sidecond := Eval lazy in (snd (fst car13c)).
Definition HS13c : list bool := Eval lazy in (snd car13c).
Lemma car13c_eq : carry LG13c KN13b [] = (KN13c, CS13c, HS13c).
Proof. apply AX2L.carry_viaF3. vm_cast_no_check (eq_refl car13c). Qed.


Lemma itinerary3b_ok : (PC13c =? A_internal_mmap_ecall, SC13c, CS13c) = (false, [], []).
Proof. vmeq_cast. Qed.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.NodesMmDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.MallocSymAux.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Definition IT_Kn3b : itab := AX2F.mk_itab_rs SEGS [
  (263468, 20%nat); (402244, 22%nat); (402448, 10%nat); (415980, 1193%nat); (423748, 15%nat); (423844, 16%nat); (540688, 88%nat)] PTLeaf.
Lemma IT_Kn3b_ok : itab_sound SEGS IT_Kn3b.
Proof. apply AX2F.mk_itab_rs_sound. apply AX2F.itab_leaf_sound. Qed.


(* [comment removed for export] *)
Definition run13c := ltac:(nf_run KN13b ((AX2L.sym_execFS6 SEGS IT_Kn3b KN13b F8 true STOPS3 noscr (SS PC13b SR13b [] KN13b 27) []))).
Definition PC13c : Z := Eval lazy in (s_pc (fst (fst run13c))).
Definition SR13c : list expr := Eval lazy in (s_regs (fst (fst run13c))).
Definition LG13c : list sentry := s_log (fst (fst run13c)).
Definition SK13c : list kentry := s_know (fst (fst run13c)).
Definition NX13c : nat := Eval lazy in (s_next (fst (fst run13c))).
Definition SC13c : list sidecond := Eval lazy in (snd (fst run13c)).
Definition SP13c : scripts := Eval lazy in (snd run13c).
Lemma run13c_eq : sym_exec SEGS F8 true STOPS3 noscr (SS PC13b SR13b [] KN13b 27) [] = (SSR PC13c SR13c LG13c SK13c NX13c None, SC13c, SP13c).
Proof. apply (AX2L.sym_exec_viaFS6 SEGS IT_Kn3b KN13b); [exact IT_Kn3b_ok | reflexivity | vm_cast_no_check (eq_refl run13c)]. Qed.
Definition KCb3b_50 : list kentry := Eval vm_compute in (NFC.d_kl "$0010$#+?80&,+%,8010-%?40@>01$:$+$$08201$:0$/&-001$:$+$#080/.+&201$:$+#@080.#+':01$:$/&.080$#%%-.201$:$/&-080+.,#@0000@-%,-08201$:0$/&/0010$#.?80+.,#@0010$#-?80$#%%',0010$#,?820100-&?01$:$+#/08201$:0$/&+001$:$+#.080-%%.<01$:$+#-080-,+%201$:$/&,080$#%%-.001$:$/&+080+.,#@0").
Definition KCb3b_51 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$+#,08201$:0$/&&001$:$+#+080-.@%:01$:$+#'080,@.,401$:$/&'080$#%%--001$:$/&&080+.,$&001$:$+#&08201$:0$/&$001$:$+#%080/$+->01$:$+#$080.%,#201$:$/&%080$#%%-,>01$:$/&$080+.,#@001$:$+##08201$:0$/%@001$:$'@@080$$$'#:01$:$'@/080$#+%&801$:$/&#080$#%%-,<01$:$/%@080+.,#@001$:$'@.08201$:0$/%.0").
Definition KCb3b_52 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$'@-080-%$-:01$:$'@,080-%$+401$:$/%/080$#%%-,:01$:$/%.080+.,#@001$:$'@+08201$:0$/%,001$:$'@'080/.'&<01$:$'@&080@.&&:01$:$/%-080$#%%-,801$:$/%,080+.,#@001$:$'@%08201$:0$/%'001$:$'@$080$#-/&201$:$'@#080@.&%801$:$/%+080$#%%-,001$:$/%'080+.,#,001$:$'/@08201$:0$/%%001$:$'//080..-%<").
Definition KCb3b_53 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$'/.080$#-/#<01$:$/%&080$#%%-+801$:$/%%080+.,#@001$:$'/-08201$:0$/%#001$:$'/,080@@,+001$:$'/+080.%+/401$:$/%$080$#%%-+601$:$/%#080+.,#@001$:$'/'08201$:0$/$/001$:$'/&080$#+$+<01$:$'/%080.',@401$:$/$@080$#%%-+401$:$/$/080+.,#@001$:$'/$08201$:0$/$-001$:$'/#080-'.,201$:$'.@080$$&,$6").
Definition KCb3b_54 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$/$.080$#%%-+201$:$/$-080+.,#@001$:$'./08201$:0$/$+001$:$'..080/@#/401$:$'.-080,@.'201$:$/$,080$#%%-+001$:$/$+080+.,#@001$:$'.,08201$:0$/$&001$:$'.+080.#'':01$:$'.'080/'#$<01$:$/$'080$#%%-'>01$:$/$&080+.,#@001$:$'.&08201$:0$/$$001$:$'.%080/.&,001$:$'.$080$#$'.601$:$/$%080$#%%-'<").
Definition KCb3b_55 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$/$$080+.,#@001$:$'.#08201$:0$/#@001$:$'-@080.%'.601$:$'-/080,,%,<01$:$/$#080$#%%-':01$:$/#@080+.,#@001$:$'-.08201$:0$/#.001$:$'--080$#-.%<01$:$'-,080@@,%<01$:$/#/080$#%%-'801$:$/#.080+.,#@001$:$'-+08201$:0$/#,001$:$'-'080-%#+>01$:$'-&080$#&-+201$:$/#-080$#%%-'601$:$/#,080+.,#@0").
Definition KCb3b_56 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$'-%08201$:0$/#'001$:$'-$080@,&#601$:$'-#080.#'%801$:$/#+080$#%%-'401$:$/#'080+.,#@001$:$',@08201$:0$/#%001$:$',/080$$$&%<01$:$',.080@,%/201$:$/#&080$#%%-'201$:$/#%080+.,#@001$:$',-08201$:0$/##001$:$',,080,,$.601$:$',+080$#-.#:01$:$/#$080$#%%-'001$:$/##080+.,#@001$:$','08201$:0$.@/0").
Definition KCb3b_57 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$',&080$$&+%201$:$',%080.@&'201$:$.@@080$#%%-&>01$:$.@/080+.,#@001$:$',$08201$:0$.@-001$:$',#080$#--#>01$:$'+@080/.&&>01$:$.@.080$#%%-&<01$:$.@-080+.,#@001$:$'+/08201$:0$.@+001$:$'+.080/,#-001$:$'+-080@.%@>01$:$.@,080$#%%-&:01$:$.@+080+.,#@001$:$'+,08201$:0$.@&001$:$'++080/&@+>").
Definition KCb3b_58 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$'+'080/@#,201$:$.@'080$#%%-&801$:$.@&080+.,#@001$:$'+&08201$:0$.@$001$:$'+%080$$&'.801$:$'+$080@@,#201$:$.@%080$#%%-&001$:$.@$080+.,#,001$:$'+#08201$:0$./@001$:$''@080-',@801$:$''/080,.'$001$:$.@#080$#%%-%001$:$./@080+.,$&001$:$''.08201$:0$./.001$:$''-080-.-/>01$:$'',080,,$,0").
Definition KCb3b_59 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$.//080$#%%-$001$:$./.080+.,#,001$:$''+08201$:0$./,001$:$'''080$#-,&601$:$''&080$#+$&601$:$./-080$#%%-#<01$:$./,080+.,#@001$:$''%08201$:0$./'001$:$''$080-,'@001$:$''#080-',/601$:$./+080$#%%-#:01$:$./'080+.,#@001$:$'&@08201$:0$./%001$:$'&/080-',%801$:$'&.080.@&$201$:$./&080$#%%-#8").
Definition KCb3b_60 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$./%080+.,#@001$:$'&-08201$:0$./#001$:$'&,080$$&&@<01$:$'&+080.%',201$:$./$080$#%%-#601$:$./#080+.,#@001$:$'&'08201$:0$../001$:$'&&080$$$#/<01$:$'&%080.#'#601$:$..@080$#%%-#401$:$../080+.,#@001$:$'&$08201$:0$..-001$:$'&#080$$'/'601$:$'%@080$$$#-601$:$...080$#%%-#201$:$..-080+.,#@0").
Definition KCb3b_61 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$'%/08201$:0$..+001$:$'%.080@&+/201$:$'%-080@#/&<01$:$..,080$#%%-#001$:$..+080+.,#@001$:$'%,08201$:0$..&001$:$'%+080.#&'401$:$'%'080,,$'801$:$..'080$#%%,@001$:$..&080+.,$&001$:$'%&08201$:0$..$001$:$'%%080/&/@<01$:$'%$080.',-801$:$..%080$#%%,/001$:$..$080+.,$&001$:$'%#08201$:0$.-@0").
Definition KCb3b_62 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$'$@080/.%+>01$:$'$/080,&%@801$:$..#080$#%%,.001$:$.-@080+.,$&001$:$'$.08201$:0$.-.001$:$'$-080@.$,001$:$'$,080/#+/<01$:$.-/080$#%%,-201$:$.-.080+.,#@001$:$'$+08201$:0$.-,001$:$'$'080-'+%601$:$'$&080-.-,>01$:$.--080$#%%,-001$:$.-,080+.,#@001$:$'$%08201$:0$.-'001$:$'$$080/.#%2").
Definition KCb3b_63 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$'$#080$#./%401$:$.-+080$#%%,,801$:$.-'080+.,#,001$:$'#@08201$:0$.-%001$:$'#/080,,#@<01$:$'#.080/&//201$:$.-&080$#%%,,001$:$.-%080+.,#@001$:$'#-08201$:0$.-#001$:$'#,080/-//401$:$'#+080$#-,#801$:$.-$080$#%%,+001$:$.-#080+.,&+001$:$'#'08201$:0$.,/001$:$'#&080@+//201$:$'#%080$$&&.8").
Definition KCb3b_64 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$.,@080$#%%,'001$:$.,/080+.,&+001$:$'#$08201$:0$.,-001$:$'##080/-.$201$:$&@@080-'+#201$:$.,.080$#%%,&001$:$.,-080+.,&+001$:$&@/08201$:0$.,+001$:$&@.080-$@%201$:$&@-080..-$001$:$.,,080$#%%,%001$:$.,+080+.,&+001$:$&@,08201$:0$.,&001$:$&@+080$#$''<01$:$&@'080@''+401$:$.,'080$#%%,$4").
Definition KCb3b_65 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$.,&080+.,#@001$:$&@&08201$:0$.,$001$:$&@%080-''->01$:$&@$080,'%/401$:$.,%080$#%%,$201$:$.,$080+.,#@001$:$&@#08201$:0$.+@001$:$&/@080@#.,401$:$&//080$$&&,001$:$.,#080$#%%,$001$:$.+@080+.,#@001$:$&/.08201$:0$.+.001$:$&/-080$#+#/801$:$&/,080/@#+601$:$.+/080$#%%,#001$:$.+.080+.,$&0").
Definition KCb3b_66 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$&/+08201$:0$.+,001$:$&/'080@.#%601$:$&/&080/@#$>01$:$.+-080$#%%+@001$:$.+,080+.,&+001$:$&/%08201$:0$.+'001$:$&/$080-.-%001$:$&/#080,.&/>01$:$.++080$#%%+/401$:$.+'080+.,#@001$:$&.@08201$:0$.+%001$:$&./080..,+<01$:$&..080.,+'401$:$.+&080$#%%+/201$:$.+%080+.,#@001$:$&.-08201$:0$.+#0").
Definition KCb3b_67 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$&.,080$#@$@401$:$&.+080,,#-<01$:$.+$080$#%%+/001$:$.+#080+.,#@001$:$&.'08201$:0$.'/001$:$&.&080.'',401$:$&.%080$$&&'401$:$.'@080$#%%+.801$:$.'/080+.,&$001$:$&.$08201$:0$.'-001$:$&.#080,.$.801$:$&-@080@.##801$:$.'.080$#%%+.001$:$.'-080+.,&$001$:$&-/08201$:0$.'+001$:$&-.080@&&->").
Definition KCb3b_68 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$&--080$$$#+:01$:$.',080$#%%+-801$:$.'+080+.,&$001$:$&-,08201$:0$.'&001$:$&-+080$$#/'401$:$&-'080.''':01$:$.''080$#%%+-001$:$.'&080+.,&$001$:$&-&08201$:0$.'$001$:$&-%080-$.#>01$:$&-$080@@+/601$:$.'%080$#%%+,801$:$.'$080+.,&$001$:$&-#08201$:0$.&@001$:$&,@080$#/@.>01$:$&,/080..,'4").
Definition KCb3b_69 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$.'#080$#%%+,001$:$.&@080+.,&$001$:$&,.08201$:0$.&.001$:$&,-080$#$'$<01$:$&,,080$#-+/>01$:$.&/080$#%%++801$:$.&.080+.,#@001$:$&,+08201$:0$.&,001$:$&,'080@@'&801$:$&,&080-,'->01$:$.&-080$#%%++001$:$.&,080+.,#,001$:$&,%08201$:0$.&'001$:$&,$080-.,&>01$:$&,#080$#&-&601$:$.&+080$#%%+':").
Definition KCb3b_70 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$.&'080+.,#@001$:$&+@08201$:0$.&%001$:$&+/080,@-+:01$:$&+.080./,#801$:$.&&080$#%%+'801$:$.&%080+.,#@001$:$&+-08201$:0$.&#001$:$&+,080-.',001$:$&++080.#&$>01$:$.&$080$#%%+'601$:$.&#080+.,#@001$:$&+'08201$:0$.%/001$:$&+&080/$+'201$:$&+%080/$+%801$:$.%@080$#%%+'401$:$.%/080+.,#@0").
Definition KCb3b_71 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$&+$08201$:0$.%-001$:$&+#080-$-%:01$:$&'@080-.'&801$:$.%.080$#%%+'201$:$.%-080+.,#@001$:$&'/08201$:0$.%+001$:$&'.080-$+.:01$:$&'-080/--@>01$:$.%,080$#%%+'001$:$.%+080+.,#@001$:$&',08201$:0$.%&001$:$&'+080$#-+$401$:$&''080,-&-801$:$.%'080$#%%+&801$:$.%&080+.,#,001$:$&'&08201$:0$.%$0").
Definition KCb3b_72 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$&'%080/$''001$:$&'$080,,#,001$:$.%%080$#%%+&001$:$.%$080+.,#@001$:$&'#08201$:0$.$@001$:$&&@080/&/&201$:$&&/080.%''<01$:$.%#080$#%%+%001$:$.$@080+.,$&001$:$&&.08201$:0$.$.001$:$&&-080/&-@:01$:$&&,080$#$'#201$:$.$/080$#%%+$001$:$.$.080+.,#@001$:$&&+08201$:0$.$,001$:$&&'080@+.+>").
Definition KCb3b_73 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$&&&080/--/<01$:$.$-080$#%%+#001$:$.$,080+.,$&001$:$&&%08201$:0$.$'001$:$&&$080@+-.:01$:$&&#080./,&<01$:$.$+080$#%%'@801$:$.$'080+.,#,001$:$&%@08201$:0$.$%001$:$&%/080$#+#'>01$:$&%.080/,#+601$:$.$&080$#%%'@601$:$.$%080+.,#@001$:$&%-08201$:0$.$#001$:$&%,080/$&,001$:$&%+080,@-%>").
Definition KCb3b_74 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$.$$080$#%%'@401$:$.$#080+.,#@001$:$&%'08201$:0$.#/001$:$&%&080@&%/<01$:$&%%080,'%,:01$:$.#@080$#%%'@201$:$.#/080+.,#@001$:$&%$08201$:0$.#-001$:$&%#080@&$@401$:$&$@080$$#/$:01$:$.#.080$#%%'@001$:$.#-080+.,#@001$:$&$/08201$:0$.#+001$:$&$.080/+@/<01$:$&$-080/---801$:$.#,080$#%%'/0").
Definition KCb3b_75 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$.#+080+.,$&001$:$&$,08201$:0$.#&001$:$&$+080$#&+,201$:$&$'080-,'+>01$:$.#'080$#%%'.001$:$.#&080+.,#@001$:$&$&08201$:0$.#$001$:$&$%080..+'801$:$&$$080@&$-201$:$.#%080$#%%'-001$:$.#$080+.,$&001$:$&$#08201$:0$-@@001$:$&#@080$#-&/001$:$&#/080,.$-401$:$.##080$#%%',001$:$-@@080+.,#@0").
Definition KCb3b_76 : list kentry := Eval vm_compute in (NFC.d_kl "$0010$#'?80,#%&,8010$#&?80$@4010$#%?80&#+###'-@#&/@$+,-$4010$#$?80,#%&,0010$##?80'.#.,/0010@@?80',%###-#/+%$/+.'%-4010@/?80$#%%',0010@.?80%%.%/801$:$&#.08201$:0$-@.001$:$&#-080/'.&001$:$&#,080-#$,801$:$-@/080'.#.-#201$:$-@.080+.,#@001$:$&#+08201$:0$-@,001$:$&#'080.&$@:01$:$&#&080@.@#2").
Definition KCb3b_77 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$-@-080'.#.-#001$:$-@,080+.,#@001$:$&#%08201$:0$-@'001$:$&#$080./@/801$:$&##080@-+.<01$:$-@+080'.#.,@001$:$-@'080+.,$&001$:$%@@08201$:0$-@%001$:$%@/080$#%%.:01$:$%@.080$#'#/201$:$-@&080'.#.,/201$:$-@%080+.,#@001$:$%@-08201$:0$-@#001$:$%@,080$#@-+401$:$%@+080--.#601$:$-@$080'.#.,/0").
Definition KCb3b_78 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$-@#080+.,#@0010-&?8201$:0$%@+0010-#?800010-$?800010-%110$@4010-%310$@4010-%510$@4010-%710$@4000'.#.-#0200000'.#.,@080--+%4000'.#.,/0200010,+?40$%401$://$08201$:0$%@$001$://#080$#'@/401$:/.@080.#%@:01$:$%@'080--+%4").
Definition KCb3b_79 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$%@&010201$:$%@%0820100,,?01$:$%@$080+.,%.001$:/./08201$:0$%/.001$:/..080@@&/<01$:/.-080@@&.<01$:$%@#080--+%401$:$%/@010001$:$%//0820100,,?01$:$%/.080+.,%.001$:/.,08201$:0$%/,001$:/.+080.@'-001$:/.'080$#-/@:01$:$%/-080$#%%-.<01$:$%/,080+.,#@001$:/.&08201$:0$%/'0").
Definition KCb3b_80 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:/.%080-.@+601$:/.$080$$$'+<01$:$%/+080$#%%-.:01$:$%/'080+.,#@001$:/.#08201$:0$%/%001$:/-@080.@&@201$:/-/080,@.-<01$:$%/&080$#%%-.801$:$%/%080+.,#@001$:/-.08201$:0$%/#001$:/--080@@-%<01$:/-,080.@&,401$:$%/$080$#%%-.601$:$%/#080+.,#@001$:/-+08201$:0$%./001$:/-'080@#/.6").
Definition KCb3b_81 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:/-&080@#/,201$:$%.@080$#%%-.401$:$%./080+.,#@001$:/-%08201$:0$%.-001$:/-$080/.+&201$:/-#080.#+':01$:$%..080$#%%-.201$:$%.-080+.,#@001$:/,@08201$:0$%.+001$:/,/080-%%.<01$:/,.080-,+%201$:$%.,080$#%%-.001$:$%.+080+.,#@001$:/,-08201$:0$%.&001$:/,,080-.@%:01$:/,+080,@.,4").
Definition KCb3b_82 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$%.'080$#%%--001$:$%.&080+.,$&001$:/,'08201$:0$%.$001$:/,&080/$+->01$:/,%080.%,#201$:$%.%080$#%%-,>01$:$%.$080+.,#@001$:/,$08201$:0$%-@001$:/,#080$$$'#:01$:/+@080$#+%&801$:$%.#080$#%%-,<01$:$%-@080+.,#@001$:/+/08201$:0$%-.001$:/+.080-%$-:01$:/+-080-%$+401$:$%-/080$#%%-,:").
Definition KCb3b_83 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$%-.080+.,#@001$:/+,08201$:0$%-,001$:/++080/.'&<01$:/+'080@.&&:01$:$%--080$#%%-,801$:$%-,080+.,#@001$:/+&08201$:0$%-'001$:/+%080$#-/&201$:/+$080@.&%801$:$%-+080$#%%-,001$:$%-'080+.,#,001$:/+#08201$:0$%-%001$:/'@080..-%<01$:/'/080$#-/#<01$:$%-&080$#%%-+801$:$%-%080+.,#@0").
Definition KCb3b_84 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:/'.08201$:0$%-#001$:/'-080@@,+001$:/',080.%+/401$:$%-$080$#%%-+601$:$%-#080+.,#@001$:/'+08201$:0$%,/001$:/''080$#+$+<01$:/'&080.',@401$:$%,@080$#%%-+401$:$%,/080+.,#@001$:/'%08201$:0$%,-001$:/'$080-'.,201$:/'#080$$&,$601$:$%,.080$#%%-+201$:$%,-080+.,#@001$:/&@08201$:0$%,+0").
Definition KCb3b_85 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:/&/080/@#/401$:/&.080,@.'201$:$%,,080$#%%-+001$:$%,+080+.,#@001$:/&-08201$:0$%,&001$:/&,080.#'':01$:/&+080/'#$<01$:$%,'080$#%%-'>01$:$%,&080+.,#@001$:/&'08201$:0$%,$001$:/&&080/.&,001$:/&%080$#$'.601$:$%,%080$#%%-'<01$:$%,$080+.,#@001$:/&$08201$:0$%+@001$:/&#080.%'.6").
Definition KCb3b_86 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:/%@080,,%,<01$:$%,#080$#%%-':01$:$%+@080+.,#@001$:/%/08201$:0$%+.001$:/%.080$#-.%<01$:/%-080@@,%<01$:$%+/080$#%%-'801$:$%+.080+.,#@001$:/%,08201$:0$%+,001$:/%+080-%#+>01$:/%'080$#&-+201$:$%+-080$#%%-'601$:$%+,080+.,#@001$:/%&08201$:0$%+'001$:/%%080@,&#601$:/%$080.#'%8").
Definition KCb3b_87 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$%++080$#%%-'401$:$%+'080+.,#@001$:/%#08201$:0$%+%001$:/$@080$$$&%<01$:/$/080@,%/201$:$%+&080$#%%-'201$:$%+%080+.,#@001$:/$.08201$:0$%+#001$:/$-080,,$.601$:/$,080$#-.#:01$:$%+$080$#%%-'001$:$%+#080+.,#@001$:/$+08201$:0$%'/001$:/$'080$$&+%201$:/$&080.@&'201$:$%'@080$#%%-&>").
Definition KCb3b_88 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$%'/080+.,#@001$:/$%08201$:0$%'-001$:/$$080$#--#>01$:/$#080/.&&>01$:$%'.080$#%%-&<01$:$%'-080+.,#@001$:/#@08201$:0$%'+001$:/#/080/,#-001$:/#.080@.%@>01$:$%',080$#%%-&:01$:$%'+080+.,#@001$:/#-08201$:0$%'&001$:/#,080/&@+>01$:/#+080/@#,201$:$%''080$#%%-&801$:$%'&080+.,#@0").
Definition KCb3b_89 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:/#'08201$:0$%'$001$:/#&080$$&'.801$:/#%080@@,#201$:$%'%080$#%%-&001$:$%'$080+.,#,001$:/#$08201$:0$%&@001$:/##080-',@801$:.@@080,.'$001$:$%'#080$#%%-%001$:$%&@080+.,$&001$:.@/08201$:0$%&.001$:.@.080-.-/>01$:.@-080,,$,001$:$%&/080$#%%-$001$:$%&.080+.,#,001$:.@,08201$:0$%&,0").
Definition KCb3b_90 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:.@+080$#-,&601$:.@'080$#+$&601$:$%&-080$#%%-#<01$:$%&,080+.,#@001$:.@&08201$:0$%&'001$:.@%080-,'@001$:.@$080-',/601$:$%&+080$#%%-#:01$:$%&'080+.,#@001$:.@#08201$:0$%&%001$:./@080-',%801$:.//080.@&$201$:$%&&080$#%%-#801$:$%&%080+.,#@001$:./.08201$:0$%&#001$:./-080$$&&@<").
Definition KCb3b_91 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:./,080.%',201$:$%&$080$#%%-#601$:$%&#080+.,#@001$:./+08201$:0$%%/001$:./'080$$$#/<01$:./&080.#'#601$:$%%@080$#%%-#401$:$%%/080+.,#@001$:./%08201$:0$%%-001$:./$080$$'/'601$:./#080$$$#-601$:$%%.080$#%%-#201$:$%%-080+.,#@001$:..@08201$:0$%%+001$:../080@&+/201$:...080@#/&<").
Definition KCb3b_92 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$%%,080$#%%-#001$:$%%+080+.,#@001$:..-08201$:0$%%&001$:..,080.#&'401$:..+080,,$'801$:$%%'080$#%%,@001$:$%%&080+.,$&001$:..'08201$:0$%%$001$:..&080/&/@<01$:..%080.',-801$:$%%%080$#%%,/001$:$%%$080+.,$&001$:..$08201$:0$%$@001$:..#080/.%+>01$:.-@080,&%@801$:$%%#080$#%%,.0").
Definition KCb3b_93 : list kentry := Eval vm_compute in (NFC.d_kl "801$:$%$@080+.,$&001$:.-/08201$:0$%$.001$:.-.080@.$,001$:.--080/#+/<01$:$%$/080$#%%,-201$:$%$.080+.,#@001$:.-,08201$:0$%$,001$:.-+080-'+%6").
Definition KCb3b_94 : list kentry := Eval vm_compute in (NFC.d_kl "801$:--$08201$:0$$'@001$:--#080$#-&/001$:-,@080,.$-401$:$$+#080$#%%',001$:$$'@080+.,#@001$:-,/08201$:0$$'.001$:-,.080-/-$>01$:-,-080$$$/':").
Definition KCb3b_95 : list kentry := Eval vm_compute in (NFC.d_kl "$0010,$9100010,$;100010,$=100010,$?100010,%9100010,%;102010,%=100010,%?100010,@?81$:000@-%,,08201$:0,$-.011$:&&,00$-#011$:-$.20>11$:-%$20>11$://%00%&-011$:$%/@20>11$:$%@&20>").
Definition KCb3b_96 : list kentry := Eval vm_compute in (NFC.d_kl "311$:$+$%00%./011$:$/&/00'&&@061$:00,$-.0").
Definition KCb3b_97 : list kentry := Eval vm_compute in (NFC.d_kl "?510+,-%-,+/,%/'%0+,-%./&'&.'#&0410%0520201020400$01120400$012400$0140%&0+,-%-,+/,%/,'0+,-%./&'&.'%+05112$#-05120%@05130$$&''>5140%'&%/05150%+,#,##-+<610,+,.@#?0,+,.@$0110,+,.@#?0,+,-.-00100811010$0820201020400$011400$0120%$0010%084024021120201020400$01120400$012130%$20201020400$011400$012&08060201020400$011400$012'080,$.+0").
Definition KCb3b_98 : list kentry := Eval vm_compute in (NFC.d_kl ">3$#$'/#0$#$'/&03$#$/#.>$#$/#/03$#%%&&>$#%%',03$#%%-/0'.#-@-03'.#-@-2'.#-@-83'.#-@/>'.#-@@03'.#-@@8'.#.##03'.#.#$8'.#.,/03'.#.,/4'.#.,@03'.#.-#4'.-$,/03'.-$,@0'.-$-$03'.-$-,0'.-%#'03'.-%#+0'.-%,@03'.-%-$2'.-%-%0").
Definition car13c := ltac:(nf_car (KCb3b_50 ++ KCb3b_51 ++ KCb3b_52 ++ KCb3b_53 ++ KCb3b_54 ++ KCb3b_55 ++ KCb3b_56 ++ KCb3b_57 ++ KCb3b_58 ++ KCb3b_59 ++ KCb3b_60 ++ KCb3b_61 ++ KCb3b_62 ++ KCb3b_63 ++ KCb3b_64 ++ KCb3b_65 ++ KCb3b_66 ++ KCb3b_67 ++ KCb3b_68 ++ KCb3b_69 ++ KCb3b_70 ++ KCb3b_71 ++ KCb3b_72 ++ KCb3b_73 ++ KCb3b_74 ++ KCb3b_75 ++ KCb3b_76 ++ KCb3b_77 ++ KCb3b_78 ++ KCb3b_79 ++ KCb3b_80 ++ KCb3b_81 ++ KCb3b_82 ++ KCb3b_83 ++ KCb3b_84 ++ KCb3b_85 ++ KCb3b_86 ++ KCb3b_87 ++ KCb3b_88 ++ KCb3b_89 ++ KCb3b_90 ++ KCb3b_91 ++ KCb3b_92 ++ KCb3b_93 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_231 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_232 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_233 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_234 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_235 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_236 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_237 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_238 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_239 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_240 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_241 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_242 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_243 ++ KCb3b_94 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_245 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_246 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_247 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_248 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_249 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_250 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_251 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_252 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_253 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_254 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_255 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_256 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_257 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_258 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_259 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_260 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_261 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_262 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_263 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_264 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_265 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_266 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_267 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_268 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_269 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_270 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_271 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_272 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_273 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_161 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_162 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_163 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_164 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_165 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_274 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_275 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_168 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_169 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_170 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_171 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_172 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_173 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_174 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_175 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_176 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_177 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_178 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_179 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_180 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_181 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_182 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_183 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_184 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_185 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_186 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_187 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_188 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_189 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_190 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_191 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_192 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_193 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_194 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_195 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_196 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_197 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_198 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_199 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_200 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_201 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_202 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_276 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_204 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_205 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_206 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_207 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_208 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_209 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_210 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_211 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_212 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_213 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_214 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_215 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_216 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_217 ++ KCb3b_95 ++ KCb3b_96 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_278 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_221 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_222 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_150 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_223 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_224 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_225 ++ KCb3b_97 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_227 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_157 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_228 ++ KCb3b_98 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB.KCb3a_159) ((AX2L.carryF3 LG13c KN13b []))).
Definition KN13c : list kentry := fst (fst car13c).
Definition CS13c : list sidecond := Eval lazy in (snd (fst car13c)).
Definition HS13c : list bool := Eval lazy in (snd car13c).
Lemma car13c_eq : carry LG13c KN13b [] = (KN13c, CS13c, HS13c).
Proof. apply AX2L.carry_viaF3. vm_cast_no_check (eq_refl car13c). Qed.


Lemma itinerary3b_ok : (PC13c =? A_internal_mmap_ecall, SC13c, CS13c) = (false, [], []).
Proof. vmeq_cast. Qed.
End TwB.
End BootKn3b.

(* [comment removed for export] *)
Module BootKn3c.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AxNfCodec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanPlan AxSymExec3F. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3F.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require EntryKn EntryGlue. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBlock__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.NodesMmDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.MallocSymAux.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Img. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require Import KnKeepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require Import AxSymExec3L.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Definition IT_Kn3c : itab := AX2F.mk_itab_rs SEGS [
  (237068, 28%nat); (237268, 8%nat); (263444, 67%nat); (263720, 2%nat); (263812, 3%nat); (263844, 4%nat); (263944, 47%nat); (306224, 20%nat); (351768, 2%nat); (352264, 21%nat); (352576, 9%nat); (357752, 4%nat); (380560, 25%nat); (381932, 4%nat); (381972, 39%nat); (383244, 15%nat); (385920, 4%nat); (402140, 22%nat); (402344, 10%nat); (402484, 9%nat); (402560, 3%nat); (411788, 1%nat); (411860, 1%nat); (412572, 9%nat); (412628, 28%nat); (413056, 10%nat); (414680, 6%nat); (415028, 2%nat); (420236, 112%nat); (421888, 25%nat); (422040, 22%nat); (422284, 41%nat); (422492, 16%nat); (422672, 17%nat); (422904, 9%nat); (422996, 26%nat); (423120, 17%nat); (423196, 11%nat); (423644, 15%nat); (424476, 9%nat); (424600, 10%nat); (424692, 1%nat); (424968, 17%nat); (425552, 10%nat); (426648, 1%nat); (427360, 21%nat); (430252, 11%nat); (430304, 49%nat); (430532, 2%nat); (431876, 1%nat); (432472, 1%nat); (432488, 13%nat); (432552, 20%nat); (435780, 17%nat); (436116, 10%nat); (437768, 3%nat); (456072, 4%nat); (456128, 4%nat); (456596, 3%nat); (460436, 1%nat); (463364, 1%nat); (528156, 3%nat); (540936, 6%nat); (605052, 24%nat); (605216, 21%nat); (605572, 3%nat)] PTLeaf.
Lemma IT_Kn3c_ok : itab_sound SEGS IT_Kn3c.
Proof. apply AX2F.mk_itab_rs_sound. apply AX2F.itab_leaf_sound. Qed.


(* [comment removed for export] *)
Definition run13d := ltac:(nf_run KN13c ((AX2L.sym_execFS6 SEGS IT_Kn3c KN13c F8 true STOPS3 noscr (SS PC13c SR13c [] KN13c 27) []))).
Definition PC13d : Z := Eval lazy in (s_pc (fst (fst run13d))).
Definition SR13d : list expr := Eval lazy in (s_regs (fst (fst run13d))).
Definition LG13d : list sentry := s_log (fst (fst run13d)).
Definition SK13d : list kentry := s_know (fst (fst run13d)).
Definition NX13d : nat := Eval lazy in (s_next (fst (fst run13d))).
Definition SC13d : list sidecond := Eval lazy in (snd (fst run13d)).
Definition SP13d : scripts := Eval lazy in (snd run13d).
Lemma run13d_eq : sym_exec SEGS F8 true STOPS3 noscr (SS PC13c SR13c [] KN13c 27) [] = (SSR PC13d SR13d LG13d SK13d NX13d None, SC13d, SP13d).
Proof. apply (AX2L.sym_exec_viaFS6 SEGS IT_Kn3c KN13c); [exact IT_Kn3c_ok | reflexivity | vm_cast_no_check (eq_refl run13d)]. Qed.
Definition KCa3c_1 : list kentry := Eval vm_compute in (NFC.d_kl "$0010%+?80,#$%@0010%'?80&%.$&0010%&?80,#$%@0010%%?80&%/,/8000,$'&$840&<000,#//$8102000,#//$0404010%,?80,$'%.0000,#$&.<102000$#%$-$>100000$#%$-$<102000$#%$-$:100000$#%$-$8100000$#%$-$6100000$#%$-$4100000$#%$-$2102").
Definition KCa3c_2 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$-$0100000$#%$-#>100000$#%$-#<100000$#%$-#:100000$#%$-#8100000$#%$-#6100000$#%$-#4102000$#%$-#210$,8000$#%$-#010%+4000$#%$,@>100000$#%$,@<100000$#%$,@:102000$#%$,@8102000$#%$,@6100000$#%$,@4100000$#%$,@2100").
Definition KCa3c_3 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$,@0102000$#%$,/>100000$#%$,/<100000$#%$,/:100000$#%$,/8100000$#%$,/6102000$#%$,/4102000$#%$,/2102000$#%$,/0102000$#%$,.>102000$#%$,.<102000$#%$,.:102000$#%$,.8102000$#%$,.6102000$#%$,.4102000$#%$,.2102").
Definition KCa3c_4 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$,.0102000$#%$,->102000$#%$,-<102000$#%$,-:100000$#%$,-8102000$#%$,-6100000$#%$,-4100000$#%$,-2100000$#%$,-0100000$#%$,,>100000$#%$,,<100000$#%$,,:100000$#%$,,8100000$#%$,,6100000$#%$,,4102000$#%$,,210%+8").
Definition KCa3c_5 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$,,010$#4000$#%$,+>100000$#%$,+<100000$#%$,+:100000$#%$,+8100000$#%$,+6100000$#%$,+4100000$#%$,+2100000$#%$,+0100000$#%$,'>100000$#%$,'<100000$#%$,':102000$#%$,'8102000$#%$,'6102000$#%$,'4100000$#%$,'2102").
Definition KCa3c_6 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$,'0100000$#%$,&>100000$#%$,&<100000$#%$,&:100000$#%$,&8100000$#%$,&6100000$#%$,&4102000$#%$,&210->000$#%$,&010$%4000$#%$,%>100000$#%$,%<100000$#%$,%:100000$#%$,%8100000$#%$,%6100000$#%$,%4102000$#%$,%210->").
Definition KCa3c_7 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$,%010$%4000$#%$,$>100000$#%$,$<100000$#%$,$:100000$#%$,$8100000$#%$,$6100000$#%$,$4102000$#%$,$210.4000$#%$,$010%,4000$#%$,#>100000$#%$,#<100000$#%$,#:100000$#%$,#8100000$#%$,#6100000$#%$,#4100000$#%$,#2100").
Definition KCa3c_8 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$,#0102000$#%$+@>10%/>000$#%$+@<10%/>000$#%$+@:10%/>000$#%$+@810%/>000$#%$+@6100000$#%$+@4100000$#%$+@2100000$#%$+@0100000$#%$+/>100000$#%$+/<100000$#%$+/:100000$#%$+/8100000$#%$+/6100000$#%$+/4100000$#%$+/2100").
Definition KCa3c_9 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$+/0100000$#%$+.>100000$#%$+.<100000$#%$+.:100000$#%$+.8100000$#%$+.6100000$#%$+.4100000$#%$+.2100000$#%$+.0100000$#%$+->100000$#%$+-<100000$#%$+-:100000$#%$+-8100000$#%$+-6100000$#%$+-4100000$#%$+-2100").
Definition KCa3c_10 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$+-0100000$#%$+,>100000$#%$+,<100000$#%$+,:100000$#%$+,8100000$#%$+,6100000$#%$+,4100000$#%$+,2100000$#%$+,0100000$#%$++>100000$#%$++<100000$#%$++:100000$#%$++8100000$#%$++6100000$#%$++4100000$#%$++2102").
Definition KCa3c_11 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$++0100000$#%$+'>100000$#%$+'<100000$#%$+':100000$#%$+'8100000$#%$+'6100000$#%$+'4102000$#%$+'210&0000$#%$+'010$#:000$#%$+&>10%/>000$#%$+&<10%/>000$#%$+&:10%/>000$#%$+&810%/>000$#%$+&610%/>000$#%$+&410%/>000$#%$+&210%/>").
Definition KCa3c_12 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$+&010%/>000$#%$+%>100000$#%$+%<100000$#%$+%:100000$#%$+%8100000$#%$+%6100000$#%$+%4102000$#%$+%2100000$#%$+%0102000$#%$+$>100000$#%$+$<100000$#%$+$:100000$#%$+$8100000$#%$+$6100000$#%$+$4100000$#%$+$2100").
Definition KCa3c_13 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$+$0100000$#%$+#>100000$#%$+#<100000$#%$+#:100000$#%$+#8100000$#%$+#6100000$#%$+#4100000$#%$+#2100000$#%$+#0100000$#%$'@>100000$#%$'@<100000$#%$'@:100000$#%$'@8100000$#%$'@6100000$#%$'@4100000$#%$'@2100").
Definition KCa3c_14 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$'@0100000$#%$'/>100000$#%$'/<100000$#%$'/:100000$#%$'/8102000$#%$'/6100000$#%$'/4100000$#%$'/2100000$#%$'/0100000$#%$'.>100000$#%$'.<100000$#%$'.:102000$#%$'.8102000$#%$'.6102000$#%$'.4100000$#%$'.2102").
Definition KCa3c_15 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$'.0102000$#%$'->100000$#%$'-<100000$#%$'-:100000$#%$'-8100000$#%$'-6100000$#%$'-4100000$#%$'-2100000$#%$'-0100000$#%$',>100000$#%$',<100000$#%$',:100000$#%$',8100000$#%$',6100000$#%$',4100000$#%$',2100").
Definition KCa3c_16 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$',0100000$#%$'+>100000$#%$'+<100000$#%$'+:100000$#%$'+8100000$#%$'+6100000$#%$'+4100000$#%$'+2100000$#%$'+0100000$#%$''>100000$#%$''<100000$#%$'':100000$#%$''8100000$#%$''6100000$#%$''4100000$#%$''2100").
Definition KCa3c_17 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$''0100000$#%$'&>100000$#%$'&<100000$#%$'&:100000$#%$'&810&<000$#%$'&6100000$#%$'&4102000$#%$'&2100000$#%$'&0100000$#%$'%>100000$#%$'%<100000$#%$'%:100000$#%$'%8100000$#%$'%6100000$#%$'%4102000$#%$'%210->").
Definition KCa3c_18 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$'%010$%4000$#%$'$>100000$#%$'$<100000$#%$'$:100000$#%$'$8100000$#%$'$6100000$#%$'$4100000$#%$'$2100000$#%$'$0100000$#%$'#>100000$#%$'#<100000$#%$'#:100000$#%$'#8100000$#%$'#6100000$#%$'#4100000$#%$'#2100").
Definition KCa3c_19 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$'#0100000$#%$&@>100000$#%$&@<100000$#%$&@:100000$#%$&@8100000$#%$&@6100000$#%$&@4100000$#%$&@2100000$#%$&@0102010&,7102010'$;100010',740',%###-#/,#&/-.'+$>010',?100010'.?800010'/?800010+%?80',%###-#/,#&/-.'+$>").
Definition KCa3c_20 : list kentry := Eval vm_compute in (NFC.d_kl "$0010+&=100010+'?800010++?800010+,?800010+.;100010&'1100010&'3102010&'5100010&'7100010&'9100010&';100010&'=102010&'?100010&+1100010&+3100010&+5100").
Definition KCa3c_21 : list kentry := Eval vm_compute in (NFC.d_kl "$0010&+7100010&+9100010&+;102010&+=10$,8010&+?10%+4010&,1100010&,3100010&,5102010&,9100010&,;100010&,=100010&,?102010&-1100010&-3100010&-5100010&-7100").
Definition KCa3c_22 : list kentry := Eval vm_compute in (NFC.d_kl "$0010&-9102010&-;102010&-=102010&-?102010&.1102010&.3102010&.5102010&.7102010&.9102010&.;102010&.=102010&.?102010&/1102010&/3102010&/5100010&/7102").
Definition KCa3c_23 : list kentry := Eval vm_compute in (NFC.d_kl "$0010&/9100010&/;100010&/=100010&/?100010&@1100010&@3100010&@5100010&@7100010&@9100010&@;102010&@=10%+8010&@?10$#4010'#1100010'#3100010'#5100010'#7100").
Definition KCa3c_24 : list kentry := Eval vm_compute in (NFC.d_kl "$0010'#9100010'#;100010'#=100010'#?100010'$1100010'$3100010'$5102010'$7102010'$9102010'$=102010'$?100010'%1100010'%3100010'%5100010'%7100010'%9100").
Definition KCa3c_25 : list kentry := Eval vm_compute in (NFC.d_kl "$0010'%;102010'%=10->010'%?10$%4010'&1100010'&3100010'&5100010'&7100010'&9100010'&;102010'&=10->010'&?10$%4010''1100010''3100010''5100010''7100010''9100").
Definition KCa3c_26 : list kentry := Eval vm_compute in (NFC.d_kl "$0010'';102010''=10.4010''?10%,4010'+1100010'+3100010'+5100010'+7100010'+9100010'+;100010'+=100010'+?102010',9100010',;100010',=100010'-1100010'-3100").
Definition KCa3c_27 : list kentry := Eval vm_compute in (NFC.d_kl "$0010'-5100010'-7100010'-9100010'-;100010'-=100010'-?100010'@1100010'@3100010'@5100010'@7100010'@9100010'@;100010'@=100010'@?100010+#1100010+#3100").
Definition KCa3c_28 : list kentry := Eval vm_compute in (NFC.d_kl "$0010+#5100010+#7100010+#9100010+#;100010+#=102010+#?100010+$1100010+$3100010+$5100010+$7100010+$9100010+$;102010+$=10&0010+$?10$#:010+&1100010+&3100").
Definition KCa3c_29 : list kentry := Eval vm_compute in (NFC.d_kl "$0010+&5100010+&7100010+&9100010+&;102010+&?102010+-1100010+-3100010+-5100010+-7102010+-9100010+-;100010+-=100010+-?100010+.1100010+.3100010+.5102").
Definition KCa3c_30 : list kentry := Eval vm_compute in (NFC.d_kl "$0010+.7102010+.9102010+.=102010+.?102010+/1100010+/3100010+/5100010+/7100010+/9100010+/;100010+/=100010+/?100010+@1100010+@3100010+@5100010+@7100").
Definition KCa3c_31 : list kentry := Eval vm_compute in (NFC.d_kl "$0010+@9100010+@;100010+@=100010+@?100010,#1100010,#3100010,#5100010,#7100010,#9100010,#;100010,#=100010,#?100010,$1100010,$3100010,$5100010,$7100").
Definition KCa3c_32 : list kentry := Eval vm_compute in (NFC.d_kl "$0010,$9100010,$;100010,$=100010,$?100010,%1100010,%3100010,%5100010,%710&<010,%9100010,%;102010,%=100010,%?100010,&1100010,&3100010,&5100010,&7100").
Definition KCa3c_33 : list kentry := Eval vm_compute in (NFC.d_kl "$0010,&9100010,&;102010,&=10->010,&?10$%4010,'1100010,'3100010,'5100010,'7100010,'9100010,';100010,'=100010,'?100010,+1100010,+3100010,+5100010,+7100").
Definition KCa3c_34 : list kentry := Eval vm_compute in (NFC.d_kl "$0010,+9100010,+;100010,+=100010,+?100010,,1100010,,3100010,,5100010,,7100010,,9100010,,;100010,,=100010,,?102000,#$&#040$#-0000,#$%@840%@0000$#$&.%0400010$$#?80$@4").
Definition KCa3c_35 : list kentry := Eval vm_compute in (NFC.d_kl "$0010$#@?80&#+###'-@#&/@$+,-$4010$#/?80,#$%@0010$#.?80'.#-,%0010$#-?80/#.'4010$#,?820100-&?010$#+?80&,--%0010$#&?80$@4010$#%?80&#+###'-@#&/@$+,-$4010$#$?80,#$%@0010$##?80'.#-,%0010@@?80',%###-#/+%$/+.'%-4010@/?80$#%$&@0010@.?80%%.%-0010-#?800010-$?800010,-?800").
Definition KCa3c_36 : list kentry := Eval vm_compute in (NFC.d_kl "$0010,.?800010$$&?80$,%0010$$%?8201$:0$/++0010$$$?820100,@?01$:$/+/210001$:$/+/010,2000@-$,#08201$:0$/+@001$:$/+.210001$:$/+.010$%801$:$/+->10$%801$:$/+-<10$&:01$:$/+-:10$%<01$:$/+-810$#>01$:$/+-610$%<01$:$/+-410$&401$:$/+-210$&:").
Definition KCa3c_37 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$/+-010$&801$:$/+,>10$$:01$:$/+,<10$&401$:$/+,:10$#>01$:$/+,810$'201$:$/+,610$$201$:$/+,410$%:01$:$/+,210$#>01$:$/+,010$&401$:$/++>10$%>01$:$/++<10$&801$:$/++:10$$201$:$/++810$$601$:$/++610$%>01$:$/++410$%801$:$/++210$%8").
Definition KCa3c_38 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$/++010$$2010-%?40$#<01$:$+&#08201$:0$/+$001$:$+%@080$#'@/401$:$+%/080.#%@:01$:$/+'080--+%401$:$/+&010201$:$/+%0820100-&?01$:$/+$080+.+%#001$:$+%.08201$:0$/'.001$:$+%-080@@&@<01$:$+%,080@@&/<01$:$/+#080--+%401$:$/'@010001$:$/'/0820100-&?01$:$/'.080+.+%#0").
Definition KCa3c_39 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$+%+08201$:0$/',001$:$+%'080.@'-001$:$+%&080$#-/@:01$:$/'-080$#%$-$<01$:$/',080+.+#%001$:$+%%08201$:0$/''001$:$+%$080-.@+601$:$+%#080$$$'+<01$:$/'+080$#%$-$:01$:$/''080+.+#%001$:$+$@08201$:0$/'%001$:$+$/080.@&@201$:$+$.080,@.-<01$:$/'&080$#%$-$801$:$/'%080+.+#%001$:$+$-08201$:0$/'#0").
Definition KCa3c_40 : list kentry := Eval vm_compute in (NFC.d_kl "$001$:$+$,080@@-&<01$:$+$+080.@&,401$:$/'$080$#%$-$601$:$/'#080+.+#%001$:$+$'08201$:0$/&/001$:$+$&080@#//601$:$+$%080@#/-201$:$/&@080$#%$-$401$:$/&/080+.+#%001$:$+$$08201$:0$/&-001$:$+$#080/.+&201$:$+#@080.#+':01$:$/&.080$#%$-$201$:$/&-080+.+#%001$:$+#/08201$:0$/&+001$:$+#.080-%%.<").
Definition KCa3c_41 : list kentry := Eval vm_compute in (NFC.d_kl "301$:$+#-080-,+%201$:$/&,080$#%$-$001$:$/&+080+.+#%0").
Definition KCa3c_42 : list kentry := Eval vm_compute in (NFC.d_kl "9010$#'?80,#$%@801$:$&#.08201$:0$-@.001$:$&#-080/'.&001$:$&#,080-#$,801$:$-@/080'.#-,'201$:$-@.080+.+#%001$:$&#+08201$:0$-@,001$:$&#'080.&$@:01$:$&#&080@.@$2").
Definition KCa3c_43 : list kentry := Eval vm_compute in (NFC.d_kl "=01$:$-@#080+.+#%0010-&?8201$:0$%@+0010-%110$@4010-%310$@4010-%510$@4010-%710$@4000'.#-,'0200000'.#-,&080--+%4000'.#-,%020001$://$08201$:0$%@$001$://#080$#'@/401$:/.@080.#%@:01$:$%@'080--+%4").
Definition KCa3c_44 : list kentry := Eval vm_compute in (NFC.d_kl "901$:$$$@080'.#,@#001$:$$$/080+.+#%0000'.#,@+0402000'.#,@%040%@2000'.#,@$080%$.@%+&/,@-$%&@/0000'.#,@#8400000'.#,@#0100000'.#,@'080--+%4000'.#,@&0402").
Definition KCa3c_45 : list kentry := Eval vm_compute in (NFC.d_kl "$0010/'?80,#$&.:000,#$&.060%+,#,##-,0000,#$&.>100010/+?80,#$&.8000,#$&'840'%,0000,#$&'0100010/,?80,#$&.0000,#$&&080',#@@@$%.$0010/-?80,#$&-8000,#$&%080%$.@%+&-$',,%&&&2010/.?80,#$&-0000,#$&$040%$&0000,#$&-0800000,#$&,8102010//?80,#$&,8000,#$&,040@:").
Definition KCa3c_46 : list kentry := Eval vm_compute in (NFC.d_kl "$0010/@?80,#$&,0000,#$&+080&@%/+'.#/&-0010@#?80,#$&+8000,#$&#840%0010@$?80,#$&+0000,#$%@040%+,#,##-+>010@%?80,#$&'8000,#$'%040,$@-2010@&?80,#$&'0010@'?80,#$&&8010@+?80,#$&&0010@,?80,#$&%>010@-?80,#$&%<010-'?80--+%4010,@?81$:000@-$+@08201$:0,$-.0").
Definition KCa3c_47 : list kentry := Eval vm_compute in (NFC.d_kl "$011$:&&,00$-#011$:-$.20>11$:-%$20>11$://%00%&-011$:$%/@20>11$:$%@&20>11$:$+&$00%,@011$:$/'@20>11$:$/+&20>11$:$/+.40<11$:$/+/40'&$/<61$:00,$-.041$:'%,051$:'%,0',%###-#/,#&&$,'/'071$:00,$-.010,+,.@#?0$.+/'.&071$:00,$-.000,$-.00'.$,#&0").
Definition KCa3c_48 : list kentry := Eval vm_compute in (NFC.d_kl "$071$:00,$-.000$%.+.%#.'00--.,,-&&%./.071$:00,$-.00@,-.#/,/@&,000,.%#$&@'+@&,071$:00,$-.00$'++$##$&000@,,&,'+/@%&071$:00,$-.00$%.+.%#.'000$-@&.@&@071$:00,$-.01700'%,0010$$'?800000$#$&.&080'%,0010,/740$-'#'##+#4010&&?800010&%?800010&$?800010&#?800010%@?800010%/?800010%.?800010%-?800").
Definition KCa3c_49 : list kentry := Eval vm_compute in (NFC.d_kl "?000$#$&.-080$$%+/+.$/%$$%$@.'+8100$#$&..00'%'>000$#$.#%080$$%+/+.$/%$$%$@.'+8100$#$.#&00'%'>000,$'&$010271700'%,000$%.+.%#.'00--.,,-&&%./.0000,$#/&080$%.+.%'@@0000,$'%/080+,-%./&'&.'%'>000$#$&.$0820100$.?010$.?80&#+###'-@#&/@$+,-$4000+/&,+080$$'.&2010$-?8202010400$0110%0010$,?80',../0010$+?80+.'@#0010$'?80,$'%.0").
Definition KCa3c_50 : list kentry := Eval vm_compute in (NFC.d_kl "$02201020400$01120400$012400$014%$00%0$92201020400$011400$012%$020130213,$-.0+/&,+03+/&,,0,#$%@03,#$&$:,#$&%03,#$&'2,#$&'83,#$&,:,#$&-03,#$&@6,#$&@83,#$'#2,#$'#83,#$'%8,#//$03,#//$:,$#/&03,$#/'0,$'%.03,$'%.8,$'%/03,$'%@0,$'&$03,$'&$2,$'&$83,$'&%0@-$+@0").
Definition KCa3c_51 : list kentry := Eval vm_compute in (NFC.d_kl "23@-$,$0$#$&.$03$#$&.%8$#$&.&0").
Definition car13d := ltac:(nf_car (KCa3c_1 ++ KCa3c_2 ++ KCa3c_3 ++ KCa3c_4 ++ KCa3c_5 ++ KCa3c_6 ++ KCa3c_7 ++ KCa3c_8 ++ KCa3c_9 ++ KCa3c_10 ++ KCa3c_11 ++ KCa3c_12 ++ KCa3c_13 ++ KCa3c_14 ++ KCa3c_15 ++ KCa3c_16 ++ KCa3c_17 ++ KCa3c_18 ++ KCa3c_19 ++ KCa3c_20 ++ KCa3c_21 ++ KCa3c_22 ++ KCa3c_23 ++ KCa3c_24 ++ KCa3c_25 ++ KCa3c_26 ++ KCa3c_27 ++ KCa3c_28 ++ KCa3c_29 ++ KCa3c_30 ++ KCa3c_31 ++ KCa3c_32 ++ KCa3c_33 ++ KCa3c_34 ++ KCa3c_35 ++ KCa3c_36 ++ KCa3c_37 ++ KCa3c_38 ++ KCa3c_39 ++ KCa3c_40 ++ KCa3c_41 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_2 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_3 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_4 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_5 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_6 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_7 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_8 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_9 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_10 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_11 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_12 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_13 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_14 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_15 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_16 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_17 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_18 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_19 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_20 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_21 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_22 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_23 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_24 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_25 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_26 ++ KCa3c_42 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_28 ++ KCa3c_43 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_30 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_31 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_32 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_33 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_34 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_35 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_36 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_37 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_38 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_39 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_40 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_41 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_42 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_43 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_44 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_85 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_86 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_87 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_88 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_89 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_90 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_91 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_92 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_93 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_94 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_95 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_96 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_97 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_45 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_99 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_100 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_101 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_102 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_103 ++ KCa3c_44 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_105 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_106 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_107 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_108 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_109 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_110 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_111 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_112 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_113 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_114 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_115 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_116 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_117 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_118 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_119 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_120 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_121 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_122 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_123 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_124 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_125 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_126 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_127 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_15 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_16 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_17 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_18 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_19 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_128 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_129 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_22 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_23 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_24 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_25 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_26 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_27 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_28 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_29 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_30 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_31 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_32 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_33 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_34 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_35 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_36 ++ KCa3c_45 ++ KCa3c_46 ++ KCa3c_47 ++ KCa3c_48 ++ KCa3c_49 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_77 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_78 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_79 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_48 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_81 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_11 ++ KCa3c_50 ++ KCa3c_51 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_49 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_13) ((AX2L.carryF3 LG13d KN13c []))).
Definition KN13d : list kentry := fst (fst car13d).
Definition CS13d : list sidecond := Eval lazy in (snd (fst car13d)).
Definition HS13d : list bool := Eval lazy in (snd car13d).
Lemma car13d_eq : carry LG13d KN13c [] = (KN13d, CS13d, HS13d).
Proof. apply AX2L.carry_viaF3. vm_cast_no_check (eq_refl car13d). Qed.


(* [comment removed for export] *)
Definition SR14 : list expr := sr_upd SR13d 10 (ELit (2 ^ 47 - 1)).

(* [comment removed for export] *)
Definition run14 := ltac:(nf_run KN13d ((AX2L.sym_execFS6 SEGS IT_Kn3c KN13d F8 true STOPS3 noscr (SS A_maxva_smeared SR14 [] KN13d 27) []))).
Definition PC14 : Z := Eval lazy in (s_pc (fst (fst run14))).
Definition SR_E7 : list expr := Eval lazy in (s_regs (fst (fst run14))).
Definition LG14 : list sentry := s_log (fst (fst run14)).
Definition SK14 : list kentry := s_know (fst (fst run14)).
Definition NX14 : nat := Eval lazy in (s_next (fst (fst run14))).
Definition SC14 : list sidecond := Eval lazy in (snd (fst run14)).
Definition SP14 : scripts := Eval lazy in (snd run14).
Lemma run14_eq : sym_exec SEGS F8 true STOPS3 noscr (SS A_maxva_smeared SR14 [] KN13d 27) [] = (SSR PC14 SR_E7 LG14 SK14 NX14 None, SC14, SP14).
Proof. apply (AX2L.sym_exec_viaFS6 SEGS IT_Kn3c KN13d); [exact IT_Kn3c_ok | reflexivity | vm_cast_no_check (eq_refl run14)]. Qed.
Definition KCa3c_52 : list kentry := Eval vm_compute in (NFC.d_kl "$0010&/?800010&.?800010&-?80$#$&.&0010&,?80%//#,'0010&+?80-@,&:010&'?800010&&?80&-,/+8010&%740'4010&$?802010&#?80,#/..0010%@?80$#%$&@0010%/?80,#$%@0010%.?80%,.'&0000,#/..2102010%-?800010%,?80,$'%.0").
Definition KCa3c_53 : list kentry := Eval vm_compute in (NFC.d_kl "$0010%+?802010%'?80$#%$&@0010%&?80,#$%@0010%%?80&%/-@0000@-$,$080&&#&@8000+/&,'080$0000,$#/'0402000$#%$&/0100000+/&,-0404000$#%$&/2300000$#%$/+080&$#/&0000$#%$@%080&&#%'0000$#%$@&080&%@@.0000,$'%/080+,-%./&'&.'%'>000,$'&$840&<000,#//$8102").
Definition KCa3c_54 : list kentry := Eval vm_compute in (NFC.d_kl "9000,#//$0404000,#$&.<102000$#%$-$>100000$#%$-$<102000$#%$-$:100000$#%$-$8100000$#%$-$6100000$#%$-$4100000$#%$-$2102").
Definition KCa3c_55 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$'#0100000$#%$&@>100000$#%$&@<100000$#%$&@:100000$#%$&@8100000$#%$&@6100000$#%$&@4100000$#%$&@2100000$#%$&@0102010'$;100010',740',%###-#/,#&/-.'+$>010',?100010'.?800010'/?800010+%?80',%###-#/,#&/-.'+$>010+&=100").
Definition KCa3c_56 : list kentry := Eval vm_compute in (NFC.d_kl "$0010+'?800010++?800010+,?800010+.;100010&@1100010&@3100010&@5100010&@7100010&@9100010&@;102010&@=10%+8010&@?10$#4010'#1100010'#3100010'#5100010'#7100").
Definition KCa3c_57 : list kentry := Eval vm_compute in (NFC.d_kl "$071$:00,$-.000$%.+.%#.'00--.,,-&&%./.071$:00,$-.00@,-.#/,/@&,000,.%#$&@'+@&,071$:00,$-.00$'++$##$&000@,,&,'+/@%&071$:00,$-.00$%.+.%#.'000$-@&.@&@071$:00,$-.01700'%,0010$$'?800000$#$&.&080'%,0010,/740$-'#'##+#4010&%?400000$#$&.-080$$%+/+.$/%$$%$@.'+8100$#$&..00'%'>000$#$.#%080$$%+/+.$/%$$%$@.'+8100$#$.#&00'%'>000,$'&$010271700'%,000$%.+.%#.'00--.,,-&&%./.0000,$#/&080$%.+.%'@@0").
Definition KCa3c_58 : list kentry := Eval vm_compute in (NFC.d_kl "7000$#$&.$0820100$.?010$.?80&#+###'-@#&/@$+,-$4000+/&,+080$$'.&2010$-?8202010400$0110%0010$,?80',../0010$+?80+.'@#0010$'?80,$'%.0").
Definition KCa3c_59 : list kentry := Eval vm_compute in (NFC.d_kl "$02201020400$01120400$012400$014%$00%0$92201020400$011400$012%$020130213,$-.0+/&,'03+/&,,0+/&,-03+/&,-8,#$%@03,#$&$:,#$&%03,#$&'2,#$&'83,#$&,:,#$&-03,#$&@6,#$&@83,#$'#2,#$'#83,#$'%8,#/..23,#/..4,#//$03,#//$:,$#/&03,$#/'8,$'%.03,$'%.8,$'%/03,$'%@0,$'&$0").
Definition KCa3c_60 : list kentry := Eval vm_compute in (NFC.d_kl "$03,$'&$2,$'&$83,$'&%0@-$+@03@-$,%0$#$&.$03$#$&.%8$#$&.&03$#$&.'0$#$&.-03$#$.#$>$#$.#%03$#%$%->$#%$&/03$#%$&/8$#%$&@03$#%$-%0$#%$/+03$#%$/,0$#%$@%03$#%$@'0'.#,@#03'.#,@#2'.#,@#83'.#,@%>'.#,@&03'.#,@&8'.#,@'03'.#,@+8'.#-,%03'.#-,%4'.#-,&0").
Definition KCa3c_61 : list kentry := Eval vm_compute in (NFC.d_kl "53'.#-,'4'.-#,%03'.-#,&0'.-#,+03'.-#,@0'.-#@.03'.-#@/0'.-$,&03'.-$,+2'.-$,,0").
Definition car14 := ltac:(nf_car (KCa3c_52 ++ KCa3c_53 ++ KCa3c_54 ++ KCa3c_2 ++ KCa3c_3 ++ KCa3c_4 ++ KCa3c_5 ++ KCa3c_6 ++ KCa3c_7 ++ KCa3c_8 ++ KCa3c_9 ++ KCa3c_10 ++ KCa3c_11 ++ KCa3c_12 ++ KCa3c_13 ++ KCa3c_14 ++ KCa3c_15 ++ KCa3c_16 ++ KCa3c_17 ++ KCa3c_18 ++ KCa3c_55 ++ KCa3c_56 ++ KCa3c_24 ++ KCa3c_25 ++ KCa3c_26 ++ KCa3c_27 ++ KCa3c_28 ++ KCa3c_29 ++ KCa3c_30 ++ KCa3c_31 ++ KCa3c_32 ++ KCa3c_33 ++ KCa3c_34 ++ KCa3c_35 ++ KCa3c_36 ++ KCa3c_37 ++ KCa3c_38 ++ KCa3c_39 ++ KCa3c_40 ++ KCa3c_41 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_2 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_3 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_4 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_5 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_6 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_7 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_8 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_9 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_10 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_11 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_12 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_13 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_14 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_15 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_16 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_17 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_18 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_19 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_20 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_21 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_22 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_23 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_24 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_25 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_26 ++ KCa3c_42 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_28 ++ KCa3c_43 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_30 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_31 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_32 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_33 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_34 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_35 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_36 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_37 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_38 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_39 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_40 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_41 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_42 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_43 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_44 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_85 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_86 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_87 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_88 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_89 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_90 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_91 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_92 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_93 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_94 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_95 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_96 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_97 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_45 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_99 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_100 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_101 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_102 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_103 ++ KCa3c_44 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_105 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_106 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_107 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_108 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_109 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_110 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_111 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_112 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_113 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_114 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_115 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_116 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_117 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_118 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_119 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_120 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_121 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_122 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_123 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_124 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_125 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_126 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_127 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_15 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_16 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_17 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_18 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_19 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_128 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_129 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_22 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_23 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_24 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_25 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_26 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_27 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_28 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_29 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_30 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_31 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_32 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_33 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_34 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_35 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_36 ++ KCa3c_45 ++ KCa3c_46 ++ KCa3c_47 ++ KCa3c_57 ++ KCa3c_58 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_77 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_78 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_79 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_48 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_81 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_11 ++ KCa3c_59 ++ KCa3c_60 ++ KCa3c_61 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_13) ((AX2L.carryF3 LG14 KN13d []))).
Definition KN14 : list kentry := fst (fst car14).
Definition CS14 : list sidecond := Eval lazy in (snd (fst car14)).
Definition HS14 : list bool := Eval lazy in (snd car14).
Lemma car14_eq : carry LG14 KN13d [] = (KN14, CS14, HS14).
Proof. apply AX2L.carry_viaF3. vm_cast_no_check (eq_refl car14). Qed.


(* [comment removed for export] *)
Definition gc7 (k : kentry) : bool := gc_keep_stack (-288) k && gc_keep_base 26 k.
Definition KCa3c_62 : list kentry := Eval vm_compute in (NFC.d_kl "9010&%740'4010&$?802010&#?80,#/..0010%@?80$#%$&@0010%/?80,#$%@0010%.?80%,.'&0000,#/..2102010%-?800010%,?80,$'%.0").
Definition KCa3c_63 : list kentry := Eval vm_compute in (NFC.d_kl "$0000$#%$'#0100000$#%$&@>100000$#%$&@<100000$#%$&@:100000$#%$&@8100000$#%$&@6100000$#%$&@4100000$#%$&@2100000$#%$&@0102000,#$&#040$#-0000,#$%@840%@0000$#$&.%0400000@-$,#08201$:0$/+@0000'.#-,'0200000'.#-,&080--+%4000'.#-,%0200").
Definition KCa3c_64 : list kentry := Eval vm_compute in (NFC.d_kl "$0000'.#,@+0402000'.#,@%040%@2000'.#,@$080%$.@%+&/,@-$%&@/0000'.#,@#8400000'.#,@#0100000'.#,@'080--+%4000'.#,@&0402000'.#,@%<100000'.#,@%8200000,#$&@4100000,#$&$8100000,#$'$080--+%4000,#$'#8404000,#$'#0102000,#$&@8400000,#$&@0202").
Definition KCa3c_65 : list kentry := Eval vm_compute in (NFC.d_kl "$0000,#$&/080%$.@%+&/-#/$'@/#2000,#$&.060%+,#,##-,0000,#$&.>100000,#$&'840'%,0000,#$&'0100000,#$&&080',#@@@$%.$0000,#$&%080%$.@%+&-$',,%&&&2000,#$&$040%$&0000,#$&-0800000,#$&,8102000,#$&,040@:000,#$&+080&@%/+'.#/&-0000,#$&#840%0000,#$%@040%+,#,##-+>000,#$'%040,$@-2000@-$+@08201$:0,$-.0").
Definition KCa3c_66 : list kentry := Eval vm_compute in (NFC.d_kl ">71$:00,$-.000$%.+.%#.'00--.,,-&&%./.071$:00,$-.00@,-.#/,/@&,000,.%#$&@'+@&,071$:00,$-.00$'++$##$&000@,,&,'+/@%&071$:00,$-.00$%.+.%#.'000$-@&.@&@071$:00,$-.01700'%,0000$#$&.&080'%,0010&%?400000$#$&.-080$$%+/+.$/%$$%$@.'+8100$#$&..00'%'>000$#$.#%080$$%+/+.$/%$$%$@.'+8100$#$.#&00'%'>000,$'&$010271700'%,000$%.+.%#.'00--.,,-&&%./.0000,$#/&080$%.+.%'@@0").
Definition KN_E7 : list kentry := ltac:(nf_rope (KCa3c_62 ++ KCa3c_53 ++ KCa3c_54 ++ KCa3c_2 ++ KCa3c_3 ++ KCa3c_4 ++ KCa3c_5 ++ KCa3c_6 ++ KCa3c_7 ++ KCa3c_8 ++ KCa3c_9 ++ KCa3c_10 ++ KCa3c_11 ++ KCa3c_12 ++ KCa3c_13 ++ KCa3c_14 ++ KCa3c_15 ++ KCa3c_16 ++ KCa3c_17 ++ KCa3c_18 ++ KCa3c_63 ++ KCa3c_64 ++ KCa3c_65 ++ KCa3c_47 ++ KCa3c_66 ++ KCa3c_58 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_77 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_78 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_79 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.KCa3b_48 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_81 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_11 ++ KCa3c_59 ++ KCa3c_60 ++ KCa3c_61 ++ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.KCa3a_13) ((List.filter gc7 KN14))).
Lemma KN_E7_eq : List.filter gc7 KN14 = KN_E7. Proof. vmeq_cast. Qed.

Lemma itinerary3c_ok :
  (PC13d, SC13d, CS13d) = (A_maxva_smeared, [], [])
  /\ sr_get SR13d 10%bv = smear_reg (EAlu ALU_ADD (EVar 0) (ELit (-160)))
  /\ (PC14, SC14, CS14) = (A_internal_mmap_ecall, [], [])
  /\ map (fun r => sr_get SR_E7 (Z_to_bv 5 r)) [2; 10; 11; 12; 13; 14; 15; 17]
     = [EAlu ALU_ADD (EVar 0) (ELit (-288)); ELit 0; ELit 0x38e000; ELit 3; ELit 34; ELit (2 ^ 64 - 1); ELit 0; ELit 222].
Proof. vmeq_conj. Qed.
End BootKn3c.
