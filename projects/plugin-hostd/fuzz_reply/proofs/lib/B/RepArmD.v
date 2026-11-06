(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/RepArmD.v (commit f01d79f3fb5, cf refill round 3; file sha256 f95c06b6fbf9) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 24 image addresses moved by function pairs the comparison kit cmpkit 86da41d3ef68 calls the same code except at the by-hand acceptances named below (strictcmp3 65688e94214a, by funcpair_reply 6963bc4a94fc on the cgif twin ce511d541cda; 17 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the pair, each data one a pc-relative target of both paired functions; 7 code pcs the tool read as sizes, by the pair; 1 pair(s) carry a BY-HAND acceptance (accept.tsv, re-measured each run): _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE17PopulateFreeArrayEPNS_14AllocatorStatsEmPNS5_10RegionInfoEm+0xb0 (lui-in-section: CONSTANT (size; enters a store base only as a scaled count into a runtime array): kUserMapSize = 0x40000)), and 21 pcs named in comments; 1 hand maps (resolve-run-f01d79f3fb5.tsv (sha256 ba54f3af32ab; internal record), each with its evidence: pinned image bytes, YImgTop, the unit AF twin); no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, RepF1Top): the SYMBOLIC STATES of PopulateFreeArray's class-full report
   arm, in the vocabulary of the B3 refill walk (YFk8cf / YFkpcf / YFhz).  Each state is `Eval vm_compute in` a run
   from the previous one, and [rep_arm_stops] checks every pc, status and register this file's users rely on.

   The arm, from the B3 walk's state R3_M4 (YFk8cf.v:60, pc 0x36efc, the `bgeu a3, a1` of
   `rg_mapped_user + kUserMapSize` against kFreeArrayOffset + 1):
   - the branch TAKEN (kFreeArrayOffset < mu + kUserMapSize) reaches 0x370b0 `lbu a0, 0x44(s0)` and stops at the
     `beqz a0` of 0x370b4 on the class's exhausted byte, the junk atom rJEX ([R3_X]);
   - byte <> 0: the class is already flagged, so the arm prints nothing; 0x370b8 sets a1 = 0 and joins the
     populate-false return 0x37038, and the run ends at the refill's own `ret` 0x36a78 with a0 = 0 ([R3_XN]);
   - byte = 0: 0x370f0 loads *SanitizerToolName through the GOT (0x9e240 -> 0xa00e0 -> 0x202c7), stores 1 into the
     byte and calls Printf.  The two read-only image cells are None-based literal regions ([RGOT], [RTNM]), since a
     data load reads mem before seg_rom; their values are cells of Tfib_const (YF0m.v:180) and of rep_img_facts
     (RepIFcf.v).  [R3_XP] is the state at Printf's entry 0x685dc.
   - after Printf #1 returns at 0x37114 ([R3_XC1], the frame kept is the caller's own 0x40 bytes [STKC]), the inline
     ClassID -> Size of 0x37118-0x37174 splits on the class exactly as 0x36e60 / 0x36e68 do, and the three arms join
     at Printf #2's entry with a3 pinned to the class size ([R3_XK31] / [R3_XK16] / [R3_XKM], equal after the pin).
   rule 24: proves no function (kind: measurement). *)
(* Built against the report interface at RepIFcf 2d6dcb3547a (errb_call_pre's lk / errb_slack). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YFhy YFhz YFkpcf YFk6cf YFk8cf.
Import ListNotations. Open Scope Z_scope.

(* the GOT word and the tool-name pointer, as None-based literal regions *)
Definition addreg (r : YP09.region) (ss : sstate) : sstate :=
  mkSS (ss_pc ss) (ss_regs ss) (r :: ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition RGOT : YP09.region :=
  YP09.mkRegion None 0x9df88 0x9df90 0 0 [YP09.mkChunk 0x9df88 (CVal 8 (SLit 0x9fe38))].
Definition RTNM : YP09.region :=
  YP09.mkRegion None 0x9fe38 0x9fe40 0 0 [YP09.mkChunk 0x9fe38 (CVal 8 (SLit 0x2036f))].
Definition RNUL : YP09.region := YP09.mkRegion None 0 0 0 0 [].

(* 0x36efc bgeu taken: the class is full *)
Definition R3_XA : sstate := Eval vm_compute in arm BC_GEU true (SOff rMU 262144) (SLit 3758096385) R3_M4.
Definition R3_X : sstate := Eval vm_compute in runto 0x7ffffff0 R3_XA.
(* the class's byte is already 1: no report, the populate-false return *)
Definition R3_XN : sstate := Eval vm_compute in runto 0x7ffffff0 (arm BC_EQ false (SOff rJEX 0) (SLit 0) R3_X).
(* the class's byte is 0: the report *)
Definition R3_XT : sstate :=
  Eval vm_compute in addreg RTNM (addreg RGOT (arm BC_EQ true (SOff rJEX 0) (SLit 0) R3_X)).
Definition R3_XP : sstate := Eval vm_compute in runto 0x685dc R3_XT.
(* the caller's own frame, the only region Printf's contract lets the walk keep *)
Definition STKC : YP09.region :=
  Eval vm_compute in match nth_error (ss_mem R3_XP) 2 with Some r => trim_lo r (-224) | None => RNUL end.
Definition R3_XC1 : sstate := Eval vm_compute in ss_after_call R3_XP [STKC] 112 0x37114.
Definition R3_XC1b : sstate := Eval vm_compute in runto 0x7ffffff0 R3_XC1.
Definition R3_XK31 : sstate :=
  Eval vm_compute in noconds (pin (runto 0x7ffffff0 (arm BC_EQ true (SOff rCL 0) (SLit 31) R3_XC1b)) 13%bv (SOff rCSZ 0)).
Definition R3_XC0 : sstate := Eval vm_compute in runto 0x7ffffff0 (arm BC_EQ false (SOff rCL 0) (SLit 31) R3_XC1b).
Definition R3_XK16 : sstate :=
  Eval vm_compute in noconds (pin (runto 0x7ffffff0 (arm BC_LTU false (SLit 16) (SOff rCL 0) R3_XC0)) 13%bv (SOff rCSZ 0)).
Definition R3_XKM : sstate :=
  Eval vm_compute in noconds (pin (runto 0x7ffffff0 (arm BC_LTU true (SLit 16) (SOff rCL 0) R3_XC0)) 13%bv (SOff rCSZ 0)).

(* Every number the proof files quote.  0x370b4 = 223176, 0x36a78 = 221580, 0x685dc = 421144, 0x37114 = 223272,
   0x37188 = 223388, 0x1e8a4 = 125092, 0x202c7 = 131783, TFIB_TP = 6132240, 0x3711c = 223280, 0x37124 = 223288. *)
Lemma rep_arm_stops :
ss_pc R3_X = 0x370b4 /\
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 R3_XA) = RS_stopped (SR_branch BC_EQ (SOff rJEX 0) (SLit 0)) /\
sr_get (ss_regs R3_X) 10%bv = SOff rJEX 0 /\
ss_pc R3_XN = 0x36a78 /\
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 (arm BC_EQ false (SOff rJEX 0) (SLit 0) R3_X))
  = RS_stopped (SR_jalr (SOff 1 0)) /\
ss_resv R3_XN = None /\
sr_get (ss_regs R3_XN) 10%bv = SLit 0 /\ sr_get (ss_regs R3_XN) 1%bv = SOff 1 0 /\
sr_get (ss_regs R3_XN) 4%bv = SLit TFIB_TP /\
Forall (fun r : bv 5 => sr_get (ss_regs R3_XN) r = SOff (Z.to_nat (bv_unsigned r)) 0)
  [2; 3; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv /\
(exists cs, nth_error (ss_mem R3_XN) 0 = Some (YP09.mkRegion (Some 2%nat) (-1024) 0 (-1024) 0 cs)) /\
YP09.region_wf RGOT = true /\ YP09.region_wf RTNM = true /\
ss_pc R3_XP = 0x685dc /\
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 R3_XT) = RS_stopped SR_fetch /\
sr_get (ss_regs R3_XP) 10%bv = SLit 0x1e908 /\ sr_get (ss_regs R3_XP) 11%bv = SLit 0x2036f /\
sr_get (ss_regs R3_XP) 1%bv = SLit 0x37114 /\ sr_get (ss_regs R3_XP) 2%bv = SOff 2 (-224) /\
sr_get (ss_regs R3_XP) 3%bv = SOff 3 0 /\ sr_get (ss_regs R3_XP) 4%bv = SLit TFIB_TP /\
sr_get (ss_regs R3_XP) 8%bv = SOff rCL 0 /\ ss_resv R3_XP = None /\
YP09.r_base STKC = Some 2%nat /\ YP09.r_lo STKC = -224 /\ YP09.r_hi STKC = 0 /\
ss_pc R3_XC1 = 0x37114 /\ ss_resv R3_XC1 = None /\
ss_atoms_lt 112 R3_XP = true /\ regions_wf [STKC] = true /\ no_cdata [STKC] = true /\ mem_atoms_lt 112 [STKC] = true /\
ss_pc R3_XC1b = 0x3711c /\
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 R3_XC1) = RS_stopped (SR_branch BC_EQ (SOff rCL 0) (SLit 31)) /\
ss_pc R3_XC0 = 0x37124 /\
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 (arm BC_EQ false (SOff rCL 0) (SLit 31) R3_XC1b))
  = RS_stopped (SR_branch BC_LTU (SLit 16) (SOff rCL 0)) /\
ss_pc R3_XK31 = 0x685dc /\ ss_pc R3_XK16 = 0x685dc /\ ss_pc R3_XKM = 0x685dc /\
sr_get (ss_regs R3_XK16) 10%bv = SLit 0x20223 /\ sr_get (ss_regs R3_XK16) 11%bv = SLit 4096 /\
sr_get (ss_regs R3_XK16) 12%bv = SOff rCL 0 /\ sr_get (ss_regs R3_XK16) 13%bv = SOff rCSZ 0 /\
sr_get (ss_regs R3_XK16) 1%bv = SLit 0x37188 /\ sr_get (ss_regs R3_XK16) 2%bv = SOff 2 (-224) /\
sr_get (ss_regs R3_XK16) 3%bv = SOff 3 0 /\ sr_get (ss_regs R3_XK16) 4%bv = SLit TFIB_TP /\
ss_resv R3_XK16 = None.
Proof.
vm_compute. repeat apply conj; try reflexivity;
try (eexists; reflexivity);
try (repeat (apply Forall_cons; [reflexivity|]); apply Forall_nil).
Qed.

(* The three class arms are the SAME state once a3 is the class size. *)
Lemma rep_arm_join : R3_XK31 = R3_XK16 /\ R3_XKM = R3_XK16.
Proof. split; vm_compute; reflexivity. Qed.
