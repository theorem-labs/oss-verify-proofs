(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.GcFlush02.  (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Pm4PlanKit.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(440664, 1%nat) ; (440668, 1%nat) ; (455832, 39%nat) ; (455988, 690%nat) ; (458748, 45%nat) ; (483836, 102%nat) ; (524852, 1%nat) ; (524860, 1%nat) ; (527500, 188%nat) ; (529468, 380%nat) ; (562832, 40%nat) ; (604684, 24%nat) ; (604864, 13%nat) ; (605024, 7%nat) ; (1350932, 21%nat) ; (1351016, 78%nat) ; (1351772, 40%nat) ; (1352376, 108%nat) ; (1352808, 908%nat) ; (1356440, 16%nat) ; (1356504, 61%nat) ; (1377692, 7%nat) ; (1387168, 257%nat) ; (1388196, 62%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [1351864].
Definition STOPS1 : list Z := [1351864] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; ELit 722244; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; ELit 86575; EAlu Instr.ALU_ADD (EVar 2) (ELit (24)); EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332552704 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-3232)) (ELit 3232);
   KUnk (SA (EVar 2) (-3232)) (ELit 3232);
   KImg 65536 1449984;
   KZero (SA (EAlu Instr.ALU_SRL (EVar 2) (ELit 3)) (2147450762)) (ELit 24);
   KWord (SA (ELit 0) (2147461696)) 8 (ELit 0);
   KWord (SA (ELit 0) (2148334840)) 8 (ELit 0);
   KWr (SA (ELit 0) (1463608)) (ELit 4);
   KWr (SA (ELit 0) (1463616)) (ELit 8);
   KWr (SA (ELit 0) (1463624)) (ELit 8);
   KWr (SA (ELit 0) (1463640)) (ELit 8);
   KWr (SA (ELit 0) (1463648)) (ELit 8);
   KWr (SA (ELit 0) (1463664)) (ELit 8);
   KWr (SA (ELit 0) (1463680)) (ELit 8);
   KWr (SA (ELit 0) (1463744)) (ELit 4);
   KWr (SA (ELit 0) (7071728)) (ELit 1);
   KWord (SA (ELit 0) (1485784)) 1 (ELit 1);
   KWord (SA (ELit 0) (2079356)) 1 (ELit 1);
   KWord (SA (ELit 0) (1482488)) 8 (ELit 2147450880);
   KWord (SA (ELit 0) (1452744)) 8 (ELit 1377692);
   KWord (SA (ELit 0) (1452752)) 8 (ELit 1352376);
   KWord (SA (ELit 0) (7069712)) 8 (EVar 40);
   KWord (SA (ELit 0) (1463748)) 4 (ELit 4294967295);
   KWord (SA (ELit 0) (1463608)) 4 (ELit 5);
   KWord (SA (ELit 0) (1463704)) 8 (ELit 1024);
   KWord (SA (ELit 0) (1463640)) 8 (ELit 0);
   KWord (SA (ELit 0) (1463744)) 4 (ELit 0);
   KWord (SA (ELit 0) (1463696)) 8 (ELit 7071728);
   KWord (SA (ELit 0) (1463752)) 4 (ELit 10);
   KWord (SA (ELit 0) (1485785)) 1 (ELit 1);
   KWord (SA (ELit 0) (1453128)) 8 (ELit 1387168);
   KWord (SA (EVar 2) (24)) 4 (ELit 0);
   KWord (SA (ELit 0) (1453136)) 8 (ELit 1388196);
   KWord (SA (ELit 0) (1463680)) 8 (ELit 1351772);
   KWord (SA (ELit 0) (1463728)) 4 (ELit 1)].
Definition ss0 : sym_state := SS 440664 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-3232), ELit 3232); (ELit 0, (1463608), ELit 4); (ELit 0, (1463744), ELit 4); (ELit 0, (1463664), ELit 8); (ELit 0, (1463616), ELit 8); (ELit 0, (1463624), ELit 8); (ELit 0, (1463640), ELit 8); (ELit 0, (1463648), ELit 8); (ELit 0, (7071728), ELit 1); (ELit 0, (1463680), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-3232), 3232); (ELit 0, (1463608), 4); (ELit 0, (1463744), 4); (ELit 0, (1463664), 8); (ELit 0, (1463616), 8); (ELit 0, (1463624), 8); (ELit 0, (1463640), 8); (ELit 0, (1463648), 8); (ELit 0, (7071728), 1); (ELit 0, (1463680), 8)].
Definition BF : nat := 200000.
(* [comment removed for export] *)
Definition BR : list SGP.bfact := [].
(* [comment removed for export] *)
Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

(* [comment removed for export] *)
Definition ex1 := Eval vm_compute in (AUTO 20000 ss0).   (* [comment removed for export] *)
Definition s1 : sym_state := snd (snd ex1).
Eval vm_compute in (1001, length (fst ex1), fst (snd ex1), s_pc s1, s_next s1).
Lemma ex1_reached_end : fst (snd ex1) = 93. Proof. vm_compute. reflexivity. Qed.

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.   (* [comment removed for export] *)
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.
(* [comment removed for export] *)
Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)      (* [comment removed for export] *)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

(* [comment removed for export] *)
Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 1351864 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 440664 regs0 kn0 = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 440664 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
