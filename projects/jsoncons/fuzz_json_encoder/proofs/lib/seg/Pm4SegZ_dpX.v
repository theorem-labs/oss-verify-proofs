(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Pm4PlanKit.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(366240, 36%nat) ; (430728, 371%nat) ; (432320, 26%nat) ; (536784, 324%nat) ; (558976, 6%nat) ; (654096, 12%nat) ; (722136, 4%nat) ; (914460, 12%nat) ; (1316636, 70%nat) ; (1317312, 50%nat) ; (1349968, 105%nat) ; (1351512, 12%nat) ; (1388196, 62%nat) ; (1390432, 191%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [1316644].
Definition STOPS1 : list Z := [1316644] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; ELit 1315408; EVar 2; EVar 3; ELit 6938576; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332552704 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-320)) (ELit 320);
   KUnk (SA (EVar 2) (-320)) (ELit 320);
   KImg 65536 1449984;
   KImg 1464128 1468480;
   KWr (SA (ELit 0) (1468480)) (ELit 8);
   KWr (SA (ELit 0) (1468560)) (ELit 1);
   KWr (SA (ELit 0) (1472432)) (ELit 8);
   KWr (SA (ELit 0) (7069728)) (ELit 1);
   KWr (SA (ELit 0) (7069736)) (ELit 4);
   KWr (SA (ELit 0) (7069744)) (ELit 8);
   KWr (SA (ELit 0) (7070272)) (ELit 4);
   KWr (SA (ELit 0) (2147469652)) (ELit 4);
   KWr (SA (ELit 0) (2147469696)) (ELit 12);
   KWr (SA (ELit 0) (2147469712)) (ELit 68);
   KWr (SA (ELit 0) (2147469844)) (ELit 336);
   KWr (SA (ELit 0) (2147470188)) (ELit 1328);
   KWr (SA (ELit 0) (2147471584)) (ELit 12);
   KWr (SA (ELit 0) (2147471628)) (ELit 40);
   KWr (SA (ELit 0) (2147628616)) (ELit 52);
   KWr (SA (ELit 0) (2147633896)) (ELit 544);
   KWord (SA (ELit 0) (6938408)) 4 (EVar 44);
   KRange (EVar 44) 1 4194303;
   KWord (SA (ELit 0) (7070272)) 4 (ELit 0);
   KWord (SA (ELit 0) (7070307)) 1 (ELit 0);
   KWord (SA (ELit 0) (7069744)) 8 (ELit 7069752);
   KWord (SA (ELit 0) (7069736)) 4 (ELit 2);
   KWord (SA (ELit 0) (7069760)) 8 (ELit 1317312);
   KWord (SA (ELit 0) (7070016)) 8 (ELit 654096);
   KWord (SA (ELit 0) (7069732)) 4 (ELit 0);
   KWord (SA (ELit 0) (2080160)) 1 (ELit 0);
   KWord (SA (ELit 0) (7069752)) 8 (ELit 0);
   KWord (SA (ELit 0) (1468560)) 1 (ELit 0);
   KWord (SA (ELit 0) (1452624)) 8 (ELit 1452624);
   KWord (SA (ELit 0) (1468480)) 8 (ELit 1);
   KWord (SA (ELit 0) (1472272)) 4 (ELit 1);
   KWord (SA (ELit 0) (1472432)) 8 (ELit 0);
   KWord (SA (ELit 0) (1485784)) 1 (ELit 1);
   KWord (SA (ELit 0) (1482488)) 8 (ELit 2147450880);
   KWord (SA (ELit 0) (7069768)) 8 (ELit 1317312);
   KWord (SA (ELit 0) (7070024)) 8 (ELit 722136);
   KWord (SA (ELit 0) (6931796)) 1 (ELit 0);
   KWord (SA (ELit 0) (1480540)) 1 (ELit 1);
   KWord (SA (ELit 0) (2079392)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1453136)) 8 (ELit 1388196);
   KWord (SA (ELit 0) (7071704)) 8 (ELit 0);
   KWord (SA (ELit 0) (1464080)) 8 (ELit 1463848);
   KWord (SA (ELit 0) (1463988)) 4 (ELit 4294967295);
   KWord (SA (ELit 0) (1463888)) 8 (ELit 0);
   KWord (SA (ELit 0) (1463904)) 8 (ELit 0);
   KWord (SA (ELit 0) (1463856)) 8 (ELit 0);
   KWord (SA (ELit 0) (1463864)) 8 (ELit 0);
   KWord (SA (ELit 0) (1463840)) 8 (ELit 1463608);
   KWord (SA (ELit 0) (1463748)) 4 (ELit 4294967295);
   KWord (SA (ELit 0) (1463648)) 8 (ELit 7071728);
   KWord (SA (ELit 0) (1463664)) 8 (ELit 7071728);
   KWord (SA (ELit 0) (1463616)) 8 (ELit 0);
   KWord (SA (ELit 0) (1463624)) 8 (ELit 0);
   KWord (SA (ELit 0) (1463600)) 8 (ELit 1463368);
   KWord (SA (ELit 0) (1463508)) 4 (ELit 4294967295);
   KWord (SA (ELit 0) (1463408)) 8 (ELit 0);
   KWord (SA (ELit 0) (1463424)) 8 (ELit 0);
   KWord (SA (ELit 0) (1463376)) 8 (ELit 0);
   KWord (SA (ELit 0) (1463384)) 8 (ELit 0)].
Definition ss0 : sym_state := SS 1317396 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-320), ELit 320); (ELit 0, (1468480), ELit 8); (ELit 0, (1468560), ELit 1); (ELit 0, (1472432), ELit 8); (ELit 0, (7069728), ELit 1); (ELit 0, (7069736), ELit 4); (ELit 0, (7069744), ELit 8); (ELit 0, (7070272), ELit 4); (ELit 0, (2147469652), ELit 4); (ELit 0, (2147469696), ELit 12); (ELit 0, (2147469712), ELit 68); (ELit 0, (2147469844), ELit 336); (ELit 0, (2147470188), ELit 1328); (ELit 0, (2147471584), ELit 12); (ELit 0, (2147471628), ELit 40); (ELit 0, (2147628616), ELit 52); (ELit 0, (2147633896), ELit 544)].
Definition F0L : list SR.region := [(EVar 2, (-320), 320); (ELit 0, (1468480), 8); (ELit 0, (1468560), 1); (ELit 0, (1472432), 8); (ELit 0, (7069728), 1); (ELit 0, (7069736), 4); (ELit 0, (7069744), 8); (ELit 0, (7070272), 4); (ELit 0, (2147469652), 4); (ELit 0, (2147469696), 12); (ELit 0, (2147469712), 68); (ELit 0, (2147469844), 336); (ELit 0, (2147470188), 1328); (ELit 0, (2147471584), 12); (ELit 0, (2147471628), 40); (ELit 0, (2147628616), 52); (ELit 0, (2147633896), 544)].
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
Definition ps0 : SR.post_spec := SR.PS 1316644 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1317396 regs0 kn0 = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 1317396 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
