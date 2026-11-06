(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Bo0PlanKit.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(777800, 7%nat) ; (778360, 29%nat) ; (801216, 100%nat) ; (802720, 105%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [777808].
Definition STOPS1 : list Z := [777808] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 0; ELit 896160; EVar 110; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 118; EVar 119; EVar 120; ELit 6494536; EVar 122; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332552704 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-16)) (ELit 16);
   KUnk (SA (EVar 2) (-16)) (ELit 16);
   KImg 65536 884736;
   KWr (SA (ELit 0) (896192)) (ELit 8);
   KWr (SA (ELit 0) (896200)) (ELit 8);
   KWr (SA (ELit 0) (896216)) (ELit 8);
   KWord (SA (ELit 0) (896248)) 8 (ELit 6496280);
   KWord (SA (ELit 0) (896256)) 8 (ELit 1024);
   KWord (SA (ELit 0) (6494536)) 8 (EVar 40);
   KWord (SA (EVar 2) (40)) 8 (EVar 40);
   KWord (SA (EVar 2) (104)) 8 (ELit 802896);
   KWord (SA (EVar 2) (96)) 8 (ELit 896160);
   KWord (SA (EVar 2) (88)) 8 (EVar 9);
   KWord (SA (EVar 2) (80)) 8 (EVar 18);
   KWord (SA (EVar 2) (72)) 8 (EVar 19);
   KWord (SA (EVar 2) (64)) 8 (EVar 20);
   KWord (SA (EVar 2) (56)) 8 (EVar 21);
   KWord (SA (EVar 2) (48)) 8 (EVar 22);
   KWord (SA (ELit 0) (896168)) 8 (ELit 0);
   KWord (SA (ELit 0) (896176)) 8 (ELit 0);
   KWord (SA (ELit 0) (896152)) 8 (ELit 895920);
   KWord (SA (ELit 0) (896060)) 4 (ELit 4294967295);
   KWord (SA (ELit 0) (895960)) 8 (ELit 0);
   KWord (SA (ELit 0) (895976)) 8 (ELit 0);
   KWord (SA (ELit 0) (895928)) 8 (ELit 0);
   KWord (SA (ELit 0) (895936)) 8 (ELit 0);
   KWord (SA (EVar 2) (120)) 8 (ELit 778468);
   KWord (SA (EVar 2) (112)) 8 (EVar 10)].
Definition ss0 : sym_state := SS 801364 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-16), ELit 16); (ELit 0, (896192), ELit 8); (ELit 0, (896200), ELit 8); (ELit 0, (896216), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-16), 16); (ELit 0, (896192), 8); (ELit 0, (896200), 8); (ELit 0, (896216), 8)].
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
Definition ex1 := Eval vm_compute in (AUTO 4000 ss0).
Definition s1 : sym_state := snd (snd ex1).
Eval vm_compute in (1000+1, length (fst ex1), fst (snd ex1), s_pc s1, s_next s1).

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
Definition ps0 : SR.post_spec := SR.PS 777808 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.
Eval vm_compute in (3500+0, Z.eqb (s_pc s1) 777808, s_pc s1).

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 801364 regs0 kn0 = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 801364 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
Check seg_sound_ax.
Eval vm_compute in (3003, regs0).
Eval vm_compute in (3004, kn0).
Eval vm_compute in (3100+0, regs_out0).
Eval vm_compute in (3200+0, cells0).
Eval vm_compute in (3300+0, nfresh0, exit_sp_off0).
Eval vm_compute in (3400+0, s_know s1).
Eval vm_compute in (3600, length SXALL).
Eval vm_compute in (3601, map (fun st => (s_pc st, spoff_of st, (s_next st - NX0)%nat)) SXALL).
Eval vm_compute in (3602, map s_regs SXALL).
Eval vm_compute in (3603, map (fun st => cells_of st (spoff_of st)) SXALL).
Eval vm_compute in (3604, map s_know SXALL).
