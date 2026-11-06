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
Definition ITR : list (Z * nat) := [(597456, 153%nat) ; (597340, 29%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [597836].
Definition STOPS1 : list Z := [597696; 597740; 597756; 597768; 597836; 597908; 597984; 418668; 419148] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-96))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 41; EVar 19; ELit 2147450880; ELit 18446744073709551615; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332487280 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-112)) (ELit 112);
   KImg 860160 884736;
   KWord (SA (ELit 0) 911160) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 911168) 4 (ELit 1);
   KRange (EVar 37) 4096 140737488355328;
   KAlign (EVar 37) 8;
   KRange (APC.eadd (EVar 37) (EMd Instr.M_MUL (ELit 8) (EVar 35))) 4104 140737488355328;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 37) 0) (EMd Instr.M_MUL (ELit 8) (EVar 35));
   KZero (SA (EAlu Instr.ALU_SRL (EVar 37) (ELit 3)) 2147450880) (EVar 35);
   KDisj (SA (EVar 2) (-112)) (ELit 112) (SA (EVar 37) 0) (EMd Instr.M_MUL (ELit 8) (EVar 35));
   KRange (EVar 38) 4096 140737488355328;
   KAlign (EVar 38) 8;
   KRange (APC.eadd (EVar 38) (EMd Instr.M_MUL (ELit 8) (EVar 35))) 4104 140737488355328;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 38) 0) (EMd Instr.M_MUL (ELit 8) (EVar 35));
   KZero (SA (EAlu Instr.ALU_SRL (EVar 38) (ELit 3)) 2147450880) (EVar 35);
   KDisj (SA (EVar 2) (-112)) (ELit 112) (SA (EVar 38) 0) (EMd Instr.M_MUL (ELit 8) (EVar 35));
   KWord (SA (EVar 2) (-80)) 8 (EVar 37);
   KWord (SA (EVar 2) (-96)) 8 (EVar 38);
   KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 2) (ELit (-80))) (ELit 3)) 2147450880) (ELit 1);
   KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 2) (ELit (-96))) (ELit 3)) 2147450880) (ELit 1);
   KRange (EVar 35) 1 300;
   KRange (EVar 41) 0 299;
   KRange (APC.esub (EVar 35) (EVar 41)) 1 300;
   KWord (SA (EAlu Instr.ALU_ADD (EVar 37) (EMd Instr.M_MUL (ELit 8) (EVar 41))) 0) 8 (EVar 42);
   KRange (EVar 42) 0 18446744073709551615;
   KWord (SA (EAlu Instr.ALU_ADD (EVar 38) (EMd Instr.M_MUL (ELit 8) (EVar 41))) 0) 8 (EVar 43);
   KRange (EVar 43) 0 18446744073709551615].
Definition ss0 : sym_state := SS 597768 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-104), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-104), 8)].
Definition BF : nat := 1000.
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
Definition s1 : sym_state := Eval vm_compute in (match BLOCK ss0 with Some s => s | None => ss0 end).
Eval vm_compute in (5000+1, match BLOCK ss0 with Some s => (1, s_pc s, s_next s) | None => (0, 0, 0%nat) end).

(* [comment removed for export] *)
Definition ex2 := Eval vm_compute in (AUTO 60 s1).
Definition s2 : sym_state := snd (snd ex2).
Eval vm_compute in (1000+2, length (fst ex2), fst (snd ex2), s_pc s2, s_next s2).

Definition plan : SGP.splan := SGP.PStep (SR.SBlock STOPS1) (SGA.mkplan (fst ex2) (SGP.PEnd 0)).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.   (* [comment removed for export] *)
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
Definition regs_out0 : list expr := Eval vm_compute in (s_regs s2).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s2).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s2 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s2 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s2).
Definition ps0 : SR.post_spec := SR.PS 597836 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.
Eval vm_compute in (3500+0, Z.eqb (s_pc s2) 597836, s_pc s2).

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 597768 regs0 kn0 = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 597768 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
Check seg_sound_ax.
Eval vm_compute in (3003, regs0).
Eval vm_compute in (3004, kn0).
Eval vm_compute in (3100+0, regs_out0).
Eval vm_compute in (3200+0, cells0).
Eval vm_compute in (3300+0, nfresh0, exit_sp_off0).
Eval vm_compute in (3400+0, s_know s2).
Eval vm_compute in (3600, length SXALL).
Eval vm_compute in (3601, map (fun st => (s_pc st, spoff_of st, (s_next st - NX0)%nat)) SXALL).
Eval vm_compute in (3602, map s_regs SXALL).
Eval vm_compute in (3603, map (fun st => cells_of st (spoff_of st)) SXALL).
Eval vm_compute in (3604, map s_know SXALL).
