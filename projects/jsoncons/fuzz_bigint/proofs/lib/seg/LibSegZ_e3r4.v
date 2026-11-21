(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the segment's start knowledge takes the run's CONFIG_RSEQ flag, with the auxv region 464 bytes, was 160, and the launch's auxv claims (SegAuxv.aux_kn) in place of the old twenty words, and the walk is computed in the build for each value of the flag and checked against the post spec read off the walk at the flag false, in place of the recorded walk. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Src0PlanKit Src0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require SegItab_S_079d1e.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegAuxv.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_S_079d1e.ITR.
Definition IT : itab := SegItab_S_079d1e.IT.
Definition ENDS : list Z := [140244].
Definition STOPS1 : list Z := [364196; 362788; 364652; 309572; 309252; 309576] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (480)); ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)); EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 (r : bool) : list kentry := [KRange (EVar 2) 1099511627776 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-7936)) (ELit 8416);
   KUnk (SA (EVar 2) (-7936)) (ELit 8416);
   KRange (EVar 10) 4224 140737488355328;
   KAlign (EVar 10) 16;
   KWr (SA (EVar 10) (-128)) (ELit 144);
   KUnk (SA (EVar 10) (-128)) (ELit 144);
   KRange (EVar 32) 1099511627776 140737488355328;
   KAlign (EVar 32) 8;
   KDisj (SA (EVar 2) (-7936)) (ELit 8480) (SA (EVar 10) (-128)) (ELit 144);
   KDisj (SA (EVar 10) (-128)) (ELit 144) (SA (EVar 32) 0) (ELit 464);
   KDisj (SA (EVar 2) (-7936)) (ELit 8480) (SA (EVar 32) 0) (ELit 464);
   KDisj (SA (EVar 10) (-128)) (ELit 144) (SA (ELit 0) 65536) (ELit 528384);
   KImg 65536 390664;
   KImg 390704 390736;
   KImg 390752 390760;
   KWord (SA (EVar 10) (-16)) 8 (ELit 0);
   KWord (SA (ELit 0) (591528)) 8 (EVar 33);
   KWord (SA (ELit 0) (591568)) 8 (EVar 32)]
   ++ aux_kn r 10 ++
  [KWord (SA (EVar 10) (-8)) 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (896)));
   KWord (SA (EVar 10) (-32)) 8 (ELit 4849336966747728640);
   KWord (SA (EVar 2) (536)) 8 (ELit 139904);
   KWord (SA (EVar 2) (528)) 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (960)));
   KWord (SA (EVar 2) (520)) 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (848)));
   KWord (SA (ELit 0) (459617)) 1 (ELit 1);
   KWord (SA (ELit 0) (459618)) 1 (ELit 0);
   KWord (SA (ELit 0) (459619)) 1 (ELit 1);
   KWord (SA (ELit 0) (459620)) 1 (ELit 0);
   KWord (SA (ELit 0) (459621)) 1 (ELit 1);
   KWord (SA (ELit 0) (459622)) 1 (ELit 0)].
Definition ss0 (r : bool) : sym_state := SS 141380 regs0 [] (kn0 r) NX0.
Definition F0 : list SGP.region := [(EVar 2, (-7936), ELit 8416)].
Definition F0L : list SR.region := [(EVar 2, (-7936), 8416)].
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
(* the walk from each r's start knowledge, computed in the build *)
Definition ex1_0 := Eval vm_compute in (AUTO 2000 (ss0 false)).
Definition ex1_1 := Eval vm_compute in (AUTO 2000 (ss0 true)).
Definition ex1 (r : bool) := if r then ex1_1 else ex1_0.
Definition s1 (r : bool) : sym_state := snd (snd (ex1 r)).

Definition plan (r : bool) : SGP.splan := SGA.mkplan (fst (ex1 r)) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) (kn0 false).
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
Definition regs_out0 : list expr := Eval vm_compute in (s_regs (s1 false)).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of (s1 false)).
Definition cells0 : list kentry := Eval vm_compute in (cells_of (s1 false) exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next (s1 false) - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc (s1 false)).
(* the post spec, read off r = false's walk; [cert] checks both walks against it *)
Definition ps0 : SR.post_spec := SR.PS 140244 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert (r : bool) : SGP.cert_ok RSEGS SegItab_S_079d1e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS (plan r) 141380 regs0 (kn0 r) = true.
Proof. destruct r; vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax (r : bool) := src0_plan_sound_it SegItab_S_079d1e.IT SegItab_S_079d1e.IT_sound BF NX0 BR XSTEP F0 PSS (plan r) 141380 regs0 (kn0 r) (cert r) (SGP.xstep_none_ok RSEGS NX0 BR F0).
