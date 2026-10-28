(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0PlanKit_b Ba0PlanKitIt_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require SegPlanFast.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(702272, 40%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
Definition ENDS : list Z := [702620].
Definition STOPS1 : list Z := [702360] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332491264 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-4096)) (ELit 4096);
   KWord (SA (ELit 0) 1309752) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1309760) 4 (ELit 1);
   KRange (EVar 33) 6905856 140737488355295;
   KAlign (EVar 33) 8;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 33) 0) (ELit 24);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 33) (ELit 3)) 2147450880) (ELit 3);
   KDisj (SA (EVar 2) (-4096)) (ELit 4096) (SA (EVar 33) 0) (ELit 24);
   KDisj (SA (ELit 0) 65536) (ELit 6840320) (SA (EVar 33) 0) (ELit 24);
   KWord (SA (EVar 33) 0) 8 ((EVar 36));
   KWord (SA (EVar 33) 16) 8 ((EVar 41));
   KRange (EVar 36) 4096 140737488355288;
   KAlign (EVar 36) 16;
   KRange (EVar 41) 4136 140737488355327;
   KWord (SA (EVar 33) 8) 8 (EAlu Instr.ALU_ADD (EVar 36) (EMd Instr.M_MUL (ELit 40) (EVar 39)));
   KRange (EVar 39) 0 2048;
   KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 36)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-40)) (EVar 39)) (EVar 41))) 0 81920;
   KImg 65536 1282048;
   KWr (SA (EVar 33) 8) (ELit 8)].
Definition ss0 : sym_state := SS 702272 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-16), ELit 16); ((EVar 33), 8, ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-16), 16); ((EVar 33), 8, 8)].
Definition BF : nat := 1000.
Definition BR : list SGP.bfact := [].
Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition lp_reg (J : nat) (s : sym_state) (re : list (nat * expr)) : list expr :=
  map (fun i => match find (fun p : nat * expr => Nat.eqb (fst p) i) re with
                | Some (_, e) => APC.esubst 999 (EVar J) (APC.esubst 998 (nth i (s_regs s) (ELit 0)) e)
                | None => nth i (s_regs s) (ELit 0) end) (seq 0 32).
Definition lp_dropK (bs : list expr) (K : kentry) : bool :=
  match K with
  | KWord (SA b _) _ _ | KZero (SA b _) _ | KUnk (SA b _) _ | KBlob (SA b _) _ _ | KFill (SA b _) _ _ => existsb (expr_eqb b) bs
  | _ => false
  end.
Definition lp_inv (J : nat) (s : sym_state) (re : list (nat * expr)) (bs : list expr) : sym_state :=
  SS (s_pc s) (lp_reg J s re) [] (filter (fun K => negb (lp_dropK bs K)) (s_know s)) (S J).
Fixpoint lp_respell (rs : list nat) (inv0 : sym_state) (p : SGP.splan) : SGP.splan :=
  match rs with [] => p | r :: t => SGP.PRespell r (nth r (s_regs inv0) (ELit 0)) (lp_respell t inv0 p) end.
Definition armsC := Eval vm_compute in (SGP.case_arms ss0 (EVar 39) 0).
Definition c0 : sym_state := match armsC with Some (Some s, _) => s | _ => ss0 end.
Definition c1 : sym_state := match armsC with Some (_, Some s) => s | _ => ss0 end.
Definition ex3 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 c0).
Definition s3 : sym_state := snd (snd ex3).
Definition ex4 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 c1).
Definition s4 : sym_state := snd (snd ex4).
Definition LJ5 : nat := Eval vm_compute in (s_next s4).
Definition LN5 : expr := EAlu Instr.ALU_ADD (EVar 39) (ELit (-1)).
Definition inv5 : sym_state := Eval vm_compute in (lp_inv LJ5 s4 [(16%nat, EAlu Instr.ALU_SUB (EVar 998) (EMd Instr.M_MUL (ELit 40) (EVar 999)))] []).
Definition ex6 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 (SGP.inst inv5 LJ5 LN5)).
Definition s6 : sym_state := snd (snd ex6).
Definition plan : SGP.splan := SGP.PCase (EVar 39) 0 (SGA.mkplan (fst ex3) (SGP.PEnd 1)) (SGA.mkplan (fst ex4) (lp_respell [16%nat] (SGP.inst inv5 LJ5 (ELit 0)) (SGP.PLoop LJ5 LN5 inv5 (SGP.PStep (SR.SBlock STOPS1) SGP.PNext) (SGA.mkplan (fst ex6) (SGP.PEnd 0))))).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.
Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s6).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s6).
Definition ps0 : SR.post_spec := SR.PS 702620 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.
Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 702620 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 702272 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it IT IT_sound BF NX0 BR XSTEP F0 PSS plan 702272 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
