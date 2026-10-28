(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0PlanKit_u Bs0PlanKitIt_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.seg Require SegItab_Bs_d70b56_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require SegPlanFast.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Bs_d70b56_u.ITR.
Definition IT : itab := SegItab_Bs_d70b56_u.IT.
Definition ENDS : list Z := [701568].
Definition STOPS1 : list Z := [701568] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-96)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EAlu Instr.ALU_ADD (EVar 2) (ELit (-64)); EVar 38; EVar 37; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 34; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483152 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-96)) (ELit 96);
   KRange (EVar 10) 140735332483072 140737488355304;
   KAlign (EVar 10) 8;
   KWr (SA (EVar 10) 0) (ELit 24);
   KDisj (SA (EVar 2) (-96)) (ELit 96) (SA (EVar 10) 0) (ELit 24);
   KRange (EVar 33) 4096 140737488355328;
   KRange (EVar 34) 0 134217728;
   KRange (EVar 35) 1 134217728;
   KRange (EVar 43) 1 134217728;
   KRange (EVar 38) 1 134217728;
   KRange (EVar 37) 4096 140737488355328;
   KAlign (EVar 37) 16;
   KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 34)) (EAlu Instr.ALU_ADD (EVar 38) (EMd Instr.M_MUL (ELit (-1)) (EVar 43)))) 0 134217728;
   KWr (SA (EVar 37) 0) (EVar 38);
   KDisj (SA (EVar 37) 0) (EVar 38) (SA (EVar 10) 0) (ELit 24);
   KDisj (SA (EVar 37) 0) (EVar 38) (SA (EVar 2) (-96)) (ELit 96);
   KWord (SA (EVar 2) (-8)) 8 (EVar 44);
   KWord (SA (EVar 2) (-16)) 8 (EVar 45);
   KWord (SA (EVar 2) (-24)) 8 (EVar 46);
   KWord (SA (EVar 2) (-32)) 8 (EVar 10);
   KWord (SA (EVar 2) (-40)) 8 (ELit 0);
   KWord (SA (EVar 2) (-72)) 8 (ELit 235368);
   KWord (SA (EVar 2) (-80)) 8 (EVar 10);
   KWord (SA (EVar 2) (-88)) 8 (EVar 43);
   KWord (SA (EVar 2) (-96)) 8 (EVar 47);
   KWord (SA (EVar 10) 0) 8 (EVar 33);
   KWord (SA (EVar 10) 8) 8 (EAlu Instr.ALU_ADD (EVar 33) (EVar 34));
   KWord (SA (EVar 10) 16) 8 (EAlu Instr.ALU_ADD (EVar 33) (EVar 35));
   KWr (SA (EAlu Instr.ALU_ADD (EVar 34) (EVar 37)) 0) (EVar 43);
   KDisj (SA (EAlu Instr.ALU_ADD (EVar 34) (EVar 37)) 0) (EVar 43) (SA (EVar 10) 0) (ELit 24);
   KDisj (SA (EAlu Instr.ALU_ADD (EVar 34) (EVar 37)) 0) (EVar 43) (SA (EVar 2) (-96)) (ELit 96)].
Definition ss0 : sym_state := SS 235604 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-96), ELit 96); ((EAlu Instr.ALU_ADD (EVar 34) (EVar 37)), (0), (EVar 43))].
Definition F0L : list SR.region := [((EVar 2), (-96), 96)].
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
(* [comment removed for export] *)
Definition ex1 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 ss0).
Definition s1 : sym_state := snd (snd ex1).
Definition arms2 := Eval vm_compute in (SGP.case_arms s1 (EVar 34) (0)).
Definition lo2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition hi2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.
Definition ex3 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 lo2).
Definition s3 : sym_state := snd (snd ex3).
Definition LJ4 : nat := Eval vm_compute in (s_next s3).
Definition LN4 : expr := EAlu Instr.ALU_ADD (EVar 43) (ELit (-1)).
Definition inv4 : sym_state := Eval vm_compute in (lp_inv LJ4 s3 [(11%nat, EAlu Instr.ALU_SUB (EVar 998) (EVar 999)); (12%nat, EAlu Instr.ALU_ADD (EVar 998) (EVar 999))] [EAlu Instr.ALU_ADD (EVar 34) (EVar 37)]).
Definition ex5 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 (SGP.inst inv4 LJ4 LN4)).
Definition s5 : sym_state := snd (snd ex5).
Definition ex6 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 hi2).
Definition s6 : sym_state := snd (snd ex6).
Definition LJ7 : nat := Eval vm_compute in (s_next s6).
Definition LN7 : expr := EAlu Instr.ALU_ADD (EVar 43) (ELit (-1)).
Definition inv7 : sym_state := Eval vm_compute in (lp_inv LJ7 s6 [(11%nat, EAlu Instr.ALU_SUB (EVar 998) (EVar 999)); (12%nat, EAlu Instr.ALU_ADD (EVar 998) (EVar 999))] [EAlu Instr.ALU_ADD (EVar 34) (EVar 37)]).
Definition ex8 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 (SGP.inst inv7 LJ7 LN7)).
Definition s8 : sym_state := snd (snd ex8).
Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PCase (EVar 34) (0) (SGA.mkplan (fst ex3) (lp_respell [11%nat; 12%nat] (SGP.inst inv4 LJ4 (ELit 0)) (SGP.PLoop LJ4 LN4 inv4 (SGP.PStep (SR.SBlock STOPS1) (SGP.PNext)) (SGA.mkplan (fst ex5) (SGP.PEnd 0))))) (SGA.mkplan (fst ex6) (lp_respell [11%nat; 12%nat] (SGP.inst inv7 LJ7 (ELit 0)) (SGP.PLoop LJ7 LN7 inv7 (SGP.PStep (SR.SBlock STOPS1) (SGP.PNext)) (SGA.mkplan (fst ex8) (SGP.PEnd 1)))))).
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
Definition regs_out0 : list expr := Eval vm_compute in (s_regs s5).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s5).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s5 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s5 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s5).
Definition ps0 : SR.post_spec := SR.PS 701568 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.
Definition regs_out1 : list expr := Eval vm_compute in (s_regs s8).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s8).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s8 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s8 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s8).
Definition ps1 : SR.post_spec := SR.PS 701568 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_Bs_d70b56_u.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 235604 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound_it SegItab_Bs_d70b56_u.IT SegItab_Bs_d70b56_u.IT_sound BF NX0 BR XSTEP F0 PSS plan 235604 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
