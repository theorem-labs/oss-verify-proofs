(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0PlanKit_b Ba0PlanKitIt_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require SegItab_Ba_9d9840_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require SegPlanFast.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Ba_9d9840_b.ITR.
Definition IT : itab := SegItab_Ba_9d9840_b.IT.
Definition ENDS : list Z := [689688].
Definition STOPS1 : list Z := [689688] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 58; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-128))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-128))); EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; (EVar 40); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 40) (ELit 3)) (ELit (2147450880))); (EAlu Instr.ALU_ADD (EVar 40) (ELit (32))); (EAlu Instr.ALU_ADD (EVar 40) (ELit (96))); (EAlu Instr.ALU_ADD (EVar 40) (ELit (464))); (EAlu Instr.ALU_ADD (EVar 40) (ELit (1024))); (EVar 40); ELit 2147450880; ELit 18446744073709551608; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332487360 140737488355328;
   KAlign (EVar 2) 32;
   KWr (SA (EVar 2) (-128)) (ELit 128);
   KImg 1249280 1282048;
   KWord (SA (ELit 0) 1309752) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1309760) 4 (ELit 1);
   KRange (EVar 40) 4096 140737488353280;
   KAlign (EVar 40) 32;
   KUnk (SA (EVar 40) 0) (ELit 2048);
   KWr (SA (EVar 40) 0) (ELit 2048);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 40) 0) (ELit 2048);
   KWr (SA (EAlu Instr.ALU_SRL (EVar 40) (ELit 3)) 2147450880) (ELit 256);
   KWord (SA (EVar 40) 2040) 8 (EVar 41);
   KRange (EVar 41) 4096 140737488355327;
   KWr (SA (EVar 41) 0) (ELit 1);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 41) 0) (ELit 1);
   KDisj (SA (EVar 40) 0) (ELit 2048) (SA (EVar 41) 0) (ELit 1);
   KDisj (SA (EVar 2) (-128)) (ELit 144) (SA (EVar 40) 0) (ELit 2048);
   KDisj (SA (EVar 2) (-128)) (ELit 144) (SA (EVar 41) 0) (ELit 1);
   KDisj (SA (ELit 0) 65536) (ELit 6840320) (SA (EVar 40) 0) (ELit 2048);
   KDisj (SA (ELit 0) 65536) (ELit 6840320) (SA (EVar 41) 0) (ELit 1)].
Definition ss0 : sym_state := SS 689460 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_SRL (EVar 40) (ELit 3)), (2147450934), ELit 1); ((EAlu Instr.ALU_SRL (EVar 40) (ELit 3)), (2147450938), ELit 53)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_SRL (EVar 40) (ELit 3)), (2147450934), 1); ((EAlu Instr.ALU_SRL (EVar 40) (ELit 3)), (2147450938), 53)].
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
Definition ex1 : list SGA.aitem * (Z * sym_state) :=
  (([SGA.AStep (SR.SBlock [689688; 689688])], (93, SS 689688 [ELit 0; EVar 58; EAlu Instr.ALU_ADD (EVar 2) (ELit (-128)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EAlu Instr.ALU_ADD (EVar 2) (ELit (-128)); ELit 18446744073709551608; ELit 1279288; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 40; EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 40) (ELit 3)) (ELit 2147450880); EAlu Instr.ALU_ADD (EVar 40) (ELit 32); EAlu Instr.ALU_ADD (EVar 40) (ELit 96); ELit 1266024; EAlu Instr.ALU_ADD (EVar 40) (ELit 1024); EVar 40; ELit 2147450880; ELit 18446744073709551608; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450990 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450989 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450988 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450987 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450986 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450985 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450980 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450979 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450978 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450977 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450984 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450983 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450982 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450981 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450972 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450971 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450970 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450969 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450976 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450975 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450974 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450973 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450964 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450963 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450962 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450961 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450968 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450967 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450966 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450965 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450956 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450955 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450954 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450953 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450960 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450959 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450958 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450957 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450948 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450947 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450946 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450945 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450952 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450951 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450950 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450949 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450940 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450939 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450938 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450934 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450944 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450943 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450942 |} 1 (ELit 18446744073709551608); KWord {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450941 |} 1 (ELit 18446744073709551608); KRange (EVar 2) 140735332487360 140737488355328; KAlign (EVar 2) 32; KWr {| a_base := EVar 2; a_off := -128 |} (ELit 128); KImg 1249280 1282048; KWord {| a_base := ELit 0; a_off := 1309752 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1309760 |} 4 (ELit 1); KRange (EVar 40) 4096 140737488353280; KAlign (EVar 40) 32; KUnk {| a_base := EVar 40; a_off := 0 |} (ELit 2048); KWr {| a_base := EVar 40; a_off := 0 |} (ELit 2048); KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EVar 40; a_off := 0 |} (ELit 2048); KWr {| a_base := EAlu Instr.ALU_SRL (EVar 40) (ELit 3); a_off := 2147450880 |} (ELit 256); KWord {| a_base := EVar 40; a_off := 2040 |} 8 (EVar 41); KRange (EVar 41) 4096 140737488355327; KWr {| a_base := EVar 41; a_off := 0 |} (ELit 1); KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EVar 41; a_off := 0 |} (ELit 1); KDisj {| a_base := EVar 40; a_off := 0 |} (ELit 2048) {| a_base := EVar 41; a_off := 0 |} (ELit 1); KDisj {| a_base := EVar 2; a_off := -128 |} (ELit 144) {| a_base := EVar 40; a_off := 0 |} (ELit 2048); KDisj {| a_base := EVar 2; a_off := -128 |} (ELit 144) {| a_base := EVar 41; a_off := 0 |} (ELit 1); KDisj {| a_base := ELit 0; a_off := 65536 |} (ELit 6840320) {| a_base := EVar 40; a_off := 0 |} (ELit 2048); KDisj {| a_base := ELit 0; a_off := 65536 |} (ELit 6840320) {| a_base := EVar 41; a_off := 0 |} (ELit 1)] 64))).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
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
Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 689688 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_Ba_9d9840_b.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 689460 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := as0_plan_sound_it SegItab_Ba_9d9840_b.IT SegItab_Ba_9d9840_b.IT_sound BF NX0 BR XSTEP F0 PSS plan 689460 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
