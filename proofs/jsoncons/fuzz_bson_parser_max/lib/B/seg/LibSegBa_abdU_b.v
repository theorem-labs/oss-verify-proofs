(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0PlanKit_b Ba0PlanKitIt_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require SegItab_Ba_20fe7e_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require SegPlanFast.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Ba_20fe7e_b.ITR.
Definition IT : itab := SegItab_Ba_20fe7e_b.IT.
Definition ENDS : list Z := [715700].
Definition STOPS1 : list Z := [] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-224))); (EVar 3); (EVar 4); EVar 5; EVar 6; EVar 7; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-112))); (EAlu Instr.ALU_ADD (EVar 2) (ELit (-116))); EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-120))); (ELit 2147450880); (EVar 50); (EVar 36); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit 400)) (ELit 3)) (ELit 2147450880)); (EVar 34); (EAlu Instr.ALU_ADD (EVar 50) (ELit 32)); (EVar 50); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit 2147450880)); (ELit 2147450880); EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KImg 65536 1282048;
    KWord (SA (ELit 0) 1309752) 8 (ELit 2147450880);
    KWord (SA (ELit 0) 1309760) 4 (ELit 1);
    KRange (EVar 2) 140735332487296 140737488355328;
    KAlign (EVar 2) 32;
    KWr (SA (EVar 2) (-224)) (ELit 224);
    KRange (EVar 33) 6905856 140737488354912;
    KAlign (EVar 33) 8;
    KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 33) 0) (ELit 416);
    KZero (SA (EAlu Instr.ALU_SRL (EVar 33) (ELit 3)) 2147450880) (ELit 2);
    KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit (10))) (ELit 3)) 2147450880) (ELit 1);
    KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit (312))) (ELit 3)) 2147450880) (ELit 1);
    KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit (392))) (ELit 3)) 2147450880) (ELit 3);
    KDisj (SA (EVar 2) (-224)) (ELit 224) (SA (EVar 33) 0) (ELit 416);
    KRange (EVar 50) 6905856 140737488355264;
    KAlign (EVar 50) 32;
    KUnk (SA (EVar 50) 0) (ELit 64);
    KWr (SA (EVar 50) 0) (ELit 64);
    KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 50) 0) (ELit 64);
    KWr (SA (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) 2147450880) (ELit 8);
    KWord (SA (EVar 50) 56) 8 (EVar 51);
    KRange (EVar 51) 4096 140737488355327;
    KWr (SA (EVar 51) 0) (ELit 1);
    KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 51) 0) (ELit 1);
    KDisj (SA (EVar 50) 0) (ELit 64) (SA (EVar 51) 0) (ELit 1);
    KDisj (SA (EVar 2) (-224)) (ELit 224) (SA (EVar 50) 0) (ELit 64);
    KDisj (SA (EVar 2) (-224)) (ELit 224) (SA (EVar 51) 0) (ELit 1);
    KDisj (SA (EVar 33) 0) (ELit 416) (SA (EVar 50) 0) (ELit 64);
    KDisj (SA (EVar 33) 0) (ELit 416) (SA (EVar 51) 0) (ELit 1);
    KDisj (SA (EAlu Instr.ALU_SRL (EVar 33) (ELit 3)) 2147450880) (ELit 52) (SA (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) 2147450880) (ELit 8);
    KRange (EVar 34) 6905856 140737488355320;
    KAlign (EVar 34) 8;
    KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 34) 0) (ELit 8);
    KZero (SA (EAlu Instr.ALU_SRL (EVar 34) (ELit 3)) 2147450880) (ELit 1);
    KDisj (SA (EVar 2) (-224)) (ELit 224) (SA (EVar 34) 0) (ELit 8);
    KDisj (SA (EVar 33) 0) (ELit 416) (SA (EVar 34) 0) (ELit 8);
    KDisj (SA (EVar 50) 0) (ELit 64) (SA (EVar 34) 0) (ELit 8);
    KDisj (SA (EVar 51) 0) (ELit 1) (SA (EVar 34) 0) (ELit 8);
    KWord (SA (EVar 34) 0) 8 (ELit 1251456);
    KZero (SA (ELit 0) 2147607320) (ELit 1);
    KDisj (SA (EAlu Instr.ALU_SRL (EVar 34) (ELit 3)) 2147450880) (ELit 1) (SA (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) 2147450880) (ELit 8);
    KWord (SA (EVar 50) 32) 4 (EVar 46);
    KRange (EVar 46) 0 4294967295;
    KWr (SA (EVar 33) 8) (ELit 1);
    KWord (SA (EVar 33) 10) 1 (ELit 0);
    KWord (SA (EVar 33) 392) 8 (EVar 41);
    KWord (SA (EVar 33) 400) 8 (EAlu Instr.ALU_ADD (EVar 41) (EVar 42));
    KWord (SA (EVar 33) 408) 8 (EAlu Instr.ALU_ADD (EVar 41) (EVar 43));
    KRange (EVar 41) 4096 140737488314328;
    KAlign (EVar 41) 8;
    KRange (EVar 42) 40 41000;
    KAlign (EVar 42) 8;
    KRange (EVar 43) 40 81920;
    KAlign (EVar 43) 8;
    KWord (SA (EVar 2) (-136)) 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 392));
    KWord (SA (EVar 2) (-144)) 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 400));
    KWord (SA (EVar 2) (-208)) 8 (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 41) (EVar 42)) (ELit 40));
    KWord (SA (EVar 2) (-216)) 8 (EAlu Instr.ALU_ADD (EVar 41) (EVar 42));
    KWord (SA (EVar 2) (-224)) 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 392));
    KWord (SA (EVar 2) (-200)) 8 (EAlu Instr.ALU_ADD (EVar 41) (EVar 42));
    KWord (SA (EVar 2) (-192)) 8 (EVar 50);
    KWord (SA (EVar 2) (-184)) 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-160)));
    KWord (SA (EVar 2) (-176)) 8 (EVar 2);
    KWord (SA (EVar 2) (-168)) 8 (ELit 715660);
    KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_ADD (EVar 41) (EVar 42)) (EAlu Instr.ALU_ADD (EVar 41) (EVar 43))) 1 1;
    KWord (SA (EVar 2) (-120)) 4 (ELit 2);
    KWord (SA (EVar 2) (-112)) 8 (ELit 4);
    KWord (SA (EVar 33) 8) 1 (ELit 1);
    KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 2) (ELit (-120))) (ELit 3)) 2147450880) (ELit 1);
    KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 2) (ELit (-116))) (ELit 3)) 2147450880) (ELit 1);
    KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 2) (ELit (-112))) (ELit 3)) 2147450880) (ELit 1);
    KWr (SA (EVar 2) (-240)) (ELit 240);
    KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 2) (ELit (-224))) (ELit 3)) 2147450880) (ELit 1);
    KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 2) (ELit (-216))) (ELit 3)) 2147450880) (ELit 1);
    KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 2) (ELit (-208))) (ELit 3)) 2147450880) (ELit 1);
    KDisj (SA (EVar 2) (-240)) (ELit 240) (SA (EVar 33) 0) (ELit 416);
    KDisj (SA (EVar 2) (-240)) (ELit 240) (SA (EVar 50) 0) (ELit 64);
    KDisj (SA (EVar 2) (-240)) (ELit 240) (SA (EVar 51) 0) (ELit 1);
    KDisj (SA (EVar 2) (-240)) (ELit 240) (SA (EVar 34) 0) (ELit 8);
    KWr (SA (EVar 33) 392) (ELit 24);
    KWord (SA (EVar 2) (-128)) 8 (EVar 50);
    KWord (SA (EVar 2) (-8)) 8 (EVar 60);
    KWord (SA (EVar 2) (-16)) 8 (EVar 61);
    KWord (SA (EVar 2) (-24)) 8 (EVar 62);
    KWord (SA (EVar 2) (-32)) 8 (EVar 63);
    KWord (SA (EVar 2) (-40)) 8 (EVar 64);
    KWord (SA (EVar 2) (-48)) 8 (EVar 65);
    KWord (SA (EVar 2) (-56)) 8 (EVar 66);
    KWord (SA (EVar 2) (-64)) 8 (EVar 67);
    KWord (SA (EVar 2) (-72)) 8 (EVar 68);
    KWord (SA (EVar 2) (-80)) 8 (EVar 69);
    KWord (SA (EVar 2) (-88)) 8 (EVar 70);
    KWord (SA (EVar 2) (-96)) 8 (EVar 71);
    KWord (SA (EVar 2) (-104)) 8 (EVar 72);
    KWr (SA (EVar 2) (-160)) (ELit 160);
    KDisj (SA (EVar 2) (-160)) (ELit 160) (SA (EVar 33) 0) (ELit 416);
    KDisj (SA (EVar 2) (-160)) (ELit 160) (SA (EVar 50) 0) (ELit 64);
    KDisj (SA (EVar 2) (-160)) (ELit 160) (SA (EVar 51) 0) (ELit 1);
    KRange (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 41) (EVar 42)) (ELit 40)) 4136 140737488355327;
    KAlign (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 41) (EVar 42)) (ELit 40)) 8;
    KDisj (SA (ELit 0) 65536) (ELit 6840320) (SA (EAlu Instr.ALU_ADD (EVar 41) (EVar 42)) 0) (ELit 40);
    KRange (EAlu Instr.ALU_ADD (EVar 41) (EVar 42)) 4136 140737488355287;
    KWr (SA (EAlu Instr.ALU_ADD (EVar 41) (EVar 42)) 0) (ELit 40);
    KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 41) (EVar 42)) (ELit 3)) 2147450880) (ELit 1);
    KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 41) (EVar 42)) (ELit 8)) (ELit 3)) 2147450880) (ELit 1);
    KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 41) (EVar 42)) (ELit 16)) (ELit 3)) 2147450880) (ELit 1);
    KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 41) (EVar 42)) (ELit 24)) (ELit 3)) 2147450880) (ELit 1);
    KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 41) (EVar 42)) (ELit 32)) (ELit 3)) 2147450880) (ELit 1);
    KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EAlu Instr.ALU_ADD (EVar 41) (EVar 42)) 0) (ELit 40);
    KDisj (SA (EVar 2) (-240)) (ELit 240) (SA (EAlu Instr.ALU_ADD (EVar 41) (EVar 42)) 0) (ELit 40);
    KDisj (SA (EVar 33) 0) (ELit 416) (SA (EAlu Instr.ALU_ADD (EVar 41) (EVar 42)) 0) (ELit 40);
    KDisj (SA (EVar 50) 0) (ELit 64) (SA (EAlu Instr.ALU_ADD (EVar 41) (EVar 42)) 0) (ELit 40);
    KDisj (SA (EVar 51) 0) (ELit 1) (SA (EAlu Instr.ALU_ADD (EVar 41) (EVar 42)) 0) (ELit 40);
    KDisj (SA (EVar 34) 0) (ELit 8) (SA (EAlu Instr.ALU_ADD (EVar 41) (EVar 42)) 0) (ELit 40)].
Definition ss0 : sym_state := SS 730612 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_ADD (EVar 41) (EVar 42)), (0), ELit 40); ((EVar 33), (400), ELit 8); ((EVar 2), (-240), ELit 80)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_ADD (EVar 41) (EVar 42)), (0), 40); ((EVar 33), (400), 8); ((EVar 2), (-240), 80)].
Definition BF : nat := 1000.
Definition BR : list SGP.bfact := [].
Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 ss0).
Definition s1 : sym_state := snd (snd ex1).
Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 715700 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_Ba_20fe7e_b.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 730612 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it SegItab_Ba_20fe7e_b.IT SegItab_Ba_20fe7e_b.IT_sound BF NX0 BR XSTEP F0 PSS plan 730612 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
