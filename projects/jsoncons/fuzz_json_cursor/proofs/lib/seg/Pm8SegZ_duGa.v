(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Pm8PlanKit.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(455824, 54%nat) ; (716004, 177%nat) ; (1259116, 18%nat) ; (1292244, 100%nat) ; (1296156, 108%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [1261176].
Definition STOPS1 : list Z := [1261176] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 0; ELit 1407328; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 118; EVar 119; EVar 120; ELit 7015056; EVar 122; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332552704 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-16)) (ELit 16);
   KUnk (SA (EVar 2) (-16)) (ELit 16);
   KImg 65536 1392640;
   KRange (EVar 33) 140735332552704 140737488355311;
   KRange (EVar 34) 0 66;
   KDisj (SA (EVar 2) (-16)) (ELit 16) (SA (EVar 33) 0) (EAlu Instr.ALU_ADD (EVar 34) (ELit 1));
   KWr (SA (ELit 0) (1407328)) (ELit 4);
   KWr (SA (ELit 0) (1407360)) (ELit 8);
   KWr (SA (ELit 0) (1407368)) (ELit 8);
   KWr (SA (ELit 0) (1407384)) (ELit 8);
   KWr (SA (ELit 0) (1407416)) (ELit 8);
   KWr (SA (ELit 0) (1407424)) (ELit 8);
   KWord (SA (ELit 0) (1407416)) 8 ((EAlu Instr.ALU_ADD (EVar 2) (ELit (128))));
   KWord (SA (ELit 0) (1407424)) 8 (ELit 80);
   KWord (SA (ELit 0) (7015056)) 8 (EVar 40);
   KWord (SA (EVar 2) (40)) 8 (EVar 40);
   KWord (SA (EVar 2) (104)) 8 (ELit 1296452);
   KWord (SA (EVar 2) (96)) 8 (ELit 1407328);
   KWord (SA (EVar 2) (88)) 8 ((EAlu Instr.ALU_ADD (EVar 34) (ELit (14))));
   KWord (SA (EVar 2) (80)) 8 (ELit 7015056);
   KWord (SA (EVar 2) (72)) 8 (ELit 1);
   KWord (SA (EVar 2) (64)) 8 (ELit 7017064);
   KWord (SA (EVar 2) (56)) 8 (ELit 0);
   KWord (SA (EVar 2) (48)) 8 (EVar 22);
   KWord (SA (ELit 0) (1407328)) 4 (ELit 5);
   KWord (SA (EVar 2) (416)) 8 (EVar 40);
   KWord (SA (EVar 2) (472)) 8 (ELit 456016);
   KWord (SA (EVar 2) (464)) 8 (ELit 91464);
   KWord (SA (EVar 2) (456)) 8 (ELit 1407328);
   KWord (SA (EVar 2) (448)) 8 ((EAlu Instr.ALU_ADD (EVar 2) (ELit (544))));
   KWord (SA (EVar 2) (440)) 8 (EVar 19);
   KWord (SA (EVar 2) (432)) 8 (EVar 20);
   KWord (SA (EVar 2) (424)) 8 (EVar 21);
   KWord (SA (EVar 2) (536)) 8 (ELit 716440);
   KWord (SA (EVar 2) (528)) 8 (EVar 8);
   KWord (SA (EVar 2) (520)) 8 (EVar 9);
   KWord (SA (EVar 2) (512)) 8 (EVar 18);
   KWord (SA (EVar 2) (664)) 8 (ELit 1259184);
   KWord (SA (EVar 2) (656)) 8 (EVar 41);
   KWord (SA (EVar 2) (648)) 8 (EVar 42);
   KWord (SA (EVar 2) (640)) 8 (EVar 43);
   KWord (SA (EVar 2) (632)) 8 (EVar 44);
   KWord (SA (EVar 2) (624)) 8 (EVar 45);
   KWord (SA (EVar 2) (616)) 8 (EVar 46);
   KWord (SA (EVar 2) (608)) 8 (EVar 47);
   KWord (SA (EVar 2) (600)) 8 (EVar 48)].
Definition ss0 : sym_state := SS 1292392 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-16), ELit 16); (ELit 0, (1407328), ELit 4); (ELit 0, (1407360), ELit 8); (ELit 0, (1407368), ELit 8); (ELit 0, (1407384), ELit 8); (ELit 0, (1407416), ELit 8); (ELit 0, (1407424), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-16), 16); (ELit 0, (1407328), 4); (ELit 0, (1407360), 8); (ELit 0, (1407368), 8); (ELit 0, (1407384), 8); (ELit 0, (1407416), 8); (ELit 0, (1407424), 8)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) :=
  (([SGA.AStep (SR.SBlock [1261176; 1261176])], (93, SS 1261176 [ELit 0; ELit 1259188; EAlu Instr.ALU_ADD (EVar 2) (ELit 672); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 41; EVar 42; EVar 8; EVar 40; EVar 40; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 43; EVar 44; EVar 45; EVar 46; EVar 47; EVar 48; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := ELit 0; a_off := 1407328 |} 4 (ELit 5); KWord {| a_base := ELit 0; a_off := 1407424 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1407416 |} 8 (ELit 7017064); KWord {| a_base := ELit 0; a_off := 1407384 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1407368 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1407360 |} 8 (ELit 0); KRange (EVar 2) 140735332552704 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -16 |} (ELit 16); KUnk {| a_base := EVar 2; a_off := -16 |} (ELit 16); KImg 65536 1392640; KRange (EVar 33) 140735332552704 140737488355311; KRange (EVar 34) 0 66; KDisj {| a_base := EVar 2; a_off := -16 |} (ELit 16) {| a_base := EVar 33; a_off := 0 |} (EAlu Instr.ALU_ADD (EVar 34) (ELit 1)); KWr {| a_base := ELit 0; a_off := 1407328 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 1407360 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 1407368 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 1407384 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 1407416 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 1407424 |} (ELit 8); KWord {| a_base := ELit 0; a_off := 7015056 |} 8 (EVar 40); KWord {| a_base := EVar 2; a_off := 40 |} 8 (EVar 40); KWord {| a_base := EVar 2; a_off := 104 |} 8 (ELit 1296452); KWord {| a_base := EVar 2; a_off := 96 |} 8 (ELit 1407328); KWord {| a_base := EVar 2; a_off := 88 |} 8 (EAlu Instr.ALU_ADD (EVar 34) (ELit 14)); KWord {| a_base := EVar 2; a_off := 80 |} 8 (ELit 7015056); KWord {| a_base := EVar 2; a_off := 72 |} 8 (ELit 1); KWord {| a_base := EVar 2; a_off := 64 |} 8 (ELit 7017064); KWord {| a_base := EVar 2; a_off := 56 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := 48 |} 8 (EVar 22); KWord {| a_base := EVar 2; a_off := 416 |} 8 (EVar 40); KWord {| a_base := EVar 2; a_off := 472 |} 8 (ELit 456016); KWord {| a_base := EVar 2; a_off := 464 |} 8 (ELit 91464); KWord {| a_base := EVar 2; a_off := 456 |} 8 (ELit 1407328); KWord {| a_base := EVar 2; a_off := 448 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit 544)); KWord {| a_base := EVar 2; a_off := 440 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := 432 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := 424 |} 8 (EVar 21); KWord {| a_base := EVar 2; a_off := 536 |} 8 (ELit 716440); KWord {| a_base := EVar 2; a_off := 528 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := 520 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := 512 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := 664 |} 8 (ELit 1259184); KWord {| a_base := EVar 2; a_off := 656 |} 8 (EVar 41); KWord {| a_base := EVar 2; a_off := 648 |} 8 (EVar 42); KWord {| a_base := EVar 2; a_off := 640 |} 8 (EVar 43); KWord {| a_base := EVar 2; a_off := 632 |} 8 (EVar 44); KWord {| a_base := EVar 2; a_off := 624 |} 8 (EVar 45); KWord {| a_base := EVar 2; a_off := 616 |} 8 (EVar 46); KWord {| a_base := EVar 2; a_off := 608 |} 8 (EVar 47); KWord {| a_base := EVar 2; a_off := 600 |} 8 (EVar 48)] 140))).
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
Definition ps0 : SR.post_spec := SR.PS 1261176 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1292392 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 1292392 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
