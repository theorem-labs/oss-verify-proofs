(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Pm9PlanKit.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(436532, 1%nat) ; (445820, 157%nat) ; (558724, 40%nat) ; (1297808, 100%nat) ; (1300276, 21%nat) ; (1300360, 78%nat) ; (1300672, 46%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [1297944].
Definition STOPS1 : list Z := [1297944] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; ELit 717464; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; ELit 91029; ELit 31; ELit 1; ELit 1412392; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332552704 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-2304)) (ELit 2304);
   KUnk (SA (EVar 2) (-2304)) (ELit 2304);
   KImg 65536 1400832;
   KWr (SA (ELit 0) (1412400)) (ELit 8);
   KWr (SA (ELit 0) (1412408)) (ELit 8);
   KWr (SA (ELit 0) (1412424)) (ELit 8);
   KWr (SA (ELit 0) (1412432)) (ELit 8);
   KWr (SA (ELit 0) (1412448)) (ELit 8);
   KWr (SA (ELit 0) (1412528)) (ELit 4);
   KWord (SA (ELit 0) (1436120)) 1 (ELit 1);
   KWord (SA (ELit 0) (1401720)) 8 (ELit 1300672);
   KWord (SA (ELit 0) (1412532)) 4 (ELit 4294967295);
   KWord (SA (ELit 0) (1412424)) 8 (ELit 0);
   KWord (SA (ELit 0) (1412528)) 4 (ELit 0);
   KWord (SA (ELit 0) (1412392)) 4 (ELit 5);
   KWord (SA (ELit 0) (1412480)) 8 (ELit 7021992);
   KWord (SA (ELit 0) (1412488)) 8 (ELit 0);
   KWord (SA (ELit 0) (1412464)) 8 (ELit 1297808);
   KWord (SA (ELit 0) (7019984)) 8 (EVar 40);
   KWord (SA (ELit 0) (1412512)) 4 (ELit 2)].
Definition ss0 : sym_state := SS 436532 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-2304), ELit 2304); (ELit 0, (1412400), ELit 8); (ELit 0, (1412408), ELit 8); (ELit 0, (1412424), ELit 8); (ELit 0, (1412432), ELit 8); (ELit 0, (1412448), ELit 8); (ELit 0, (1412528), ELit 4)].
Definition F0L : list SR.region := [(EVar 2, (-2304), 2304); (ELit 0, (1412400), 8); (ELit 0, (1412408), 8); (ELit 0, (1412424), 8); (ELit 0, (1412432), 8); (ELit 0, (1412448), 8); (ELit 0, (1412528), 4)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) :=
  (([SGA.AStep (SR.SBlock [1297944; 1297944])], (93, SS 1297944 [ELit 0; ELit 1300808; EAlu Instr.ALU_ADD (EVar 2) (ELit (-2304)); EVar 3; EVar 4; EVar 5; ELit 1297808; EVar 7; ELit 31; ELit 1412392; ELit 2; EAlu Instr.ALU_ADD (EVar 2) (ELit (-2280)); ELit 1; ELit 0; ELit 1300672; EVar 15; EVar 16; ELit 66; ELit 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-2280)); ELit 1; ELit 7019984; ELit 31; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -2272 |} 8 (ELit 31); KWord {| a_base := EVar 2; a_off := -2280 |} 8 (ELit 91029); KWord {| a_base := EVar 2; a_off := -2288 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -2296 |} 8 (ELit 7021992); KWord {| a_base := EVar 2; a_off := -2264 |} 8 (EVar 40); KWord {| a_base := EVar 2; a_off := -2256 |} 8 (EVar 22); KWord {| a_base := EVar 2; a_off := -2248 |} 8 (ELit 1); KWord {| a_base := EVar 2; a_off := -2240 |} 8 (ELit 1); KWord {| a_base := EVar 2; a_off := -2232 |} 8 (ELit 1412392); KWord {| a_base := EVar 2; a_off := -2224 |} 8 (ELit 31); KWord {| a_base := EVar 2; a_off := -2216 |} 8 (ELit 31); KWord {| a_base := EVar 2; a_off := -2208 |} 8 (ELit 1); KWord {| a_base := EVar 2; a_off := -2200 |} 8 (ELit 1300808); KWord {| a_base := ELit 0; a_off := 1412432 |} 8 (ELit 7021992); KWord {| a_base := ELit 0; a_off := 1412424 |} 8 (ELit 7021992); KWord {| a_base := ELit 0; a_off := 1412408 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1412400 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1412448 |} 8 (ELit 7021992); KWord {| a_base := ELit 0; a_off := 1412528 |} 4 (ELit 18446744073709551615); KWord {| a_base := EVar 2; a_off := -2184 |} 8 (ELit 1); KWord {| a_base := EVar 2; a_off := -2176 |} 8 (ELit 1); KWord {| a_base := EVar 2; a_off := -2168 |} 8 (ELit 1412392); KWord {| a_base := EVar 2; a_off := -2160 |} 8 (ELit 91029); KWord {| a_base := EVar 2; a_off := -2152 |} 8 (ELit 31); KWord {| a_base := EVar 2; a_off := -2144 |} 8 (EVar 2); KWord {| a_base := EVar 2; a_off := -2136 |} 8 (ELit 445912); KWord {| a_base := EVar 2; a_off := -56 |} 8 (EVar 21); KWord {| a_base := EVar 2; a_off := -48 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (ELit 717464); KRange (EVar 2) 140735332552704 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -2304 |} (ELit 2304); KUnk {| a_base := EVar 2; a_off := -2304 |} (ELit 8); KUnk {| a_base := EVar 2; a_off := -2192 |} (ELit 8); KUnk {| a_base := EVar 2; a_off := -2128 |} (ELit 2072); KImg 65536 1400832; KWr {| a_base := ELit 0; a_off := 1412400 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 1412408 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 1412424 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 1412432 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 1412448 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 1412528 |} (ELit 4); KWord {| a_base := ELit 0; a_off := 1436120 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1401720 |} 8 (ELit 1300672); KWord {| a_base := ELit 0; a_off := 1412532 |} 4 (ELit 4294967295); KWord {| a_base := ELit 0; a_off := 1412392 |} 4 (ELit 5); KWord {| a_base := ELit 0; a_off := 1412480 |} 8 (ELit 7021992); KWord {| a_base := ELit 0; a_off := 1412488 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1412464 |} 8 (ELit 1297808); KWord {| a_base := ELit 0; a_off := 7019984 |} 8 (EVar 40); KWord {| a_base := ELit 0; a_off := 1412512 |} 4 (ELit 2)] 56))).
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
Definition ps0 : SR.post_spec := SR.PS 1297944 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 436532 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 436532 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
