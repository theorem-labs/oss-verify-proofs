(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the segment's start knowledge takes the run's CONFIG_RSEQ flag, with the auxv region 464 bytes, was 160, and the launch's auxv claims (SegAuxv.aux_kn) in place of the old twenty words, and the walk is computed in the build for each value of the flag and checked against the post spec read off the walk at the flag false, in place of the recorded walk. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Ub0PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegAuxv.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(132836, 1%nat) ; (133096, 339%nat) ; (134720, 581%nat) ; (137252, 1611%nat) ; (143880, 363%nat) ; (145428, 5%nat) ; (145808, 6%nat) ; (256344, 1%nat) ; (256628, 22%nat) ; (257316, 9%nat) ; (257528, 7%nat) ; (259768, 117%nat) ; (260312, 31%nat) ; (260536, 54%nat) ; (260824, 22%nat) ; (261808, 17%nat) ; (262228, 6%nat) ; (262364, 1%nat) ; (262432, 98%nat) ; (262920, 220%nat) ; (263996, 47%nat) ; (264924, 15%nat) ; (265108, 22%nat) ; (265288, 24%nat) ; (266356, 33%nat) ; (281584, 47%nat) ; (281848, 13%nat) ; (282052, 14%nat) ; (282352, 86%nat) ; (282828, 19%nat) ; (283220, 25%nat) ; (284192, 25%nat) ; (284388, 21%nat) ; (284652, 50%nat) ; (284920, 72%nat) ; (285288, 56%nat) ; (285624, 63%nat) ; (285988, 26%nat) ; (286192, 19%nat) ; (286368, 29%nat) ; (286588, 14%nat) ; (287048, 43%nat) ; (287360, 74%nat) ; (288080, 47%nat) ; (288388, 129%nat) ; (288992, 52%nat) ; (289312, 16%nat) ; (289604, 70%nat) ; (290048, 34%nat) ; (290344, 5%nat) ; (293400, 142%nat) ; (294112, 91%nat) ; (294992, 29%nat) ; (295360, 17%nat) ; (295704, 30%nat) ; (296216, 10%nat) ; (297076, 22%nat) ; (298364, 38%nat) ; (298684, 25%nat) ; (299140, 16%nat) ; (299492, 20%nat) ; (300128, 50%nat) ; (300600, 16%nat) ; (300764, 19%nat) ; (300996, 53%nat) ; (301600, 22%nat) ; (304572, 33%nat) ; (304808, 49%nat) ; (305292, 133%nat) ; (306552, 132%nat) ; (308388, 132%nat) ; (311632, 72%nat) ; (311984, 21%nat) ; (312384, 122%nat) ; (312976, 12%nat) ; (313100, 235%nat) ; (314132, 49%nat) ; (314408, 27%nat) ; (314596, 78%nat) ; (315004, 25%nat) ; (315456, 57%nat) ; (315788, 6%nat) ; (316068, 274%nat) ; (317232, 82%nat) ; (318248, 52%nat) ; (318592, 101%nat) ; (365600, 29%nat) ; (365876, 33%nat) ; (366284, 108%nat) ; (367008, 62%nat) ; (367464, 34%nat) ; (368556, 3%nat) ; (371628, 75%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [142416].
Definition STOPS1 : list Z := [367008; 365600] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; ELit 67584; ELit 462648; EVar 5; EVar 6; EVar 7; EVar 8; EVar 10; EVar 10; ELit 388192; ELit 256628; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 (r : bool) : list kentry := [KRange (EVar 2) 1099511627776 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-7936)) (ELit 7936);
   KRange (EVar 10) 4224 140737488355328;
   KAlign (EVar 10) 16;
   KWr (SA (EVar 10) (-128)) (ELit 144);
   KUnk (SA (EVar 10) (-128)) (ELit 128);
   KRange (EVar 32) 1099511627776 140737488355328;
   KAlign (EVar 32) 8;
   KDisj (SA (EVar 2) (-7936)) (ELit 8352) (SA (EVar 10) (-128)) (ELit 144);
   KDisj (SA (EVar 2) (-7936)) (ELit 8352) (SA (EVar 32) 0) (ELit 464);
   KDisj (SA (EVar 10) (-128)) (ELit 144) (SA (EVar 32) 0) (ELit 464);
   KDisj (SA (EVar 10) (-128)) (ELit 144) (SA (ELit 0) 65536) (ELit 532480);
   KImg 65536 393472;
   KImg 393512 393544;
   KWord (SA (ELit 0) 459776) 4 (ELit 0);
   KWr (SA (ELit 0) 459776) (ELit 4);
   KWord (SA (ELit 0) 594344) 8 (EVar 33);
   KWord (SA (ELit 0) 594384) 8 (EVar 32);
   KWr (SA (ELit 0) 462433) (ELit 6);
   KWord (SA (ELit 0) 462433) 1 (ELit 1);
   KWord (SA (ELit 0) 462434) 1 (ELit 0);
   KWord (SA (ELit 0) 462435) 1 (ELit 1);
   KWord (SA (ELit 0) 462436) 1 (ELit 0);
   KWord (SA (ELit 0) 462437) 1 (ELit 1);
   KWord (SA (ELit 0) 462438) 1 (ELit 0)]
   ++ aux_kn r 10 ++
  [KWord (SA (EVar 2) 248) 8 (EVar 40);
   KWord (SA (EVar 2) 256) 8 (EVar 41);
   KWord (SA (EVar 2) 264) 8 (EVar 42);
   KWord (SA (EVar 2) 272) 8 (EVar 43);
   KWord (SA (EVar 2) 280) 8 (EVar 44);
   KWord (SA (EVar 2) 288) 8 (EVar 45);
   KWord (SA (EVar 2) 296) 8 (EVar 46);
   KWord (SA (EVar 2) 304) 8 (EVar 47);
   KWord (SA (EVar 2) 312) 8 (EVar 48);
   KWord (SA (EVar 2) 320) 8 (EVar 49);
   KWord (SA (EVar 2) 328) 8 (EVar 50);
   KWord (SA (EVar 2) 336) 8 (EVar 51);
   KWord (SA (EVar 2) 344) 8 (ELit 140436);
   KWord (SA (EVar 2) 384) 8 (EVar 52);
   KWord (SA (EVar 2) 392) 8 (ELit 134416);
   KWord (SA (EVar 2) 400) 8 (EVar 53);
   KWord (SA (EVar 2) 408) 8 (ELit 133204)].
Definition ss0 (r : bool) : sym_state := SS 142392 regs0 [] (kn0 r) NX0.
Definition F0 : list SGP.region := [(EVar 2, (-7936), ELit 7936); (EVar 10, (-120), ELit 40); (EVar 10, (-68), ELit 68); (ELit 0, (459776), ELit 4); (ELit 0, (462433), ELit 6)].
Definition F0L : list SR.region := [(EVar 2, (-7936), 7936); (EVar 10, (-120), 40); (EVar 10, (-68), 68); (ELit 0, (459776), 4); (ELit 0, (462433), 6)].
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
Definition ps0 : SR.post_spec := SR.PS 142416 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert (r : bool) : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS (plan r) 142392 regs0 (kn0 r) = true.
Proof. destruct r; vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax (r : bool) := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS (plan r) 142392 regs0 (kn0 r) (cert r) (SGP.xstep_none_ok RSEGS NX0 BR F0).
