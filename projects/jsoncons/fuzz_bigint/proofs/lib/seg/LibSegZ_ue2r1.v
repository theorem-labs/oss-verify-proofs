(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the segment's start knowledge takes the run's CONFIG_RSEQ flag, with the auxv region 464 bytes, was 160, and the launch's auxv claims (SegAuxv.aux_kn) in place of the old twenty words, and the walk is computed in the build for each value of the flag and checked against the post spec read off the walk at the flag false, in place of the recorded walk. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin SegPlanAutoX As0PlanKit As0PlanKitIt XIcptA XIcptAs0Kit.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require SegItab_A_fa86c0.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegAuxv.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_A_fa86c0.ITR.
Definition IT : itab := SegItab_A_fa86c0.IT.
Definition ENDS : list Z := [598052].
Definition STOPS1 : list Z := [385224; 385232; 318384; 392280; 392276; 392288; 422120; 318480; 385228] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; ELit 67584; ELit 6360328; EVar 5; EVar 6; EVar 7; EAlu Instr.ALU_ADD (EVar 2) (ELit (352)); EVar 9; EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)); EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 (r : bool) : list kentry := [KRange (EVar 2) 140735332552704 140737488355264;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-10560)) (ELit 10560);
   KUnk (SA (EVar 2) (-10560)) (ELit 10560);
   KRange (EVar 10) 4224 140737488355328;
   KAlign (EVar 10) 16;
   KWr (SA (EVar 10) (-128)) (ELit 144);
   KUnk (SA (EVar 10) (-128)) (ELit 144);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (-128)) (ELit 144);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) (2147450864)) (ELit 18);
   KRange (EVar 32) 1099511627776 140737488355328;
   KAlign (EVar 32) 8;
   KDisj (SA (EVar 2) (-10560)) (ELit 14656) (SA (EVar 10) (-128)) (ELit 144);
   KDisj (SA (EVar 10) (-128)) (ELit 144) (SA (EVar 32) 0) (ELit 464);
   KDisj (SA (EVar 10) (-128)) (ELit 144) (SA (EVar 40) 0) (ELit 160);
   KDisj (SA (EVar 10) (-128)) (ELit 144) (SA (EVar 41) 0) (ELit 64);
   KDisj (SA (EVar 10) (-128)) (ELit 144) (SA (EVar 42) 0) (ELit 4096);
   KDisj (SA (EVar 2) (-10560)) (ELit 11008) (SA (EVar 32) 0) (ELit 464);
   KDisj (SA (EVar 32) 0) (ELit 464) (SA (EVar 40) 0) (ELit 160);
   KDisj (SA (EVar 32) 0) (ELit 464) (SA (EVar 41) 0) (ELit 64);
   KDisj (SA (EVar 32) 0) (ELit 464) (SA (EVar 42) 0) (ELit 4096);
   KDisj (SA (EVar 2) (-10560)) (ELit 14656) (SA (EVar 40) 0) (ELit 160);
   KDisj (SA (EVar 40) 0) (ELit 160) (SA (EVar 41) 0) (ELit 64);
   KDisj (SA (EVar 40) 0) (ELit 160) (SA (EVar 42) 0) (ELit 4096);
   KDisj (SA (EVar 2) (-10560)) (ELit 14656) (SA (EVar 41) 0) (ELit 64);
   KDisj (SA (EVar 41) 0) (ELit 64) (SA (EVar 42) 0) (ELit 4096);
   KDisj (SA (EVar 2) (-10560)) (ELit 14656) (SA (EVar 42) 0) (ELit 4096);
   KDisj (SA (EVar 10) (-128)) (ELit 144) (SA (ELit 0) 65536) (ELit 6434816);
   KDisj (SA (EVar 40) 0) (ELit 160) (SA (ELit 0) 65536) (ELit 6434816);
   KDisj (SA (EVar 41) 0) (ELit 64) (SA (ELit 0) 65536) (ELit 6434816);
   KDisj (SA (EVar 42) 0) (ELit 4096) (SA (ELit 0) 65536) (ELit 6434816);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 2) (ELit 3)) (2147449560)) (ELit 1320);
   KImg 65536 880640;
   KImg 892736 892768;
   KWord (SA (ELit 0) 874680) 8 (ELit 908088);
   KWord (SA (ELit 0) 908088) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 874688) 8 (ELit 911400);
   KWord (SA (ELit 0) 911400) 8 (ELit 0);
   KWord (SA (ELit 0) 874696) 8 (ELit 911408);
   KWord (SA (ELit 0) 911408) 8 (ELit 0);
   KWord (SA (ELit 0) 874704) 8 (ELit 911392);
   KWord (SA (ELit 0) 911392) 8 (ELit 140737488355327);
   KWord (SA (ELit 0) 877600) 8 (ELit 911385);
   KWord (SA (ELit 0) 911385) 1 (ELit 1);
   KWord (SA (ELit 0) 882712) 8 (ELit 834348);
   KWord (SA (ELit 0) 882704) 8 (ELit 833320);
   KWord (SA (ELit 0) 911384) 1 (ELit 1);
   KWord (SA (ELit 0) 882488) 8 (ELit 836764);
   KWord (SA (ELit 0) 6360320) 8 (ELit 6360360);
   KWord (SA (ELit 0) 6360368) 8 (ELit 6362376);
   KWord (SA (ELit 0) 906144) 1 (ELit 1);
   KWord (SA (ELit 0) 906148) 4 (ELit 0);
   KWord (SA (ELit 0) 6360240) 8 (ELit 6496432);
   KWord (SA (ELit 0) 874664) 8 (ELit 1504872);
   KWord (SA (ELit 0) 1505009) 1 (ELit 1);
   KWord (SA (ELit 0) 874760) 8 (ELit 1496536);
   KWord (SA (ELit 0) 1496536) 4 (ELit 0);
   KWord (SA (ELit 0) 878208) 8 (ELit 8);
   KWord (SA (ELit 0) 6496432) 8 (EVar 40);
   KWord (SA (EVar 40) 152) 8 (EVar 41);
   KWord (SA (EVar 41) 48) 8 (EVar 43);
   KWord (SA (EVar 41) 56) 8 (EVar 44);
   KWord (SA (ELit 0) 6360336) 8 (EVar 42);
   KWord (SA (EVar 42) 24) 8 (ELit 6360328);
   KRange (EVar 40) 4096 140737479966560;
   KRange (EVar 41) 4096 140737479966656;
   KRange (EVar 42) 4096 140737479962624;
   KWord (SA (EVar 10) (-16)) 8 (ELit 0);
   KWord (SA (ELit 0) (6491464)) 8 (EVar 33);
   KWord (SA (ELit 0) (6492064)) 8 (EVar 32)]
   ++ aux_kn r 11 ++
  [KWord (SA (EVar 10) (-8)) 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (448)));
   KWord (SA (EVar 10) (-32)) 8 (ELit 4849336966747728640);
   KWord (SA (EVar 2) (344)) 8 (ELit 597808);
   KWord (SA (EVar 2) (336)) 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (448)));
   KWord (SA (EVar 2) (328)) 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (352)));
   KWord (SA (EVar 2) (320)) 8 (EVar 45);
   KWord (SA (EVar 2) (312)) 8 (EVar 46);
   KWord (SA (EVar 2) (304)) 8 (EVar 47);
   KWord (SA (EVar 2) (296)) 8 (EVar 48);
   KWord (SA (EVar 2) (288)) 8 (EVar 49);
   KWord (SA (EVar 2) (280)) 8 (EVar 50);
   KWord (SA (EVar 2) (272)) 8 (EVar 51);
   KWord (SA (EVar 2) (264)) 8 (EVar 52);
   KWord (SA (EVar 2) (256)) 8 (EVar 53);
   KWord (SA (EVar 2) (248)) 8 (EVar 54);
   KWord (SA (ELit 0) (6360113)) 1 (ELit 1);
   KWord (SA (ELit 0) (6360114)) 1 (ELit 0);
   KWord (SA (ELit 0) (6360115)) 1 (ELit 1);
   KWord (SA (ELit 0) (6360116)) 1 (ELit 0);
   KWord (SA (ELit 0) (6360117)) 1 (ELit 1);
   KWord (SA (ELit 0) (6360118)) 1 (ELit 0)].
Definition ss0 (r : bool) : sym_state := SS 602780 regs0 [] (kn0 r) NX0.
Definition F0 : list SGP.region := [(EVar 2, (-10560), ELit 10560)].
Definition F0L : list SR.region := [(EVar 2, (-10560), 10560)].
Definition BF : nat := 200000.
(* [comment removed for export] *)
Definition BR : list SGP.bfact := [].
(* [comment removed for export] *)
Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition PXA : list (Z * nat) := [(385224, 0%nat); (385232, 1%nat); (318480, 2%nat)].
Definition AUTO := SGAX.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0 XSTEP PXA.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

(* [comment removed for export] *)
(* the walk from each r's start knowledge, computed in the build *)
Definition ex1_0 := Eval vm_compute in (AUTO 2000 (ss0 false)).
Definition ex1_1 := Eval vm_compute in (AUTO 2000 (ss0 true)).
Definition ex1 (r : bool) := if r then ex1_1 else ex1_0.
Definition s1 (r : bool) : sym_state := snd (snd (ex1 r)).

Definition plan (r : bool) : SGP.splan := SGAX.mkplan (fst (ex1 r)) (SGP.PEnd 0).
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
Definition ps0 : SR.post_spec := SR.PS 598052 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert (r : bool) : SGP.cert_ok RSEGS SegItab_A_fa86c0.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS (plan r) 602780 regs0 (kn0 r) = true.
Proof. destruct r; vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax (r : bool) := as0_plan_sound_it SegItab_A_fa86c0.IT SegItab_A_fa86c0.IT_sound BF NX0 BR XSTEP F0 PSS (plan r) 602780 regs0 (kn0 r) (cert r) (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
