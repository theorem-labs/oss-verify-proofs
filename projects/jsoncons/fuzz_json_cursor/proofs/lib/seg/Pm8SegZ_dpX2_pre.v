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
Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Definition ITR : list (Z * nat) := [(361172, 36%nat) ; (425660, 371%nat) ; (427252, 26%nat) ; (531716, 324%nat) ; (553908, 6%nat) ; (649028, 12%nat) ; (717068, 4%nat) ; (858188, 12%nat) ; (1260492, 51%nat) ; (1261092, 50%nat) ; (1292244, 100%nat) ; (1293748, 105%nat) ; (1295292, 12%nat) ; (1331976, 62%nat) ; (1334212, 191%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [1292380].
Definition STOPS1 : list Z := [1292380] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; ELit 1259188; EVar 2; EVar 3; ELit 6883920; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332552704 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-320)) (ELit 320);
   KUnk (SA (EVar 2) (-320)) (ELit 320);
   KImg 65536 1392640;
   KImg 1408096 1413856;
   KWr (SA (ELit 0) (1413888)) (ELit 8);
   KWr (SA (ELit 0) (1413968)) (ELit 1);
   KWr (SA (ELit 0) (1417840)) (ELit 8);
   KWr (SA (ELit 0) (7015072)) (ELit 1);
   KWr (SA (ELit 0) (7015080)) (ELit 4);
   KWr (SA (ELit 0) (7015088)) (ELit 8);
   KWr (SA (ELit 0) (7015616)) (ELit 4);
   KWr (SA (ELit 0) (2147469504)) (ELit 292);
   KWr (SA (ELit 0) (2147469804)) (ELit 20);
   KWr (SA (ELit 0) (2147469828)) (ELit 12);
   KWr (SA (ELit 0) (2147469876)) (ELit 16);
   KWr (SA (ELit 0) (2147469924)) (ELit 12);
   KWr (SA (ELit 0) (2147469944)) (ELit 300);
   KWr (SA (ELit 0) (2147470304)) (ELit 12);
   KWr (SA (ELit 0) (2147470336)) (ELit 24);
   KWr (SA (ELit 0) (2147470368)) (ELit 1320);
   KWr (SA (ELit 0) (2147621592)) (ELit 72);
   KWr (SA (ELit 0) (2147626892)) (ELit 720);
   KWord (SA (ELit 0) (6883752)) 4 (EVar 44);
   KRange (EVar 44) 1 4194303;
   KWord (SA (ELit 0) (7015616)) 4 (ELit 0);
   KWord (SA (ELit 0) (7015651)) 1 (ELit 0);
   KWord (SA (ELit 0) (7015088)) 8 (ELit 7015096);
   KWord (SA (ELit 0) (7015080)) 4 (ELit 2);
   KWord (SA (ELit 0) (7015104)) 8 (ELit 1261092);
   KWord (SA (ELit 0) (7015360)) 8 (ELit 649028);
   KWord (SA (ELit 0) (7015076)) 4 (ELit 0);
   KWord (SA (ELit 0) (2025568)) 1 (ELit 0);
   KWord (SA (ELit 0) (7015096)) 8 (ELit 0);
   KWord (SA (ELit 0) (1413968)) 1 (ELit 0);
   KWord (SA (ELit 0) (1396576)) 8 (ELit 1396576);
   KWord (SA (ELit 0) (1413888)) 8 (ELit 1);
   KWord (SA (ELit 0) (1417680)) 4 (ELit 1);
   KWord (SA (ELit 0) (1417840)) 8 (ELit 0);
   KWord (SA (ELit 0) (1431192)) 1 (ELit 1);
   KWord (SA (ELit 0) (1427896)) 8 (ELit 2147450880);
   KWord (SA (ELit 0) (7015112)) 8 (ELit 1261092);
   KWord (SA (ELit 0) (7015368)) 8 (ELit 717068);
   KWord (SA (ELit 0) (6877204)) 1 (ELit 0);
   KWord (SA (ELit 0) (1425948)) 1 (ELit 1);
   KWord (SA (ELit 0) (2024800)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1397088)) 8 (ELit 1331976);
   KWord (SA (ELit 0) (7017048)) 8 (ELit 0);
   KWord (SA (ELit 0) (1408040)) 8 (ELit 1407808);
   KWord (SA (ELit 0) (1407948)) 4 (ELit 4294967295);
   KWord (SA (ELit 0) (1407848)) 8 (ELit 0);
   KWord (SA (ELit 0) (1407864)) 8 (ELit 0);
   KWord (SA (ELit 0) (1407816)) 8 (ELit 0);
   KWord (SA (ELit 0) (1407824)) 8 (ELit 0);
   KWord (SA (ELit 0) (1407800)) 8 (ELit 1407568);
   KWord (SA (ELit 0) (1407708)) 4 (ELit 4294967295);
   KWord (SA (ELit 0) (1407608)) 8 (ELit 7017074);
   KWord (SA (ELit 0) (1407624)) 8 (ELit 7017072);
   KWord (SA (ELit 0) (1407640)) 8 (ELit 1292244);
   KWord (SA (ELit 0) (7015056)) 8 (EVar 40);
   KWord (SA (ELit 0) (1407688)) 4 (ELit 1)].
Definition ss0 : sym_state := SS 1261176 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-320), ELit 320); (ELit 0, (1413888), ELit 8); (ELit 0, (1413968), ELit 1); (ELit 0, (1417840), ELit 8); (ELit 0, (7015072), ELit 1); (ELit 0, (7015080), ELit 4); (ELit 0, (7015088), ELit 8); (ELit 0, (7015616), ELit 4); (ELit 0, (2147469504), ELit 292); (ELit 0, (2147469804), ELit 20); (ELit 0, (2147469828), ELit 12); (ELit 0, (2147469876), ELit 16); (ELit 0, (2147469924), ELit 12); (ELit 0, (2147469944), ELit 300); (ELit 0, (2147470304), ELit 12); (ELit 0, (2147470336), ELit 24); (ELit 0, (2147470368), ELit 1320); (ELit 0, (2147621592), ELit 72); (ELit 0, (2147626892), ELit 720)].
Definition F0L : list SR.region := [(EVar 2, (-320), 320); (ELit 0, (1413888), 8); (ELit 0, (1413968), 1); (ELit 0, (1417840), 8); (ELit 0, (7015072), 1); (ELit 0, (7015080), 4); (ELit 0, (7015088), 8); (ELit 0, (7015616), 4); (ELit 0, (2147469504), 292); (ELit 0, (2147469804), 20); (ELit 0, (2147469828), 12); (ELit 0, (2147469876), 16); (ELit 0, (2147469924), 12); (ELit 0, (2147469944), 300); (ELit 0, (2147470304), 12); (ELit 0, (2147470336), 24); (ELit 0, (2147470368), 1320); (ELit 0, (2147621592), 72); (ELit 0, (2147626892), 720)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 := Eval vm_compute in (AUTO 20000 ss0).
Definition s1 : sym_state := snd (snd ex1).
Eval vm_compute in (1001, length (fst ex1), fst (snd ex1), s_pc s1, s_next s1).
Lemma ex1_reached_end : fst (snd ex1) = 93. Proof. vmc_refl. Qed.

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
Definition ps0 : SR.post_spec := SR.PS 1292380 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1261176 regs0 kn0 = true.
Proof. vmc_refl. Qed.

Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 1261176 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
