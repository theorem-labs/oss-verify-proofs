(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Eb0PlanKit Eb0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require SegPlanFast.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.seg Require BndT_Eb_000.

Module LibSegEb_bplJ64.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000.SegItab_Eb_5f3685.ITR.
Definition IT : itab := BndT_Eb_000.SegItab_Eb_5f3685.IT.
Definition ENDS : list Z := [721076].
Definition STOPS1 : list Z := [721076] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$8+$2-80$37$38$39$=$>$?$10$11$2?$;+$:#8$15+&6$2?#3#7???8000$2?$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 1273856 1306624;
   KWord (SA (ELit 0) 1335544) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1335552) 4 (ELit 1);
   KRange (EVar 2) 140735332487328 140737488355328;
   KAlign (EVar 2) 32;
   KWr (SA (EVar 2) (-128)) (ELit 128);
   KRange (EVar 10) 4096 140737488355272;
   KAlign (EVar 10) 8].
Definition ss0 : sym_state := SS 720848 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;00;4#;00;4#5=#;00;4,20#$1+$2-80$3$4$5$6$7$8+$2-80$37$38$39$=$>$?$10$11$2?$;+$:#8$15+&6$2?#3#7???8000$2?$18$19$1:$1;$1<$1=$1>$1?,,8%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010:0#800000000000&$2#20($2-80#80'$:#1000#7?????????<8&$:#8,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 721076 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000.SegItab_Eb_5f3685.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 720848 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000.SegItab_Eb_5f3685.IT BndT_Eb_000.SegItab_Eb_5f3685.IT_sound BF NX0 BR XSTEP F0 PSS plan 720848 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bplJ64.

Module LibSegEb_bplJ8.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000.SegItab_Eb_5f3685.ITR.
Definition IT : itab := BndT_Eb_000.SegItab_Eb_5f3685.IT.
Definition ENDS : list Z := [721076].
Definition STOPS1 : list Z := [721076] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$8+$2-80$37$38$39$=$>$?$10$11$2?$;+$:#8$15+&6$2?#3#7???8000$2?$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",18%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010:0#800000000000&$2#20($2-80#80'$2?#1000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-80#80$2?##40)$2-80#80$30##1)$:##38$2?##40)$:##38$30##1)&6$:#3#7???8000#7&6$2?#3#7???8000#8'$:#1000#7?????????<8&$:#8"%pstring).
Definition ss0 : sym_state := SS 720932 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (4), ELit 1)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (4), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;00;4#;00;4#5=#;00;4,20#$1+$2-80$3$4$5$6$7$8+$2-80^#?#??????????????8$38$39$=$>$?$10$11$2?$;+$:#8$15+&6$2?#3#7???8000$2?$18$19$1:$1;$1<$1=$1>$1?,,19!&6$2?#3#7???8004,1^#?#??????????????8%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010:0#800000000000&$2#20($2-80#80'$2?#1000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-80#80$2?##40)$2-80#80$30##1)$:##38$2?##40)$:##38$30##1)&6$:#3#7???8000#7&6$2?#3#7???8000#8'$:#1000#7?????????<8&$:#8,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 721076 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000.SegItab_Eb_5f3685.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 720932 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000.SegItab_Eb_5f3685.IT BndT_Eb_000.SegItab_Eb_5f3685.IT_sound BF NX0 BR XSTEP F0 PSS plan 720932 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bplJ8.

Module LibSegEb_bplP8.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000.SegItab_Eb_5f3685.ITR.
Definition IT : itab := BndT_Eb_000.SegItab_Eb_5f3685.IT.
Definition ENDS : list Z := [731028].
Definition STOPS1 : list Z := [731028] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$8+$2-80$37$38$39$=$>$?$10$11$2?$;+$:#8+$2?#20+&6$2?#3#7???8000$2?$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",19%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010:0#800000000000&$2#20($2-80#80'$2?#1000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-80#80$2?##40)$2-80#80$30##1)$:##38$2?##40)$:##38$30##1)&6$:#3#7???8000#7&6$2?#3#7???8000#8'$:#1000#7?????????<8&$:#8'$;##??"%pstring).
Definition ss0 : sym_state := SS 720908 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-73), ELit 1); ((EVar 47), (32), ELit 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (4), ELit 1)].
Definition F0L : list SR.region := [((EVar 2), (-73), 1); ((EVar 47), (32), 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (4), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;2794#;2794#5=#;2794,20##;0024+$2-80$3$4$5$6$7$8+$2-80+$2?#20+$2-49$39$=$>$?$10$11$2?$;+$:#8+$2?#20+&6$2?#3#7???8000$2?$18$19$1:$1;$1<$1=$1>$1?,,1:!$2?#20,8+$:#8!&6$2?#3#7???8004,1#!$2-49,1$;'$2#7???7?8010:0#800000000000&$2#20($2-80#80'$2?#1000#7?????????<0&$2?#20,$2?##20,$2?#28#18($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-80#80$2?##40)$2-80#80$30##1)$:##38$2?##40)$:##38$30##1)&6$:#3#7???8000#7&6$2?#3#7???8000#8'$:#1000#7?????????<8&$:#8'$;##??,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 731028 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000.SegItab_Eb_5f3685.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 720908 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000.SegItab_Eb_5f3685.IT BndT_Eb_000.SegItab_Eb_5f3685.IT_sound BF NX0 BR XSTEP F0 PSS plan 720908 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bplP8.

Module LibSegEb_bplW16.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000.SegItab_Eb_5f3685.ITR.
Definition IT : itab := BndT_Eb_000.SegItab_Eb_5f3685.IT.
Definition ENDS : list Z := [728004].
Definition STOPS1 : list Z := [728004] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$8+$2-80$37$38$39$=$>$?$10$11$2?$;+$:#8$15+&6$2?#3#7???8000$2?$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010:0#800000000000&$2#20($2-80#80'$:#1000#7?????????<8&$:#8'$;#100#7???"%pstring).
Definition ss0 : sym_state := SS 720996 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;1;<4#;1;<4#5=#;1;<4,20##;0070+$2-80$3$4$5$6$7$8+$2-80$;+$:#8$39$=$>$?$10$11$2?$;+$:#8$15+&6$2?#3#7???8000$2?$18$19$1:$1;$1<$1=$1>$1?,,9%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010:0#800000000000&$2#20($2-80#80'$:#1000#7?????????<8&$:#8'$;#100#7???,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 728004 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000.SegItab_Eb_5f3685.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 720996 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000.SegItab_Eb_5f3685.IT BndT_Eb_000.SegItab_Eb_5f3685.IT_sound BF NX0 BR XSTEP F0 PSS plan 720996 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bplW16.

Module LibSegEb_bplW32.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000.SegItab_Eb_5f3685.ITR.
Definition IT : itab := BndT_Eb_000.SegItab_Eb_5f3685.IT.
Definition ENDS : list Z := [728484].
Definition STOPS1 : list Z := [728484] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$8+$2-80$37$38$39$=$>$?$10$11$2?$;+$:#8$15+&6$2?#3#7???8000$2?$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010:0#800000000000&$2#20($2-80#80'$:#1000#7?????????<8&$:#8'$;#8000#7???????"%pstring).
Definition ss0 : sym_state := SS 721064 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;1=:4#;1=:4#5=#;1=:4,20##;00;4+$2-80$3$4$5$6$7$8+$2-80$;+$:#8$39$=$>$?$10$11$2?$;+$:#8$15+&6$2?#3#7???8000$2?$18$19$1:$1;$1<$1=$1>$1?,,9%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010:0#800000000000&$2#20($2-80#80'$:#1000#7?????????<8&$:#8'$;#8000#7???????,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 728484 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000.SegItab_Eb_5f3685.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 721064 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000.SegItab_Eb_5f3685.IT BndT_Eb_000.SegItab_Eb_5f3685.IT_sound BF NX0 BR XSTEP F0 PSS plan 721064 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bplW32.

Module LibSegEb_bplW64.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000.SegItab_Eb_5f3685.ITR.
Definition IT : itab := BndT_Eb_000.SegItab_Eb_5f3685.IT.
Definition ENDS : list Z := [728996].
Definition STOPS1 : list Z := [728996] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$8+$2-80$37$38$39$=$>$?$10$11$2?$;+$:#8$15+&6$2?#3#7???8000$2?$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010:0#800000000000&$2#20($2-80#80'$:#1000#7?????????<8&$:#8'$;#80000000^#7#???????????????"%pstring).
Definition ss0 : sym_state := SS 720836 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;1?:4#;1?:4#5=#;1?:4,20##:??=0+$2-80$3$4$5$6$7$8+$2-80$;+$:#8$39$=$>$?$10$11$2?$;+$:#8$15+&6$2?#3#7???8000$2?$18$19$1:$1;$1<$1=$1>$1?,,9%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010:0#800000000000&$2#20($2-80#80'$:#1000#7?????????<8&$:#8'$;#80000000^#7#???????????????,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 728996 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000.SegItab_Eb_5f3685.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 720836 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000.SegItab_Eb_5f3685.IT BndT_Eb_000.SegItab_Eb_5f3685.IT_sound BF NX0 BR XSTEP F0 PSS plan 720836 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bplW64.

Module LibSegEb_bpqA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000.SegItab_Eb_1b7ea3.ITR.
Definition IT : itab := BndT_Eb_000.SegItab_Eb_1b7ea3.IT.
Definition ENDS : list Z := [511016].
Definition STOPS1 : list Z := [511016] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9+$21#18$22$23$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",17'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8$24!$21#20,8+$24$25!$21#28,8$29'$24#1000#7?????????>8&$24#8'$25##;?>8&$25#8'$29#1018#7???????????'&1$29+$24$25#18#<000'&1$29$24#18#12000"%pstring).
Definition ss0 : sym_state := SS 722164 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-96), ELit 96)].
Definition F0L : list SR.region := [((EVar 2), (-96), 96)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<<28#7<<28#5=#7<<28,20##;09?0+$2-50$3$4$5$6$7$23$22$24$29+$24$25++$24$25#18#1##$11#7???8000$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,21!$2-58,8#;09?0!$2-50,8$23!$2-48,8#;0558!$2-28,8++$24$25#18!$2-30,8+$24$25!$2-38,8+$21#18!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8$24!$21#20,8+$24$25!$21#28,8$29'$24#1000#7?????????>8&$24#8'$25##;?>8&$25#8'$29#1018#7???????????'&1$29+$24$25#18#<000'&1$29$24#18#12000,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 511016 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000.SegItab_Eb_1b7ea3.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 722164 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000.SegItab_Eb_1b7ea3.IT BndT_Eb_000.SegItab_Eb_1b7ea3.IT_sound BF NX0 BR XSTEP F0 PSS plan 722164 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bpqA.

Module LibSegEb_bpqB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000.SegItab_Eb_1b7ea3.ITR.
Definition IT : itab := BndT_Eb_000.SegItab_Eb_1b7ea3.IT.
Definition ENDS : list Z := [722432].
Definition STOPS1 : list Z := [722432] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$23$22$:$;$<$=$>$?$10$11#7???8000$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3:'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38($21#18#18!$21#18,8$24!$21#20,8+$24$25!$21#28,8$29'$24#1000#7?????????>8&$24#8'$25##;?>8&$25#8'$29#1018#7???????????'&1$29+$24$25#18#<000'&1$29$24#18#12000'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4)$21##38$22##4'$26##3'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##38$23##8'$27##1000000!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-48,8#;0558!$2-50,8$23!$2-38,8+$21#18!$2-30,8+$24$25!$2-28,8++$24$25#18(+$24$25##18#&6+$24$25#3#7???8000#3)##7???7000#100000001000+$24$25##18'+$24$25#1000#7?????????>8)$2-1000#1000+$24$25##18)$21##38+$24$25##18)$22##4+$24$25##18)$23##8+$24$25##18)##10000#68<000+$24$25##18"%pstring).
Definition ss0 : sym_state := SS 723440 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_ADD (EVar 36) (EVar 37)), (0), ELit 24); ((EVar 2), (-48), ELit 8); ((EVar 33), (32), ELit 8); ((EVar 2), (-80), ELit 16)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_ADD (EVar 36) (EVar 37)), (0), 24); ((EVar 2), (-48), 8); ((EVar 33), (32), 8); ((EVar 2), (-80), 16)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;0600#;0600#5=#;0600,20#$2;$2$3$4$5$6$7$2<$2=+$21#18++$24$25#18#++$24$25#18#7???8000#$10$11$2>$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,3=!$21#20,8++$24$25#18!$2-48,8#;05><!$2-30,8++$24$25#18!+$24$25#10,8#!+$24$25#8,8$27!+$24$25#,4$26'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38($21#18#18!$21#18,8$24!$21#28,8$29'$24#1000#7?????????>8&$24#8'$25##;?>8&$25#8'$29#1018#7???????????'&1$29+$24$25#18#<000'&1$29$24#18#12000'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4)$21##38$22##4'$26##3'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##38$23##8'$27##1000000!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-50,8$23!$2-38,8+$21#18!$2-28,8++$24$25#18(+$24$25##18#&6+$24$25#3#7???8000#3)##7???7000#100000001000+$24$25##18'+$24$25#1000#7?????????>8)$2-1000#1000+$24$25##18)$21##38+$24$25##18)$22##4+$24$25##18)$23##8+$24$25##18)##10000#68<000+$24$25##18,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 722432 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000.SegItab_Eb_1b7ea3.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 723440 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000.SegItab_Eb_1b7ea3.IT BndT_Eb_000.SegItab_Eb_1b7ea3.IT_sound BF NX0 BR XSTEP F0 PSS plan 723440 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bpqB.

Module LibSegEb_bpqE0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000.SegItab_Eb_24db52.ITR.
Definition IT : itab := BndT_Eb_000.SegItab_Eb_24db52.IT.
Definition ENDS : list Z := [1271400].
Definition STOPS1 : list Z := [1271400] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9+$21#18$22$23$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8#!$21#20,8#!$21#28,8#"%pstring).
Definition ss0 : sym_state := SS 722504 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-176), ELit 176)].
Definition F0L : list SR.region := [((EVar 2), (-176), 176)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#136668#136668#5=#136668,20##;0;>4+$2-:0$3$4$5$6$7+$2-48#1#18#20#1460?8+$21#18^#:#::::::::::::::;#$10$11+$2-60#+&6+$2-48#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,21!$2-:8,8#;0;>4!$2-40,8+$21#18!$2-48,8#!$2-98,8#7???8000!$2-90,8+&6+$21#20#3#7???8000!$2-88,8$22!$2-80,8$23!$2-78,8+$21#18!$2-70,8+$21#20!$2-68,8#;0720!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8#!$21#20,8#!$21#28,8#,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1271400 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000.SegItab_Eb_24db52.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 722504 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000.SegItab_Eb_24db52.IT BndT_Eb_000.SegItab_Eb_24db52.IT_sound BF NX0 BR XSTEP F0 PSS plan 722504 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bpqE0.

Module LibSegEb_bpqE1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000.SegItab_Eb_24db52.ITR.
Definition IT : itab := BndT_Eb_000.SegItab_Eb_24db52.IT.
Definition ENDS : list Z := [495168].
Definition STOPS1 : list Z := [495168] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-48#1$28$;$<$=$>$?$10$11+$2-60#+&6+$2-48#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3:'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8#!$21#20,8#!$21#28,8#'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4)$21##38$22##4'$26##3'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##38$23##8'$27##1000000'$28#1000#7?????????>8&$28#10)##7???7000#100000001000$28##18#&6$28#3#7???8000#3($28##18)$2-1000#1000$28##18)$21##38$28##18)$22##4$28##18)$23##8$28##18)##10000#68<000$28##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-68,8#;0720!$2-70,8+$21#20!$2-78,8+$21#18!$2-80,8$23!$2-88,8$22!$2-90,8+&6+$21#20#3#7???8000!$2-98,8#7???8000!$2-48,8#!$2-40,8+$21#18"%pstring).
Definition ss0 : sym_state := SS 723940 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-208), ELit 208); ((EVar 40), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-208), 208); ((EVar 40), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#78>40#78>40#5=#78>40,20##;0==<+$2-;0$3$4$5$6$7+$2-60+$21#18$28#####1&6+$21#28#3$11+$21#20+$2-58$28#7???8000+&6+$21#20#3#7???8000+&6+$2-58#3#7???8000+&6+$21#18#3#7???8000$19$1:$1;$1<$1=$1>$1?,,46!$2-<8,8#;1110!$2-<0,8+$2-60!$2-;8,8#;0=40!$2-;0,8$18!$2-:8,8$17!$2-:0,8$16!$2-98,8#7???8000!$2-90,8+&6+$21#20#3#7???8000!$2-88,8$22!$2-80,8$23!$2-78,8+$21#18!$2-70,8+$21#20!$2-68,8#;07;8!$2-50,8+$28#18!$28#10,8#!$28#8,8$27!$28#,4$26!$2-48,8+$28#18!$2-58,8$28!$2-60,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8#!$21#20,8#!$21#28,8#'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4)$21##38$22##4'$26##3'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##38$23##8'$27##1000000'$28#1000#7?????????>8&$28#10)##7???7000#100000001000$28##18#&6$28#3#7???8000#3($28##18)$2-1000#1000$28##18)$21##38$28##18)$22##4$28##18)$23##8$28##18)##10000#68<000$28##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8+$21#18,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 495168 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000.SegItab_Eb_24db52.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 723940 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000.SegItab_Eb_24db52.IT BndT_Eb_000.SegItab_Eb_24db52.IT_sound BF NX0 BR XSTEP F0 PSS plan 723940 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bpqE1.

Module LibSegEb_bpqE2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000.SegItab_Eb_24db52.ITR.
Definition IT : itab := BndT_Eb_000.SegItab_Eb_24db52.IT.
Definition ENDS : list Z := [511016].
Definition STOPS1 : list Z := [511016] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-;0$3$4$5$6$7+$2-60+$21#18$:$;$<$=$>$?$10$11+$21#20+$2-58$28#7???8000+&6+$21#20#3#7???8000+&6+$2-58#3#7???8000+&6+$21#18#3#7???8000$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",31'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38($21#18#18!$21#18,8#!$21#20,8#!$21#28,8#'$28#1000#7?????????>8&$28#10)##7???7000#100000001000$28##18#&6$28#3#7???8000#3($28##18)$2-1000#1000$28##18)$21##38$28##18)$22##4$28##18)$23##8$28##18)##10000#68<000$28##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-68,8#;07;8!$2-70,8+$21#20!$2-78,8+$21#18!$2-80,8$23!$2-88,8$22!$2-90,8+&6+$21#20#3#7???8000!$2-98,8#7???8000!$2-:0,8$16!$2-:8,8$17!$2-;0,8$18!$2-60,8$28!$2-58,8$28!$2-50,8+$28#18!$2-48,8+$28#18!$2-40,8+$21#18"%pstring).
Definition ss0 : sym_state := SS 724444 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-208), ELit 208); ((EVar 33), (24), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-208), 208); ((EVar 33), (24), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<<28#7<<28#5=#7<<28,20##;11=<+$2-70$3$4$5$6$7+$21#20+$21#18$28+$28#18+$28#18+$28#18#1##1#$23$22+&6+$21#20#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,31!$2-78,8#;11=<!$2-70,8+$21#20!$2-68,8#;07;8!$2-60,8#!$2-48,8#!$21#28,8+$28#18!$2-50,8#!$21#20,8+$28#18!$2-58,8#!$21#18,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38($21#18#18'$28#1000#7?????????>8&$28#10)##7???7000#100000001000$28##18#&6$28#3#7???8000#3($28##18)$2-1000#1000$28##18)$21##38$28##18)$22##4$28##18)$23##8$28##18)##10000#68<000$28##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-80,8$23!$2-88,8$22!$2-90,8+&6+$21#20#3#7???8000!$2-98,8#7???8000!$2-:0,8$16!$2-:8,8$17!$2-;0,8$18!$2-40,8+$21#18,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 511016 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000.SegItab_Eb_24db52.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 724444 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000.SegItab_Eb_24db52.IT BndT_Eb_000.SegItab_Eb_24db52.IT_sound BF NX0 BR XSTEP F0 PSS plan 724444 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bpqE2.

Module LibSegEb_bpqE3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000.SegItab_Eb_24db52.ITR.
Definition IT : itab := BndT_Eb_000.SegItab_Eb_24db52.IT.
Definition ENDS : list Z := [722928].
Definition STOPS1 : list Z := [722928] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7+$21#20+$21#18$:$;$<$=$>$?$10$11$23$22+&6+$21#20#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",20'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8$28!$21#20,8+$28#18!$21#28,8+$28#18'$28#1000#7?????????=0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-68,8#;07;8!$2-70,8+$21#20!$2-60,8#!$2-58,8#!$2-50,8#!$2-48,8#!$2-40,8+$21#18"%pstring).
Definition ss0 : sym_state := SS 725468 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-208), ELit 208)].
Definition F0L : list SR.region := [((EVar 2), (-208), 208)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;07?0#;07?0#5=#;07?0,20#$2;$2$3$4$5$6$7$2<$2=+$28#18+$2-40##7???8000&6+$2-40#3+&6+$2-50#3#7???8000##$2>$2?$30$31$16$17$18$19$1:$1;$1<$1=$1>$1?,,20!$2-68,8#;07<<'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8$28!$21#20,8+$28#18!$21#28,8+$28#18'$28#1000#7?????????=0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-70,8+$21#20!$2-60,8#!$2-58,8#!$2-50,8#!$2-48,8#!$2-40,8+$21#18,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 722928 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000.SegItab_Eb_24db52.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 725468 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000.SegItab_Eb_24db52.IT BndT_Eb_000.SegItab_Eb_24db52.IT_sound BF NX0 BR XSTEP F0 PSS plan 725468 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bpqE3.

Module LibSegEb_bpqG1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000.SegItab_Eb_24db52.ITR.
Definition IT : itab := BndT_Eb_000.SegItab_Eb_24db52.IT.
Definition ENDS : list Z := [511016].
Definition STOPS1 : list Z := [511016] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-48#2$28$;$<$=$>$?$10$11+$2-60#1+&6+$2-48#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8$24!$21#20,8+$24#18!$21#28,8+$24#18'$24#1000#7?????????>8&$24#8'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4)$21##38$22##4'$26##3'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##38$23##8'$27##1000000'$28#1000#7?????????=0&$28#10(+$28#18##18#&6+$28#18#3#7???8000#3)##7???7000#100000001000+$28#18##18'+$28#18#1000#7?????????>8)$2-1000#1000+$28#18##18)$21##38+$28#18##18)$22##4+$28#18##18)$23##8+$28#18##18)##10000#68<000+$28#18##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-68,8#;0720!$2-70,8+$21#20!$2-78,8+$21#18!$2-80,8$23!$2-88,8$22!$2-90,8+&6+$21#20#3#7???8000!$2-98,8#7???8000!$2-48,8#!$2-40,8+$21#18"%pstring).
Definition ss0 : sym_state := SS 723940 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-208), ELit 208); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (24))), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-208), 208); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (24))), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<<28#7<<28#5=#7<<28,20##;1110+$2-<0$3$4$5$6$7+$2-60+$21#18$24+$24#18+$24#18+$24#18#1#&6+$21#28#3$11$23$22+&6+$21#20#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,49!$2-<8,8#;1110!$2-<0,8+$2-60!$2-;8,8#;0=40!$2-;0,8$18!$2-:8,8$17!$2-:0,8$16!$2-98,8#7???8000!$2-90,8+&6+$21#20#3#7???8000!$2-88,8$22!$2-80,8$23!$2-78,8+$21#18!$2-70,8+$21#20!$2-68,8#;07;8!$2-50,8+$28#30!$28#28,8#!$28#20,8$27!$28#18,4$26!$2-48,8+$28#30!$2-58,8+$28#18!$2-60,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8$24!$21#20,8+$24#18!$21#28,8+$24#18'$24#1000#7?????????>8&$24#8'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4)$21##38$22##4'$26##3'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##38$23##8'$27##1000000'$28#1000#7?????????=0&$28#10(+$28#18##18#&6+$28#18#3#7???8000#3)##7???7000#100000001000+$28#18##18'+$28#18#1000#7?????????>8)$2-1000#1000+$28#18##18)$21##38+$28#18##18)$22##4+$28#18##18)$23##8+$28#18##18)##10000#68<000+$28#18##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8+$21#18,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 511016 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000.SegItab_Eb_24db52.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 723940 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000.SegItab_Eb_24db52.IT BndT_Eb_000.SegItab_Eb_24db52.IT_sound BF NX0 BR XSTEP F0 PSS plan 723940 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bpqG1.

Module LibSegEb_bpqG10.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000.SegItab_Eb_24db52.ITR.
Definition IT : itab := BndT_Eb_000.SegItab_Eb_24db52.IT.
Definition ENDS : list Z := [511016].
Definition STOPS1 : list Z := [511016] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-48#400$28$;$<$=$>$?$10$11+$2-60#200+&6+$2-48#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8$24!$21#20,8+$24#3000!$21#28,8+$24#3000'$24#1000#7?????????>8&$24#8'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4)$21##38$22##4'$26##3'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##38$23##8'$27##1000000'$28#1000#7???????:000&$28#10(+$28#3000##18#&6+$28#3000#3#7???8000#3)##7???7000#100000001000+$28#3000##18'+$28#3000#1000#7?????????>8)$2-1000#1000+$28#3000##18)$21##38+$28#3000##18)$22##4+$28#3000##18)$23##8+$28#3000##18)##10000#68<000+$28#3000##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-68,8#;0720!$2-70,8+$21#20!$2-78,8+$21#18!$2-80,8$23!$2-88,8$22!$2-90,8+&6+$21#20#3#7???8000!$2-98,8#7???8000!$2-48,8#!$2-40,8+$21#18"%pstring).
Definition ss0 : sym_state := SS 723940 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-208), ELit 208); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (12288))), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-208), 208); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (12288))), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<<28#7<<28#5=#7<<28,20##;1110+$2-<0$3$4$5$6$7+$2-60+$21#18$24+$24#3000+$24#3000+$24#3000#1#&6+$21#28#3$11$23$22+&6+$21#20#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,49!$2-<8,8#;1110!$2-<0,8+$2-60!$2-;8,8#;0=40!$2-;0,8$18!$2-:8,8$17!$2-:0,8$16!$2-98,8#7???8000!$2-90,8+&6+$21#20#3#7???8000!$2-88,8$22!$2-80,8$23!$2-78,8+$21#18!$2-70,8+$21#20!$2-68,8#;07;8!$2-50,8+$28#3018!$28#3010,8#!$28#3008,8$27!$28#3000,4$26!$2-48,8+$28#6000!$2-58,8+$28#3000!$2-60,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8$24!$21#20,8+$24#3000!$21#28,8+$24#3000'$24#1000#7?????????>8&$24#8'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4)$21##38$22##4'$26##3'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##38$23##8'$27##1000000'$28#1000#7???????:000&$28#10(+$28#3000##18#&6+$28#3000#3#7???8000#3)##7???7000#100000001000+$28#3000##18'+$28#3000#1000#7?????????>8)$2-1000#1000+$28#3000##18)$21##38+$28#3000##18)$22##4+$28#3000##18)$23##8+$28#3000##18)##10000#68<000+$28#3000##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8+$21#18,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 511016 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000.SegItab_Eb_24db52.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 723940 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000.SegItab_Eb_24db52.IT BndT_Eb_000.SegItab_Eb_24db52.IT_sound BF NX0 BR XSTEP F0 PSS plan 723940 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bpqG10.
