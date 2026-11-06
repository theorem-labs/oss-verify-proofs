(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Eb0PlanKit Eb0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require SegPlanFast.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.seg Require BndT_Eb_000S9.

Module LibSegEb_bfdZ.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_0dbce9.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_0dbce9.IT.
Definition ENDS : list Z := [706880].
Definition STOPS1 : list Z := [706880] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$8$9#1$38$39$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 1273856 1306624;
   KWord (SA (ELit 0) 1335544) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1335552) 4 (ELit 1);
   KRange (EVar 2) 140735332487232 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-64)) (ELit 64)].
Definition ss0 : sym_state := SS 706876 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:<940#:<940#5:#:<940,20#$1$2$3$4$5$6$7$8$9#1$38$39$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,6%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801040#800000000000&$2#10($2-40#40,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 706880 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_0dbce9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 706876 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_0dbce9.IT BndT_Eb_000S9.SegItab_Eb_0dbce9.IT_sound BF NX0 BR XSTEP F0 PSS plan 706876 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bfdZ.

Module LibSegEb_bhnA0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_4e8169.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_4e8169.IT.
Definition ENDS : list Z := [389768].
Definition STOPS1 : list Z := [389768] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EVar 2); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 33; EVar 34; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332487392 140737488355328;
   KAlign (EVar 2) 32;
   KWr (SA (EVar 2) (-160)) (ELit 160);
   KImg 1273856 1306624;
   KWord (SA (ELit 0) 1335544) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1335552) 4 (ELit 1)].
Definition ss0 : sym_state := SS 692560 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-160), ELit 160)].
Definition F0L : list SR.region := [((EVar 2), (-160), 160)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#5?288#5?288#5=#5?288,20##:91<4+$2-:0$3$4$5$6$7$2+$2-:0#480#1460?8#1$=$>$?$10$11$12$13$14$15$22$21$18$19$1:#7???8000$1<$1=$1>$1?,,14!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1!$2-:0,8#'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0%#137000#13?000!##1460?8,8#7???8000!##146100,4#1,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
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
Definition ps0 : SR.post_spec := SR.PS 389768 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_4e8169.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 692560 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_4e8169.IT BndT_Eb_000S9.SegItab_Eb_4e8169.IT_sound BF NX0 BR XSTEP F0 PSS plan 692560 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bhnA0.

Module LibSegEb_bhnA16.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_4e8169.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_4e8169.IT.
Definition ENDS : list Z := [389768].
Definition STOPS1 : list Z := [389768] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2#10$3$4$5$6$7$8$9$21$22$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332487392 140737488355312;
   KAlign (EVar 2) 32;
   KWr (SA (EVar 2) (-160)) (ELit 176);
   KImg 1273856 1306624;
   KWord (SA (ELit 0) 1335544) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1335552) 4 (ELit 1)].
Definition ss0 : sym_state := SS 692560 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-160), ELit 176)].
Definition F0L : list SR.region := [((EVar 2), (-160), 176)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#5?288#5?288#5=#5?288,20##:91<4+$2-:0$3$4$5$6$7+$2#10+$2-:0#480#1460?8#1$=$>$?$10$11$12$13$14$15$22$21$18$19$1:#7???8000$1<$1=$1>$1?,,14!$2-58,8$1;!$2-50,8$1:!$2-48,8$19!$2-40,8$18!$2-38,8$17!$2-30,8$16!$2-28,8$15!$2-20,8$14!$2-18,8$13!$2-10,8$12!$2-8,8$9!$2#,8$8!$2#8,8$1!$2-90,8#'$2#7???7?8010>0#7??????????0&$2#20($2-:0#;0%#137000#13?000!##1460?8,8#7???8000!##146100,4#1,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
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
Definition ps0 : SR.post_spec := SR.PS 389768 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_4e8169.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 692560 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_4e8169.IT BndT_Eb_000S9.SegItab_Eb_4e8169.IT_sound BF NX0 BR XSTEP F0 PSS plan 692560 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bhnA16.

Module LibSegEb_bhnB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_4e8169.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_4e8169.IT.
Definition ENDS : list Z := [695456].
Definition STOPS1 : list Z := [695456] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$3:+$2-:0$3$4$5$6$7$8+$2-:0$28$;$<$=$>$?$10$11$12$13$14$15$22$21$18$19$1:#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",16'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$28#1000#7????????800&$28#20,$28##800($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100#&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1)##10000#68<000$28##800)##10000#68<000$29##1"%pstring).
Definition ss0 : sym_state := SS 692676 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-136), ELit 8); ((EVar 2), (-120), ELit 8); ((EVar 40), (0), ELit 24); ((EAlu Instr.ALU_SRL (EVar 40) (ELit 3)), (2147450880), ELit 144)].
Definition F0L : list SR.region := [((EVar 2), (-136), 8); ((EVar 2), (-120), 8); ((EVar 40), (0), 24); ((EAlu Instr.ALU_SRL (EVar 40) (ELit 3)), (2147450880), 144)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:9<:0#:9<:0#5=#:9<:0,20##:948<+$2-:0$3$4$5$6$7$8+$2-:0+$28#20$21$22#:9150^#?#??????????????1$?$10$11+$28#20+&6$28#3#7???8000$14+$28#60$22$21$18$19$28#7???8000$1<$1=$1>$1?,,:;!&6$28#3#7???808;,1^#?#??????????????2!&6$28#3#7???808:,1^#?#??????????????2!&6$28#3#7???8089,1^#?#??????????????2!&6$28#3#7???8088,1^#?#??????????????2!&6$28#3#7???808?,1^#?#??????????????3!&6$28#3#7???808>,1^#?#??????????????3!&6$28#3#7???808=,1^#?#??????????????8!&6$28#3#7???808<,1^#?#??????????????8!&6$28#3#7???8083,1^#?#??????????????2!&6$28#3#7???8082,1^#?#??????????????2!&6$28#3#7???8081,1^#?#??????????????2!&6$28#3#7???8080,1^#?#??????????????2!&6$28#3#7???8087,1^#?#??????????????8!&6$28#3#7???8086,1^#?#??????????????8!&6$28#3#7???8085,1^#?#??????????????8!&6$28#3#7???8084,1^#?#??????????????8!&6$28#3#7???807;,1^#?#??????????????2!&6$28#3#7???807:,1^#?#??????????????8!&6$28#3#7???8079,1^#?#??????????????8!&6$28#3#7???8078,1^#?#??????????????8!&6$28#3#7???807?,1^#?#??????????????2!&6$28#3#7???807>,1^#?#??????????????2!&6$28#3#7???807=,1^#?#??????????????2!&6$28#3#7???807<,1^#?#??????????????2!&6$28#3#7???8073,1^#?#??????????????8!&6$28#3#7???8072,1^#?#??????????????8!&6$28#3#7???8071,1^#?#??????????????8!&6$28#3#7???8070,1^#?#??????????????8!&6$28#3#7???8077,1^#?#??????????????8!&6$28#3#7???8076,1^#?#??????????????8!&6$28#3#7???8075,1^#?#??????????????8!&6$28#3#7???8074,1^#?#??????????????8!&6$28#3#7???806;,1^#?#??????????????8!&6$28#3#7???806:,1^#?#??????????????8!&6$28#3#7???8069,1^#?#??????????????8!&6$28#3#7???8068,1^#?#??????????????8!&6$28#3#7???806?,1^#?#??????????????8!&6$28#3#7???806>,1^#?#??????????????8!&6$28#3#7???806=,1^#?#??????????????8!&6$28#3#7???806<,1^#?#??????????????8!&6$28#3#7???8063,1^#?#??????????????8!&6$28#3#7???8062,1^#?#??????????????8!&6$28#3#7???8061,1^#?#??????????????8!&6$28#3#7???8060,1^#?#??????????????8!&6$28#3#7???8067,1^#?#??????????????8!&6$28#3#7???8066,1^#?#??????????????8!&6$28#3#7???8065,1^#?#??????????????8!&6$28#3#7???8064,1^#?#??????????????8!&6$28#3#7???805;,1^#?#??????????????8!&6$28#3#7???805:,1^#?#??????????????8!&6$28#3#7???8059,1^#?#??????????????8!&6$28#3#7???8058,1^#?#??????????????8!&6$28#3#7???805?,1^#?#??????????????8!&6$28#3#7???805>,1^#?#??????????????8!&6$28#3#7???805=,1^#?#??????????????8!&6$28#3#7???805<,1^#?#??????????????8!&6$28#3#7???8053,1^#?#??????????????8!&6$28#3#7???8052,1^#?#??????????????8!&6$28#3#7???8051,1^#?#??????????????8!&6$28#3#7???8050,1^#?#??????????????8!&6$28#3#7???8057,1^#?#??????????????8!&6$28#3#7???8056,1^#?#??????????????8!&6$28#3#7???8055,1^#?#??????????????8!&6$28#3#7???8054,1^#?#??????????????8!&6$28#3#7???804;,1^#?#??????????????8!&6$28#3#7???804:,1^#?#??????????????8!&6$28#3#7???8049,1^#?#??????????????2!&6$28#3#7???8048,1^#?#??????????????2!&6$28#3#7???804?,1^#?#??????????????8!&6$28#3#7???804>,1^#?#??????????????8!&6$28#3#7???804=,1^#?#??????????????8!&6$28#3#7???804<,1^#?#??????????????8!&6$28#3#7???8043,1^#?#??????????????8!&6$28#3#7???8042,1^#?#??????????????8!&6$28#3#7???8041,1^#?#??????????????8!&6$28#3#7???8040,1^#?#??????????????8!&6$28#3#7???8047,1^#?#??????????????2!&6$28#3#7???8046,1^#?#??????????????2!&6$28#3#7???8045,1^#?#??????????????2!&6$28#3#7???8044,1^#?#??????????????8!&6$28#3#7???803;,1^#?#??????????????2!&6$28#3#7???803:,1^#?#??????????????2!&6$28#3#7???8039,1^#?#??????????????2!&6$28#3#7???8038,1^#?#??????????????8!&6$28#3#7???803?,1^#?#??????????????8!&6$28#3#7???803>,1^#?#??????????????8!&6$28#3#7???803=,1^#?#??????????????2!&6$28#3#7???803<,1^#?#??????????????2!&6$28#3#7???8033,1^#?#??????????????2!&6$28#3#7???8032,1^#?#??????????????2!&6$28#3#7???8031,1^#?#??????????????2!&6$28#3#7???8030,1^#?#??????????????2!&6$28#3#7???8037,1^#?#??????????????8!&6$28#3#7???8036,1^#?#??????????????8!&6$28#3#7???8035,1^#?#??????????????2!&6$28#3#7???8034,1^#?#??????????????2!&6$28#3#7???802;,1^#?#??????????????8!&6$28#3#7???802:,1^#?#??????????????8!&6$28#3#7???8029,1^#?#??????????????8!&6$28#3#7???8028,1^#?#??????????????8!&6$28#3#7???802?,1^#?#??????????????2!&6$28#3#7???802>,1^#?#??????????????2!&6$28#3#7???802=,1^#?#??????????????8!&6$28#3#7???802<,1^#?#??????????????8!&6$28#3#7???8023,1^#?#??????????????8!&6$28#3#7???8022,1^#?#??????????????8!&6$28#3#7???8021,1^#?#??????????????8!&6$28#3#7???8020,1^#?#??????????????8!&6$28#3#7???8027,1^#?#??????????????8!&6$28#3#7???8026,1^#?#??????????????8!&6$28#3#7???8025,1^#?#??????????????8!&6$28#3#7???8024,1^#?#??????????????8!&6$28#3#7???801;,1^#?#??????????????8!&6$28#3#7???801:,1^#?#??????????????8!&6$28#3#7???8019,1^#?#??????????????8!&6$28#3#7???8018,1^#?#??????????????8!&6$28#3#7???801?,1^#?#??????????????8!&6$28#3#7???801>,1^#?#??????????????8!&6$28#3#7???801=,1^#?#??????????????8!&6$28#3#7???801<,1^#?#??????????????8!&6$28#3#7???8013,1^#?#??????????????8!&6$28#3#7???8012,1^#?#??????????????8!&6$28#3#7???8011,1^#?#??????????????8!&6$28#3#7???8010,1^#?#??????????????8!&6$28#3#7???8017,1^#?#??????????????8!&6$28#3#7???8016,1^#?#??????????????8!&6$28#3#7???8015,1^#?#??????????????8!&6$28#3#7???8014,1^#?#??????????????8!&6$28#3#7???800;,1^#?#??????????????2!&6$28#3#7???800:,1^#?#??????????????2!&6$28#3#7???8009,1^#?#??????????????2!&6$28#3#7???8008,1^#?#??????????????2!&6$28#3#7???800?,1^#?#??????????????8!&6$28#3#7???800>,1^#?#??????????????8!&6$28#3#7???800=,1^#?#??????????????8!&6$28#3#7???800<,1^#?#??????????????8!&6$28#3#7???8007,1^#?#??????????????2!&6$28#3#7???8006,1#!&6$28#3#7???8005,1#!&6$28#3#7???8004,1#!&6$28#3#7???8003,1^#?#??????????????1!&6$28#3#7???8002,1^#?#??????????????1!&6$28#3#7???8001,1^#?#??????????????1!&6$28#3#7???8000,1^#?#??????????????1!$28#10,8#:9150!$28#8,8#14334!$28#,8#41;58:;3!$2-78,8$28!$2-88,8$28'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$28#1000#7????????800&$28#20,$28#18#7>8($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100#&6$28#3#7???8090#70!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1)##10000#68<000$28##800)##10000#68<000$29##1,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
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
Definition ps0 : SR.post_spec := SR.PS 695456 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_4e8169.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 692676 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_4e8169.IT BndT_Eb_000S9.SegItab_Eb_4e8169.IT_sound BF NX0 BR XSTEP F0 PSS plan 692676 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bhnB.

Module LibSegEb_bhnC.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_4e8169.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_4e8169.IT.
Definition ENDS : list Z := [695816].
Definition STOPS1 : list Z := [695816] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$3:+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11+$28#20+&6$28#3#7???8000$14+$28#60$22$21$18$19$28#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0'$28#1000#7????????800&$28#20,$28##800($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1"%pstring).
Definition ss0 : sym_state := SS 693388 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_SRL (EVar 40) (ELit 3)), (2147450892), ELit 34); ((EVar 2), (-144), ELit 8)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_SRL (EVar 40) (ELit 3)), (2147450892), 34); ((EVar 2), (-144), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:9>08#:9>08#5=#:9>08,20##:9528+$2-:0$3$4$5$6$7$8+$2-:0+$28#60+$28#20#8$=$>$?$10$11+$28#20+&6$28#3#7???8000$14+$28#60$22$21$18$19$28#7???8000$1<$1=$1>$1?,,33!$2-90,8+$28#20!&6$28#3#7???802=,1#!&6$28#3#7???802<,1#!&6$28#3#7???8027,1#!&6$28#3#7???8026,1#!&6$28#3#7???8025,1#!&6$28#3#7???8024,1#!&6$28#3#7???802;,1#!&6$28#3#7???802:,1#!&6$28#3#7???8029,1#!&6$28#3#7???8028,1#!&6$28#3#7???801?,1#!&6$28#3#7???801>,1#!&6$28#3#7???801=,1#!&6$28#3#7???801<,1#!&6$28#3#7???8023,1#!&6$28#3#7???8022,1#!&6$28#3#7???8021,1#!&6$28#3#7???8020,1#!&6$28#3#7???8017,1#!&6$28#3#7???8016,1#!&6$28#3#7???8015,1#!&6$28#3#7???8014,1#!&6$28#3#7???801;,1#!&6$28#3#7???801:,1#!&6$28#3#7???8019,1#!&6$28#3#7???8018,1#!&6$28#3#7???800?,1#!&6$28#3#7???800>,1#!&6$28#3#7???800=,1#!&6$28#3#7???800<,1#!&6$28#3#7???8013,1#!&6$28#3#7???8012,1#!&6$28#3#7???8011,1#!&6$28#3#7???8010,1#'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0'$28#1000#7????????800&$28#20,$28##800($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
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
Definition ps0 : SR.post_spec := SR.PS 695816 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_4e8169.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 693388 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_4e8169.IT BndT_Eb_000S9.SegItab_Eb_4e8169.IT_sound BF NX0 BR XSTEP F0 PSS plan 693388 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bhnC.

Module LibSegEb_bhnD1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_4e8169.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_4e8169.IT.
Definition ENDS : list Z := [496348].
Definition STOPS1 : list Z := [496348] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$3:+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11+$28#20+&6$28#3#7???8000$14+$28#60$22$21$18$19$28#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0'$28#1000#7????????800&$28#20,$28##800($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1"%pstring).
Definition ss0 : sym_state := SS 693544 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_SRL (EVar 40) (ELit 3)), (2147450934), ELit 3)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_SRL (EVar 40) (ELit 3)), (2147450934), 3)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#792=<#792=<#5=#792=<,20##:954<+$2-:0$3$4$5$6$7$8+$2-:0+$28#1;0##18$=$>$?$10$11+$28#20+&6$28#3#7???8000$14+$28#60+$28#1;0+$28#1?0$18$19$28#7???8000$1<$1=$1>$1?,,13!&6$28#3#7???8038,1#!&6$28#3#7???8037,1#!&6$28#3#7???8036,1#'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0'$28#1000#7????????800&$28#20,$28##800($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
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
Definition ps0 : SR.post_spec := SR.PS 496348 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_4e8169.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 693544 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_4e8169.IT BndT_Eb_000S9.SegItab_Eb_4e8169.IT_sound BF NX0 BR XSTEP F0 PSS plan 693544 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bhnD1.

Module LibSegEb_bhnD2a.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_4e8169.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_4e8169.IT.
Definition ENDS : list Z := [693624].
Definition STOPS1 : list Z := [693624] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$3:+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11+$28#20+&6$28#3#7???8000$14+$28#60+$28#1;0+$28#1?0$18$19$28#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0'$28#1000#7????????800&$28#20,$28##800($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1"%pstring).
Definition ss0 : sym_state := SS 693580 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_SRL (EVar 40) (ELit 3)), (2147450942), ELit 7); ((EVar 40), (496), ELit 8)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_SRL (EVar 40) (ELit 3)), (2147450942), 7); ((EVar 40), (496), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:9578#:9578#5=#:9578,20#$3:+$2-:0$3$4$5$6$7$8+$2-:0+$28#1?8#137=80$<$=$>$?$10$11+$28#20+&6$28#3#7???8000$14+$28#60+$28#1;0+$28#1?0$18$19$28#7???8000$1<$1=$1>$1?,,19!$28#1?0,8#137=80!&6$28#3#7???8044,1#!&6$28#3#7???8043,1#!&6$28#3#7???8042,1#!&6$28#3#7???8041,1#!&6$28#3#7???8040,1#!&6$28#3#7???803?,1#!&6$28#3#7???803>,1#'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0'$28#1000#7????????800&$28#20,$28##1?0,$28#1?8#608($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
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
Definition ps0 : SR.post_spec := SR.PS 693624 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_4e8169.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 693580 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_4e8169.IT BndT_Eb_000S9.SegItab_Eb_4e8169.IT_sound BF NX0 BR XSTEP F0 PSS plan 693580 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bhnD2a.

Module LibSegEb_bhnD2b.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_4e8169.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_4e8169.IT.
Definition ENDS : list Z := [496348].
Definition STOPS1 : list Z := [496348] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$3:+$2-:0$3$4$5$6$7$8+$2-:0+$28#1?8#137=80$<$=$>$?$10$11+$28#20+&6$28#3#7???8000$14+$28#60+$28#1;0+$28#1?0$18$19$28#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",11'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0'$28#1000#7????????800&$28#20,$28##800($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1#&6$28#3#7???803>#7"%pstring).
Definition ss0 : sym_state := SS 693624 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 40), (504), ELit 12)].
Definition F0L : list SR.region := [((EVar 40), (504), 12)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#792=<#792=<#5=#792=<,20##:95:<+$2-:0$3$4$5$6$7$8+$2-:0+$28#208##1<$=$>$?$10$11+$28#208+&6$28#3#7???8000#400+$28#60+$28#1;0+$28#1?0+$28#420+$28#250$28#7???8000$1<$1=$1>$1?,,14!$28#200,4#400!$28#1?8,8+$28#1;0'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0'$28#1000#7????????800&$28#20,$28##1?8,$28#204#5?<($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1#&6$28#3#7???803>#7,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
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
Definition ps0 : SR.post_spec := SR.PS 496348 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_4e8169.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 693624 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_4e8169.IT BndT_Eb_000S9.SegItab_Eb_4e8169.IT_sound BF NX0 BR XSTEP F0 PSS plan 693624 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bhnD2b.

Module LibSegEb_bhnE.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_4e8169.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_4e8169.IT.
Definition ENDS : list Z := [739668].
Definition STOPS1 : list Z := [739668] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$3:+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11+$28#208+&6$28#3#7???8000#400+$28#60+$28#1;0+$28#1?0+$28#420+$28#250$28#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0'$28#1000#7????????800&$28#20,$28##800($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1"%pstring).
Definition ss0 : sym_state := SS 693676 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_SRL (EVar 40) (ELit 3)), (2147450954), ELit 49); ((EAlu Instr.ALU_SRL (EVar 40) (ELit 3)), (2147451012), ELit 4); ((EVar 40), (1056), ELit 32)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_SRL (EVar 40) (ELit 3)), (2147450954), 49); ((EAlu Instr.ALU_SRL (EVar 40) (ELit 3)), (2147451012), 4); ((EVar 40), (1056), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;4954#;4954#5=#;4954,20##:96;<+$2-:0$3$4$5$6$7$8+$2-:0+$28#250+$28#60+$28#420+$2-70$>$?$10$11+$28#208+&6$28#3#7???8000#400+$28#60+$28#1;0+$28#1?0+$28#420+$28#250$28#7???8000$1<$1=$1>$1?,,4;!$28#438,4#400!$28#43<,4#!$28#430,8#137;>0!$28#428,8#1000000!$28#420,8#137;;8!&6$28#3#7???8086,1#!&6$28#3#7???8085,1#!&6$28#3#7???8084,1#!&6$28#3#7???807:,1#!&6$28#3#7???8087,1#!&6$28#3#7???8075,1#!&6$28#3#7???8074,1#!&6$28#3#7???8073,1#!&6$28#3#7???8072,1#!&6$28#3#7???8079,1#!&6$28#3#7???8078,1#!&6$28#3#7???8077,1#!&6$28#3#7???8076,1#!&6$28#3#7???806=,1#!&6$28#3#7???806<,1#!&6$28#3#7???806;,1#!&6$28#3#7???806:,1#!&6$28#3#7???8071,1#!&6$28#3#7???8070,1#!&6$28#3#7???806?,1#!&6$28#3#7???806>,1#!&6$28#3#7???8065,1#!&6$28#3#7???8064,1#!&6$28#3#7???8063,1#!&6$28#3#7???8062,1#!&6$28#3#7???8069,1#!&6$28#3#7???8068,1#!&6$28#3#7???8067,1#!&6$28#3#7???8066,1#!&6$28#3#7???805=,1#!&6$28#3#7???805<,1#!&6$28#3#7???805;,1#!&6$28#3#7???805:,1#!&6$28#3#7???8061,1#!&6$28#3#7???8060,1#!&6$28#3#7???805?,1#!&6$28#3#7???805>,1#!&6$28#3#7???8055,1#!&6$28#3#7???8054,1#!&6$28#3#7???8053,1#!&6$28#3#7???8052,1#!&6$28#3#7???8059,1#!&6$28#3#7???8058,1#!&6$28#3#7???8057,1#!&6$28#3#7???8056,1#!&6$28#3#7???804=,1#!&6$28#3#7???804<,1#!&6$28#3#7???804;,1#!&6$28#3#7???804:,1#!&6$28#3#7???8051,1#!&6$28#3#7???8050,1#!&6$28#3#7???804?,1#!&6$28#3#7???804>,1#'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0'$28#1000#7????????800&$28#20,$28##420,$28#440#3<0($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
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
Definition ps0 : SR.post_spec := SR.PS 739668 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_4e8169.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 693676 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_4e8169.IT BndT_Eb_000S9.SegItab_Eb_4e8169.IT_sound BF NX0 BR XSTEP F0 PSS plan 693676 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bhnE.

Module LibSegEb_bhnF.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_4e8169.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_4e8169.IT.
Definition ENDS : list Z := [915468].
Definition STOPS1 : list Z := [915468] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$3:+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11+$28#208+&6$28#3#7???8000#400+$28#60+$28#1;0+$28#1?0+$28#420+$28#250$28#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",11'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0'$28#1000#7????????800&$28#20,$28##800($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1#&6$28#3#7???807:#1"%pstring).
Definition ss0 : sym_state := SS 693948 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 40), (976), ELit 8); ((EAlu Instr.ALU_SRL (EVar 40) (ELit 3)), (2147451012), ELit 4); ((EAlu Instr.ALU_SRL (EVar 40) (ELit 3)), (2147451020), ELit 2); ((EVar 40), (1120), ELit 4)].
Definition F0L : list SR.region := [((EVar 40), (976), 8); ((EAlu Instr.ALU_SRL (EVar 40) (ELit 3)), (2147451012), 4); ((EAlu Instr.ALU_SRL (EVar 40) (ELit 3)), (2147451020), 2); ((EVar 40), (1120), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=?80<#=?80<#5=#=?80<,20##:96?<+$2-:0$3$4$5$6$7$8+$2-:0+$28#3=0#$<$=$>$?$10$11+$28#208+&6$28#3#7???8000^#?#??????????????8+$28#60+$28#1;0+$28#1?0+$28#460+$28#250$28#7???8000$1<$1=$1>$1?,,1;!$28#460,4#!&6$28#3#7???8087,1^#?#??????????????8!&6$28#3#7???8086,1^#?#??????????????8!&6$28#3#7???8085,1^#?#??????????????8!&6$28#3#7???8084,1^#?#??????????????8!&6$28#3#7???808=,1#!&6$28#3#7???808<,1#!$28#3=0,8+$28#1?0'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0'$28#1000#7????????800&$28#20,$28##3=0,$28#3=8#88,$28#464#39<($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1#&6$28#3#7???807:#1,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
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
Definition ps0 : SR.post_spec := SR.PS 915468 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_4e8169.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 693948 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_4e8169.IT BndT_Eb_000S9.SegItab_Eb_4e8169.IT_sound BF NX0 BR XSTEP F0 PSS plan 693948 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bhnF.

Module LibSegEb_bhnG.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_4e8169.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_4e8169.IT.
Definition ENDS : list Z := [696492].
Definition STOPS1 : list Z := [696492] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$3:+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11+$28#208+&6$28#3#7???8000^#?#??????????????8+$28#60+$28#1;0+$28#1?0+$28#460+$28#250$28#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0'$28#1000#7????????800&$28#20,$28##800($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1"%pstring).
Definition ss0 : sym_state := SS 694012 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 40), (1128), ELit 8)].
Definition F0L : list SR.region := [((EVar 40), (1128), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#::0:<#::0:<#5=#::0:<,20##:970<+$2-:0$3$4$5$6$7$8+$2-:0+$28#250+$28#460$<$=$>$?$10$11+$28#208+&6$28#3#7???8000^#?#??????????????8+$28#60+$28#1;0+$28#1?0+$28#460+$28#250$28#7???8000$1<$1=$1>$1?,,12!$28#468,8$:'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0'$28#1000#7????????800&$28#20,$28##468,$28#470#390($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
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
Definition ps0 : SR.post_spec := SR.PS 696492 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_4e8169.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 694012 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_4e8169.IT BndT_Eb_000S9.SegItab_Eb_4e8169.IT_sound BF NX0 BR XSTEP F0 PSS plan 694012 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bhnG.

Module LibSegEb_bhnI.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_4e8169.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_4e8169.IT.
Definition ENDS : list Z := [698216].
Definition STOPS1 : list Z := [698216] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$3:+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11+$28#208+&6$28#3#7???8000^#?#??????????????8+$28#60+$28#1;0+$28#1?0+$28#460+$28#250$28#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0'$28#1000#7????????800&$28#20,$28##800($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1"%pstring).
Definition ss0 : sym_state := SS 694028 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_SRL (EVar 40) (ELit 3)), (2147451020), ELit 2); ((EVar 40), (592), ELit 8); ((EVar 2), (-112), ELit 8)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_SRL (EVar 40) (ELit 3)), (2147451020), 2); ((EVar 40), (592), 8); ((EVar 2), (-112), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#::768#::768#5=#::768,20##:9730+$2-:0$3$4$5$6$7$8+$2-:0+$2-70$;$<$=$>$?$10$11+$28#208+&6$28#3#7???8000^#?#??????????????8+$28#60+$28#1;0+$28#1?0+$28#460+$28#250$28#7???8000$1<$1=$1>$1?,,15!$2-70,8+$28#3;8!$28#250,8#137<38!&6$28#3#7???808=,1^#?#??????????????8!&6$28#3#7???808<,1^#?#??????????????8'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0'$28#1000#7????????800&$28#20,$28##250,$28#258#5:8($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
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
Definition ps0 : SR.post_spec := SR.PS 698216 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_4e8169.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 694028 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_4e8169.IT BndT_Eb_000S9.SegItab_Eb_4e8169.IT_sound BF NX0 BR XSTEP F0 PSS plan 694028 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bhnI.

Module LibSegEb_bhnJl.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_4e8169.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_4e8169.IT.
Definition ENDS : list Z := [889352].
Definition STOPS1 : list Z := [889352; 694092] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$3:+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11+$28#208+&6$28#3#7???8000^#?#??????????????8+$28#60+$28#1;0+$28#1?0+$28#460+$28#250$28#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",15'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0'$28#1000#7????????800&$28#20,$28##800($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1!$28#3:0,1$24'$24##??'&9$24#1#1#1!$28#3:0,8$25!$28#3;0,8$26"%pstring).
Definition ss0 : sym_state := SS 694064 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=9208#:974<#=9208#5=#=9208,20##:974<+$2-:0$3$4$5$6$7$8+$2-:0$26@#2&6$25#1$<$=$>$?$10$11+$28#208+&6$28#3#7???8000^#?#??????????????8+$28#60+$28#1;0+$28#1?0+$28#460+$28#250$28#7???8000$1<$1=$1>$1?,,15'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0'$28#1000#7????????800&$28#20,$28##800($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1!$28#3:0,1$24'$24##??'&9$24#1#1#1!$28#3:0,8$25!$28#3;0,8$26,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
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
Definition ps0 : SR.post_spec := SR.PS 889352 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_4e8169.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 694064 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_4e8169.IT BndT_Eb_000S9.SegItab_Eb_4e8169.IT_sound BF NX0 BR XSTEP F0 PSS plan 694064 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bhnJl.

Module LibSegEb_bhnJs.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_4e8169.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_4e8169.IT.
Definition ENDS : list Z := [694092].
Definition STOPS1 : list Z := [694092; 889352] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$3:+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11+$28#208+&6$28#3#7???8000^#?#??????????????8+$28#60+$28#1;0+$28#1?0+$28#460+$28#250$28#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",13'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0'$28#1000#7????????800&$28#20,$28##800($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1!$28#3:0,1$24'$24##??'&9$24#1##"%pstring).
Definition ss0 : sym_state := SS 694064 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#:974<#=9208#:974<#5=#:974<,20#$3:+$2-:0$3$4$5$6$7$8+$2-:0#$;$<$=$>$?$10$11+$28#208+&6$28#3#7???8000^#?#??????????????8+$28#60+$28#1;0+$28#1?0+$28#460+$28#250$28#7???8000$1<$1=$1>$1?,,13'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0'$28#1000#7????????800&$28#20,$28##800($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1!$28#3:0,1$24'$24##??'&9$24#1##,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
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
Definition ps0 : SR.post_spec := SR.PS 694092 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_4e8169.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 694064 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_4e8169.IT BndT_Eb_000S9.SegItab_Eb_4e8169.IT_sound BF NX0 BR XSTEP F0 PSS plan 694064 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bhnJs.
