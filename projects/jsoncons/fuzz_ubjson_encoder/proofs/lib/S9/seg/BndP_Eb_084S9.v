(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Eb0PlanKit Eb0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require SegPlanFast.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.seg Require BndT_Eb_001S9 BndT_Eb_002S9 BndT_Eb_000S9.

Module LibSegEb_doB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_d464f3.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_d464f3.IT.
Definition ENDS : list Z := [410908].
Definition STOPS1 : list Z := [410908] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7+$2#8<0$9$:$;$<$=$>$?$10$11$12#1?284$78$79$7:$7;+$2#38^#:#:::::::::::::::^#?#???????????????#25$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2>'$2#7???7?811000#800000000000&$2#10($2-380#<40,$2-380#<40%#10000#13?000'$21#7???7?811000#7?????????>?'$22##1????)$2-380#<40$21#+$22#1#&6$2#3#7???80=>#20!##7???;>48,8#!##7???;>50,8#(##1420=0#4(##1420=8#8(##1420>0#8(##1420?0#8(##1420?8#8(##142108#8(##142128#8(##142130#8(##142158#4!$2#8;8,8#694=<!$2#8;0,8#1?271!$2#8:8,8#1420=0!$2#8:0,8+$2#900!$2#898,8$13!$2#890,8$14!$2#888,8$15!$2#880,8$16!$2#878,8$17!$2#870,8$18!$2#868,8$19!$2#860,8$1:!$2#858,8$1;!##13?758,8#127448!$2#8=8,8+$2#900!##69:1<0,8$28!##14215<,4#????????!##1420=0,4#5!##142130,8#!##142128,8#69:998!##142158,4#!##142160,4#????????!##146==9,1#1!##1460?8,8#7???8000!##13?8=0,8#12?<30!$2#900,8$21"%pstring).
Definition ss0 : sym_state := SS 427456 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-896), ELit 3136); (ELit 0, (1319120), ELit 4); (ELit 0, (1319128), ELit 8); (ELit 0, (1319136), ELit 8); (ELit 0, (1319152), ELit 8); (ELit 0, (1319160), ELit 8); (ELit 0, (1319176), ELit 8); (ELit 0, (1319208), ELit 8); (ELit 0, (1319216), ELit 8); (ELit 0, (1319256), ELit 4)].
Definition F0L : list SR.region := [(EVar 2, (-896), 3136); (ELit 0, (1319120), 4); (ELit 0, (1319128), 8); (ELit 0, (1319136), 8); (ELit 0, (1319152), 8); (ELit 0, (1319160), 8); (ELit 0, (1319176), 8); (ELit 0, (1319208), 8); (ELit 0, (1319216), 8); (ELit 0, (1319256), 4)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#6451<#6451<#5=#6451<,20##127<10+$2#530$3$4##6>#6?#25#7???????$21#7???????+$2#750+$2#908#1?^#?#?????????????<6#73#8#7?????>>#11#1420=0#1?284#$21#^#?#???????????????###74$1=$1>$1?,,95!$2#5:0,8$21!$2#750,8+$2#908!##1420?8,8+$2#771!$2#4:0,8$18!$2#4:8,8#1?282!$2#4;0,8#!$2#4;8,8#1?282!$2#4<0,8#1420=0!$2#4<8,8#!$2#4=0,8#1?282!$2#4=8,8#!$2#4>0,8#1420=0!$2#4>8,8#126??<!$2#4?8,8#1?282!$2#500,8#1420=0!$2#508,8#11!$2#510,8#7?????>>!$2#518,8#7???????!$2#520,8#25!$2#528,8#127740!$2#770,1#20!$2#76?,1#6>!$2#76>,1#65!$2#76=,1#70!$2#76<,1#6?!$2#76;,1#20!$2#76:,1#74!$2#769,1#6?!$2#768,1#6>!$2#767,1#6>!$2#766,1#61!$2#765,1#63!$2#764,1#20!$2#763,1#3:!$2#762,1#69!$2#761,1#6<!$2#760,1#63!$2#558,8^#?#???????<<<<<<<=!$2#560,8^#?#??????????>????!$2#598,8#<<<<<<<!$2#580,8#12889!$2#6>0,8$28!$2#590,8#69:1<0!$2#588,8#!$2#578,8+$2#750!$2#568,8+$2#7;0!$2#570,8+$2#858!$2#6>8,8$1;!$2#6?0,8$1:!$2#6?8,8$19!$2#700,8$18!$2#708,8$17!$2#710,8$16!$2#718,8#5!$2#720,8#69:998!$2#728,8#1!$2#730,8#69:1<0!$2#738,8#1?271!$2#740,8#1420=0!$2#748,8#127550!##1420?0,8+$2#7;0!##1420>0,8#!##1420=8,8#!##142108,8+$2#760!##142158,4^#?#???????????????!##142130,8#50!##142128,8+$2#760!##1420=0,4#5!$2#870,8#!$2#868,8#!$2#860,8#!$2#858,8#!$2#878,8#!$2#758,8+$2#900!$2#880,8$28!$2#888,8$15!$2#890,8$14!$2#898,8$13!$2#8:0,8+$2#900!$2#8:8,8#1420=0!$2#8;0,8#1?271!$2#8;8,8#6951<!$2#20,8^#?#???????????????!$2#3?,1#!$2#3>,1#!$2#3=,1#!$2#3<,1#!$2#3;,1#!$2#3:,1#!$2#39,1#!$2#38,1#!$2#37,1#!$2#36,1#!$2#35,1#!$2#34,1#!$2#33,1#!$2#32,1#!$2#31,1#!$2#30,1#!$2#2?,1#!$2#2>,1#!$2#2=,1#!$2#2<,1#!$2#2;,1#!$2#2:,1#!$2#29,1#!$2#28,1#!$2#1?,1#!$2#1>,1#!$2#1=,1#!$2#1<,1#!$2#1;,1#!$2#1:,1#!$2#19,1#!$2#18,1#'$2#7???7?811000#800000000000&$2#10($2-380#<40,$2-380#398,$2#40#460,$2#4?0#8,$2#530#28,$2#5:8#138,$2#771#>7%#10000#13?000'$21#7???7?811000#7?????????>?'$22##1????)$2-380#<40$21#+$22#1#&6$2#3#7???80=>#20!##7???;>48,8#!##7???;>50,8#(##1420=0#4(##1420=8#8(##1420>0#8(##1420?0#8(##1420?8#8(##142108#8(##142128#8(##142130#8(##142158#4!##13?758,8#127448!$2#8=8,8+$2#900!##69:1<0,8$28!##14215<,4#????????!##142160,4#????????!##146==9,1#1!##1460?8,8#7???8000!##13?8=0,8#12?<30!$2#900,8$21,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 410908 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_d464f3.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 427456 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_d464f3.IT BndT_Eb_001S9.SegItab_Eb_d464f3.IT_sound BF NX0 BR XSTEP F0 PSS plan 427456 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_doB.

Module LibSegEb_doD.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_002S9.SegItab_Eb_ef2189.ITR.
Definition IT : itab := BndT_Eb_002S9.SegItab_Eb_ef2189.IT.
Definition ENDS : list Z := [1212764].
Definition STOPS1 : list Z := [1212764] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7#25#7???????$22$;$<$=$>$?$10$11#7?????>>#11#1420=0#1?284#$21$18^#?#???????????????#$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10'$2#7???7?811000#800000000000&$2#10($2-8;0#8>0,$2-8;0#8>0%#10000#13?000'$21#7???7?811000#7?????????>?'$22##1????)$2-8;0#8>0$21#+$22#1(##1420?8#8!##1420=0,1#5!##1420?0,8+$2#280!##1420?8,8+$2#241!##142160,4#????????!##146==9,1#1!##13?8=0,8#12?<30!+$21$22#,1#"%pstring).
Definition ss0 : sym_state := SS 1211408 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-2224), ELit 2272); (ELit 0, (1319160), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-2224), 2272); (ELit 0, (1319160), 8)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#12815<#12815<#5=#12815<,20##128038$2$3$4$5$6$7#25#7???????$21$22#1420=0+$2#241##1$10$11##11#1420=0#1?284#$21#$22$22$22$1<$1=$1>$1?,,28!##1420?8,8+$2#241!$2-90,8#!$2-88,8$21!$2-80,8#!$2-78,8#1?284!$2-70,8#1420=0!$2-68,8#!$2-60,8#10>29!$2-58,8#!$2-50,8#1420=0!$2-48,8#126??<!$2-38,8#1?284!$2-30,8#1420=0!$2-28,8#11!$2-20,8#!$2-18,8#7???????!$2-10,8#25!$2-8,8#128038!$2#8,8#!$2#20,8$22!$2#10,8$22!$2#,8#10>29!$2#18,8#'$2#7???7?811000#800000000000&$2#10($2-8;0#8>0,$2-8;0#820,$2-40#8,$2#28#8%#10000#13?000'$21#7???7?811000#7?????????>?'$22##1????)$2-8;0#8>0$21#+$22#1(##1420?8#8!##1420=0,1#5!##1420?0,8+$2#280!##142160,4#????????!##146==9,1#1!##13?8=0,8#12?<30!+$21$22#,1#,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1212764 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_002S9.SegItab_Eb_ef2189.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1211408 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_002S9.SegItab_Eb_ef2189.IT BndT_Eb_002S9.SegItab_Eb_ef2189.IT_sound BF NX0 BR XSTEP F0 PSS plan 1211408 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_doD.

Module LibSegEb_doDl.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_788e8e.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_788e8e.IT.
Definition ENDS : list Z := [1205564].
Definition STOPS1 : list Z := [1205564] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7#25#7???????$21$22#1420=0$=$>$?$10$11##11#1420=0#1?284#$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",<'$2#7???7?811000#800000000000&$2#10($2-70#70,$2-70#70%#10000#13?000'$21#7???7?811000#7?????????>?'$22#40#1????)$2-70#70$21#+$22#1!##1420?0,8+$2#280!##1420?8,8+$2#241!##142118,8#126500!##69:1<0,8$28"%pstring).
Definition ss0 : sym_state := SS 1212764 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-112), ELit 112)].
Definition F0L : list SR.region := [(EVar 2, (-112), 112)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#12653<#12653<#5=#12653<,20##128160+$2-70$3$4$5#126500$7$22#1420=0$28$21$22$=$>$?$10$11##11#1420=0#69:1<0#$17$18$19$1:$1;$1<$1=$1>$1?,,15!$2-48,8$28!$2-40,8#!$2-38,8#1?284!$2-30,8#1420=0!$2-28,8#11!$2-20,8#!$2-18,8#7???????!$2-10,8#25!$2-8,8#128160'$2#7???7?811000#800000000000&$2#10($2-70#70,$2-70#28%#10000#13?000'$21#7???7?811000#7?????????>?'$22#40#1????)$2-70#70$21#+$22#1!##1420?0,8+$2#280!##1420?8,8+$2#241!##142118,8#126500!##69:1<0,8$28,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1205564 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_788e8e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1212764 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_788e8e.IT BndT_Eb_001S9.SegItab_Eb_788e8e.IT_sound BF NX0 BR XSTEP F0 PSS plan 1212764 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_doDl.

Module LibSegEb_doDs.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_6ca162.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_6ca162.IT.
Definition ENDS : list Z := [495164].
Definition STOPS1 : list Z := [495164] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7#25#7???????$21$22#1420=0$=$>$?$10$11##11#1420=0#1?284$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",;'$2#7???7?811000#800000000000&$2#10($2-40#40,$2-40#40%#10000#13?000'$21#7???7?811000#7?????????>?'$22##3?)$2-40#40$21#+$22#1!##1420?0,8+$2#280!##1420?8,8+$2#241!##142160,4#????????"%pstring).
Definition ss0 : sym_state := SS 1212764 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-64), ELit 64)].
Definition F0L : list SR.region := [(EVar 2, (-64), 64)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#78>3<#78>3<#5=#78>3<,20##126??<+$2-40$3$4$5$6$7#1420=0$22+$2#241$21$22$=$>$?$10$11$21##1420=0#1?284$16$17$18$19$1:$1;$1<$1=$1>$1?,,12!$2-38,8#1?284!$2-30,8#1420=0!$2-28,8#11!$2-20,8#!$2-18,8#7???????!$2-10,8#25!$2-8,8#128160'$2#7???7?811000#800000000000&$2#10($2-40#40,$2-40#8%#10000#13?000'$21#7???7?811000#7?????????>?'$22##3?)$2-40#40$21#+$22#1!##1420?0,8+$2#280!##1420?8,8+$2#241!##142160,4#????????,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 495164 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_6ca162.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1212764 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_6ca162.IT BndT_Eb_000S9.SegItab_Eb_6ca162.IT_sound BF NX0 BR XSTEP F0 PSS plan 1212764 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_doDs.

Module LibSegEb_doEa.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_6ca162.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_6ca162.IT.
Definition ENDS : list Z := [495164].
Definition STOPS1 : list Z := [495164] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 1319120; (EVar 34); EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; ELit 0; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; (EVar 34); EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",14'$2#7???7?811000#800000000000&$2#10($2-10#50,$2-10#50%#10000#13?000'$21#7???7?811000#7?????????>?'$22##3>)$2-10#50$21#+$22#1(##1420?8#8!##1420?8,8+$2#281!$2#38,8#128160!$2#30,8#25!$2#28,8#7???????!$2#20,8#!$2#18,8#11!$2#10,8#1420=0!$2#8,8#1?284!##1420=0,1#5!##1420?0,8+$2#2<0!##142160,4#????????"%pstring).
Definition ss0 : sym_state := SS 1208316 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-16), ELit 80); (ELit 0, (1319160), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-16), 80); (ELit 0, (1319160), 8)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#78>3<#78>3<#5=#78>3<,20##126??<$2$3$4$5$6$7#1420=0#1++$2$22#281#1?284#1$=$>$?$10$11#1?284##1420=0#1?285#1#1?284$18$19#1$1;$1<$1=$1>$1?,,14!$2#8,8#1?285!$2#10,8#1420=0!$2#18,8+$22#11!$2#20,8+@-1$22#7?????>>!$2#28,8#7???????!$2#30,8#25!$2#38,8#127740!##1420?8,8++$2$22#281'$2#7???7?811000#800000000000&$2#10($2-10#50,$2-10#18%#10000#13?000'$21#7???7?811000#7?????????>?'$22##3>)$2-10#50$21#+$22#1(##1420?8#8!##1420=0,1#5!##1420?0,8+$2#2<0!##142160,4#????????,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 495164 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_6ca162.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1208316 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_6ca162.IT BndT_Eb_000S9.SegItab_Eb_6ca162.IT_sound BF NX0 BR XSTEP F0 PSS plan 1208316 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_doEa.

Module LibSegEb_doEb.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_788e8e.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_788e8e.IT.
Definition ENDS : list Z := [1205564].
Definition STOPS1 : list Z := [1205564] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 1319120; ELit 63; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; ELit 0; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; ELit 63; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",15'$2#7???7?811000#800000000000&$2#10($2-30#70,$2-30#70%#10000#13?000'$21#7???7?811000#7?????????>?'$22#3?#3?)$2-30#70$21#+$22#1(##1420?8#8!##1420?8,8+$2#281!$2#38,8#128160!$2#30,8#25!$2#28,8#7???????!$2#20,8#!$2#18,8#11!$2#10,8#1420=0!$2#8,8#1?284!##1420=0,1#5!##1420?0,8+$2#2<0!##142118,8#126500!##69:1<0,8$28"%pstring).
Definition ss0 : sym_state := SS 1208316 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-48), ELit 112); (ELit 0, (1319160), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-48), 112); (ELit 0, (1319160), 8)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#12653<#12653<#5=#12653<,20##127740+$2-30$3$4$5#126500$7#1#1420=0$28#1?284#1$=$>$?$10$11#7?????:?#50#1420=0#69:1<0#1#1?284$18$19#1$1;$1<$1=$1>$1?,,17!$2-8,8$28!$2#,8#1!$2#8,8#1?285!$2#10,8#1420=0!$2#18,8#50!$2#20,8#7?????:?!$2#28,8#7???????!$2#30,8#25!$2#38,8#127740!##1420?8,8+$2#2<0'$2#7???7?811000#800000000000&$2#10($2-30#70,$2-30#28%#10000#13?000'$21#7???7?811000#7?????????>?'$22#3?#3?)$2-30#70$21#+$22#1(##1420?8#8!##1420=0,1#5!##1420?0,8+$2#2<0!##142118,8#126500!##69:1<0,8$28,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1205564 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_788e8e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1208316 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_788e8e.IT BndT_Eb_001S9.SegItab_Eb_788e8e.IT_sound BF NX0 BR XSTEP F0 PSS plan 1208316 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_doEb.

Module LibSegEb_doEc.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_002S9.SegItab_Eb_e230d1.ITR.
Definition IT : itab := BndT_Eb_002S9.SegItab_Eb_e230d1.IT.
Definition ENDS : list Z := [1205564].
Definition STOPS1 : list Z := [1205564] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; (EVar 34); ELit 1319120; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; ELit 6922688; EVar 122; EVar 123; ELit 0; EVar 125; (EVar 34); EVar 127; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2>'$2#7???7?811000#800000000000&$2#10($2-840#:?0,$2-840#:?0%#10000#13?000'$21#7???7?811000#7?????????>?'$22#40#1????)$2-840#:?0$21#+$22#1#&6$2#3#7???8046#18!##7???;>50,8#(##1420?0#8(##1420?8#8(##142108#8!##142128,8+$2#2:0!##142130,8#50!##69:1<0,8$28!$2#28,8$28!$2#68,8#128160!$2#60,8#25!$2#58,8#7???????!$2#50,8#!$2#48,8#11!$2#40,8#1420=0!$2#38,8#1?284!$2#30,8#!##1420=0,1#5!##142160,4#????????!##146==9,1#1!##1460?8,8#7???8000!##13?8=0,8#12?<30!$2#=0,8#69:1<0!$2#220,8$28!$2#288,8#127550!$2#280,8#1420=0!$2#278,8#1?271!$2#270,8#69:1<0!$2#268,8#1!$2#260,8#69:998!$2#258,8#5!$2#250,8$16!$2#248,8$17!$2#240,8$18!$2#238,8$19!$2#230,8$1:!$2#228,8$1;!##142118,8#126500"%pstring).
Definition ss0 : sym_state := SS 1205652 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-2112), ELit 2800); (ELit 0, (1319152), ELit 8); (ELit 0, (1319160), ELit 8); (ELit 0, (1319176), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-2112), 2800); (ELit 0, (1319152), 8); (ELit 0, (1319160), 8); (ELit 0, (1319176), 8)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#12653<#12653<#5=#12653<,20##127570+$2#220$3$4$5$6$7##1420=0$28###126500###$11#69:1<0#1#69:998#69:1<0$16$17$18$19$1:$1;$1<$1=$1>$1?,,3?!$2#248,8$28!$2#250,8$16!$2#258,8#!$2#260,8#69:998!$2#268,8#1!$2#270,8#69:1<0!$2#278,8+$22#12!$2#280,8#1420=0!$2#288,8#127570!##1420?8,8+$2#2:1!$2#2:0,1#:!$2-20,8#!$2-18,8#1?284!$2-10,8#1!$2-8,8#1?285!$2#,8#1420=0!$2#8,8#!$2#10,8#1?284!$2#18,8#1!$2#20,8#1420=0!$2#28,8#126??<!$2#38,8#1?285!$2#40,8#1420=0!$2#48,8+$22#11!$2#50,8+@-1$22#7?????>>!$2#58,8#7???????!$2#60,8#25!$2#68,8#127740!##142108,8+$2#2:0!##1420?0,8+$2#2?0'$2#7???7?811000#800000000000&$2#10($2-840#:?0,$2-840#820,$2#30#8,$2#70#1=8,$2#290#10,$2#2:1#?%#10000#13?000'$21#7???7?811000#7?????????>?'$22#40#1????)$2-840#:?0$21#+$22#1#&6$2#3#7???8046#18!##7???;>50,8#(##1420?0#8(##1420?8#8(##142108#8!##142128,8+$2#2:0!##142130,8#50!##69:1<0,8$28!$2#30,8#!##1420=0,1#5!##142160,4#????????!##146==9,1#1!##1460?8,8#7???8000!##13?8=0,8#12?<30!$2#=0,8#69:1<0!$2#220,8$28!$2#240,8$18!$2#238,8$19!$2#230,8$1:!$2#228,8$1;!##142118,8#126500,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1205564 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_002S9.SegItab_Eb_e230d1.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1205652 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_002S9.SegItab_Eb_e230d1.IT BndT_Eb_002S9.SegItab_Eb_e230d1.IT_sound BF NX0 BR XSTEP F0 PSS plan 1205652 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_doEc.

Module LibSegEb_doFa.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_002S9.SegItab_Eb_f20429.ITR.
Definition IT : itab := BndT_Eb_002S9.SegItab_Eb_f20429.IT.
Definition ENDS : list Z := [1205564].
Definition STOPS1 : list Z := [1205564] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 1319120; ELit 1; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; ELit 0; EVar 20; EVar 21; ELit 1; EVar 123; EVar 124; EVar 125; ELit 1; EVar 127; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",22'$2#7???7?811000#800000000000&$2#10($2-10#270,$2-10#270%#10000#13?000'$21#7???7?811000#7?????????>?'$22##3>)$2-10#270$21#+$22#1(##1420?8#8!##1420?8,8++$2$22#281!$2#38,8#127740!$2#30,8#25!$2#28,8#7???????!$2#20,8&1#7?????>>$22!$2#18,8+$22#11!$2#10,8#1420=0!$2#8,8#1?285!$2#:0,8#69:1<0!##69:1<0,8$28!$2#1?0,8$28!$2#258,8#127550!$2#250,8#1420=0!$2#248,8#1?271!$2#240,8#69:1<0!$2#238,8#1!$2#230,8#69:998!$2#228,8#5!$2#220,8$16!$2#218,8$17!$2#210,8$18!$2#208,8$19!$2#200,8$1:!$2#1?8,8$1;!##142118,8#126500"%pstring).
Definition ss0 : sym_state := SS 1208316 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-16), ELit 624); (ELit 0, (1319160), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-16), 624); (ELit 0, (1319160), 8)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#12653<#12653<#5=#12653<,20##127570+$2#1?0$3$4$5$6$7##1420=0$28###126500$>$?$10$11#69:1<0#1#69:998#69:1<0$16$17$18$19$1:$1;$1<$1=$1>$1?,,22!$2#218,8$28!$2#220,8$16!$2#228,8#!$2#230,8#69:998!$2#238,8#1!$2#240,8#69:1<0!$2#248,8+$22#12!$2#250,8#1420=0!$2#258,8#127570!##1420?8,8++$2$22#282'$2#7???7?811000#800000000000&$2#10($2-10#270,$2-10#228%#10000#13?000'$21#7???7?811000#7?????????>?'$22##3>)$2-10#270$21#+$22#1(##1420?8#8!$2#38,8#127740!$2#30,8#25!$2#28,8#7???????!$2#20,8&1#7?????>>$22!$2#18,8+$22#11!$2#10,8#1420=0!$2#8,8#1?285!$2#:0,8#69:1<0!##69:1<0,8$28!$2#1?0,8$28!$2#210,8$18!$2#208,8$19!$2#200,8$1:!$2#1?8,8$1;!##142118,8#126500,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1205564 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_002S9.SegItab_Eb_f20429.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1208316 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_002S9.SegItab_Eb_f20429.IT BndT_Eb_002S9.SegItab_Eb_f20429.IT_sound BF NX0 BR XSTEP F0 PSS plan 1208316 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_doFa.

Module LibSegEb_doGa.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_002S9.SegItab_Eb_fbf5e2.ITR.
Definition IT : itab := BndT_Eb_002S9.SegItab_Eb_fbf5e2.IT.
Definition ENDS : list Z := [1174436].
Definition STOPS1 : list Z := [1174436] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 0; ELit 1319120; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 118; EVar 119; EVar 120; ELit 6922688; EVar 122; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",27'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#13?000'$21#7???7?811000#7?????????>?'$22##3>)$2-10#10$21#+$22#1(##1420=0#4(##1420?0#8(##1420?8#8(##142108#8(##142128#8(##142130#8!##142128,8+$2#80!##142130,8#50!##69:1<0,8$28!$2#28,8$28!$2#68,8#127570!$2#60,8#1420=0!$2#58,8+$22#12!$2#50,8#69:1<0!$2#48,8#1!$2#40,8#69:998!$2#38,8#!$2#30,8$16!##1420=0,4#5!$2#1:0,8$28!$2#1=8,8#6951<!$2#1=0,8#1?271!$2#1<8,8#1420=0!$2#1<0,8+$2#220!$2#1;8,8$13!$2#1;0,8$14!$2#1:8,8$15!$2#218,8#:8?14!$2#210,8$8!$2#208,8$9!$2#200,8$12"%pstring).
Definition ss0 : sym_state := SS 1205652 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-16), ELit 16); (ELit 0, (1319120), ELit 4); (ELit 0, (1319152), ELit 8); (ELit 0, (1319160), ELit 8); (ELit 0, (1319176), ELit 8); (ELit 0, (1319208), ELit 8); (ELit 0, (1319216), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-16), 16); (ELit 0, (1319120), 4); (ELit 0, (1319152), 8); (ELit 0, (1319160), 8); (ELit 0, (1319176), 8); (ELit 0, (1319208), 8); (ELit 0, (1319216), 8)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#11>;:4#11>;:4#5=#11>;:4,20##:8?40+$2#250$3$4$5$6$7$8$9#2$28$28$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,2:!##1420=0,4#5!##142130,8#!##142128,8#69:998!##142108,8#!##1420?8,8#!##1420?0,8#'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#13?000'$21#7???7?811000#7?????????>?'$22##3>)$2-10#10$21#+$22#1(##1420=0#4(##1420?0#8(##1420?8#8(##142108#8(##142128#8(##142130#8!##69:1<0,8$28!$2#28,8$28!$2#68,8#127570!$2#60,8#1420=0!$2#58,8+$22#12!$2#50,8#69:1<0!$2#48,8#1!$2#40,8#69:998!$2#38,8#!$2#30,8$16!$2#1:0,8$28!$2#1=8,8#6951<!$2#1=0,8#1?271!$2#1<8,8#1420=0!$2#1<0,8+$2#220!$2#1;8,8$13!$2#1;0,8$14!$2#1:8,8$15!$2#218,8#:8?14!$2#210,8$8!$2#208,8$9!$2#200,8$12,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1174436 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_002S9.SegItab_Eb_fbf5e2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1205652 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_002S9.SegItab_Eb_fbf5e2.IT BndT_Eb_002S9.SegItab_Eb_fbf5e2.IT_sound BF NX0 BR XSTEP F0 PSS plan 1205652 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_doGa.

Module LibSegEb_doGb1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_cce71f.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_cce71f.IT.
Definition ENDS : list Z := [1205564].
Definition STOPS1 : list Z := [1205564] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 1; ELit 1319120; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; ELit 6922688; EVar 122; EVar 123; EVar 124; EVar 125; ELit 1; EVar 127; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",27'$2#7???7?811000#800000000000&$2#10($2-10#2:0,$2-10#2:0%#10000#13?000'$21#7???7?811000#7?????????>?'$22#3?#3?)$2-10#2:0$21#+$22#1(##1420?0#8(##1420?8#8(##142108#8!##142128,8+$2#2:0!##142130,8#50!##69:1<0,8$28!$2#28,8$28!$2#68,8#127740!$2#60,8#25!$2#58,8#7???????!$2#50,8#7?????:?!$2#48,8#50!$2#40,8#1420=0!$2#38,8#1?285!$2#30,8#1!$2#=0,8#69:1<0!$2#220,8$28!$2#288,8#127550!$2#280,8#1420=0!$2#278,8#1?271!$2#270,8#69:1<0!$2#268,8#1!$2#260,8#69:998!$2#258,8#5!$2#250,8$16!$2#248,8$17!$2#240,8$18!$2#238,8$19!$2#230,8$1:!$2#228,8$1;!##142118,8#126500"%pstring).
Definition ss0 : sym_state := SS 1205652 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-16), ELit 672); (ELit 0, (1319152), ELit 8); (ELit 0, (1319160), ELit 8); (ELit 0, (1319176), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-16), 672); (ELit 0, (1319152), 8); (ELit 0, (1319160), 8); (ELit 0, (1319176), 8)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#12653<#12653<#5=#12653<,20##127570+$2#220$3$4$5$6$7##1420=0$28###126500$>$?$10$11#69:1<0#1#69:998#69:1<0$16$17$18$19$1:$1;$1<$1=$1>$1?,,2:!$2#248,8$28!$2#250,8$16!$2#258,8#!$2#260,8#69:998!$2#268,8#1!$2#270,8#69:1<0!$2#278,8#51!$2#280,8#1420=0!$2#288,8#127570!##142108,8+$2#2:0!##1420?8,8+$2#2:0!##1420?0,8+$2#2?0'$2#7???7?811000#800000000000&$2#10($2-10#2:0,$2-10#258%#10000#13?000'$21#7???7?811000#7?????????>?'$22#3?#3?)$2-10#2:0$21#+$22#1(##1420?0#8(##1420?8#8(##142108#8!##142128,8+$2#2:0!##142130,8#50!##69:1<0,8$28!$2#28,8$28!$2#68,8#127740!$2#60,8#25!$2#58,8#7???????!$2#50,8#7?????:?!$2#48,8#50!$2#40,8#1420=0!$2#38,8#1?285!$2#30,8#1!$2#=0,8#69:1<0!$2#220,8$28!$2#240,8$18!$2#238,8$19!$2#230,8$1:!$2#228,8$1;!##142118,8#126500,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1205564 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_cce71f.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1205652 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_cce71f.IT BndT_Eb_001S9.SegItab_Eb_cce71f.IT_sound BF NX0 BR XSTEP F0 PSS plan 1205652 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_doGb1.

Module LibSegEb_doGb2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_002S9.SegItab_Eb_fbf5e2.ITR.
Definition IT : itab := BndT_Eb_002S9.SegItab_Eb_fbf5e2.IT.
Definition ENDS : list Z := [1174436].
Definition STOPS1 : list Z := [1174436] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 0; ELit 1319120; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 118; EVar 119; EVar 120; ELit 6922688; EVar 122; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",27'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#13?000'$21#7???7?811000#7?????????>?'$22#3?#3?)$2-10#10$21#+$22#1(##1420=0#4(##1420?0#8(##1420?8#8(##142108#8(##142128#8(##142130#8!##142128,8+$2#80!##142130,8#50!##69:1<0,8$28!$2#28,8$28!$2#68,8#127570!$2#60,8#1420=0!$2#58,8#51!$2#50,8#69:1<0!$2#48,8#1!$2#40,8#69:998!$2#38,8#!$2#30,8$16!##1420=0,4#5!$2#1:0,8$28!$2#1=8,8#6951<!$2#1=0,8#1?271!$2#1<8,8#1420=0!$2#1<0,8+$2#220!$2#1;8,8$13!$2#1;0,8$14!$2#1:8,8$15!$2#218,8#:8?14!$2#210,8$8!$2#208,8$9!$2#200,8$12"%pstring).
Definition ss0 : sym_state := SS 1205652 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-16), ELit 16); (ELit 0, (1319120), ELit 4); (ELit 0, (1319152), ELit 8); (ELit 0, (1319160), ELit 8); (ELit 0, (1319176), ELit 8); (ELit 0, (1319208), ELit 8); (ELit 0, (1319216), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-16), 16); (ELit 0, (1319120), 4); (ELit 0, (1319152), 8); (ELit 0, (1319160), 8); (ELit 0, (1319176), 8); (ELit 0, (1319208), 8); (ELit 0, (1319216), 8)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#11>;:4#11>;:4#5=#11>;:4,20##:8?40+$2#250$3$4$5$6$7$8$9#2$28$28$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,2:!##1420=0,4#5!##142130,8#!##142128,8#69:998!##142108,8#!##1420?8,8#!##1420?0,8#'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#13?000'$21#7???7?811000#7?????????>?'$22#3?#3?)$2-10#10$21#+$22#1(##1420=0#4(##1420?0#8(##1420?8#8(##142108#8(##142128#8(##142130#8!##69:1<0,8$28!$2#28,8$28!$2#68,8#127570!$2#60,8#1420=0!$2#58,8#51!$2#50,8#69:1<0!$2#48,8#1!$2#40,8#69:998!$2#38,8#!$2#30,8$16!$2#1:0,8$28!$2#1=8,8#6951<!$2#1=0,8#1?271!$2#1<8,8#1420=0!$2#1<0,8+$2#220!$2#1;8,8$13!$2#1;0,8$14!$2#1:8,8$15!$2#218,8#:8?14!$2#210,8$8!$2#208,8$9!$2#200,8$12,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1174436 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_002S9.SegItab_Eb_fbf5e2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1205652 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_002S9.SegItab_Eb_fbf5e2.IT BndT_Eb_002S9.SegItab_Eb_fbf5e2.IT_sound BF NX0 BR XSTEP F0 PSS plan 1205652 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_doGb2.

Module LibSegEb_doGc.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_002S9.SegItab_Eb_fbf5e2.ITR.
Definition IT : itab := BndT_Eb_002S9.SegItab_Eb_fbf5e2.IT.
Definition ENDS : list Z := [1174436].
Definition STOPS1 : list Z := [1174436] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 0; ELit 1319120; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 118; EVar 119; EVar 120; ELit 6922688; EVar 122; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",27'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#13?000'$21#7???7?811000#7?????????>?'$22#40#1????)$2-10#10$21#+$22#1(##1420=0#4(##1420?0#8(##1420?8#8(##142108#8(##142128#8(##142130#8!##142128,8+$2#80!##142130,8#50!##69:1<0,8$28!$2#28,8$28!$2#68,8#127570!$2#60,8#1420=0!$2#58,8+$22#12!$2#50,8#69:1<0!$2#48,8#1!$2#40,8#69:998!$2#38,8#!$2#30,8$16!##1420=0,4#5!$2#1:0,8$28!$2#1=8,8#6951<!$2#1=0,8#1?271!$2#1<8,8#1420=0!$2#1<0,8+$2#220!$2#1;8,8$13!$2#1;0,8$14!$2#1:8,8$15!$2#218,8#:8?14!$2#210,8$8!$2#208,8$9!$2#200,8$12"%pstring).
Definition ss0 : sym_state := SS 1205652 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-16), ELit 16); (ELit 0, (1319120), ELit 4); (ELit 0, (1319152), ELit 8); (ELit 0, (1319160), ELit 8); (ELit 0, (1319176), ELit 8); (ELit 0, (1319208), ELit 8); (ELit 0, (1319216), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-16), 16); (ELit 0, (1319120), 4); (ELit 0, (1319152), 8); (ELit 0, (1319160), 8); (ELit 0, (1319176), 8); (ELit 0, (1319208), 8); (ELit 0, (1319216), 8)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#11>;:4#11>;:4#5=#11>;:4,20##:8?40+$2#250$3$4$5$6$7$8$9#2$28$28$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,2:!##1420=0,4#5!##142130,8#!##142128,8#69:998!##142108,8#!##1420?8,8#!##1420?0,8#'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#13?000'$21#7???7?811000#7?????????>?'$22#40#1????)$2-10#10$21#+$22#1(##1420=0#4(##1420?0#8(##1420?8#8(##142108#8(##142128#8(##142130#8!##69:1<0,8$28!$2#28,8$28!$2#68,8#127570!$2#60,8#1420=0!$2#58,8+$22#12!$2#50,8#69:1<0!$2#48,8#1!$2#40,8#69:998!$2#38,8#!$2#30,8$16!$2#1:0,8$28!$2#1=8,8#6951<!$2#1=0,8#1?271!$2#1<8,8#1420=0!$2#1<0,8+$2#220!$2#1;8,8$13!$2#1;0,8$14!$2#1:8,8$15!$2#218,8#:8?14!$2#210,8$8!$2#208,8$9!$2#200,8$12,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1174436 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_002S9.SegItab_Eb_fbf5e2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1205652 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_002S9.SegItab_Eb_fbf5e2.IT BndT_Eb_002S9.SegItab_Eb_fbf5e2.IT_sound BF NX0 BR XSTEP F0 PSS plan 1205652 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_doGc.

Module LibSegEb_dpA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_72b87b.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_72b87b.IT.
Definition ENDS : list Z := [1208904].
Definition STOPS1 : list Z := [1208904] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20##:9144$2$3$4$5$6$7$8$9#14?3?+$2#18$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",25'$2#7???7?811000#800000000000&$2#10($2-<:0#<:0,$2-<:0#<:0%#10000#13?000#&6$2#3#7???7?8<#18!##7???:9>0,8#!##7???:9>8,8#!##800<;530,8#(##1421<0#4(##1421<8#8(##1421=0#8(##1421>0#8(##1421>8#8(##1421?8#8(##142208#8(##142248#4(##69:9:0#1!##146==8,1#1!##1=7<7<,1#1!##1460?8,8#7???8000!##13?750,8#12=72<!##13?758,8#127448!##69:1<0,8$28!##14224<,4#????????!##1421<0,4#5!##142220,8#400!##1421>0,8#!##142248,4#!##142218,8#69:9:0!##142250,4#:!##146==9,1#1!##13?8=0,8#12?<30!$2#18,4#!##13?8=8,8#130034!##142208,8#1271><!##142238,4#1"%pstring).
Definition ss0 : sym_state := SS 410968 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-3232), ELit 3232); (ELit 0, (1319360), ELit 4); (ELit 0, (1319368), ELit 8); (ELit 0, (1319376), ELit 8); (ELit 0, (1319392), ELit 8); (ELit 0, (1319400), ELit 8); (ELit 0, (1319416), ELit 8); (ELit 0, (1319432), ELit 8); (ELit 0, (1319496), ELit 4); (ELit 0, (6924704), ELit 1)].
Definition F0L : list SR.region := [(EVar 2, (-3232), 3232); (ELit 0, (1319360), 4); (ELit 0, (1319368), 8); (ELit 0, (1319376), 8); (ELit 0, (1319392), 8); (ELit 0, (1319400), 8); (ELit 0, (1319416), 8); (ELit 0, (1319432), 8); (ELit 0, (1319496), 4); (ELit 0, (6924704), 1)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#127248#127248#5=#127248,20##126?>0+$2-450$3$4#$6$7#69:1<0#1#1#5413+$2-450#14?41#5413#1#1421<0#1=#14?41#1##14?42#1#14?41#1##1#1$1<$1=$1>$1?,,<3!##142208,8#126500!$2-448,8$28!$2-440,8#1421<0!$2-438,8#126?>0!$2-428,8#14?42!$2-420,8#1421<0!$2-418,8#1!$2-410,8#7??????>!$2-408,8#7???????!$2-400,8#25!$2-3?8,8#127740!##1421>8,8#69:9:1!$2-480,8#1!$2-478,8+$2-340!$2-470,8#!$2-468,8#14?41!$2-460,8#1421<0!$2-458,8#!$2-450,8+$2-340!##69:9:0,1#30!$2-340,1#30!$2-430,8#!$2-3>8,8#!$2-3=0,8#1!$2-3>0,8#!$2-3?0,8#10>29!$2-3=8,8#!$2-380,8#!$2-1=0,8+$2#20!$2-3<8,8^#?#???????<<<<<<<=!$2-3<0,8^#?#??????????>????!$2-388,8#<<<<<<<!$2-3:0,8#12889!$2-240,8$28!$2-390,8#69:1<0!$2-398,8#!$2-3:8,8+$2-1=0!$2-3;8,8+$2-170!$2-3;0,8+$2-<8!$2-238,8$1;!$2-230,8$1:!$2-228,8$19!$2-220,8$18!$2-218,8$17!$2-210,8$16!$2-208,8#5!$2-200,8#!$2-1?8,8#1!$2-1?0,8#69:1<0!$2-1>8,8#14?3?!$2-1>0,8#1421<0!$2-1=8,8#127550!##1421>0,8#69:=:0!##1421=0,8#!##1421<8,8#!##1421?8,8#69:9:0!##142248,4^#?#???????????????!##1421<0,4#5!$2-;0,8#!$2-;8,8#!$2-<0,8#!$2-<8,8#!$2-:8,8#!$2-1<8,8+$2#18!$2-:0,8$28!$2-98,8$15!$2-90,8$14!$2-88,8$13!$2-80,8+$2#18!$2-78,8#1421<0!$2-70,8#14?3?!$2-68,8#68<6<!$2-900,8^#?#???????????????!$2-8>1,1#!$2-8>2,1#!$2-8>3,1#!$2-8>4,1#!$2-8>5,1#!$2-8>6,1#!$2-8>7,1#!$2-8>8,1#!$2-8>9,1#!$2-8>:,1#!$2-8>;,1#!$2-8><,1#!$2-8>=,1#!$2-8>>,1#!$2-8>?,1#!$2-8?0,1#!$2-8?1,1#!$2-8?2,1#!$2-8?3,1#!$2-8?4,1#!$2-8?5,1#!$2-8?6,1#!$2-8?7,1#!$2-8?8,1#!$2-901,1#!$2-902,1#!$2-903,1#!$2-904,1#!$2-905,1#!$2-906,1#!$2-907,1#!$2-908,1#!$2-940,8#:!$2-938,8#14?3?!$2-930,8+$2-60!$2-928,8#684<0!$2-918,8+$2-=8!$2-910,8#209<1!$2-60,8+$2#18!$2-58,8+$2#18!$2-50,8$12!$2-48,8+$2#18!$2-40,8#14?3?!$2-38,8#680?<!$2-8=0,8^#?#???????????????!$2-8;1,1#!$2-8;2,1#!$2-8;3,1#!$2-8;4,1#!$2-8;5,1#!$2-8;6,1#!$2-8;7,1#!$2-8;8,1#!$2-8;9,1#!$2-8;:,1#!$2-8;;,1#!$2-8;<,1#!$2-8;=,1#!$2-8;>,1#!$2-8;?,1#!$2-8<0,1#!$2-8<1,1#!$2-8<2,1#!$2-8<3,1#!$2-8<4,1#!$2-8<5,1#!$2-8<6,1#!$2-8<7,1#!$2-8<8,1#!$2-8=1,1#!$2-8=2,1#!$2-8=3,1#!$2-8=4,1#!$2-8=5,1#!$2-8=6,1#!$2-8=7,1#!$2-8=8,1#!$2-8>0,8#147;9!$2-28,8+$2#18!$2-20,8+$2#18!$2-18,8$9!$2-10,8$8!$2-8,8#:9144'$2#7???7?811000#800000000000&$2#10($2-<:0#<:0,$2-<:0#360,$2-920#8,$2-8;0#430,$2-378#38,$2-33?#??,$2-1<0#?8,$2-30#8%#10000#13?000#&6$2#3#7???7?8<#18!##7???:9>0,8#!##7???:9>8,8#!##800<;530,8#(##1421<0#4(##1421<8#8(##1421=0#8(##1421>0#8(##1421>8#8(##1421?8#8(##142208#8(##142248#4(##69:9:0#1!##146==8,1#1!##1=7<7<,1#1!##1460?8,8#7???8000!##13?750,8#12=72<!##13?758,8#127448!##69:1<0,8$28!##14224<,4#????????!##142220,8#400!##142218,8#69:9:0!##142250,4#:!##146==9,1#1!##13?8=0,8#12?<30!$2#18,4#!##13?8=8,8#130034!##142238,4#1,38!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1208904 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_72b87b.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 410968 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_72b87b.IT BndT_Eb_000S9.SegItab_Eb_72b87b.IT_sound BF NX0 BR XSTEP F0 PSS plan 410968 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_dpA.

Module LibSegEb_dpA2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_18c550.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_18c550.IT.
Definition ENDS : list Z := [692548].
Definition STOPS1 : list Z := [692548] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20##:9144$2$3$4$5$6$7$8$9#14?3?+$2#18$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1='$2#7???7?811000#800000000000&$2#10($2-<:0#<:0,$2-<:0#<:0%#10000#13?000#&6$2#3#7???7?8<#18!##7???:9>0,8#!##7???:9>8,8#!##800<;530,8#(##1421<0#4(##1421>8#8(##69:9:0#1(##69:9:1#1!##146==8,1#1!##1=7<7<,1#1!##1460?8,8#7???8000!##13?750,8#12=72<!##13?758,8#127448!##69:1<0,8$28!##14224<,4#????????!##1421<0,4#5!##142220,8#400!##1421>0,8#69:=:0!##1421>8,8#69:9:0!##142250,4#????????!##146==9,1#1!##13?8=0,8#12?<30!$2#18,4#!##13?8=8,8#130034"%pstring).
Definition ss0 : sym_state := SS 410968 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-3232), ELit 3232); (ELit 0, (1319360), ELit 4); (ELit 0, (1319400), ELit 8); (ELit 0, (6924704), ELit 1); (ELit 0, (6924705), ELit 1)].
Definition F0L : list SR.region := [(EVar 2, (-3232), 3232); (ELit 0, (1319360), 4); (ELit 0, (1319400), 8); (ELit 0, (6924704), 1); (ELit 0, (6924705), 1)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:9144#:9144#5=#:9144,20##:9144$2$3$4#2$6$7$8$9#2$28$28#69:9:2##2#1#:$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,;8!##1421<0,4#5!##1421>8,8#69:9:2!##69:9:1,1#:!$2-480,8#1!$2-478,8#14?41!$2-470,8#1!$2-468,8#14?42!$2-460,8#1421<0!$2-458,8#!$2-450,8#14?41!$2-448,8#1!$2-440,8#1421<0!$2-438,8#126??<!$2-428,8#14?42!$2-420,8#1421<0!$2-418,8#1!$2-410,8#7??????>!$2-408,8#7???????!$2-400,8#25!$2-3?8,8#127740!##69:9:0,1#30!$2-340,1#30!$2-430,8#!$2-3>8,8#!$2-3=0,8#1!$2-3>0,8#!$2-3?0,8#10>29!$2-3=8,8#!$2-380,8#!$2-1=0,8+$2#20!$2-3<8,8^#?#???????<<<<<<<=!$2-3<0,8^#?#??????????>????!$2-388,8#<<<<<<<!$2-3:0,8#12889!$2-240,8$28!$2-390,8#69:1<0!$2-398,8#!$2-3:8,8+$2-1=0!$2-3;8,8+$2-170!$2-3;0,8+$2-<8!$2-238,8$1;!$2-230,8$1:!$2-228,8$19!$2-220,8$18!$2-218,8$17!$2-210,8$16!$2-208,8#5!$2-200,8#!$2-1?8,8#1!$2-1?0,8#69:1<0!$2-1>8,8#14?3?!$2-1>0,8#1421<0!$2-1=8,8#127550!$2-;0,8#!$2-;8,8#!$2-<0,8#!$2-<8,8#!$2-:8,8#!$2-1<8,8+$2#18!$2-:0,8$28!$2-98,8$15!$2-90,8$14!$2-88,8$13!$2-80,8+$2#18!$2-78,8#1421<0!$2-70,8#14?3?!$2-68,8#68<6<!$2-900,8^#?#???????????????!$2-8>1,1#!$2-8>2,1#!$2-8>3,1#!$2-8>4,1#!$2-8>5,1#!$2-8>6,1#!$2-8>7,1#!$2-8>8,1#!$2-8>9,1#!$2-8>:,1#!$2-8>;,1#!$2-8><,1#!$2-8>=,1#!$2-8>>,1#!$2-8>?,1#!$2-8?0,1#!$2-8?1,1#!$2-8?2,1#!$2-8?3,1#!$2-8?4,1#!$2-8?5,1#!$2-8?6,1#!$2-8?7,1#!$2-8?8,1#!$2-901,1#!$2-902,1#!$2-903,1#!$2-904,1#!$2-905,1#!$2-906,1#!$2-907,1#!$2-908,1#!$2-940,8#:!$2-938,8#14?3?!$2-930,8+$2-60!$2-928,8#684<0!$2-918,8+$2-=8!$2-910,8#209<1!$2-60,8+$2#18!$2-58,8+$2#18!$2-50,8$12!$2-48,8+$2#18!$2-40,8#14?3?!$2-38,8#680?<!$2-8=0,8^#?#???????????????!$2-8;1,1#!$2-8;2,1#!$2-8;3,1#!$2-8;4,1#!$2-8;5,1#!$2-8;6,1#!$2-8;7,1#!$2-8;8,1#!$2-8;9,1#!$2-8;:,1#!$2-8;;,1#!$2-8;<,1#!$2-8;=,1#!$2-8;>,1#!$2-8;?,1#!$2-8<0,1#!$2-8<1,1#!$2-8<2,1#!$2-8<3,1#!$2-8<4,1#!$2-8<5,1#!$2-8<6,1#!$2-8<7,1#!$2-8<8,1#!$2-8=1,1#!$2-8=2,1#!$2-8=3,1#!$2-8=4,1#!$2-8=5,1#!$2-8=6,1#!$2-8=7,1#!$2-8=8,1#!$2-8>0,8#147;9!$2-28,8+$2#18!$2-20,8+$2#18!$2-18,8$9!$2-10,8$8!$2-8,8#:9144'$2#7???7?811000#800000000000&$2#10($2-<:0#<:0,$2-<:0#360,$2-920#8,$2-8;0#430,$2-378#38,$2-33?#??,$2-1<0#?8,$2-30#8%#10000#13?000#&6$2#3#7???7?8<#18!##7???:9>0,8#!##7???:9>8,8#!##800<;530,8#(##1421<0#4(##1421>8#8(##69:9:0#1(##69:9:1#1!##146==8,1#1!##1=7<7<,1#1!##1460?8,8#7???8000!##13?750,8#12=72<!##13?758,8#127448!##69:1<0,8$28!##14224<,4#????????!##142220,8#400!##1421>0,8#69:=:0!##142250,4#????????!##146==9,1#1!##13?8=0,8#12?<30!$2#18,4#!##13?8=8,8#130034,38!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 692548 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_18c550.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 410968 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_18c550.IT BndT_Eb_000S9.SegItab_Eb_18c550.IT_sound BF NX0 BR XSTEP F0 PSS plan 410968 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_dpA2.
