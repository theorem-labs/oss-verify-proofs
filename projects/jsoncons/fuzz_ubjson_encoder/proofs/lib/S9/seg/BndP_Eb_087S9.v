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

Module LibSegEb_duA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_99f177.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_99f177.IT.
Definition ENDS : list Z := [427612].
Definition STOPS1 : list Z := [427612] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; ELit 691812; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; ELit 1319120; ELit 91005; (EVar 33); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",='$2#7???7?811000#800000000000&$2#10($2-930#930,$2-930#930%#10000#13?000'$21#7???7?811000#7?????????>?'$22##1????)$2-930#930$21#+$22#1!##7???:<68,8#!##7???:<70,8#!##146==8,1#1!##1=7<7<,1#1!##1460?8,8#7???8000"%pstring).
Definition ss0 : sym_state := SS 410984 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-2352), ELit 2352)].
Definition F0L : list SR.region := [(EVar 2, (-2352), 2352)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#6865<#6865<#5=#6865<,20##68554+$2-930$3$4$5$6$7+$2-70^#?#???????????????$21##73#73#$?$10$11#:#16386#15=<:+$2-28$21#9+$2-8?8^#:#:::::::::::::::^#?#???????????????#25$1<$1=$1>$1?,,3>!$2-8?4,1#73!$2-900,8#16386!$2-8?8,1#!$2-908,8#16384!$2-910,8^#?#???????????????!$2-8?1,1#!$2-8?2,1#!$2-8?3,1#!$2-8?5,1#!$2-8?6,1#!$2-8?7,1#!$2-911,1#!$2-912,1#!$2-913,1#!$2-914,1#!$2-915,1#!$2-916,1#!$2-917,1#!$2-918,1#!$2-928,8+$2->8!$2-920,8#209<1!$2-=8,8$1;!$2-=0,8$1:!$2-<8,8$19!$2-<0,8$18!$2-;8,8$17!$2-;0,8$16!$2-:8,8$15!$2-:0,8$14!$2-98,8$13!$2-90,8+$2-30!$2-88,8#1420=0!$2-80,8#1637=!$2-78,8#694=<!$2-60,8+$2-30!$2-58,8+$2-30!$2-68,8+$2-30!$2-18,8$?!$2-20,8$>!$2-28,8$=!$2-30,8$21!$2-8,8$11!$2-10,8$10!$2-50,8$12!$2-48,8$9!$2-40,8$8!$2-38,8#:8>64'$2#7???7?811000#800000000000&$2#10($2-930#930,$2-930#8,$2-8?0#818,$2-70#8%#10000#13?000'$21#7???7?811000#7?????????>?'$22##1????)$2-930#930$21#+$22#1!##7???:<68,8#!##7???:<70,8#!##146==8,1#1!##1=7<7<,1#1!##1460?8,8#7???8000,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 427612 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_99f177.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 410984 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_99f177.IT BndT_Eb_001S9.SegItab_Eb_99f177.IT_sound BF NX0 BR XSTEP F0 PSS plan 410984 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_duA.

Module LibSegEb_duB.
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
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7+$2#8<0$9$:$;$<$=$>$?$10$11$12#16386$78$79$7:$7;+$2#38^#:#:::::::::::::::^#?#???????????????#25$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2>'$2#7???7?811000#800000000000&$2#10($2-380#<40,$2-380#<40%#10000#13?000'$21#7???7?811000#7?????????>?'$22##1????)$2-380#<40$21#+$22#1#&6$2#3#7???80=>#18!##7???:<68,8#!##7???:<70,8#(##1420=0#4(##1420=8#8(##1420>0#8(##1420?0#8(##1420?8#8(##142108#8(##142128#8(##142130#8(##142158#4!$2#8;8,8#694=<!$2#8;0,8#1637=!$2#8:8,8#1420=0!$2#8:0,8+$2#900!$2#898,8$13!$2#890,8$14!$2#888,8$15!$2#880,8$16!$2#878,8$17!$2#870,8$18!$2#868,8$19!$2#860,8$1:!$2#858,8$1;!##13?758,8#127448!$2#8=8,8+$2#900!##69:1<0,8$28!##14215<,4#????????!##1420=0,4#5!##142130,8#!##142128,8#69:998!##142158,4#!##142160,4#????????!##146==9,1#1!##1460?8,8#7???8000!##13?8=0,8#12?<30!$2#900,8$21"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#6451<#6451<#5=#6451<,20##127<10+$2#530$3$4#$6$7#25#7???????$21#7???????+$2#750+$2#908#1?^#?#?????????????<6#73#8#7??????8#7#1420=0#16386#$21#^#?#???????????????##$1<$1=$1>$1?,,8;!$2#5:0,8$21!$2#750,8+$2#908!##1420?8,8+$2#767!$2#4:0,8$18!$2#4:8,8#16384!$2#4;0,8#!$2#4;8,8#16384!$2#4<0,8#1420=0!$2#4<8,8#!$2#4=0,8#16384!$2#4=8,8#!$2#4>0,8#1420=0!$2#4>8,8#126??<!$2#4?8,8#16384!$2#500,8#1420=0!$2#508,8#7!$2#510,8#7??????8!$2#518,8#7???????!$2#520,8#25!$2#528,8#127740!$2#766,1#20!$2#765,1#3:!$2#764,1#65!$2#763,1#67!$2#762,1#61!$2#761,1#73!$2#760,1#75!$2#558,8^#?#???????<<<<<<<=!$2#560,8^#?#??????????>????!$2#598,8#<<<<<<<!$2#580,8#12889!$2#6>0,8$28!$2#590,8#69:1<0!$2#588,8#!$2#578,8+$2#750!$2#568,8+$2#7;0!$2#570,8+$2#858!$2#6>8,8$1;!$2#6?0,8$1:!$2#6?8,8$19!$2#700,8$18!$2#708,8$17!$2#710,8$16!$2#718,8#5!$2#720,8#69:998!$2#728,8#1!$2#730,8#69:1<0!$2#738,8#1637=!$2#740,8#1420=0!$2#748,8#127550!##1420?0,8+$2#7;0!##1420>0,8#!##1420=8,8#!##142108,8+$2#760!##142158,4^#?#???????????????!##142130,8#50!##142128,8+$2#760!##1420=0,4#5!$2#870,8#!$2#868,8#!$2#860,8#!$2#858,8#!$2#878,8#!$2#758,8+$2#900!$2#880,8$28!$2#888,8$15!$2#890,8$14!$2#898,8$13!$2#8:0,8+$2#900!$2#8:8,8#1420=0!$2#8;0,8#1637=!$2#8;8,8#6951<!$2#20,8^#?#???????????????!$2#3?,1#!$2#3>,1#!$2#3=,1#!$2#3<,1#!$2#3;,1#!$2#3:,1#!$2#39,1#!$2#38,1#!$2#37,1#!$2#36,1#!$2#35,1#!$2#34,1#!$2#33,1#!$2#32,1#!$2#31,1#!$2#30,1#!$2#2?,1#!$2#2>,1#!$2#2=,1#!$2#2<,1#!$2#2;,1#!$2#2:,1#!$2#29,1#!$2#28,1#!$2#1?,1#!$2#1>,1#!$2#1=,1#!$2#1<,1#!$2#1;,1#!$2#1:,1#!$2#19,1#!$2#18,1#'$2#7???7?811000#800000000000&$2#10($2-380#<40,$2-380#398,$2#40#460,$2#4?0#8,$2#530#28,$2#5:8#138,$2#767#?1%#10000#13?000'$21#7???7?811000#7?????????>?'$22##1????)$2-380#<40$21#+$22#1#&6$2#3#7???80=>#18!##7???:<68,8#!##7???:<70,8#(##1420=0#4(##1420=8#8(##1420>0#8(##1420?0#8(##1420?8#8(##142108#8(##142128#8(##142130#8(##142158#4!##13?758,8#127448!$2#8=8,8+$2#900!##69:1<0,8$28!##14215<,4#????????!##142160,4#????????!##146==9,1#1!##1460?8,8#7???8000!##13?8=0,8#12?<30!$2#900,8$21,8<!"%pstring).
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
End LibSegEb_duB.

Module LibSegEb_duD.
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
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7#25#7???????$22$;$<$=$>$?$10$11#7??????8#7#1420=0#16386#$21$18^#?#???????????????#$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10'$2#7???7?811000#800000000000&$2#10($2-8;0#8>0,$2-8;0#8>0%#10000#13?000'$21#7???7?811000#7?????????>?'$22##1????)$2-8;0#8>0$21#+$22#1(##1420?8#8!##1420=0,1#5!##1420?0,8+$2#280!##1420?8,8+$2#237!##142160,4#????????!##146==9,1#1!##13?8=0,8#12?<30!+$21$22#,1#"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#12815<#12815<#5=#12815<,20##128038$2$3$4$5$6$7#25#7???????$21$22#1420=0+$2#237##3$10$11##7#1420=0#16386#$21#$22$22$22$1<$1=$1>$1?,,28!##1420?8,8+$2#237!$2-90,8#!$2-88,8$21!$2-80,8#!$2-78,8#16386!$2-70,8#1420=0!$2-68,8#!$2-60,8#10>29!$2-58,8#!$2-50,8#1420=0!$2-48,8#126??<!$2-38,8#16386!$2-30,8#1420=0!$2-28,8#7!$2-20,8#!$2-18,8#7???????!$2-10,8#25!$2-8,8#128038!$2#8,8#!$2#20,8$22!$2#10,8$22!$2#,8#10>29!$2#18,8#'$2#7???7?811000#800000000000&$2#10($2-8;0#8>0,$2-8;0#820,$2-40#8,$2#28#8%#10000#13?000'$21#7???7?811000#7?????????>?'$22##1????)$2-8;0#8>0$21#+$22#1(##1420?8#8!##1420=0,1#5!##1420?0,8+$2#280!##142160,4#????????!##146==9,1#1!##13?8=0,8#12?<30!+$21$22#,1#,8<!"%pstring).
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
End LibSegEb_duD.

Module LibSegEb_duDl.
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
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7#25#7???????$21$22#1420=0$=$>$?$10$11##7#1420=0#16386#$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",<'$2#7???7?811000#800000000000&$2#10($2-70#70,$2-70#70%#10000#13?000'$21#7???7?811000#7?????????>?'$22#4:#1????)$2-70#70$21#+$22#1!##1420?0,8+$2#280!##1420?8,8+$2#237!##142118,8#126500!##69:1<0,8$28"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#12653<#12653<#5=#12653<,20##128160+$2-70$3$4$5#126500$7$22#1420=0$28$21$22$=$>$?$10$11##7#1420=0#69:1<0#$17$18$19$1:$1;$1<$1=$1>$1?,,15!$2-48,8$28!$2-40,8#!$2-38,8#16386!$2-30,8#1420=0!$2-28,8#7!$2-20,8#!$2-18,8#7???????!$2-10,8#25!$2-8,8#128160'$2#7???7?811000#800000000000&$2#10($2-70#70,$2-70#28%#10000#13?000'$21#7???7?811000#7?????????>?'$22#4:#1????)$2-70#70$21#+$22#1!##1420?0,8+$2#280!##1420?8,8+$2#237!##142118,8#126500!##69:1<0,8$28,8<!"%pstring).
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
End LibSegEb_duDl.

Module LibSegEb_duDs.
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
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7#25#7???????$21$22#1420=0$=$>$?$10$11##7#1420=0#16386$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",;'$2#7???7?811000#800000000000&$2#10($2-40#40,$2-40#40%#10000#13?000'$21#7???7?811000#7?????????>?'$22##49)$2-40#40$21#+$22#1!##1420?0,8+$2#280!##1420?8,8+$2#237!##142160,4#????????"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#78>3<#78>3<#5=#78>3<,20##126??<+$2-40$3$4$5$6$7#1420=0$22+$2#237$21$22$=$>$?$10$11$21##1420=0#16386$16$17$18$19$1:$1;$1<$1=$1>$1?,,12!$2-38,8#16386!$2-30,8#1420=0!$2-28,8#7!$2-20,8#!$2-18,8#7???????!$2-10,8#25!$2-8,8#128160'$2#7???7?811000#800000000000&$2#10($2-40#40,$2-40#8%#10000#13?000'$21#7???7?811000#7?????????>?'$22##49)$2-40#40$21#+$22#1!##1420?0,8+$2#280!##1420?8,8+$2#237!##142160,4#????????,8<!"%pstring).
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
End LibSegEb_duDs.

Module LibSegEb_duEa.
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
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",14'$2#7???7?811000#800000000000&$2#10($2-10#50,$2-10#50%#10000#13?000'$21#7???7?811000#7?????????>?'$22##42)$2-10#50$21#+$22#1(##1420?8#8!##1420?8,8+$2#277!$2#38,8#128160!$2#30,8#25!$2#28,8#7???????!$2#20,8#!$2#18,8#7!$2#10,8#1420=0!$2#8,8#16386!##1420=0,1#5!##1420?0,8+$2#2<0!##142160,4#????????"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#78>3<#78>3<#5=#78>3<,20##126??<$2$3$4$5$6$7#1420=0#7++$2$22#277#16386#7$=$>$?$10$11#16386##1420=0#1638=#7#16386$18$19#7$1;$1<$1=$1>$1?,,14!$2#8,8#1638=!$2#10,8#1420=0!$2#18,8+$22#7!$2#20,8+@-1$22#7??????8!$2#28,8#7???????!$2#30,8#25!$2#38,8#127740!##1420?8,8++$2$22#277'$2#7???7?811000#800000000000&$2#10($2-10#50,$2-10#18%#10000#13?000'$21#7???7?811000#7?????????>?'$22##42)$2-10#50$21#+$22#1(##1420?8#8!##1420=0,1#5!##1420?0,8+$2#2<0!##142160,4#????????,8<!"%pstring).
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
End LibSegEb_duEa.

Module LibSegEb_duEb.
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
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 1319120; (EVar 34); EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; ELit 0; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; (EVar 34); EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",15'$2#7???7?811000#800000000000&$2#10($2-30#70,$2-30#70%#10000#13?000'$21#7???7?811000#7?????????>?'$22#43#49)$2-30#70$21#+$22#1(##1420?8#8!##1420?8,8+$2#277!$2#38,8#128160!$2#30,8#25!$2#28,8#7???????!$2#20,8#!$2#18,8#7!$2#10,8#1420=0!$2#8,8#16386!##1420=0,1#5!##1420?0,8+$2#2<0!##142118,8#126500!##69:1<0,8$28"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#12653<#12653<#5=#12653<,20##127740+$2-30$3$4$5#126500$7#7#1420=0$28#16386#7$=$>$?$10$11+@-1$22#7??????8+$22#7#1420=0#69:1<0#7#16386$18$19#7$1;$1<$1=$1>$1?,,17!$2-8,8$28!$2#,8#7!$2#8,8#1638=!$2#10,8#1420=0!$2#18,8+$22#7!$2#20,8+@-1$22#7??????8!$2#28,8#7???????!$2#30,8#25!$2#38,8#127740!##1420?8,8++$2$22#277'$2#7???7?811000#800000000000&$2#10($2-30#70,$2-30#28%#10000#13?000'$21#7???7?811000#7?????????>?'$22#43#49)$2-30#70$21#+$22#1(##1420?8#8!##1420=0,1#5!##1420?0,8+$2#2<0!##142118,8#126500!##69:1<0,8$28,8<!"%pstring).
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
End LibSegEb_duEb.

Module LibSegEb_duEc.
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
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2>'$2#7???7?811000#800000000000&$2#10($2-840#:?0,$2-840#:?0%#10000#13?000'$21#7???7?811000#7?????????>?'$22#4:#1????)$2-840#:?0$21#+$22#1#&6$2#3#7???8046#18!##7???:<70,8#(##1420?0#8(##1420?8#8(##142108#8!##142128,8+$2#2:0!##142130,8#50!##69:1<0,8$28!$2#28,8$28!$2#68,8#128160!$2#60,8#25!$2#58,8#7???????!$2#50,8#!$2#48,8#7!$2#40,8#1420=0!$2#38,8#16386!$2#30,8#!##1420=0,1#5!##142160,4#????????!##146==9,1#1!##1460?8,8#7???8000!##13?8=0,8#12?<30!$2#=0,8#69:1<0!$2#220,8$28!$2#288,8#127550!$2#280,8#1420=0!$2#278,8#1637=!$2#270,8#69:1<0!$2#268,8#1!$2#260,8#69:998!$2#258,8#5!$2#250,8$16!$2#248,8$17!$2#240,8$18!$2#238,8$19!$2#230,8$1:!$2#228,8$1;!##142118,8#126500"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#12653<#12653<#5=#12653<,20##127570+$2#220$3$4+$2#2:6$6$7##1420=0$28###126500##50#55#54#69:1<0#1#69:998#69:1<0$16$17$18$19$1:$1;$1<$1=$1>$1?,,45!$2#248,8$28!$2#250,8$16!$2#258,8#!$2#260,8#69:998!$2#268,8#1!$2#270,8#69:1<0!$2#278,8+$22#>!$2#280,8#1420=0!$2#288,8#127570!##1420?8,8+$2#2:7!$2#2:6,1#:!$2#2:5,1#54!$2#2:4,1#55!$2#2:3,1#50!$2#2:2,1#4>!$2#2:1,1#49!$2#2:0,1#20!$2-20,8#!$2-18,8#16386!$2-10,8#7!$2-8,8#1638=!$2#,8#1420=0!$2#8,8#!$2#10,8#16386!$2#18,8#7!$2#20,8#1420=0!$2#28,8#126??<!$2#38,8#1638=!$2#40,8#1420=0!$2#48,8+$22#7!$2#50,8+@-1$22#7??????8!$2#58,8#7???????!$2#60,8#25!$2#68,8#127740!##142108,8+$2#2:0!##1420?0,8+$2#2?0'$2#7???7?811000#800000000000&$2#10($2-840#:?0,$2-840#820,$2#30#8,$2#70#1=8,$2#290#10,$2#2:7#9%#10000#13?000'$21#7???7?811000#7?????????>?'$22#4:#1????)$2-840#:?0$21#+$22#1#&6$2#3#7???8046#18!##7???:<70,8#(##1420?0#8(##1420?8#8(##142108#8!##142128,8+$2#2:0!##142130,8#50!##69:1<0,8$28!$2#30,8#!##1420=0,1#5!##142160,4#????????!##146==9,1#1!##1460?8,8#7???8000!##13?8=0,8#12?<30!$2#=0,8#69:1<0!$2#220,8$28!$2#240,8$18!$2#238,8$19!$2#230,8$1:!$2#228,8$1;!##142118,8#126500,8<!"%pstring).
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
End LibSegEb_duEc.

Module LibSegEb_duFa.
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
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 1319120; ELit 7; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; ELit 0; EVar 20; EVar 21; ELit 7; EVar 123; EVar 124; EVar 125; ELit 7; EVar 127; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",22'$2#7???7?811000#800000000000&$2#10($2-10#270,$2-10#270%#10000#13?000'$21#7???7?811000#7?????????>?'$22##42)$2-10#270$21#+$22#1(##1420?8#8!##1420?8,8++$2$22#277!$2#38,8#127740!$2#30,8#25!$2#28,8#7???????!$2#20,8&1#7??????8$22!$2#18,8+$22#7!$2#10,8#1420=0!$2#8,8#1638=!$2#:0,8#69:1<0!##69:1<0,8$28!$2#1?0,8$28!$2#258,8#127550!$2#250,8#1420=0!$2#248,8#1637=!$2#240,8#69:1<0!$2#238,8#1!$2#230,8#69:998!$2#228,8#5!$2#220,8$16!$2#218,8$17!$2#210,8$18!$2#208,8$19!$2#200,8$1:!$2#1?8,8$1;!##142118,8#126500"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#12653<#12653<#5=#12653<,20##127570+$2#1?0$3$4$5$6$7##1420=0$28###126500$>$?$10$11#69:1<0#1#69:998#69:1<0$16$17$18$19$1:$1;$1<$1=$1>$1?,,22!$2#218,8$28!$2#220,8$16!$2#228,8#!$2#230,8#69:998!$2#238,8#1!$2#240,8#69:1<0!$2#248,8+$22#>!$2#250,8#1420=0!$2#258,8#127570!##1420?8,8++$2$22#27>'$2#7???7?811000#800000000000&$2#10($2-10#270,$2-10#228%#10000#13?000'$21#7???7?811000#7?????????>?'$22##42)$2-10#270$21#+$22#1(##1420?8#8!$2#38,8#127740!$2#30,8#25!$2#28,8#7???????!$2#20,8&1#7??????8$22!$2#18,8+$22#7!$2#10,8#1420=0!$2#8,8#1638=!$2#:0,8#69:1<0!##69:1<0,8$28!$2#1?0,8$28!$2#210,8$18!$2#208,8$19!$2#200,8$1:!$2#1?8,8$1;!##142118,8#126500,8<!"%pstring).
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
End LibSegEb_duFa.

Module LibSegEb_duGa.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_4677b1.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_4677b1.IT.
Definition ENDS : list Z := [1174436].
Definition STOPS1 : list Z := [1174436] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 0; ELit 1319120; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 118; EVar 119; EVar 120; ELit 6922688; EVar 122; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",30'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#13?000'$21#7???7?811000#7?????????>?'$22##42)$2-10#10$21#+$22#1(##1420=0#4(##1420?0#8(##1420?8#8(##142108#8(##142128#8(##142130#8!##142128,8+$2#80!##142130,8#50!##69:1<0,8$28!$2#28,8$28!$2#68,8#127570!$2#60,8#1420=0!$2#58,8+$22#>!$2#50,8#69:1<0!$2#48,8#1!$2#40,8#69:998!$2#38,8#!$2#30,8$16!##1420=0,4#5!$2#1:0,8$28!$2#1=8,8#6951<!$2#1=0,8#1637=!$2#1<8,8#1420=0!$2#1<0,8+$2#220!$2#1;8,8$13!$2#1;0,8$14!$2#1:8,8$15!$2#218,8#:8>64!$2#210,8$8!$2#208,8$9!$2#200,8$12!$2#298,8#11>3=<!$2#290,8$29!$2#288,8$2:!$2#280,8$2;!$2#278,8$2<!$2#270,8$2=!$2#268,8$2>!$2#260,8$2?!$2#258,8$30"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#11>;:4#11>;:4#5=#11>;:4,20##11>3>0+$2#2:0$3$4$5$6$7$29$2:$8$28$28$=$>$?$10$11$2;$2<$2=$2>$2?$30$18$19$1:$1;$1<$1=$1>$1?,,33!##1420=0,4#5!##142130,8#!##142128,8#69:998!##142108,8#!##1420?8,8#!##1420?0,8#'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#13?000'$21#7???7?811000#7?????????>?'$22##42)$2-10#10$21#+$22#1(##1420=0#4(##1420?0#8(##1420?8#8(##142108#8(##142128#8(##142130#8!##69:1<0,8$28!$2#28,8$28!$2#68,8#127570!$2#60,8#1420=0!$2#58,8+$22#>!$2#50,8#69:1<0!$2#48,8#1!$2#40,8#69:998!$2#38,8#!$2#30,8$16!$2#1:0,8$28!$2#1=8,8#6951<!$2#1=0,8#1637=!$2#1<8,8#1420=0!$2#1<0,8+$2#220!$2#1;8,8$13!$2#1;0,8$14!$2#1:8,8$15!$2#218,8#:8>64!$2#210,8$8!$2#208,8$9!$2#200,8$12!$2#298,8#11>3=<!$2#290,8$29!$2#288,8$2:!$2#280,8$2;!$2#278,8$2<!$2#270,8$2=!$2#268,8$2>!$2#260,8$2?!$2#258,8$30,8<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_4677b1.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1205652 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_4677b1.IT BndT_Eb_000S9.SegItab_Eb_4677b1.IT_sound BF NX0 BR XSTEP F0 PSS plan 1205652 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_duGa.

Module LibSegEb_duGb1.
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
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 7; ELit 1319120; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; ELit 6922688; EVar 122; EVar 123; EVar 124; EVar 125; ELit 7; EVar 127; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",27'$2#7???7?811000#800000000000&$2#10($2-10#2:0,$2-10#2:0%#10000#13?000'$21#7???7?811000#7?????????>?'$22#43#49)$2-10#2:0$21#+$22#1(##1420?0#8(##1420?8#8(##142108#8!##142128,8+$2#2:0!##142130,8#50!##69:1<0,8$28!$2#28,8$28!$2#68,8#127740!$2#60,8#25!$2#58,8#7???????!$2#50,8&1#7??????8$22!$2#48,8+$22#7!$2#40,8#1420=0!$2#38,8#1638=!$2#30,8#7!$2#=0,8#69:1<0!$2#220,8$28!$2#288,8#127550!$2#280,8#1420=0!$2#278,8#1637=!$2#270,8#69:1<0!$2#268,8#1!$2#260,8#69:998!$2#258,8#5!$2#250,8$16!$2#248,8$17!$2#240,8$18!$2#238,8$19!$2#230,8$1:!$2#228,8$1;!##142118,8#126500"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#12653<#12653<#5=#12653<,20##127570+$2#220$3$4$5$6$7##1420=0$28###126500$>$?$10$11#69:1<0#1#69:998#69:1<0$16$17$18$19$1:$1;$1<$1=$1>$1?,,2:!$2#248,8$28!$2#250,8$16!$2#258,8#!$2#260,8#69:998!$2#268,8#1!$2#270,8#69:1<0!$2#278,8+$22#>!$2#280,8#1420=0!$2#288,8#127570!##142108,8+$2#2:0!##1420?8,8+$2#2:0!##1420?0,8+$2#2?0'$2#7???7?811000#800000000000&$2#10($2-10#2:0,$2-10#258%#10000#13?000'$21#7???7?811000#7?????????>?'$22#43#49)$2-10#2:0$21#+$22#1(##1420?0#8(##1420?8#8(##142108#8!##142128,8+$2#2:0!##142130,8#50!##69:1<0,8$28!$2#28,8$28!$2#68,8#127740!$2#60,8#25!$2#58,8#7???????!$2#50,8&1#7??????8$22!$2#48,8+$22#7!$2#40,8#1420=0!$2#38,8#1638=!$2#30,8#7!$2#=0,8#69:1<0!$2#220,8$28!$2#240,8$18!$2#238,8$19!$2#230,8$1:!$2#228,8$1;!##142118,8#126500,8<!"%pstring).
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
End LibSegEb_duGb1.

Module LibSegEb_duGb2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_4677b1.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_4677b1.IT.
Definition ENDS : list Z := [1174436].
Definition STOPS1 : list Z := [1174436] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 0; ELit 1319120; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 118; EVar 119; EVar 120; ELit 6922688; EVar 122; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",30'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#13?000'$21#7???7?811000#7?????????>?'$22#43#49)$2-10#10$21#+$22#1(##1420=0#4(##1420?0#8(##1420?8#8(##142108#8(##142128#8(##142130#8!##142128,8+$2#80!##142130,8#50!##69:1<0,8$28!$2#28,8$28!$2#68,8#127570!$2#60,8#1420=0!$2#58,8+$22#>!$2#50,8#69:1<0!$2#48,8#1!$2#40,8#69:998!$2#38,8#!$2#30,8$16!##1420=0,4#5!$2#1:0,8$28!$2#1=8,8#6951<!$2#1=0,8#1637=!$2#1<8,8#1420=0!$2#1<0,8+$2#220!$2#1;8,8$13!$2#1;0,8$14!$2#1:8,8$15!$2#218,8#:8>64!$2#210,8$8!$2#208,8$9!$2#200,8$12!$2#298,8#11>3=<!$2#290,8$29!$2#288,8$2:!$2#280,8$2;!$2#278,8$2<!$2#270,8$2=!$2#268,8$2>!$2#260,8$2?!$2#258,8$30"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#11>;:4#11>;:4#5=#11>;:4,20##11>3>0+$2#2:0$3$4$5$6$7$29$2:$8$28$28$=$>$?$10$11$2;$2<$2=$2>$2?$30$18$19$1:$1;$1<$1=$1>$1?,,33!##1420=0,4#5!##142130,8#!##142128,8#69:998!##142108,8#!##1420?8,8#!##1420?0,8#'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#13?000'$21#7???7?811000#7?????????>?'$22#43#49)$2-10#10$21#+$22#1(##1420=0#4(##1420?0#8(##1420?8#8(##142108#8(##142128#8(##142130#8!##69:1<0,8$28!$2#28,8$28!$2#68,8#127570!$2#60,8#1420=0!$2#58,8+$22#>!$2#50,8#69:1<0!$2#48,8#1!$2#40,8#69:998!$2#38,8#!$2#30,8$16!$2#1:0,8$28!$2#1=8,8#6951<!$2#1=0,8#1637=!$2#1<8,8#1420=0!$2#1<0,8+$2#220!$2#1;8,8$13!$2#1;0,8$14!$2#1:8,8$15!$2#218,8#:8>64!$2#210,8$8!$2#208,8$9!$2#200,8$12!$2#298,8#11>3=<!$2#290,8$29!$2#288,8$2:!$2#280,8$2;!$2#278,8$2<!$2#270,8$2=!$2#268,8$2>!$2#260,8$2?!$2#258,8$30,8<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_4677b1.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1205652 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_4677b1.IT BndT_Eb_000S9.SegItab_Eb_4677b1.IT_sound BF NX0 BR XSTEP F0 PSS plan 1205652 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_duGb2.

Module LibSegEb_duGc.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_4677b1.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_4677b1.IT.
Definition ENDS : list Z := [1174436].
Definition STOPS1 : list Z := [1174436] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 0; ELit 1319120; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 118; EVar 119; EVar 120; ELit 6922688; EVar 122; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",30'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#13?000'$21#7???7?811000#7?????????>?'$22#4:#1????)$2-10#10$21#+$22#1(##1420=0#4(##1420?0#8(##1420?8#8(##142108#8(##142128#8(##142130#8!##142128,8+$2#80!##142130,8#50!##69:1<0,8$28!$2#28,8$28!$2#68,8#127570!$2#60,8#1420=0!$2#58,8+$22#>!$2#50,8#69:1<0!$2#48,8#1!$2#40,8#69:998!$2#38,8#!$2#30,8$16!##1420=0,4#5!$2#1:0,8$28!$2#1=8,8#6951<!$2#1=0,8#1637=!$2#1<8,8#1420=0!$2#1<0,8+$2#220!$2#1;8,8$13!$2#1;0,8$14!$2#1:8,8$15!$2#218,8#:8>64!$2#210,8$8!$2#208,8$9!$2#200,8$12!$2#298,8#11>3=<!$2#290,8$29!$2#288,8$2:!$2#280,8$2;!$2#278,8$2<!$2#270,8$2=!$2#268,8$2>!$2#260,8$2?!$2#258,8$30"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#11>;:4#11>;:4#5=#11>;:4,20##11>3>0+$2#2:0$3$4$5$6$7$29$2:$8$28$28$=$>$?$10$11$2;$2<$2=$2>$2?$30$18$19$1:$1;$1<$1=$1>$1?,,33!##1420=0,4#5!##142130,8#!##142128,8#69:998!##142108,8#!##1420?8,8#!##1420?0,8#'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#13?000'$21#7???7?811000#7?????????>?'$22#4:#1????)$2-10#10$21#+$22#1(##1420=0#4(##1420?0#8(##1420?8#8(##142108#8(##142128#8(##142130#8!##69:1<0,8$28!$2#28,8$28!$2#68,8#127570!$2#60,8#1420=0!$2#58,8+$22#>!$2#50,8#69:1<0!$2#48,8#1!$2#40,8#69:998!$2#38,8#!$2#30,8$16!$2#1:0,8$28!$2#1=8,8#6951<!$2#1=0,8#1637=!$2#1<8,8#1420=0!$2#1<0,8+$2#220!$2#1;8,8$13!$2#1;0,8$14!$2#1:8,8$15!$2#218,8#:8>64!$2#210,8$8!$2#208,8$9!$2#200,8$12!$2#298,8#11>3=<!$2#290,8$29!$2#288,8$2:!$2#280,8$2;!$2#278,8$2<!$2#270,8$2=!$2#268,8$2>!$2#260,8$2?!$2#258,8$30,8<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_4677b1.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1205652 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_4677b1.IT BndT_Eb_000S9.SegItab_Eb_4677b1.IT_sound BF NX0 BR XSTEP F0 PSS plan 1205652 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_duGc.

Module LibSegEb_hkcA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_002S9.SegItab_Eb_f7fa76.ITR.
Definition IT : itab := BndT_Eb_002S9.SegItab_Eb_f7fa76.IT.
Definition ENDS : list Z := [701004; 700792].
Definition STOPS1 : list Z := [701004; 700792] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",15'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24$25!$21#10,8+$24$29'$24#1000#7???????????&$24#10'$25#1#800000000000'$29#1#800000000000'&1$29$25##800000000000($21##18"%pstring).
Definition ss0 : sym_state := SS 700676 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-16), ELit 16); ((EVar 33), (8), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-16), 16); ((EVar 33), (8), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#:;24<#:;178#:;24<#:;178#5;#:;158,20#$1+$2-10$3$4$5$6$7$8$9$21+$21#8+&6+$21#8#3#7???8000$24+$24$25+@-1$24@-1$25@-1$25$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,16!$2-8,8$1'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24$25!$21#10,8+$24$29'$24#1000#7???????????&$24#10'$25#1#800000000000'$29#1#800000000000'&1$29$25##800000000000($21##18,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#:;24<#:;178#:;24<#:;178#5=#:;24<,20#$1$2$3$4$5$6$7$8$9$21$25#$24+$24$25+@-1$24@-1$25@-1$25$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,17!$21#8,8$24'&4+@-1$24@-1$25@-1$25#1#1!$2-8,8$1'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#10,8+$24$29'$24#1000#7???????????&$24#10'$25#1#800000000000'$29#1#800000000000'&1$29$25##800000000000($21##18,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#:;24<#:;178#:;24<#:;178#5:#:;178,20#$1+$2-10$3$4$5$6$7$8$9$21+$21#8+&6+$21#8#3#7???8000$24+$24$25+@-1$24@-1$25@-1$25$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,17'&4+@-1$24@-1$25@-1$25##!$2-8,8$1'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24$25!$21#10,8+$24$29'$24#1000#7???????????&$24#10'$25#1#800000000000'$29#1#800000000000'&1$29$25##800000000000($21##18,3<!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PEnd 1))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s3).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s3).
Definition ps0 : SR.post_spec := SR.PS 701004 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 700792 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_002S9.SegItab_Eb_f7fa76.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 700676 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_002S9.SegItab_Eb_f7fa76.IT BndT_Eb_002S9.SegItab_Eb_f7fa76.IT_sound BF NX0 BR XSTEP F0 PSS plan 700676 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_hkcA.
