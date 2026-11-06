(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegBoil SegFn.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegCodec. Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Jb0PlanKit Jb0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require SegItab_Jb_cc7d36.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegPlanFast.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Jb_cc7d36.ITR.
Definition IT : itab := SegItab_Jb_cc7d36.IT.
Definition ENDS : list Z := [711076].
Definition STOPS1 : list Z := [711076] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := SegFn.v0_f k.
Definition L : expr := ltac:(SegCodec.D "$4"%pstring).
Definition regs0 : list expr := ltac:(SegCodec.D ",20#$1+$2-120$3$4$5$6$7$2+$2-120$:$;$<$=$>$?$10$11#20$26+&6+$24#8#3#7???8000#22?2<+&6+$24#170#3#7???8000+$24#8+$24#9+$24#170+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := ltac:(SegCodec.D ",4:%#10000#136000!##13<:38,8#7???8000!##13<:40,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#693000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#693000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#693000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#12>760###8001=<><#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#693000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126000)&6$2?#3#7???8000#10##8001=<><#10!$2-108,8+$2?#20!$2-100,8#3!$2-?8,8#1!$2-?0,8#!$2->8,8$2?!$2->0,8+&6+$24#148#3#7???8000!$2-=8,8+$24#148!$2-=0,8+&6$25#3#7???8000!$2-<8,8+&6+$24#168#3#7???8000!$2-<0,8+$24#168!$2-;8,8$2?!$2-;0,8#?>00!$2-:8,8+$24#18!$2-:0,8+&6$26#3#7???8000!$2-98,8$24!$2-90,8$25!$2-88,8+&6+$24#9#3#7???8000!$2-70,8$2?!$24#9,1#1"%pstring).
Definition ss0 : sym_state := SS 710496 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := Nat.mul 10 100.
Definition BR : list SGP.bfact := [].
Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ex1 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,2#:=9:4#:=9:4#5=#:=9:4,20#$1+$2-120$3$4$5$6$7$2+$2-120#1#2$<$=$>$?$10$11#20$26+&6+$24#8#3#7???8000#22?2<+&6+$24#170#3#7???8000+$24#8+$24#9+$24#170+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,4:%#10000#136000!##13<:38,8#7???8000!##13<:40,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#693000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#693000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#693000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#12>760###8001=<><#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#693000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126000)&6$2?#3#7???8000#10##8001=<><#10!$2-108,8+$2?#20!$2-100,8#3!$2-?8,8#1!$2-?0,8#!$2->8,8$2?!$2->0,8+&6+$24#148#3#7???8000!$2-=8,8+$24#148!$2-=0,8+&6$25#3#7???8000!$2-<8,8+&6+$24#168#3#7???8000!$2-<0,8+$24#168!$2-;8,8$2?!$2-;0,8#?>00!$2-:8,8+$24#18!$2-:0,8+&6$26#3#7???8000!$2-98,8$24!$2-90,8$25!$2-88,8+&6+$24#9#3#7???8000!$2-70,8$2?!$24#9,1#1,48!"%pstring).
Definition s1 : sym_state := snd (snd ex1).
Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool := SegFn.in_foot_f F0L b k w.
Definition in_kn0 (K : kentry) : bool := SegFn.in_kn_f kn0 K.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := SegFn.live_f SPV spoff b k.
Definition cells_of (sF : sym_state) (spoff : Z) : list kentry := SegFn.cells_of_f live in_foot in_kn0 sF spoff.
Definition spoff_of (sF : sym_state) : Z := SegFn.spoff_of_f SPV sF.
Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SegFn.ps_f 711076 regs_out0 F0L cells0.
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec := SegFn.mkps_f F0L cells_of spoff_of st.
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.
Lemma cert : SGP.cert_ok RSEGS SegItab_Jb_cc7d36.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 710496 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.
Definition seg_sound_ax := as0_plan_sound_it SegItab_Jb_cc7d36.IT SegItab_Jb_cc7d36.IT_sound BF NX0 BR XSTEP F0 PSS plan 710496 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
