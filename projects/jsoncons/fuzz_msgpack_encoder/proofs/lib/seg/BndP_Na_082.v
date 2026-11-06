(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_003.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Na_082 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_003ASegItab_Na_eab0ed2ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1832BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1833NX0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1832BRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1835XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1832F0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1833PSSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1834planC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1835regs0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1833kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1842BFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1843NX0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1842BRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1845XSTEPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1842F0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1843PSSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1844planC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1845regs0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1843kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1852BFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1853NX0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1852BRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1855XSTEPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1852F0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1853PSSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1854planC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1855regs0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1853kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1862BFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1863NX0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1862BRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1865XSTEPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1862F0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1863PSSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1864planC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1865regs0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1863kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1872BFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1873NX0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1872BRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1875XSTEPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1872F0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1873PSSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1874planC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1875regs0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1873kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1882BFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1883NX0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1882BRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1885XSTEPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1882F0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1883PSSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1884planC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1885regs0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1883kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1892BFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1893NX0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1892BRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1895XSTEPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1892F0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1893PSSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1894planC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1895regs0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1893kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1902BFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1903NX0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1902BRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1905XSTEPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1902F0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1903PSSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1904planC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1905regs0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1903kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1912BFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1913NX0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1912BRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1915XSTEPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1912F0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1913PSSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1914planC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1915regs0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriDs1913kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082>LibSegNa_qriDu2BFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082>LibSegNa_qriDu3NX0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082>LibSegNa_qriDu2BRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082>LibSegNa_qriDu5XSTEPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082>LibSegNa_qriDu2F0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082>LibSegNa_qriDu3PSSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082>LibSegNa_qriDu4planC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082>LibSegNa_qriDu5regs0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082>LibSegNa_qriDu3kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082>LibSegNa_qriE02BFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082>LibSegNa_qriE03NX0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082>LibSegNa_qriE02BRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082>LibSegNa_qriE05XSTEPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082>LibSegNa_qriE02F0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082>LibSegNa_qriE03PSSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082>LibSegNa_qriE04planC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082>LibSegNa_qriE05regs0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082>LibSegNa_qriE03kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriE12e12BFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriE12e13NX0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriE12e12BRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriE12e15XSTEPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriE12e12F0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriE12e13PSSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriE12e14planC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriE12e15regs0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriE12e13kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriE12e22BFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriE12e23NX0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriE12e22BRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriE12e25XSTEPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriE12e22F0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriE12e23PSSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriE12e24planC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriE12e25regs0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriE12e23kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriE12o12BFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriE12o13NX0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriE12o12BRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriE12o15XSTEPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriE12o12F0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriE12o13PSSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriE12o14planC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriE12o15regs0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_082ALibSegNa_qriE12o13kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNa_qriDs183.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [865060].
Definition STOPS1 : list Z := [865060; 854996] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8!$32#60,1#;7"%pstring).
Definition ss0 : sym_state := SS 854044 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=3324#=0;=4#=3324#5=#=3324,20##=0;=4+$2-:0$3$4$5$6$7$8$9+$21#18#17+$21#160$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24#17+$21#18$19#7???8000$32$1<$1=$1>$1?,,:%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8!$32#60,1#;7,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 865060 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriDs183.

Module LibSegNa_qriDs184.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [865060].
Definition STOPS1 : list Z := [865060; 854996] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8!$32#60,1#;8"%pstring).
Definition ss0 : sym_state := SS 854044 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=3324#=0;=4#=3324#5=#=3324,20##=0;=4+$2-:0$3$4$5$6$7$8$9+$21#18#18+$21#160$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24#18+$21#18$19#7???8000$32$1<$1=$1>$1?,,:%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8!$32#60,1#;8,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 865060 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriDs184.

Module LibSegNa_qriDs185.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [865060].
Definition STOPS1 : list Z := [865060; 854996] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8!$32#60,1#;9"%pstring).
Definition ss0 : sym_state := SS 854044 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=3324#=0;=4#=3324#5=#=3324,20##=0;=4+$2-:0$3$4$5$6$7$8$9+$21#18#19+$21#160$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24#19+$21#18$19#7???8000$32$1<$1=$1>$1?,,:%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8!$32#60,1#;9,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 865060 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriDs185.

Module LibSegNa_qriDs186.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [865060].
Definition STOPS1 : list Z := [865060; 854996] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8!$32#60,1#;:"%pstring).
Definition ss0 : sym_state := SS 854044 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=3324#=0;=4#=3324#5=#=3324,20##=0;=4+$2-:0$3$4$5$6$7$8$9+$21#18#1:+$21#160$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24#1:+$21#18$19#7???8000$32$1<$1=$1>$1?,,:%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8!$32#60,1#;:,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 865060 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriDs186.

Module LibSegNa_qriDs187.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [865060].
Definition STOPS1 : list Z := [865060; 854996] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8!$32#60,1#;;"%pstring).
Definition ss0 : sym_state := SS 854044 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=3324#=0;=4#=3324#5=#=3324,20##=0;=4+$2-:0$3$4$5$6$7$8$9+$21#18#1;+$21#160$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24#1;+$21#18$19#7???8000$32$1<$1=$1>$1?,,:%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8!$32#60,1#;;,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 865060 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriDs187.

Module LibSegNa_qriDs188.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [865060].
Definition STOPS1 : list Z := [865060; 854996] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8!$32#60,1#;<"%pstring).
Definition ss0 : sym_state := SS 854044 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=3324#=0;=4#=3324#5=#=3324,20##=0;=4+$2-:0$3$4$5$6$7$8$9+$21#18#1<+$21#160$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24#1<+$21#18$19#7???8000$32$1<$1=$1>$1?,,:%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8!$32#60,1#;<,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 865060 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriDs188.

Module LibSegNa_qriDs189.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [865060].
Definition STOPS1 : list Z := [865060; 854996] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8!$32#60,1#;="%pstring).
Definition ss0 : sym_state := SS 854044 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=3324#=0;=4#=3324#5=#=3324,20##=0;=4+$2-:0$3$4$5$6$7$8$9+$21#18#1=+$21#160$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24#1=+$21#18$19#7???8000$32$1<$1=$1>$1?,,:%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8!$32#60,1#;=,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 865060 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriDs189.

Module LibSegNa_qriDs190.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [865060].
Definition STOPS1 : list Z := [865060; 854996] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8!$32#60,1#;>"%pstring).
Definition ss0 : sym_state := SS 854044 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=3324#=0;=4#=3324#5=#=3324,20##=0;=4+$2-:0$3$4$5$6$7$8$9+$21#18#1>+$21#160$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24#1>+$21#18$19#7???8000$32$1<$1=$1>$1?,,:%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8!$32#60,1#;>,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 865060 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriDs190.

Module LibSegNa_qriDs191.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [865060].
Definition STOPS1 : list Z := [865060; 854996] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8!$32#60,1#;?"%pstring).
Definition ss0 : sym_state := SS 854044 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=3324#=0;=4#=3324#5=#=3324,20##=0;=4+$2-:0$3$4$5$6$7$8$9+$21#18#1?+$21#160$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24#1?+$21#18$19#7???8000$32$1<$1=$1>$1?,,:%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8!$32#60,1#;?,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 865060 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriDs191.

Module LibSegNa_qriDu.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [725792].
Definition STOPS1 : list Z := [725792; 854148] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",11%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221;5#1!$32#60,1$23'$23##7?"%pstring).
Definition ss0 : sym_state := SS 854044 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;1320#=0884#;1320#5=#;1320,20##=0884+$2-:0$3$4$5$6$7$8$9$24$23#$21$22#;1320$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?,,11%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221;5#1!$32#60,1$23'$23##7?,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 725792 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriDu.

Module LibSegNa_qriE0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [810712].
Definition STOPS1 : list Z := [810712; 854264] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#$;$<$=$>$?$10$11$12$13$14$22$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [].
Definition ss0 : sym_state := SS 854044 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#<5>=8#=08?8#<5>=8#5=#<5>=8,20##=08?8+$2-:0$3$4$5$6$7$8$9$22#1$<$=$>$?$10$11$12$13$14$22$16$17$18$19$1:$1;$1<$1=$1>$1?,,,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 810712 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriE0.

Module LibSegNa_qriE12e1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [810712].
Definition STOPS1 : list Z := [810712; 859764] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9$31$;$<$=$>$?$10$11$12$13$14$22$16#4$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 49) 0 3].
Definition ss0 : sym_state := SS 858584 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#<5>=8#=1>74#<5>=8#5=#<5>=8,20##=1>74+$2-:0$3$4$5$6$7$8$9$22#1$<$=$>$?$10$11$12$13$14$22$16#4$18$19$1:$1;$1<$1=$1>$1?,,1'$31##3,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 810712 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 858584 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 858584 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriE12e1.

Module LibSegNa_qriE12e2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [810712].
Definition STOPS1 : list Z := [810712; 860176] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9$31$;$<$=$>$?$10$11$12$13$14$22$16#8$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 49) 0 7].
Definition ss0 : sym_state := SS 858624 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#<5>=8#=2010#<5>=8#5=#<5>=8,20##=2010+$2-:0$3$4$5$6$7$8$9$22#1$<$=$>$?$10$11$12$13$14$22$16#8$18$19$1:$1;$1<$1=$1>$1?,,1'$31##7,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 810712 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 858624 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 858624 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriE12e2.

Module LibSegNa_qriE12o1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [862896].
Definition STOPS1 : list Z := [862896; 858624] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8+$2-:0#4$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$15$16#4+$21#18+$32#220$1:$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$2#7???7?8010:0#800000000000&$2#20($2-:0#8'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400!$32#220,4$31'$31##????????(&6$32#3#7???8000#80)+$2-:0##:0$32##400"%pstring).
Definition ss0 : sym_state := SS 858584 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-160), ELit 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (70), ELit 1)].
Definition F0L : list SR.region := [((EVar 2), (-160), 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (70), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=2:;0#=1:00#=2:;0#5=#=2:;0,20##=1:00+$2-:0$3$4$5$6$7$8+$2-:0+$21#18+$32#230#8$=$>$?$10$11$12+&6$32#3#7???8000$21$15$16#8+$21#18+$32#230$1:$32$1<$1=$1>$1?,,<!&6$32#3#7???8046,1#!$2-:0,8$31'$2#7???7?8010:0#800000000000&$2#20($2-:0#8'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400!$32#220,4$31'$31##????????(&6$32#3#7???8000#80)+$2-:0##:0$32##400,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 862896 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 858584 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 858584 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriE12o1.
