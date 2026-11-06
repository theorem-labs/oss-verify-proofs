(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Asan. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require asan.XIcptA. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0178. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module BndP_Na_146.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require asan.XIcptA. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0178. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.XIcptA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0178.XIcptAs0Kit.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0178.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Na_146 () := "C47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_01126LibSym7itab_ofC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_by_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_146=LibSegNa_aliB2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_146=LibSegNa_aliB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_146=LibSegNa_aliB2BRC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0178:XIcptAFast6XIAS0F7xstep_fC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_146=LibSegNa_aliB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_146=LibSegNa_aliB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_146=LibSegNa_aliB4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_146=LibSegNa_aliB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_146=LibSegNa_aliB3kn0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0178;XIcptAs0Kit5XIAS05xstepC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0178:XIcptAFast6XIAS0F:xstep_f_eqC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_146=LibSegNa_aliB3ITRC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_146=LibSegNa_aliD2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_146=LibSegNa_aliD3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_146=LibSegNa_aliD2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_146=LibSegNa_aliD2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_146=LibSegNa_aliD3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_146=LibSegNa_aliD4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_146=LibSegNa_aliD5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_146=LibSegNa_aliD3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_146=LibSegNa_aliD3ITRC1?~~~~~~~~~~~~~~~".

Module LibSegNa_aliB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(1172152, 45%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [1172244].
Definition STOPS1 : list Z := [1172244] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 33; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$2#7???7?801020#800000000000&$2#10($2-20#20'$21#6;6000#7??????????8&$21#8)##7???7000#100000001000$21##8)$2-20#20$21##8($21##8!##692530,1#1!##692528,8#692940"%pstring).
Definition ss0 : sym_state := SS 1172152 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-32), ELit 32); ((EVar 33), (0), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-32), 32); ((EVar 33), (0), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#11>314#11>314#5=#11>314,20#$1$2$3$4$5$6$7$8$9#692940#692940$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,?!$21#,8#692940!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?801020#800000000000&$2#10($2-20#20'$21#6;6000#7??????????8&$21#8)##7???7000#100000001000$21##8)$2-20#20$21##8($21##8!##692530,1#1!##692528,8#692940,30!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1172244 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1172152 regs0 kn0 = true.
Proof. apply (Mh_0128.SegPlanFast.SGF.cert_by_fast _ _ Mh_0178.XIcptAFast.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.

Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 1172152 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
End LibSegNa_aliB.

Module LibSegNa_aliD.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(1172368, 9%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [1172400].
Definition STOPS1 : list Z := [1172400] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 33; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 33) 7036928 140737488355320;
   KWord (SA (EVar 33) 0) 8 (ELit 6891840)].
Definition ss0 : sym_state := SS 1172368 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#11>3;0#11>3;0#5=#11>3;0,20#$1$2$3$4$5$6$7$8$9#692940#692940$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,2'$21#6;6000#7??????????8!$21#,8#692940,30!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1172400 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1172368 regs0 kn0 = true.
Proof. apply (Mh_0128.SegPlanFast.SGF.cert_by_fast _ _ Mh_0178.XIcptAFast.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.

Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 1172368 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
End LibSegNa_aliD.

End BndP_Na_146.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_003.
Module BndP_Na_092.
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
Ltac2 kr_t_BndP_Na_092 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_003ASegItab_Na_eab0ed2ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092ALibSegNa_qriU12q12BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092ALibSegNa_qriU12q13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092ALibSegNa_qriU12q12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092ALibSegNa_qriU12q15XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092ALibSegNa_qriU12q12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092ALibSegNa_qriU12q13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092ALibSegNa_qriU12q14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092ALibSegNa_qriU12q15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092ALibSegNa_qriU12q13kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092BLibSegNa_qriU12qD22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092BLibSegNa_qriU12qD23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092BLibSegNa_qriU12qD22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092BLibSegNa_qriU12qD25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092BLibSegNa_qriU12qD22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092BLibSegNa_qriU12qD23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092BLibSegNa_qriU12qD24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092BLibSegNa_qriU12qD25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092BLibSegNa_qriU12qD23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092BLibSegNa_qriU12qI22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092BLibSegNa_qriU12qI23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092BLibSegNa_qriU12qI22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092BLibSegNa_qriU12qI25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092BLibSegNa_qriU12qI22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092BLibSegNa_qriU12qI23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092BLibSegNa_qriU12qI24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092BLibSegNa_qriU12qI25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092BLibSegNa_qriU12qI23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU12r2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU12r3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU12r2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU12r5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU12r2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU12r3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU12r4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU12r5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU12r3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU12t2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU12t3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU12t2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU12t5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU12t2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU12t3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU12t4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU12t5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU12t3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092?LibSegNa_qriU8a2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092?LibSegNa_qriU8a3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092?LibSegNa_qriU8a2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092?LibSegNa_qriU8a5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092?LibSegNa_qriU8a2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092?LibSegNa_qriU8a3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092?LibSegNa_qriU8a4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092?LibSegNa_qriU8a5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092?LibSegNa_qriU8a3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8a02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8a03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8a02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8a05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8a02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8a03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8a04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8a05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8a03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092?LibSegNa_qriU8b2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092?LibSegNa_qriU8b3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092?LibSegNa_qriU8b2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092?LibSegNa_qriU8b5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092?LibSegNa_qriU8b2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092?LibSegNa_qriU8b3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092?LibSegNa_qriU8b4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092?LibSegNa_qriU8b5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092?LibSegNa_qriU8b3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8cL2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8cL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8cL2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8cL5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8cL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8cL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8cL4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8cL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8cL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8cS2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8cS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8cS2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8cS5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8cS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8cS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8cS4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8cS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8cS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8dL2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8dL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8dL2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8dL5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8dL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8dL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8dL4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8dL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8dL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8dS2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8dS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8dS2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8dS5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8dS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8dS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8dS4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8dS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092@LibSegNa_qriU8dS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092?LibSegNa_qriU8q2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092?LibSegNa_qriU8q3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092?LibSegNa_qriU8q2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092?LibSegNa_qriU8q5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092?LibSegNa_qriU8q2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092?LibSegNa_qriU8q3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092?LibSegNa_qriU8q4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092?LibSegNa_qriU8q5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092?LibSegNa_qriU8q3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092>LibSegNa_qriXa2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092>LibSegNa_qriXa3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092>LibSegNa_qriXa2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092>LibSegNa_qriXa5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092>LibSegNa_qriXa2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092>LibSegNa_qriXa3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092>LibSegNa_qriXa4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092>LibSegNa_qriXa5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_092>LibSegNa_qriXa3kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNa_qriU12q1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [860608].
Definition STOPS1 : list Z := [860608] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$15$16+$32#250$18$19#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8#&6+$21#10#3#7???8000#1#&6+$21#8#3#7???8000#1!$21#10,1#($21#8#1'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80)&6+$21#8#3#7???8000#2&6$32#3#7???8000#80'$2#7???7?8010:0#800000000000&$2#20!$2-90,8+&6+$21#8#3#7???8000!$2-88,8+$21#8"%pstring).
Definition ss0 : sym_state := SS 860544 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 33), (8), ELit 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (90), ELit 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (91), ELit 1)].
Definition F0L : list SR.region := [((EVar 33), (8), 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (90), 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (91), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=21<0#=21<0#5=#=21<0,20#$1+$2-:0$3$4$5$6$7$8+$2-:0#1#$<+$21#8$>$?$10$11$12+&6$32#3#7???8000$21$15$16+$32#250$18$19#7???8000$1;$1<$1=$1>$1?,,11!$21#8,1#1!&6$32#3#7???805;,1^#?#??????????????8!&6$32#3#7???805:,1^#?#??????????????8'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8#&6+$21#10#3#7???8000#1#&6+$21#8#3#7???8000#1!$21#10,1#($21#8#1'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80)&6+$21#8#3#7???8000#2&6$32#3#7???8000#80'$2#7???7?8010:0#800000000000&$2#20,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 860608 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 860544 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 860544 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriU12q1.

Module LibSegNa_qriU12qD2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [991168].
Definition STOPS1 : list Z := [991168; 860640] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16+$32#250$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400!$32#250,1$2?'$2?##??'&9$2?#1#1#1!$32#260,8#8!$32#268,8$3;'$3;#1000#800000000000)$21##1?8$32##400"%pstring).
Definition ss0 : sym_state := SS 860608 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#?1?<0#=21>0#?1?<0#5=#?1?<0,20##=21>0+$2-:0$3$4$5$6$7$8$9$3;#40$<$=$>$?$10$11$12$13$14$15$16+$32#250$18$19$1:$1;$1<$1=$1>$1?,,:'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400!$32#250,1$2?'$2?##??'&9$2?#1#1#1!$32#260,8#8!$32#268,8$3;'$3;#1000#800000000000)$21##1?8$32##400,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 991168 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 860608 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 860608 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriU12qD2.

Module LibSegNa_qriU12qI2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [854444].
Definition STOPS1 : list Z := [854444] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12+&6$32#3#7???8000$14$15$16+$32#250$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80!$32#250,1$2?'$2?##??'&9$2?#1##)$21##1?8$32##400,$32#258#18"%pstring).
Definition ss0 : sym_state := SS 860608 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_regionP) ",8+&6$32#3#7???8000#4<#1+&6$32#3#7???8000#4=#1+&6$32#3#7???8000#44#1+&6$32#3#7???8000#46#1+&6$32#3#7???8000#4:#1+&6$32#3#7???8000#4;#1+&6$32#3#7???8000#30#1+&6$32#3#7???8000#<#1"%pstring).
Definition F0L : list SR.region := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_regionR) ",8+&6$32#3#7???8000#4<#1+&6$32#3#7???8000#4=#1+&6$32#3#7???8000#44#1+&6$32#3#7???8000#46#1+&6$32#3#7???8000#4:#1+&6$32#3#7???8000#4;#1+&6$32#3#7???8000#30#1+&6$32#3#7???8000#<#1"%pstring).
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=09:<#=09:<#5=#=09:<,20#$1+$2-:0$3$4$5$6$7$8$9^#?#??????????????8$;$<$=$>$?$10$11$12+&6$32#3#7???8000$14$15$16+$32#250$18$19$1:$1;$1<$1=$1>$1?,,11!&6$32#3#7???800<,1^#?#??????????????8!&6$32#3#7???8030,1^#?#??????????????8!&6$32#3#7???804;,1^#?#??????????????8!&6$32#3#7???804:,1^#?#??????????????8!&6$32#3#7???8046,1^#?#??????????????8!&6$32#3#7???8044,1^#?#??????????????8!&6$32#3#7???804=,1^#?#??????????????8!&6$32#3#7???804<,1^#?#??????????????8'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80!$32#250,1$2?'$2?##??'&9$2?#1##)$21##1?8$32##400,$32#258#18,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 854444 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 860608 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 860608 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriU12qI2.

Module LibSegNa_qriU12r.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [854444].
Definition STOPS1 : list Z := [854444] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12+&6$32#3#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 50) 7036928 140737488354304;
   KAlign (EVar 50) 32;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 50) 0) (ELit 1024);
   KWr (SA (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) 2147450880) (ELit 128)].
Definition ss0 : sym_state := SS 860640 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_regionP) ",8+&6$32#3#7???8000#4<#1+&6$32#3#7???8000#4=#1+&6$32#3#7???8000#44#1+&6$32#3#7???8000#46#1+&6$32#3#7???8000#4:#1+&6$32#3#7???8000#4;#1+&6$32#3#7???8000#30#1+&6$32#3#7???8000#<#1"%pstring).
Definition F0L : list SR.region := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_regionR) ",8+&6$32#3#7???8000#4<#1+&6$32#3#7???8000#4=#1+&6$32#3#7???8000#44#1+&6$32#3#7???8000#46#1+&6$32#3#7???8000#4:#1+&6$32#3#7???8000#4;#1+&6$32#3#7???8000#30#1+&6$32#3#7???8000#<#1"%pstring).
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=09:<#=09:<#5=#=09:<,20#$1+$2-:0$3$4$5$6$7$8$9^#?#??????????????8$;$<$=$>$?$10$11$12+&6$32#3#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,<!&6$32#3#7???800<,1^#?#??????????????8!&6$32#3#7???8030,1^#?#??????????????8!&6$32#3#7???804;,1^#?#??????????????8!&6$32#3#7???804:,1^#?#??????????????8!&6$32#3#7???8046,1^#?#??????????????8!&6$32#3#7???8044,1^#?#??????????????8!&6$32#3#7???804=,1^#?#??????????????8!&6$32#3#7???804<,1^#?#??????????????8'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 854444 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 860640 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 860640 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriU12r.

Module LibSegNa_qriU12t.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [860224].
Definition STOPS1 : list Z := [860224] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12+&6$32#3#7???8000$14$15$16$17$18+$32#290$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 50) 7036928 140737488354304;
   KAlign (EVar 50) 32;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 50) 0) (ELit 1024);
   KWr (SA (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) 2147450880) (ELit 128);
   KWord (SA (EVar 50) 656) 1 (ELit 0)].
Definition ss0 : sym_state := SS 858932 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (82), ELit 4)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (82), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=2040#=2040#5=#=2040,20#$1+$2-:0$3$4$5$6$7$8$9^#?#??????????????8$;$<$=$>$?$10$11$12+&6$32#3#7???8000$14$15$16$17$18+$32#290$1:$1;$1<$1=$1>$1?,,9!&6$32#3#7???8055,1^#?#??????????????8!&6$32#3#7???8054,1^#?#??????????????8!&6$32#3#7???8053,1^#?#??????????????8!&6$32#3#7???8052,1^#?#??????????????8'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80!$32#290,1#,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 860224 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 858932 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 858932 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriU12t.

Module LibSegNa_qriU8a.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [839180].
Definition STOPS1 : list Z := [839180; 856656] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$39+$32#1<0$19$1:$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 50) 7036928 140737488354304;
   KAlign (EVar 50) 32;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 50) 0) (ELit 1024);
   KWr (SA (EVar 50) 448) (ELit 32);
   KRange (EVar 57) 0 18446744073709551615].
Definition ss0 : sym_state := SS 856612 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 50), (448), ELit 32)].
Definition F0L : list SR.region := [((EVar 50), (448), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#<<>0<#=1250#<<>0<#5=#<<>0<,20##=1250+$2-:0$3$4$5$6$7$8$9+$32#1<0#3;9:<:00$<$=$>$?$10$11$12$13$14$15$16$39+$32#1<0$19$1:$32$1<$1=$1>$1?,,9!$32#1=8,8#!$32#1=0,8&6@#40000000$39#1>!$32#1<8,8&4#&6@#40000000$39#1>!$32#1<0,1#'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400($32#1<0#20'$39#^#?#???????????????,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 839180 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 856612 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 856612 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriU8a.

Module LibSegNa_qriU8a0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [856612].
Definition STOPS1 : list Z := [856612] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#8$;$<$=$>$?$10$11$12+&6$32#3#7???8000$14$15$16#8$18+$32#1:0#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 50) 7036928 140737488354304;
   KAlign (EVar 50) 32;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 50) 0) (ELit 1024);
   KUnk (SA (EVar 50) 416) (ELit 8);
   KWr (SA (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) 2147450880) (ELit 128)].
Definition ss0 : sym_state := SS 856488 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (56), ELit 4)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (56), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=1224#=1224#5=#=1224,20#$1+$2-:0$3$4$5$6$7$8$9&8+&9&6$50#18#??0000@#1000000%6&6$50#8#18&8&9&6$50#28#??00&6$50#38&9&6$50#18#??0000&8+@#100000000000000$50@#10000000000&9$50#??00&8@#1000000&9$50#??0000@#100000000%6$50#18&8@#1000000&9$50#??0000@#100000000%6$50#18&8&9&6$50#28#??00&6$50#38&9&6$50#28#??00$10$11$12+&6$32#3#7???8000$14$15$16&8&8+@#100000000000000$50@#10000000000&9$50#??00&8@#1000000&9$50#??0000@#100000000%6$50#18&8+&9&6$50#18#??0000@#1000000%6&6$50#8#18&8&9&6$50#28#??00&6$50#38+$32#1<0+$32#1:0#7???8000$32$1<$1=$1>$1?,,9!&6$32#3#7???803;,1#!&6$32#3#7???803:,1#!&6$32#3#7???8039,1#!&6$32#3#7???8038,1#'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400,$32#1:0#8(&6$32#3#7???8000#80,51!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 856612 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 856488 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 856488 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriU8a0.

Module LibSegNa_qriU8b.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [825852].
Definition STOPS1 : list Z := [825852; 856668] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$39+$32#1<0$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 57) 0 18446744073709551615].
Definition ss0 : sym_state := SS 856656 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#<99?<#=125<#<99?<#5=#<99?<,20##=125<+$2-:0$3$4$5$6$7$8$9+$32#1<0&6$39#22$<$=$>$?$10$11$12$13$14$15$16$39+$32#1<0$19$1:$1;$1<$1=$1>$1?,,1'$39#^#?#???????????????,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 825852 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 856656 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 856656 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriU8b.

Module LibSegNa_qriU8cL.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [867600].
Definition STOPS1 : list Z := [867600; 859876] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$21$15$16$17+$32#1<0$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1:'$2#7???7?8010:0#800000000000&$2#20'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)+$2-:0##:0$21##1?8'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400!$21#148,1$3:'$3:##??#&6+$21#148#3#7???8000#1'&9$3:#1#1#1#&6+$21#158#3#7???8000#1#&6+$21#150#3#7???8000#1!$21#158,8$3;'$3;#1000#7??????????8&$3;#8)##7???7000#100000001000$3;##1#&6$3;#3#7???8000#1($3;##1)+$2-:0##:0$3;##1)$3;##1$21##1?8)$3;##1$32##400)##10000#6:6000$3;##1($21#150#8"%pstring).
Definition ss0 : sym_state := SS 856668 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 59), (0), ELit 1); ((EVar 33), (336), ELit 8)].
Definition F0L : list SR.region := [((EVar 59), (0), 1); ((EVar 33), (336), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=3=10#=1>>4#=3=10#5=#=3=10,20##=1>>4+$2-:0$3$4$5$6$7$8$9+$32#1<0+$21#148$<$=$>$?$10$11$12$13$21$15$16+&6+$21#148#3#7???8000+$32#1<0+$21#148#7???8000$32$1<$1=$1>$1?,,1<!$21#150,8#!$3;#,1#'$2#7???7?8010:0#800000000000&$2#20'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)+$2-:0##:0$21##1?8'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400!$21#148,1$3:'$3:##??#&6+$21#148#3#7???8000#1'&9$3:#1#1#1#&6+$21#158#3#7???8000#1#&6+$21#150#3#7???8000#1!$21#158,8$3;'$3;#1000#7??????????8&$3;#8)##7???7000#100000001000$3;##1#&6$3;#3#7???8000#1($3;##1)+$2-:0##:0$3;##1)$3;##1$21##1?8)$3;##1$32##400)##10000#6:6000$3;##1($21#150#8,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 867600 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 856668 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 856668 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriU8cL.

Module LibSegNa_qriU8cS.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [867600].
Definition STOPS1 : list Z := [867600; 859876] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$21$15$16$17+$32#1<0$19#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",<'$2#7???7?8010:0#800000000000&$2#20'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)+$2-:0##:0$21##1?8!$21#148,1$3:'$3:##??#&6+$21#148#3#7???8000#1'&9$3:#1###&6+$21#149#3#7???8000#1($21#148#2"%pstring).
Definition ss0 : sym_state := SS 856668 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 33), (328), ELit 2)].
Definition F0L : list SR.region := [((EVar 33), (328), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=3=10#=1>>4#=3=10#5=#=3=10,20##=1>>4+$2-:0$3$4$5$6$7$8$9+$32#1<0+$21#148$<$=$>$?$10$11$12$13$21$15$16+&6+$21#148#3#7???8000+$32#1<0+$21#148#7???8000$1;$1<$1=$1>$1?,,=!$21#148,1#!$21#149,1#'$2#7???7?8010:0#800000000000&$2#20'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)+$2-:0##:0$21##1?8'$3:##??#&6+$21#148#3#7???8000#1'&9$3:#1###&6+$21#149#3#7???8000#1($21#148#2,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 867600 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 856668 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 856668 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriU8cS.

Module LibSegNa_qriU8dL.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [740912].
Definition STOPS1 : list Z := [740912; 860040] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+&6+$21#148#3#7???8000+$32#1<0+$21#148#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1<%#10000#158000'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221;?#1($32#200#10(&6$32#3#7???8000#80!$21#148,1$3:'$3:##??#&6+$21#148#3#7???8000#1)$24##60$32##400)&6$24#3#7???8000#<&6$32#3#7???8000#80)&6+$21#148#3#7???8000#3&6$32#3#7???8000#80'&9$3:#1#1#1#&6+$21#158#3#7???8000#1#&6+$21#150#3#7???8000#1!$21#158,8$3;!$21#150,8$30'$3;##800000000000'$30#^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 859876 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 50), (512), ELit 16); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (64), ELit 2)].
Definition F0L : list SR.region := [((EVar 50), (512), 16); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (64), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;4>30#=1?88#;4>30#5=#;4>30,20##=1?88+$2-:0$3$4$5$6$7$8$9$24+$32#200#7$21$22#;4>30$10$11$12+&6$32#3#7???8000$21$22$24+&6+$21#148#3#7???8000+$32#1<0+$21#148#7???8000$32$1<$1=$1>$1?,,1=!$32#208,8$30!$32#200,8$3;!&6$32#3#7???8041,1#!&6$32#3#7???8040,1#%#10000#158000'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221;?#1($32#200#10(&6$32#3#7???8000#80'$3:##??#&6+$21#148#3#7???8000#1)$24##60$32##400)&6$24#3#7???8000#<&6$32#3#7???8000#80)&6+$21#148#3#7???8000#3&6$32#3#7???8000#80'&9$3:#1#1#1#&6+$21#158#3#7???8000#1#&6+$21#150#3#7???8000#1'$3;##800000000000'$30#^#?#???????????????,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 740912 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 859876 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 859876 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriU8dL.

Module LibSegNa_qriU8dS.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [740912].
Definition STOPS1 : list Z := [740912; 860040] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+&6+$21#148#3#7???8000+$32#1<0+$21#148#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",17%#10000#158000'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221;?#1($32#200#10(&6$32#3#7???8000#80!$21#148,1$3:'$3:##??#&6+$21#148#3#7???8000#1)$24##60$32##400)&6$24#3#7???8000#<&6$32#3#7???8000#80)&6+$21#148#3#7???8000#3&6$32#3#7???8000#80'&9$3:#1###&6+$21#149#3#7???8000#1"%pstring).
Definition ss0 : sym_state := SS 859876 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 50), (512), ELit 16); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (64), ELit 2)].
Definition F0L : list SR.region := [((EVar 50), (512), 16); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (64), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;4>30#=1?88#;4>30#5=#;4>30,20##=1?88+$2-:0$3$4$5$6$7$8$9$24+$32#200#7$21$22#;4>30$10$11$12+&6$32#3#7???8000$21$22$24+&6+$21#148#3#7???8000+$32#1<0+$21#148#7???8000$32$1<$1=$1>$1?,,19!$32#208,8&6$3:#1!$32#200,8+$21#149!&6$32#3#7???8041,1#!&6$32#3#7???8040,1#%#10000#158000'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221;?#1($32#200#10(&6$32#3#7???8000#80'$3:##??#&6+$21#148#3#7???8000#1)$24##60$32##400)&6$24#3#7???8000#<&6$32#3#7???8000#80)&6+$21#148#3#7???8000#3&6$32#3#7???8000#80'&9$3:#1##,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 740912 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 859876 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 859876 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriU8dS.

Module LibSegNa_qriU8q.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [854444].
Definition STOPS1 : list Z := [854444] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$15$16$17+$32#1<0$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",15'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8#&6+$21#10#3#7???8000#1#&6+$21#8#3#7???8000#1!$21#10,1#($21#8#1'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80)&6+$21#8#3#7???8000#2&6$32#3#7???8000#80'$2#7???7?8010:0#800000000000&$2#20!$2-90,8+&6+$21#8#3#7???8000!$2-88,8+$21#8!$32#1<0,1$2?'$2?##??'&9$2?#1##)$21##1?8$32##400,$32#1<8#18"%pstring).
Definition ss0 : sym_state := SS 860040 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_regionP) ",:$21#8#1+&6$32#3#7???8000#40#1+&6$32#3#7???8000#41#1+&6$32#3#7???8000#3;#1+&6$32#3#7???8000#34#1+&6$32#3#7???8000#38#1+&6$32#3#7???8000#39#1+&6$32#3#7???8000#3:#1+&6$32#3#7???8000#30#1+&6$32#3#7???8000#<#1"%pstring).
Definition F0L : list SR.region := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_regionR) ",:$21#8#1+&6$32#3#7???8000#40#1+&6$32#3#7???8000#41#1+&6$32#3#7???8000#3;#1+&6$32#3#7???8000#34#1+&6$32#3#7???8000#38#1+&6$32#3#7???8000#39#1+&6$32#3#7???8000#3:#1+&6$32#3#7???8000#30#1+&6$32#3#7???8000#<#1"%pstring).
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=09:<#=09:<#5=#=09:<,20#$1+$2-:0$3$4$5$6$7$8+$2-:0^#?#??????????????8#$<+$21#8$>$?$10$11$12+&6$32#3#7???8000$21$15$16$17+$32#1<0$19#7???8000$32$1<$1=$1>$1?,,1=!&6$32#3#7???800<,1^#?#??????????????8!&6$32#3#7???8030,1^#?#??????????????8!&6$32#3#7???803:,1^#?#??????????????8!&6$32#3#7???8039,1^#?#??????????????8!&6$32#3#7???8038,1^#?#??????????????8!&6$32#3#7???8034,1^#?#??????????????8!&6$32#3#7???803;,1^#?#??????????????8!$21#8,1#1!&6$32#3#7???8041,1^#?#??????????????8!&6$32#3#7???8040,1^#?#??????????????8'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8#&6+$21#10#3#7???8000#1#&6+$21#8#3#7???8000#1!$21#10,1#($21#8#1'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80)&6+$21#8#3#7???8000#2&6$32#3#7???8000#80'$2#7???7?8010:0#800000000000&$2#20!$32#1<0,1$2?'$2?##??'&9$2?#1##)$21##1?8$32##400,$32#1<8#18,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 854444 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 860040 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 860040 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriU8q.

Module LibSegNa_qriXa.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [534580].
Definition STOPS1 : list Z := [534580; 854472] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$32+&6$32#3#7???8000$14$15$16$17$18$19$1:$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 50) 7036928 140737488354304;
   KAlign (EVar 50) 32;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 50) 0) (ELit 1024);
   KWr (SA (EVar 50) 0) (ELit 8)].
Definition ss0 : sym_state := SS 854444 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 50), (0), ELit 8)].
Definition F0L : list SR.region := [((EVar 50), (0), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#82834#=09<8#82834#5=#82834,20##=09<8+$2-:0$3$4$5$6$7$8$9+&6$32#3#7???8000#80$<$=$>$?$10$11$32+&6$32#3#7???8000$14$15$16$17$18$19$1:$32$1<$1=$1>$1?,,5!$32#,8#45>0360>'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400($32##8,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 534580 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854444 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854444 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriXa.

End BndP_Na_092.
Module BndP_Na_088.
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
Ltac2 kr_t_BndP_Na_088 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_003ASegItab_Na_eab0ed2ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriQRF2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriQRF3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriQRF2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriQRF5XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriQRF2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriQRF3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriQRF4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriQRF5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriQRF3kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriQSW2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriQSW3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriQSW2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriQSW5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriQSW2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriQSW3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriQSW4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriQSW5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriQSW3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088@LibSegNa_qriQSW22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088@LibSegNa_qriQSW23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088@LibSegNa_qriQSW22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088@LibSegNa_qriQSW25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088@LibSegNa_qriQSW22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088@LibSegNa_qriQSW23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088@LibSegNa_qriQSW24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088@LibSegNa_qriQSW25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088@LibSegNa_qriQSW23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriQn2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriQn3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriQn2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriQn5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriQn2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriQn3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriQn4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriQn5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriQn3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriQu2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriQu3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriQu2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriQu5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriQu2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriQu3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriQu4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriQu5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriQu3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriRF2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriRF3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriRF2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriRF5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriRF2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriRF3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriRF4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriRF5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriRF3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriSF2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriSF3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriSF2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriSF5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriSF2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriSF3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriSF4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriSF5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriSF3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSF22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSF23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSF22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSF25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSF22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSF23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSF24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSF25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSF23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSG02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSG03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSG02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSG05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSG02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSG03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSG04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSG05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSG03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSG12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSG13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSG12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSG15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSG12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSG13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSG14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSG15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSG13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriSW2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriSW3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriSW2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriSW5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriSW2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriSW3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriSW4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriSW5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088>LibSegNa_qriSW3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSW22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSW23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSW22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSW25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSW22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSW23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSW24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSW25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSW23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088@LibSegNa_qriSW2c2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088@LibSegNa_qriSW2c3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088@LibSegNa_qriSW2c2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088@LibSegNa_qriSW2c5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088@LibSegNa_qriSW2c2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088@LibSegNa_qriSW2c3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088@LibSegNa_qriSW2c4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088@LibSegNa_qriSW2c5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088@LibSegNa_qriSW2c3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSWc2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSWc3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSWc2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSWc5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSWc2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSWc3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSWc4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSWc5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_088?LibSegNa_qriSWc3kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNa_qriQRF.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [854444].
Definition STOPS1 : list Z := [854444] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$15$16$17$18$19#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8#&6+$21#10#3#7???8000#1#&6+$21#8#3#7???8000#1!$21#10,1#($21#8#1'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80)&6+$21#8#3#7???8000#2&6$32#3#7???8000#80'$2#7???7?8010:0#800000000000&$2#20!$2-90,8+&6+$21#8#3#7???8000!$2-88,8+$21#8"%pstring).
Definition ss0 : sym_state := SS 859640 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_regionP) ",5$21#8#1+&6$32#3#7???8000#4#1+&6$32#3#7???8000#5#1+&6$32#3#7???8000#30#1+&6$32#3#7???8000#<#1"%pstring).
Definition F0L : list SR.region := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_regionR) ",5$21#8#1+&6$32#3#7???8000#4#1+&6$32#3#7???8000#5#1+&6$32#3#7???8000#30#1+&6$32#3#7???8000#<#1"%pstring).
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=09:<#=09:<#5=#=09:<,20#$1+$2-:0$3$4$5$6$7$8+$2-:0^#?#??????????????8#$<#1$>$?$10$11$12+&6$32#3#7???8000$21$15$16$17$18$19#7???8000$1;$1<$1=$1>$1?,,13!&6$32#3#7???800<,1^#?#??????????????8!&6$32#3#7???8030,1^#?#??????????????8!$21#8,1#1!&6$32#3#7???8005,1^#?#??????????????8!&6$32#3#7???8004,1^#?#??????????????8'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8#&6+$21#10#3#7???8000#1#&6+$21#8#3#7???8000#1!$21#10,1#($21#8#1'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80)&6+$21#8#3#7???8000#2&6$32#3#7???8000#80'$2#7???7?8010:0#800000000000&$2#20,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 854444 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 859640 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 859640 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriQRF.

Module LibSegNa_qriQSW.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [854444].
Definition STOPS1 : list Z := [854444] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$15$16$17$18$19#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",<'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8#&6+$21#10#3#7???8000#1#&6+$21#8#3#7???8000#1!$21#10,1#($21#8#1'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80)&6+$21#8#3#7???8000#2&6$32#3#7???8000#80"%pstring).
Definition ss0 : sym_state := SS 855588 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_regionP) ",4$21#8#1+&6$32#3#7???8000#>#1+&6$32#3#7???8000#?#1+&6$32#3#7???8000#<#1"%pstring).
Definition F0L : list SR.region := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_regionR) ",4$21#8#1+&6$32#3#7???8000#>#1+&6$32#3#7???8000#?#1+&6$32#3#7???8000#<#1"%pstring).
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=09:<#=09:<#5=#=09:<,20#$1+$2-:0$3$4$5$6$7$8$9^#?#??????????????8#1#$=$>$?$10$11$12+&6$32#3#7???8000$21$15$16$17$18$19#7???8000$1;$1<$1=$1>$1?,,10!&6$32#3#7???800<,1^#?#??????????????8!$21#8,1#1!&6$32#3#7???800?,1^#?#??????????????8!&6$32#3#7???800>,1^#?#??????????????8'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8#&6+$21#10#3#7???8000#1#&6+$21#8#3#7???8000#1!$21#10,1#($21#8#1'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80)&6+$21#8#3#7???8000#2&6$32#3#7???8000#80,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 854444 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 855588 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 855588 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriQSW.

Module LibSegNa_qriQSW2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [854444].
Definition STOPS1 : list Z := [854444] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$15$16+$21#8$18$19#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",?'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8#&6+$21#10#3#7???8000#1#&6+$21#8#3#7???8000#1!$21#10,1#($21#8#1'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80)&6+$21#8#3#7???8000#2&6$32#3#7???8000#80'$2#7???7?8010:0#800000000000&$2#20!$2-88,8+&6+$21#8#3#7???8000"%pstring).
Definition ss0 : sym_state := SS 859488 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_regionP) ",4$21#8#1+&6$32#3#7???8000#2<#1+&6$32#3#7???8000#2=#1+&6$32#3#7???8000#<#1"%pstring).
Definition F0L : list SR.region := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_regionR) ",4$21#8#1+&6$32#3#7???8000#2<#1+&6$32#3#7???8000#2=#1+&6$32#3#7???8000#<#1"%pstring).
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=09:<#=09:<#5=#=09:<,20#$1+$2-:0$3$4$5$6$7$8+$2-:0^#?#??????????????8#$<$=$>$?$10$11$12+&6$32#3#7???8000$21$15$16+$21#8$18$19#7???8000$1;$1<$1=$1>$1?,,12!&6$32#3#7???800<,1^#?#??????????????8!$21#8,1#1!&6$32#3#7???802=,1^#?#??????????????8!&6$32#3#7???802<,1^#?#??????????????8'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8#&6+$21#10#3#7???8000#1#&6+$21#8#3#7???8000#1!$21#10,1#($21#8#1'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80)&6+$21#8#3#7???8000#2&6$32#3#7???8000#80'$2#7???7?8010:0#800000000000&$2#20,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 854444 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 859488 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 859488 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriQSW2.

Module LibSegNa_qriQn.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [854444].
Definition STOPS1 : list Z := [854444] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$15$16$17$18$19#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",<'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8#&6+$21#10#3#7???8000#1#&6+$21#8#3#7???8000#1!$21#10,1#($21#8#1'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80)&6+$21#8#3#7???8000#2&6$32#3#7???8000#80"%pstring).
Definition ss0 : sym_state := SS 854372 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 33), (8), ELit 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (12), ELit 1)].
Definition F0L : list SR.region := [((EVar 33), (8), 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (12), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=09:<#=09:<#5=#=09:<,20#$1+$2-:0$3$4$5$6$7$8$9^#?#??????????????8#1#$=$>$?$10$11$12+&6$32#3#7???8000$21$15$16$17$18$19#7???8000$1;$1<$1=$1>$1?,,>!&6$32#3#7???800<,1^#?#??????????????8!$21#8,1#1'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8#&6+$21#10#3#7???8000#1#&6+$21#8#3#7???8000#1!$21#10,1#($21#8#1'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80)&6+$21#8#3#7???8000#2&6$32#3#7???8000#80,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 854444 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854372 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854372 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriQn.

Module LibSegNa_qriQu.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [854444].
Definition STOPS1 : list Z := [854444] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$15$16$17$18$19#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",<'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8#&6+$21#10#3#7???8000#1#&6+$21#8#3#7???8000#1!$21#10,1#($21#8#1'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80)&6+$21#8#3#7???8000#2&6$32#3#7???8000#80"%pstring).
Definition ss0 : sym_state := SS 854148 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 33), (8), ELit 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (12), ELit 1)].
Definition F0L : list SR.region := [((EVar 33), (8), 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (12), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=09:<#=09:<#5=#=09:<,20#$1+$2-:0$3$4$5$6$7$8$9^#?#??????????????8#1#$=$>$?$10$11$12+&6$32#3#7???8000$21$15$16$17$18$19#7???8000$1;$1<$1=$1>$1?,,>!&6$32#3#7???800<,1^#?#??????????????8!$21#8,1#1'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8#&6+$21#10#3#7???8000#1#&6+$21#8#3#7???8000#1!$21#10,1#($21#8#1'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80)&6+$21#8#3#7???8000#2&6$32#3#7???8000#80,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 854444 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854148 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854148 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriQu.

Module LibSegNa_qriRF.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [744480; 810712].
Definition STOPS1 : list Z := [744480; 810712; 859640; 860740] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9$28$29$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24$2?$18$30#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",17%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221<1#1($32#20#10(&6$32#3#7???8000#80'$2?##??'$30#^#?#???????????????'$29#^#?#???????????????'$28##800000000000)$24##60$32##400)&6$24#3#7???8000#<&6$32#3#7???8000#80"%pstring).
Definition ss0 : sym_state := SS 859552 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 50), (32), ELit 16); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (4), ELit 2)].
Definition F0L : list SR.region := [((EVar 50), (32), 16); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (4), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition arms1 := Eval vm_compute in (match SGP.branch_probe IT ss0 with Some e => SGP.case_arms ss0 e 0 | None => None end).
Definition f1 : sym_state := match arms1 with Some (Some s, _) => s | _ => ss0 end.
Definition t1 : sym_state := match arms1 with Some (_, Some s) => s | _ => ss0 end.

Definition ex2 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;5<20#<5>=8#=1=?8#=2244#;5<20#<5>=8#5=#;5<20,20##=1=?8+$2-:0$3$4$5$6$7$8$9$24+$32#20$2?$21$22#;5<20$10$11$12+&6$32#3#7???8000$21$22$24$2?$18$30#7???8000$32$1<$1=$1>$1?,,1<!$32#28,8$30!$32#20,8$28!&6$32#3#7???8005,1#!&6$32#3#7???8004,1#'&4&1$29$30#1#1#1%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221<1#1($32#20#10(&6$32#3#7???8000#80'$2?##??'$30#^#?#???????????????'$29#^#?#???????????????'$28##800000000000)$24##60$32##400)&6$24#3#7???8000#<&6$32#3#7???8000#80,50!"%pstring).
Definition s2 : sym_state := snd (snd ex2).

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;5<20#<5>=8#=1=?8#=2244#;5<20#<5>=8#5=#<5>=8,20##=2244+$2-:0$3$4$5$6$7$8$9$22#1$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24$2?$18$30#7???8000$32$1<$1=$1>$1?,,18'&4&1$29$30#1##%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221<1#1($32#20#10(&6$32#3#7???8000#80'$2?##??'$30#^#?#???????????????'$29#^#?#???????????????'$28##800000000000)$24##60$32##400)&6$24#3#7???8000#<&6$32#3#7???8000#80,50!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition plan : SGP.splan := SGP.PBranch (SGA.mkplan (fst ex2) (SGP.PEnd 0)) (SGA.mkplan (fst ex3) (SGP.PEnd 1)).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s2).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s2).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s2 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s2 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s2).
Definition ps0 : SR.post_spec := SR.PS 744480 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 810712 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 859552 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 859552 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriRF.

Module LibSegNa_qriSF.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [865632; 810712].
Definition STOPS1 : list Z := [865632; 810712; 855012; 855320] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9$28$29$<$=$>$?$10$11$12$13$14$22$16$30$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 48) 0 31;
   KRange (EVar 41) 0 31].
Definition ss0 : sym_state := SS 854996 regs0 [] kn0 NX0.
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

Definition arms1 := Eval vm_compute in (match SGP.branch_probe IT ss0 with Some e => SGP.case_arms ss0 e 0 | None => None end).
Definition f1 : sym_state := match arms1 with Some (Some s, _) => s | _ => ss0 end.
Definition t1 : sym_state := match arms1 with Some (_, Some s) => s | _ => ss0 end.

Definition ex2 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#=3560#<5>=8#=0;>4#=0=18#=3560#<5>=8#5=#=3560,20##=0;>4+$2-:0$3$4$5$6$7$8$9$28$30$<$=$>$?$10$11$12$13$14$22$16$30$28$19$1:$1;$1<$1=$1>$1?,,3'&4&1$29$30#1#1#1'$30##1?'$29##1?,50!"%pstring).
Definition s2 : sym_state := snd (snd ex2).

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#=3560#<5>=8#=0;>4#=0=18#=3560#<5>=8#5=#<5>=8,20##=0=18+$2-:0$3$4$5$6$7$8$9$22#1$<$=$>$?$10$11$12$13$14$22$16$30$18$19$1:$1;$1<$1=$1>$1?,,3'&4&1$29$30#1##'$30##1?'$29##1?,50!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition plan : SGP.splan := SGP.PBranch (SGA.mkplan (fst ex2) (SGP.PEnd 0)) (SGA.mkplan (fst ex3) (SGP.PEnd 1)).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s2).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s2).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s2 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s2 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s2).
Definition ps0 : SR.post_spec := SR.PS 865632 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 810712 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854996 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854996 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriSF.

Module LibSegNa_qriSF2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [865632; 810712].
Definition STOPS1 : list Z := [865632; 810712; 855440; 858360] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9$28$29$<$=$>$?$10$11$12$13$14$22$16$17$18$30$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 48) 0 18446744073709551615;
   KRange (EVar 41) 0 18446744073709551615].
Definition ss0 : sym_state := SS 855424 regs0 [] kn0 NX0.
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

Definition arms1 := Eval vm_compute in (match SGP.branch_probe IT ss0 with Some e => SGP.case_arms ss0 e 0 | None => None end).
Definition f1 : sym_state := match arms1 with Some (Some s, _) => s | _ => ss0 end.
Definition t1 : sym_state := match arms1 with Some (_, Some s) => s | _ => ss0 end.

Definition ex2 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#=3560#<5>=8#=0=90#=18?8#=3560#<5>=8#5=#=3560,20##=0=90+$2-:0$3$4$5$6$7$8$9$28$30$<$=$>$?$10$11$12$13$14$22$16$17$28$30$1:$1;$1<$1=$1>$1?,,3'&4&1$29$30#1#1#1'$30#^#?#???????????????'$29#^#?#???????????????,50!"%pstring).
Definition s2 : sym_state := snd (snd ex2).

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#=3560#<5>=8#=0=90#=18?8#=3560#<5>=8#5=#<5>=8,20##=18?8+$2-:0$3$4$5$6$7$8$9$22#1$<$=$>$?$10$11$12$13$14$22$16$17$18$30$1:$1;$1<$1=$1>$1?,,3'&4&1$29$30#1##'$30#^#?#???????????????'$29#^#?#???????????????,50!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition plan : SGP.splan := SGP.PBranch (SGA.mkplan (fst ex2) (SGP.PEnd 0)) (SGA.mkplan (fst ex3) (SGP.PEnd 1)).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s2).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s2).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s2 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s2 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s2).
Definition ps0 : SR.post_spec := SR.PS 865632 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 810712 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 855424 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 855424 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriSF2.

Module LibSegNa_qriSG0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [854444].
Definition STOPS1 : list Z := [854444] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9$30$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$15$16$17$18$19#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8#&6+$21#8#3#7???8000#1!$21#8,1#'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80"%pstring).
Definition ss0 : sym_state := SS 855368 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (12), ELit 1)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (12), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=09:<#=09:<#5=#=09:<,20#$1+$2-:0$3$4$5$6$7$8$9^#?#??????????????8#+&6+$21#8#3#7???8000$=$>$?$10$11$12+&6$32#3#7???8000$21$15$16+$21#8$18$30#7???8000$1;$1<$1=$1>$1?,,9!&6$32#3#7???800<,1^#?#??????????????8'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8!$21#8,1#'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 854444 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 855368 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 855368 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriSG0.

Module LibSegNa_qriSG1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [865060].
Definition STOPS1 : list Z := [865060; 855424] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8+$2-:0$30$;$<$=$>$?$10$11$12$13$21$15$16$17+$21#18$19#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$2#7???7?8010:0#800000000000&$2#20($2-88#8'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)+$2-:0##:0$21##1?8#&6+$21#8#3#7???8000#1!$21#8,1#1'$30#^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 855368 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-136), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-136), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=3324#=0=80#=3324#5=#=3324,20##=0=80+$2-:0$3$4$5$6$7$8+$2-:0+$21#18$30+$21#160$=$>$?$10$11$12$13$21$15$16+$21#8+$21#18$30#7???8000$1;$1<$1=$1>$1?,,;!$2-88,8+&6+$21#8#3#7???8000'$2#7???7?8010:0#800000000000&$2#20($2-88#8'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)+$2-:0##:0$21##1?8#&6+$21#8#3#7???8000#1!$21#8,1#1'$30#^#?#???????????????,50!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 855368 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 855368 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriSG1.

Module LibSegNa_qriSW.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [740912; 810712].
Definition STOPS1 : list Z := [740912; 810712; 855588; 855032] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9$:$2:$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24$30$28$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",16%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221;?#1($32#70#10(&6$32#3#7???8000#80'$2:#^#?#???????????????'$30##1?'$28##800000000000)$24##60$32##400)&6$24#3#7???8000#<&6$32#3#7???8000#80"%pstring).
Definition ss0 : sym_state := SS 855012 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 50), (112), ELit 16); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (14), ELit 2)].
Definition F0L : list SR.region := [((EVar 50), (112), 16); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (14), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;4>30#<5>=8#=0>24#=0;?8#;4>30#<5>=8#5:#=0;>8,20#$1+$2-:0$3$4$5$6$7$8$9$:%0$2:#$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24$30$28$19#7???8000$32$1<$1=$1>$1?,,16%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221;?#1($32#70#10(&6$32#3#7???8000#80'$2:#^#?#???????????????'$30##1?'$28##800000000000)$24##60$32##400)&6$24#3#7???8000#<&6$32#3#7???8000#80,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;4>30#<5>=8#=0>24#=0;?8#;4>30#<5>=8#5=#;4>30,20##=0>24+$2-:0$3$4$5$6$7$8$9$24+$32#70#$21$22#;4>30$10$11$12+&6$32#3#7???8000$21$22$24$30$28$19#7???8000$32$1<$1=$1>$1?,,1;!$32#78,8$30!$32#70,8$28!&6$32#3#7???800?,1#!&6$32#3#7???800>,1#'&4&1%0$2:###1#1#1%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221;?#1($32#70#10(&6$32#3#7???8000#80'$2:#^#?#???????????????'$30##1?'$28##800000000000)$24##60$32##400)&6$24#3#7???8000#<&6$32#3#7???8000#80,50!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;4>30#<5>=8#=0>24#=0;?8#;4>30#<5>=8#5=#<5>=8,20##=0;?8+$2-:0$3$4$5$6$7$8$9$22#3$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24$30$28$19#7???8000$32$1<$1=$1>$1?,,17'&4&1%0$2:###1##%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221;?#1($32#70#10(&6$32#3#7???8000#80'$2:#^#?#???????????????'$30##1?'$28##800000000000)$24##60$32##400)&6$24#3#7???8000#<&6$32#3#7???8000#80,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 740912 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 810712 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 855012 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 855012 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriSW.

Module LibSegNa_qriSW2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [740912; 810712].
Definition STOPS1 : list Z := [740912; 810712; 859488; 858360] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9$:$2:$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24$17$28$30#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",16%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221;?#1($32#160#10(&6$32#3#7???8000#80'$2:#^#?#???????????????'$30#^#?#???????????????'$28##800000000000)$24##60$32##400)&6$24#3#7???8000#<&6$32#3#7???8000#80"%pstring).
Definition ss0 : sym_state := SS 855440 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 50), (352), ELit 16); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (44), ELit 2)].
Definition F0L : list SR.region := [((EVar 50), (352), 16); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (44), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;4>30#<5>=8#=1=60#=18?8#;4>30#<5>=8#5:#=0=94,20#$1+$2-:0$3$4$5$6$7$8$9$:%0$2:#$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24$17$28$30#7???8000$32$1<$1=$1>$1?,,16%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221;?#1($32#160#10(&6$32#3#7???8000#80'$2:#^#?#???????????????'$30#^#?#???????????????'$28##800000000000)$24##60$32##400)&6$24#3#7???8000#<&6$32#3#7???8000#80,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;4>30#<5>=8#=1=60#=18?8#;4>30#<5>=8#5=#;4>30,20##=1=60+$2-:0$3$4$5$6$7$8$9$24+$32#160#$21$22#;4>30$10$11$12+&6$32#3#7???8000$21$22$24$17$28$30#7???8000$32$1<$1=$1>$1?,,1;!$32#168,8$30!$32#160,8$28!&6$32#3#7???802=,1#!&6$32#3#7???802<,1#'&4&1%0$2:###1#1#1%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221;?#1($32#160#10(&6$32#3#7???8000#80'$2:#^#?#???????????????'$30#^#?#???????????????'$28##800000000000)$24##60$32##400)&6$24#3#7???8000#<&6$32#3#7???8000#80,50!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;4>30#<5>=8#=1=60#=18?8#;4>30#<5>=8#5=#<5>=8,20##=18?8+$2-:0$3$4$5$6$7$8$9$22#3$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24$17$28$30#7???8000$32$1<$1=$1>$1?,,17'&4&1%0$2:###1##%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221;?#1($32#160#10(&6$32#3#7???8000#80'$2:#^#?#???????????????'$30#^#?#???????????????'$28##800000000000)$24##60$32##400)&6$24#3#7???8000#<&6$32#3#7???8000#80,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 740912 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 810712 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 855440 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 855440 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriSW2.

Module LibSegNa_qriSW2c.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [740912; 810712].
Definition STOPS1 : list Z := [740912; 810712; 859488; 858360] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9$:$2:$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24$17$28$30#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",16%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221;?#1($32#160#10(&6$32#3#7???8000#80'$2:##6'$30#^#?#???????????????'$28##800000000000)$24##60$32##400)&6$24#3#7???8000#<&6$32#3#7???8000#80"%pstring).
Definition ss0 : sym_state := SS 855440 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 50), (352), ELit 16); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (44), ELit 2)].
Definition F0L : list SR.region := [((EVar 50), (352), 16); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (44), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ce1 : expr := EVar 42.
Definition arms1 := Eval vm_compute in (SGP.case_arms ss0 ce1 (0)).
Definition lo1 : sym_state := match arms1 with Some (Some s, _) => s | _ => ss0 end.
Definition hi1 : sym_state := match arms1 with Some (_, Some s) => s | _ => ss0 end.

Definition ex2 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;4>30#<5>=8#=1=60#=18?8#;4>30#<5>=8#5=#;4>30,20##=1=60+$2-:0$3$4$5$6$7$8$9$24+$32#160#$21$22#;4>30$10$11$12+&6$32#3#7???8000$21$22$24$17$28$30#7???8000$32$1<$1=$1>$1?,,1;!$32#168,8$30!$32#160,8$28!&6$32#3#7???802=,1#!&6$32#3#7???802<,1#'$2:##%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221;?#1($32#160#10(&6$32#3#7???8000#80'$2:##6'$30#^#?#???????????????'$28##800000000000)$24##60$32##400)&6$24#3#7???8000#<&6$32#3#7???8000#80,50!"%pstring).
Definition s2 : sym_state := snd (snd ex2).

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;4>30#<5>=8#=1=60#=18?8#;4>30#<5>=8#5=#<5>=8,20##=18?8+$2-:0$3$4$5$6$7$8$9$22#3$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24$17$28$30#7???8000$32$1<$1=$1>$1?,,17'$2:#1#6%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221;?#1($32#160#10(&6$32#3#7???8000#80'$2:##6'$30#^#?#???????????????'$28##800000000000)$24##60$32##400)&6$24#3#7???8000#<&6$32#3#7???8000#80,50!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition plan : SGP.splan := SGP.PCase ce1 (0) (SGA.mkplan (fst ex2) (SGP.PEnd 0)) (SGA.mkplan (fst ex3) (SGP.PEnd 1)).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s2).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s2).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s2 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s2 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s2).
Definition ps0 : SR.post_spec := SR.PS 740912 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 810712 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 855440 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 855440 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriSW2c.

Module LibSegNa_qriSWc.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [740912; 810712].
Definition STOPS1 : list Z := [740912; 810712; 855588; 855032] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9$:$2:$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24$30$28$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",16%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221;?#1($32#70#10(&6$32#3#7???8000#80'$2:##6'$30##1?'$28##800000000000)$24##60$32##400)&6$24#3#7???8000#<&6$32#3#7???8000#80"%pstring).
Definition ss0 : sym_state := SS 855012 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 50), (112), ELit 16); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (14), ELit 2)].
Definition F0L : list SR.region := [((EVar 50), (112), 16); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (14), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ce1 : expr := EVar 42.
Definition arms1 := Eval vm_compute in (SGP.case_arms ss0 ce1 (0)).
Definition lo1 : sym_state := match arms1 with Some (Some s, _) => s | _ => ss0 end.
Definition hi1 : sym_state := match arms1 with Some (_, Some s) => s | _ => ss0 end.

Definition ex2 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;4>30#<5>=8#=0>24#=0;?8#;4>30#<5>=8#5=#;4>30,20##=0>24+$2-:0$3$4$5$6$7$8$9$24+$32#70#$21$22#;4>30$10$11$12+&6$32#3#7???8000$21$22$24$30$28$19#7???8000$32$1<$1=$1>$1?,,1;!$32#78,8$30!$32#70,8$28!&6$32#3#7???800?,1#!&6$32#3#7???800>,1#'$2:##%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221;?#1($32#70#10(&6$32#3#7???8000#80'$2:##6'$30##1?'$28##800000000000)$24##60$32##400)&6$24#3#7???8000#<&6$32#3#7???8000#80,50!"%pstring).
Definition s2 : sym_state := snd (snd ex2).

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;4>30#<5>=8#=0>24#=0;?8#;4>30#<5>=8#5=#<5>=8,20##=0;?8+$2-:0$3$4$5$6$7$8$9$22#3$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24$30$28$19#7???8000$32$1<$1=$1>$1?,,17'$2:#1#6%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221;?#1($32#70#10(&6$32#3#7???8000#80'$2:##6'$30##1?'$28##800000000000)$24##60$32##400)&6$24#3#7???8000#<&6$32#3#7???8000#80,50!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition plan : SGP.splan := SGP.PCase ce1 (0) (SGA.mkplan (fst ex2) (SGP.PEnd 0)) (SGA.mkplan (fst ex3) (SGP.PEnd 1)).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s2).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s2).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s2 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s2 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s2).
Definition ps0 : SR.post_spec := SR.PS 740912 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 810712 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 855012 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 855012 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriSWc.

End BndP_Na_088.
Module BndP_Na_089.
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
Ltac2 kr_t_BndP_Na_089 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_003ASegItab_Na_eab0ed2ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1922BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1923NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1922BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1925XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1922F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1923PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1924planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1925regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1923kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1932BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1933NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1932BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1935XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1932F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1933PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1934planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1935regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1933kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1942BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1943NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1942BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1945XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1942F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1943PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1944planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1945regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1943kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1952BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1953NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1952BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1955XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1952F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1953PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1954planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1955regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1953kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1962BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1963NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1962BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1965XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1962F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1963PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1964planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1965regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1963kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1972BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1973NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1972BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1975XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1972F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1973PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1974planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1975regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1973kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1982BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1983NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1982BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1985XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1982F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1983PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1984planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1985regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1983kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1992BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1993NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1992BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1995XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1992F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1993PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1994planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1995regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT1993kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2002BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2003NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2002BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2005XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2002F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2003PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2004planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2005regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2003kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2012BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2013NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2012BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2015XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2012F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2013PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2014planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2015regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2013kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2022BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2023NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2022BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2025XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2022F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2023PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2024planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2025regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2023kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2032BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2033NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2032BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2035XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2032F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2033PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2034planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2035regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2033kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2042BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2043NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2042BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2045XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2042F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2043PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2044planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2045regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2043kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2052BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2053NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2052BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2055XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2052F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2053PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2054planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2055regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_089@LibSegNa_qriT2053kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNa_qriT192.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [736500].
Definition STOPS1 : list Z := [736500; 857528] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221;=#1!$32#60,1#<0"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;3<?4#=15;8#;3<?4#5=#;3<?4,20##=15;8+$2-:0$3$4$5$6$7$8$9$24#$21$22#;3<?4$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?,,10%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221;=#1!$32#60,1#<0,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 736500 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriT192.

Module LibSegNa_qriT193.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [810712].
Definition STOPS1 : list Z := [810712; 857428] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1409024;
   KRange (EVar 2) 140735332487328 140737488355328;
   KAlign (EVar 2) 32;
   KRange (EVar 50) 7036928 140737488354304;
   KAlign (EVar 50) 32;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 50) 0) (ELit 1024);
   KWord (SA (EVar 50) 96) 1 (ELit 193)].
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#<5>=8#=1554#<5>=8#5=#<5>=8,20##=1554+$2-:0$3$4$5$6$7$8$9$22#;#<1$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?,,7%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400!$32#60,1#<1,50!"%pstring).
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
End LibSegNa_qriT193.

Module LibSegNa_qriT194.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [738668].
Definition STOPS1 : list Z := [738668; 857076] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221;>#1!$32#60,1#<2"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;456<#=13?4#;456<#5=#;456<,20##=13?4+$2-:0$3$4$5$6$7$8$9$24##$21$22#;456<$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?,,10%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221;>#1!$32#60,1#<2,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 738668 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriT194.

Module LibSegNa_qriT195.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [738668].
Definition STOPS1 : list Z := [738668; 857360] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221;>#1!$32#60,1#<3"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;456<#=1510#;456<#5=#;456<,20##=1510+$2-:0$3$4$5$6$7$8$9$24#1#$21$22#;456<$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?,,10%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221;>#1!$32#60,1#<3,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 738668 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriT195.

Module LibSegNa_qriT196.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [866564].
Definition STOPS1 : list Z := [866564; 855080] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1409024;
   KRange (EVar 2) 140735332487328 140737488355328;
   KAlign (EVar 2) 32;
   KRange (EVar 50) 7036928 140737488354304;
   KAlign (EVar 50) 32;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 50) 0) (ELit 1024);
   KWord (SA (EVar 50) 96) 1 (ELit 196)].
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=3904#=0<28#=3904#5=#=3904,20##=0<28+$2-:0$3$4$5$6$7$8$9$21#<4$22$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?,,7%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400!$32#60,1#<4,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 866564 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriT196.

Module LibSegNa_qriT197.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [866564].
Definition STOPS1 : list Z := [866564; 855080] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1409024;
   KRange (EVar 2) 140735332487328 140737488355328;
   KAlign (EVar 2) 32;
   KRange (EVar 50) 7036928 140737488354304;
   KAlign (EVar 50) 32;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 50) 0) (ELit 1024);
   KWord (SA (EVar 50) 96) 1 (ELit 197)].
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=3904#=0<28#=3904#5=#=3904,20##=0<28+$2-:0$3$4$5$6$7$8$9$21#<5$22$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?,,7%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400!$32#60,1#<5,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 866564 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriT197.

Module LibSegNa_qriT198.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [866564].
Definition STOPS1 : list Z := [866564; 855080] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1409024;
   KRange (EVar 2) 140735332487328 140737488355328;
   KAlign (EVar 2) 32;
   KRange (EVar 50) 7036928 140737488354304;
   KAlign (EVar 50) 32;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 50) 0) (ELit 1024);
   KWord (SA (EVar 50) 96) 1 (ELit 198)].
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=3904#=0<28#=3904#5=#=3904,20##=0<28+$2-:0$3$4$5$6$7$8$9$21#<6$22$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?,,7%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400!$32#60,1#<6,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 866564 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriT198.

Module LibSegNa_qriT199.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [866564].
Definition STOPS1 : list Z := [866564; 854616] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1409024;
   KRange (EVar 2) 140735332487328 140737488355328;
   KAlign (EVar 2) 32;
   KRange (EVar 50) 7036928 140737488354304;
   KAlign (EVar 50) 32;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 50) 0) (ELit 1024);
   KWord (SA (EVar 50) 96) 1 (ELit 199)].
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=3904#=0:58#=3904#5=#=3904,20##=0:58+$2-:0$3$4$5$6$7$8$9$21#<7$22$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?,,7%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400!$32#60,1#<7,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 866564 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriT199.

Module LibSegNa_qriT200.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [866564].
Definition STOPS1 : list Z := [866564; 854616] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1409024;
   KRange (EVar 2) 140735332487328 140737488355328;
   KAlign (EVar 2) 32;
   KRange (EVar 50) 7036928 140737488354304;
   KAlign (EVar 50) 32;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 50) 0) (ELit 1024);
   KWord (SA (EVar 50) 96) 1 (ELit 200)].
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=3904#=0:58#=3904#5=#=3904,20##=0:58+$2-:0$3$4$5$6$7$8$9$21#<8$22$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?,,7%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400!$32#60,1#<8,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 866564 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriT200.

Module LibSegNa_qriT201.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [866564].
Definition STOPS1 : list Z := [866564; 854616] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1409024;
   KRange (EVar 2) 140735332487328 140737488355328;
   KAlign (EVar 2) 32;
   KRange (EVar 50) 7036928 140737488354304;
   KAlign (EVar 50) 32;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 50) 0) (ELit 1024);
   KWord (SA (EVar 50) 96) 1 (ELit 201)].
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=3904#=0:58#=3904#5=#=3904,20##=0:58+$2-:0$3$4$5$6$7$8$9$21#<9$22$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?,,7%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400!$32#60,1#<9,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 866564 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriT201.

Module LibSegNa_qriT202.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [862896].
Definition STOPS1 : list Z := [862896; 857756] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",8%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80!$32#60,1#<:"%pstring).
Definition ss0 : sym_state := SS 854044 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (18), ELit 1)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (18), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=2:;0#=169<#=2:;0#5=#=2:;0,20##=169<+$2-:0$3$4$5$6$7$8$9+$21#18+$32#90#4$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#90+$21#18#4#7???8000$32$1<$1=$1>$1?,,9!&6$32#3#7???8012,1#4%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80!$32#60,1#<:,50!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriT202.

Module LibSegNa_qriT203.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [862896].
Definition STOPS1 : list Z := [862896; 856780] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",8%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80!$32#60,1#<;"%pstring).
Definition ss0 : sym_state := SS 854044 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (20), ELit 1)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (20), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=2:;0#=12<<#=2:;0#5=#=2:;0,20##=12<<+$2-:0$3$4$5$6$7$8$9+$21#18+$32#:0#8$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#:0+$21#18#8#7???8000$32$1<$1=$1>$1?,,9!&6$32#3#7???8014,1#%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80!$32#60,1#<;,50!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriT203.

Module LibSegNa_qriT204.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [862896].
Definition STOPS1 : list Z := [862896; 857612] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",8%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80!$32#60,1#<<"%pstring).
Definition ss0 : sym_state := SS 854044 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (24), ELit 1)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (24), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=2:;0#=160<#=2:;0#5=#=2:;0,20##=160<+$2-:0$3$4$5$6$7$8$9+$21#18+$32#<0#1$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#<0+$21#18$19#7???8000$32$1<$1=$1>$1?,,9!&6$32#3#7???8018,1#1%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80!$32#60,1#<<,50!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriT204.

Module LibSegNa_qriT205.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [862896].
Definition STOPS1 : list Z := [862896; 855688] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",8%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80!$32#60,1#<="%pstring).
Definition ss0 : sym_state := SS 854044 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (26), ELit 1)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (26), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=2:;0#=0>88#=2:;0#5=#=2:;0,20##=0>88+$2-:0$3$4$5$6$7$8$9+$21#18+$32#=0#2$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#=0+$21#18#2#7???8000$32$1<$1=$1>$1?,,9!&6$32#3#7???801:,1#2%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80!$32#60,1#<=,50!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriT205.

End BndP_Na_089.
Module BndP_Na_090.
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
Ltac2 kr_t_BndP_Na_090 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_003ASegItab_Na_eab0ed2ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2062BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2063NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2062BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2065XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2062F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2063PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2064planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2065regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2063kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2072BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2073NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2072BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2075XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2072F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2073PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2074planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2075regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2073kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2082BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2083NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2082BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2085XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2082F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2083PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2084planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2085regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2083kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2092BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2093NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2092BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2095XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2092F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2093PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2094planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2095regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2093kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2102BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2103NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2102BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2105XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2102F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2103PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2104planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2105regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2103kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2112BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2113NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2112BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2115XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2112F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2113PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2114planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2115regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2113kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2122BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2123NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2122BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2125XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2122F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2123PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2124planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2125regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2123kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2132BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2133NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2132BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2135XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2132F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2133PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2134planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2135regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2133kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2142BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2143NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2142BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2145XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2142F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2143PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2144planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2145regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2143kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2152BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2153NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2152BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2155XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2152F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2153PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2154planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2155regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2153kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2162BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2163NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2162BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2165XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2162F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2163PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2164planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2165regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2163kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2172BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2173NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2172BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2175XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2172F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2173PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2174planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2175regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2173kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2182BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2183NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2182BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2185XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2182F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2183PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2184planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2185regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2183kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2192BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2193NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2192BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2195XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2192F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2193PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2194planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2195regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_090@LibSegNa_qriT2193kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNa_qriT206.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [862896].
Definition STOPS1 : list Z := [862896; 856268] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",8%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80!$32#60,1#<>"%pstring).
Definition ss0 : sym_state := SS 854044 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (28), ELit 1)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (28), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=2:;0#=10<<#=2:;0#5=#=2:;0,20##=10<<+$2-:0$3$4$5$6$7$8$9+$21#18+$32#>0#4$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#>0+$21#18#4#7???8000$32$1<$1=$1>$1?,,9!&6$32#3#7???801<,1#4%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80!$32#60,1#<>,50!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriT206.

Module LibSegNa_qriT207.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [862896].
Definition STOPS1 : list Z := [862896; 856020] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",8%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80!$32#60,1#<?"%pstring).
Definition ss0 : sym_state := SS 854044 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (30), ELit 1)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (30), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=2:;0#=0?=4#=2:;0#5=#=2:;0,20##=0?=4+$2-:0$3$4$5$6$7$8$9+$21#18+$32#?0#8$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#?0+$21#18#8#7???8000$32$1<$1=$1>$1?,,9!&6$32#3#7???801>,1#%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80!$32#60,1#<?,50!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriT207.

Module LibSegNa_qriT208.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [862896].
Definition STOPS1 : list Z := [862896; 857164] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",8%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80!$32#60,1#=0"%pstring).
Definition ss0 : sym_state := SS 854044 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (34), ELit 1)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (34), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=2:;0#=144<#=2:;0#5=#=2:;0,20##=144<+$2-:0$3$4$5$6$7$8$9+$21#18+$32#110#1$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#110+$21#18#1#7???8000$32$1<$1=$1>$1?,,9!&6$32#3#7???8022,1#1%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80!$32#60,1#=0,50!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriT208.

Module LibSegNa_qriT209.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [862896].
Definition STOPS1 : list Z := [862896; 855856] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",8%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80!$32#60,1#=1"%pstring).
Definition ss0 : sym_state := SS 854044 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (36), ELit 1)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (36), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=2:;0#=0?30#=2:;0#5=#=2:;0,20##=0?30+$2-:0$3$4$5$6$7$8$9+$21#18+$32#120#2$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#120+$21#18#2#7???8000$32$1<$1=$1>$1?,,9!&6$32#3#7???8024,1#2%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80!$32#60,1#=1,50!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriT209.

Module LibSegNa_qriT210.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [862896].
Definition STOPS1 : list Z := [862896; 858196] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",8%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80!$32#60,1#=2"%pstring).
Definition ss0 : sym_state := SS 854044 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (38), ELit 1)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (38), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=2:;0#=1854#=2:;0#5=#=2:;0,20##=1854+$2-:0$3$4$5$6$7$8$9+$21#18+$32#130#4$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#130+$21#18#4#7???8000$32$1<$1=$1>$1?,,9!&6$32#3#7???8026,1#4%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80!$32#60,1#=2,50!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriT210.

Module LibSegNa_qriT211.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [862896].
Definition STOPS1 : list Z := [862896; 857952] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",8%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80!$32#60,1#=3"%pstring).
Definition ss0 : sym_state := SS 854044 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (40), ELit 1)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (40), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=2:;0#=1760#=2:;0#5=#=2:;0,20##=1760+$2-:0$3$4$5$6$7$8$9+$21#18+$32#140#8$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#140+$21#18#8#7???8000$32$1<$1=$1>$1?,,9!&6$32#3#7???8028,1#%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80!$32#60,1#=3,50!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriT211.

Module LibSegNa_qriT212.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [866564].
Definition STOPS1 : list Z := [866564; 854616] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1409024;
   KRange (EVar 2) 140735332487328 140737488355328;
   KAlign (EVar 2) 32;
   KRange (EVar 50) 7036928 140737488354304;
   KAlign (EVar 50) 32;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 50) 0) (ELit 1024);
   KWord (SA (EVar 50) 96) 1 (ELit 212)].
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=3904#=0:58#=3904#5=#=3904,20##=0:58+$2-:0$3$4$5$6$7$8$9$21#=4$22$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?,,7%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400!$32#60,1#=4,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 866564 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriT212.

Module LibSegNa_qriT213.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [866564].
Definition STOPS1 : list Z := [866564; 854616] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1409024;
   KRange (EVar 2) 140735332487328 140737488355328;
   KAlign (EVar 2) 32;
   KRange (EVar 50) 7036928 140737488354304;
   KAlign (EVar 50) 32;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 50) 0) (ELit 1024);
   KWord (SA (EVar 50) 96) 1 (ELit 213)].
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=3904#=0:58#=3904#5=#=3904,20##=0:58+$2-:0$3$4$5$6$7$8$9$21#=5$22$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?,,7%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400!$32#60,1#=5,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 866564 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriT213.

Module LibSegNa_qriT214.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [866564].
Definition STOPS1 : list Z := [866564; 854616] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1409024;
   KRange (EVar 2) 140735332487328 140737488355328;
   KAlign (EVar 2) 32;
   KRange (EVar 50) 7036928 140737488354304;
   KAlign (EVar 50) 32;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 50) 0) (ELit 1024);
   KWord (SA (EVar 50) 96) 1 (ELit 214)].
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=3904#=0:58#=3904#5=#=3904,20##=0:58+$2-:0$3$4$5$6$7$8$9$21#=6$22$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?,,7%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400!$32#60,1#=6,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 866564 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriT214.

Module LibSegNa_qriT215.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [866564].
Definition STOPS1 : list Z := [866564; 854616] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1409024;
   KRange (EVar 2) 140735332487328 140737488355328;
   KAlign (EVar 2) 32;
   KRange (EVar 50) 7036928 140737488354304;
   KAlign (EVar 50) 32;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 50) 0) (ELit 1024);
   KWord (SA (EVar 50) 96) 1 (ELit 215)].
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=3904#=0:58#=3904#5=#=3904,20##=0:58+$2-:0$3$4$5$6$7$8$9$21#=7$22$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?,,7%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400!$32#60,1#=7,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 866564 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriT215.

Module LibSegNa_qriT216.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [866564].
Definition STOPS1 : list Z := [866564; 854616] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1409024;
   KRange (EVar 2) 140735332487328 140737488355328;
   KAlign (EVar 2) 32;
   KRange (EVar 50) 7036928 140737488354304;
   KAlign (EVar 50) 32;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 50) 0) (ELit 1024);
   KWord (SA (EVar 50) 96) 1 (ELit 216)].
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=3904#=0:58#=3904#5=#=3904,20##=0:58+$2-:0$3$4$5$6$7$8$9$21#=8$22$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?,,7%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400!$32#60,1#=8,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 866564 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriT216.

Module LibSegNa_qriT217.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [866564].
Definition STOPS1 : list Z := [866564; 855368] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1409024;
   KRange (EVar 2) 140735332487328 140737488355328;
   KAlign (EVar 2) 32;
   KRange (EVar 50) 7036928 140737488354304;
   KAlign (EVar 50) 32;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 50) 0) (ELit 1024);
   KWord (SA (EVar 50) 96) 1 (ELit 217)].
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=3904#=0=48#=3904#5=#=3904,20##=0=48+$2-:0$3$4$5$6$7$8$9$21#=9$22$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?,,7%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400!$32#60,1#=9,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 866564 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriT217.

Module LibSegNa_qriT218.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [866564].
Definition STOPS1 : list Z := [866564; 855368] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1409024;
   KRange (EVar 2) 140735332487328 140737488355328;
   KAlign (EVar 2) 32;
   KRange (EVar 50) 7036928 140737488354304;
   KAlign (EVar 50) 32;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 50) 0) (ELit 1024);
   KWord (SA (EVar 50) 96) 1 (ELit 218)].
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=3904#=0=48#=3904#5=#=3904,20##=0=48+$2-:0$3$4$5$6$7$8$9$21#=:$22$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?,,7%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400!$32#60,1#=:,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 866564 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriT218.

Module LibSegNa_qriT219.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [866564].
Definition STOPS1 : list Z := [866564; 855368] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1409024;
   KRange (EVar 2) 140735332487328 140737488355328;
   KAlign (EVar 2) 32;
   KRange (EVar 50) 7036928 140737488354304;
   KAlign (EVar 50) 32;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 50) 0) (ELit 1024);
   KWord (SA (EVar 50) 96) 1 (ELit 219)].
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=3904#=0=48#=3904#5=#=3904,20##=0=48+$2-:0$3$4$5$6$7$8$9$21#=;$22$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?,,7%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400!$32#60,1#=;,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 866564 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriT219.

End BndP_Na_090.
Module BndP_Na_091.
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
Ltac2 kr_t_BndP_Na_091 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_003ASegItab_Na_eab0ed2ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriT2202BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriT2203NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriT2202BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriT2205XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriT2202F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriT2203PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriT2204planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriT2205regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriT2203kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriT2212BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriT2213NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriT2212BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriT2215XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriT2212F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriT2213PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriT2214planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriT2215regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriT2213kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriT2222BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriT2223NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriT2222BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriT2225XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriT2222F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriT2223PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriT2224planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriT2225regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriT2223kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriT2232BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriT2233NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriT2232BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriT2235XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriT2232F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriT2233PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriT2234planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriT2235regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriT2233kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12an2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12an3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12an2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12an5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12an2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12an3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12an4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12an5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12an3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12az2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12az3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12az2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12az5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12az2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12az3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12az4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12az5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12az3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12b12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12b13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12b12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12b15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12b12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12b13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12b14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12b15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12b13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12b22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12b23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12b22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12b25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12b22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12b23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12b24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12b25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12b23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12cL2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12cL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12cL2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12cL5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12cL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12cL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12cL4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12cL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12cL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12cS2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12cS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12cS2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12cS5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12cS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12cS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12cS4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12cS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12cS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12dL2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12dL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12dL2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12dL5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12dL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12dL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12dL4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12dL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12dL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12dS2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12dS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12dS2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12dS5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12dS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12dS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12dS4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12dS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091ALibSegNa_qriU12dS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriU12n2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriU12n3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriU12n2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriU12n5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriU12n2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriU12n3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriU12n4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriU12n5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriU12n3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriU12p2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriU12p3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriU12p2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriU12p5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriU12p2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriU12p3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriU12p4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriU12p5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0173;BndP_Na_091@LibSegNa_qriU12p3kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNa_qriT220.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [864584].
Definition STOPS1 : list Z := [864584; 854972] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1409024;
   KRange (EVar 2) 140735332487328 140737488355328;
   KAlign (EVar 2) 32;
   KRange (EVar 50) 7036928 140737488354304;
   KAlign (EVar 50) 32;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 50) 0) (ELit 1024);
   KWord (SA (EVar 50) 96) 1 (ELit 220)].
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=3148#=0;;<#=3148#5=#=3148,20##=0;;<+$2-:0$3$4$5$6$7$8$9$21$24#=<$22$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?,,7%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400!$32#60,1#=<,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 864584 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriT220.

Module LibSegNa_qriT221.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [864584].
Definition STOPS1 : list Z := [864584; 854972] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1409024;
   KRange (EVar 2) 140735332487328 140737488355328;
   KAlign (EVar 2) 32;
   KRange (EVar 50) 7036928 140737488354304;
   KAlign (EVar 50) 32;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 50) 0) (ELit 1024);
   KWord (SA (EVar 50) 96) 1 (ELit 221)].
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=3148#=0;;<#=3148#5=#=3148,20##=0;;<+$2-:0$3$4$5$6$7$8$9$21$24#==$22$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?,,7%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400!$32#60,1#==,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 864584 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriT221.

Module LibSegNa_qriT222.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [864108].
Definition STOPS1 : list Z := [864108; 854944] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1409024;
   KRange (EVar 2) 140735332487328 140737488355328;
   KAlign (EVar 2) 32;
   KRange (EVar 50) 7036928 140737488354304;
   KAlign (EVar 50) 32;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 50) 0) (ELit 1024);
   KWord (SA (EVar 50) 96) 1 (ELit 222)].
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=2?6<#=0;:0#=2?6<#5=#=2?6<,20##=0;:0+$2-:0$3$4$5$6$7$8$9$21$24#=>$22$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?,,7%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400!$32#60,1#=>,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 864108 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriT222.

Module LibSegNa_qriT223.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [864108].
Definition STOPS1 : list Z := [864108; 854944] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1409024;
   KRange (EVar 2) 140735332487328 140737488355328;
   KAlign (EVar 2) 32;
   KRange (EVar 50) 7036928 140737488354304;
   KAlign (EVar 50) 32;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 50) 0) (ELit 1024);
   KWord (SA (EVar 50) 96) 1 (ELit 223)].
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=2?6<#=0;:0#=2?6<#5=#=2?6<,20##=0;:0+$2-:0$3$4$5$6$7$8$9$21$24#=?$22$>$?$10$11$12+&6$32#3#7???8000$21$22$24+$32#60+$21#18$19#7???8000$32$1<$1=$1>$1?,,7%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400!$32#60,1#=?,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 864108 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 854044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 854044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriT223.

Module LibSegNa_qriU12an.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [839180].
Definition STOPS1 : list Z := [839180; 858808] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8+$2-:0#8$;$<$=$>$?$10$11$12+&6$32#3#7???8000$14$15$16#8+$21#18+$32#230$1:$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",;'$2#7???7?8010:0#800000000000&$2#20($2-98#8'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400($32#250#20(&6$32#3#7???8000#80!$32#230,8$38'$38#1^#?#???????????????)+$2-:0##:0$32##400"%pstring).
Definition ss0 : sym_state := SS 858628 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-152), ELit 8); ((EVar 50), (592), ELit 32); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (74), ELit 4)].
Definition F0L : list SR.region := [((EVar 2), (-152), 8); ((EVar 50), (592), 32); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (74), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#<<>0<#=1:;8#<<>0<#5=#<<>0<,20##=1:;8+$2-:0$3$4$5$6$7$8+$2-:0+$32#250#3;9:<:00&7&8&8+@#100000000000000$38@#10000000000&9$38#??00&8@#1000000&9$38#??0000@#100000000%6$38#18+&6$38#38+&9&6$38#18#??0000+&9&6$38#28#??00@#1000000%6&6$38#8#18#3?+&6$38#38&9&6$38#28#??00&9&6$38#6#2#1$38$11$12+&6$32#3#7???8000$14$15$16#??00+$21#18+$32#230$1:$32$1<$1=$1>$1?,,14!$2-98,8+$32#250!$32#268,8#!$32#260,8+&5&8&8+@#100000000000000$38@#10000000000&9$38#??00&8@#1000000&9$38#??0000@#100000000%6$38#18+&6$38#38+&9&6$38#18#??0000+&9&6$38#28#??00@#1000000%6&6$38#8#18&7&8&8+@#100000000000000$38@#10000000000&9$38#??00&8@#1000000&9$38#??0000@#100000000%6$38#18+&6$38#38+&9&6$38#18#??0000+&9&6$38#28#??00@#1000000%6&6$38#8#18#3?@-1&7&8&8+@#100000000000000$38@#10000000000&9$38#??00&8@#1000000&9$38#??0000@#100000000%6$38#18+&6$38#38+&9&6$38#18#??0000+&9&6$38#28#??00@#1000000%6&6$38#8#18#3?!$32#258,8#1!$32#250,1&9&6$38#6#2!&6$32#3#7???804=,1#!&6$32#3#7???804<,1#!&6$32#3#7???804;,1#!&6$32#3#7???804:,1#'$2#7???7?8010:0#800000000000&$2#20($2-98#8'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400($32#250#20(&6$32#3#7???8000#80!$32#230,8$38'$38#1^#?#???????????????)+$2-:0##:0$32##400,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 839180 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 858628 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 858628 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriU12an.

Module LibSegNa_qriU12az.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [839180].
Definition STOPS1 : list Z := [839180; 858808] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8+$2-:0#8$;$<$=$>$?$10$11$12+&6$32#3#7???8000$14$15$16#8+$21#18+$32#230$1:$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$2#7???7?8010:0#800000000000&$2#20($2-98#8'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400($32#250#20(&6$32#3#7???8000#80!$32#230,8#)+$2-:0##:0$32##400"%pstring).
Definition ss0 : sym_state := SS 858628 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-152), ELit 8); ((EVar 50), (592), ELit 32); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (74), ELit 4)].
Definition F0L : list SR.region := [((EVar 2), (-152), 8); ((EVar 50), (592), 32); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (74), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#<<>0<#=1:;8#<<>0<#5=#<<>0<,20##=1:;8+$2-:0$3$4$5$6$7$8+$2-:0+$32#250#3;9:<:00#####$11$12+&6$32#3#7???8000$14$15$16#??00+$21#18+$32#230$1:$32$1<$1=$1>$1?,,13!$2-98,8+$32#250!$32#268,8#!$32#260,8#!$32#258,8#!$32#250,1#!&6$32#3#7???804=,1#!&6$32#3#7???804<,1#!&6$32#3#7???804;,1#!&6$32#3#7???804:,1#'$2#7???7?8010:0#800000000000&$2#20($2-98#8'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400($32#250#20(&6$32#3#7???8000#80!$32#230,8#)+$2-:0##:0$32##400,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 839180 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 858628 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 858628 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriU12az.

Module LibSegNa_qriU12b1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [858832].
Definition STOPS1 : list Z := [858832] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11$12$13$14$15$16#??00$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332487328 140737488355328;
   KAlign (EVar 2) 32;
   KWord (SA (EVar 2) (-160)) 8 (EVar 53);
   KRange (EVar 53) 0 4294967295].
Definition ss0 : sym_state := SS 858808 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=1:=0#=1:=0#5=#=1:=0,20#$1+$2-:0$3$4$5$6$7$8+$2-:0+&6$35#18&9&6$35#8#??00&6$35#18&9$35#??00$=$>$?$10$11$12$13$14$15$16#??00$35$19$1:$1;$1<$1=$1>$1?,,4'$2#7???7?8010:0#800000000000&$2#20!$2-:0,8$35'$35##????????,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 858832 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 858808 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 858808 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriU12b1.

Module LibSegNa_qriU12b2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [869448].
Definition STOPS1 : list Z := [869448; 858864] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8+$2-:0$36$3:$37$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400!$2-98,8+$32#250'$36##????'$37##??00'$3:#^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 858836 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=4448#=1:?0#=4448#5=#=4448,20##=1:?0+$2-:0$3$4$5$6$7$8+$2-:0+$32#250#@#100$37$=$>$?$10$11$12$13$14$15$16+$32#250$18&8&8$3:@#100$37$36$1:$1;$1<$1=$1>$1?,,9'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400!$2-98,8+$32#250'$36##????'$37##??00'$3:#^#?#???????????????,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 869448 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 858836 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 858836 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriU12b2.

Module LibSegNa_qriU12cL.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [867600].
Definition STOPS1 : list Z := [867600; 860376] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11$12$13$21$15$16$17$18$19#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1;'$2#7???7?8010:0#800000000000&$2#20!$2-98,8+$32#250'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)+$2-:0##:0$21##1?8'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400!$21#148,1$3:'$3:##??#&6+$21#148#3#7???8000#1'&9$3:#1#1#1#&6+$21#158#3#7???8000#1#&6+$21#150#3#7???8000#1!$21#158,8$3;'$3;#1000#7??????????8&$3;#8)##7???7000#100000001000$3;##1#&6$3;#3#7???8000#1($3;##1)+$2-:0##:0$3;##1)$3;##1$21##1?8)$3;##1$32##400)##10000#6:6000$3;##1($21#150#8"%pstring).
Definition ss0 : sym_state := SS 860224 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 59), (0), ELit 1); ((EVar 33), (336), ELit 8)].
Definition F0L : list SR.region := [((EVar 59), (0), 1); ((EVar 33), (336), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=3=10#=20=8#=3=10#5=#=3=10,20##=20=8+$2-:0$3$4$5$6$7$8+$2-:0+$32#250+$21#148$<$=$>$?$10$11$12$13$21$15$16+&6+$21#148#3#7???8000$18+$21#148#7???8000$32$1<$1=$1>$1?,,1=!$21#150,8#!$3;#,1#'$2#7???7?8010:0#800000000000&$2#20!$2-98,8+$32#250'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)+$2-:0##:0$21##1?8'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400!$21#148,1$3:'$3:##??#&6+$21#148#3#7???8000#1'&9$3:#1#1#1#&6+$21#158#3#7???8000#1#&6+$21#150#3#7???8000#1!$21#158,8$3;'$3;#1000#7??????????8&$3;#8)##7???7000#100000001000$3;##1#&6$3;#3#7???8000#1($3;##1)+$2-:0##:0$3;##1)$3;##1$21##1?8)$3;##1$32##400)##10000#6:6000$3;##1($21#150#8,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 867600 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 860224 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 860224 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriU12cL.

Module LibSegNa_qriU12cS.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [867600].
Definition STOPS1 : list Z := [867600; 860376] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11$12$13$21$15$16$17$18$19#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400!$2-98,8+$32#250'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)+$2-:0##:0$21##1?8!$21#148,1$3:'$3:##??#&6+$21#148#3#7???8000#1'&9$3:#1###&6+$21#149#3#7???8000#1($21#148#2"%pstring).
Definition ss0 : sym_state := SS 860224 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 33), (328), ELit 2)].
Definition F0L : list SR.region := [((EVar 33), (328), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=3=10#=20=8#=3=10#5=#=3=10,20##=20=8+$2-:0$3$4$5$6$7$8+$2-:0+$32#250+$21#148$<$=$>$?$10$11$12$13$21$15$16+&6+$21#148#3#7???8000$18+$21#148#7???8000$1;$1<$1=$1>$1?,,11!$21#148,1#!$21#149,1#'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400!$2-98,8+$32#250'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)+$2-:0##:0$21##1?8'$3:##??#&6+$21#148#3#7???8000#1'&9$3:#1###&6+$21#149#3#7???8000#1($21#148#2,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 867600 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 860224 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 860224 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriU12cS.

Module LibSegNa_qriU12dL.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [740912].
Definition STOPS1 : list Z := [740912; 860544] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+&6+$21#148#3#7???8000$18+$21#148#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1?%#10000#158000'$2#7???7?8010:0#800000000000&$2#20!$2-98,8+$32#250'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221;?#1($32#2=0#10(&6$32#3#7???8000#80!$21#148,1$3:'$3:##??#&6+$21#148#3#7???8000#1)$24##60$32##400)&6$24#3#7???8000#<&6$32#3#7???8000#80)&6+$21#148#3#7???8000#3&6$32#3#7???8000#80'&9$3:#1#1#1#&6+$21#158#3#7???8000#1#&6+$21#150#3#7???8000#1!$21#158,8$3;!$21#150,8$30'$3;##800000000000'$30#^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 860376 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 50), (720), ELit 16); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (90), ELit 2)].
Definition F0L : list SR.region := [((EVar 50), (720), 16); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (90), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;4>30#=2180#;4>30#5=#;4>30,20##=2180+$2-:0$3$4$5$6$7$8+$2-:0$24+$32#2=0#7$21$22#;4>30$10$11$12+&6$32#3#7???8000$21$22$24+$32#250$18+$21#148#7???8000$32$1<$1=$1>$1?,,1?!$32#2=8,8$30!$32#2=0,8$3;!&6$32#3#7???805;,1#!&6$32#3#7???805:,1#%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221;?#1($32#2=0#10(&6$32#3#7???8000#80'$3:##??#&6+$21#148#3#7???8000#1)$24##60$32##400)&6$24#3#7???8000#<&6$32#3#7???8000#80)&6+$21#148#3#7???8000#3&6$32#3#7???8000#80'&9$3:#1#1#1#&6+$21#158#3#7???8000#1#&6+$21#150#3#7???8000#1'$3;##800000000000'$30#^#?#???????????????,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 740912 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 860376 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 860376 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriU12dL.

Module LibSegNa_qriU12dS.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [740912].
Definition STOPS1 : list Z := [740912; 860544] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$22$24+&6+$21#148#3#7???8000$18+$21#148#7???8000$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1:%#10000#158000'$2#7???7?8010:0#800000000000&$2#20!$2-98,8+$32#250'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221;?#1($32#2=0#10(&6$32#3#7???8000#80!$21#148,1$3:'$3:##??#&6+$21#148#3#7???8000#1)$24##60$32##400)&6$24#3#7???8000#<&6$32#3#7???8000#80)&6+$21#148#3#7???8000#3&6$32#3#7???8000#80'&9$3:#1###&6+$21#149#3#7???8000#1"%pstring).
Definition ss0 : sym_state := SS 860376 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 50), (720), ELit 16); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (90), ELit 2)].
Definition F0L : list SR.region := [((EVar 50), (720), 16); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (90), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;4>30#=2180#;4>30#5=#;4>30,20##=2180+$2-:0$3$4$5$6$7$8+$2-:0$24+$32#2=0#7$21$22#;4>30$10$11$12+&6$32#3#7???8000$21$22$24+$32#250$18+$21#148#7???8000$32$1<$1=$1>$1?,,1;!$32#2=8,8&6$3:#1!$32#2=0,8+$21#149!&6$32#3#7???805;,1#!&6$32#3#7???805:,1#%#10000#158000'$2#7???7?8010:0#800000000000&$2#20'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221;?#1($32#2=0#10(&6$32#3#7???8000#80'$3:##??#&6+$21#148#3#7???8000#1)$24##60$32##400)&6$24#3#7???8000#<&6$32#3#7???8000#80)&6+$21#148#3#7???8000#3&6$32#3#7???8000#80'&9$3:#1##,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 740912 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 860376 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 860376 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriU12dS.

Module LibSegNa_qriU12n.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [831192].
Definition STOPS1 : list Z := [831192; 858932] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9$31$;$<$=$>$?$10$11$12+&6$32#3#7???8000$14$15$16+$32#250$35$39$1:$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",8'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400($32#290#20(&6$32#3#7???8000#80'$31#1^#?#???????????????'$35##????????'$39#^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 858864 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 50), (656), ELit 32); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (82), ELit 4)].
Definition F0L : list SR.region := [((EVar 50), (656), 32); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (82), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#<:>=8#=1;34#<:>=8#5=#<:>=8,20##=1;34+$2-:0$3$4$5$6$7$8$9+$32#250+$32#290$<$=$>$?$10$11$12+&6$32#3#7???8000$14$15$16+$32#250@#100000000$39+$32#290$1:$32$1<$1=$1>$1?,,10!$32#2:8,8#!$32#2:0,8&6@#100000000$39#20!$32#298,8&4#$35!$32#290,1#!&6$32#3#7???8055,1#!&6$32#3#7???8054,1#!&6$32#3#7???8053,1#!&6$32#3#7???8052,1#'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400($32#290#20(&6$32#3#7???8000#80'$31#1^#?#???????????????'$35##????????'$39#^#?#???????????????,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 831192 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 858864 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 858864 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriU12n.

Module LibSegNa_qriU12p.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [870008].
Definition STOPS1 : list Z := [870008; 860224] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9#$;$<$=$>$?$10$11$12$13$14$15$16+$32#250$18$39$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 57) 0 18446744073709551615].
Definition ss0 : sym_state := SS 858864 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=4678#=2040#=4678#5=#=4678,20##=2040+$2-:0$3$4$5$6$7$8$9+$32#250$39$<$=$>$?$10$11$12$13$14$15$16+$32#250$18$39$1:$1;$1<$1=$1>$1?,,1'$39#^#?#???????????????,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 870008 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 858864 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 858864 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriU12p.

End BndP_Na_091.
