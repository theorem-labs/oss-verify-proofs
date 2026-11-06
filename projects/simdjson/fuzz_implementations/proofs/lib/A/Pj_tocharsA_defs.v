(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjPjNum SjPjDig.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A Require Import Layout Shadow RT_iface RT_iface2 D_defs D_kit Sj_akit Sj_acps Sj_hkit Sj_num_akit Sj_num_amem
     Sj_num_aframe Sj_num_lm_kit Pj_defsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Record tcI : Type := mkTI {
  ti_q : Z;
  ti_d : Z;
  ti_NB : Z;
  ti_lo : Z;
  ti_f : Z;
  ti_ra : word; ti_gp : word;
  ti_s0 : word; ti_s1 : word; ti_s2 : word; ti_s3 : word; ti_s4 : word; ti_s5 : word;
  ti_s6 : word; ti_s7 : word; ti_s8 : word; ti_s9 : word; ti_s10 : word; ti_s11 : word;
  ti_fs0 : word }.
Definition ti_spq (I : tcI) : Z := ti_q I - 128 - ti_d I.

Definition ti_S (I : tcI) : Z := ti_f I / 8 + 2147450880.

Record tc_ok (I : tcI) : Prop := mkTOK {
  c_d : ti_d I = 0 \/ ti_d I = 16;
  c_lo : 0x6d2000 <= ti_lo I;
  c_room : ti_lo I + 160 + 0x10000 <= ti_q I;
  c_qtop : ti_q I + 16 <= 0x800000000000;
  c_nb8 : ti_NB I mod 8 = 0;
  c_nblo : 0x6d2000 <= ti_NB I;
  c_nbhi : ti_NB I + 48 <= ti_lo I;
  c_f64 : ti_f I mod 64 = 0;
  c_flo : 0x6d2000 <= ti_f I;
  c_fhi : ti_f I + 128 <= ti_lo I;
  c_fS : ti_f I + 128 <= ti_S I \/ ti_S I + 16 <= ti_f I;
  c_Shi : ti_S I + 16 <= ti_lo I;
  c_nbf : ti_NB I + 40 <= ti_f I \/ ti_f I + 128 <= ti_NB I;
  c_nbS : ti_NB I + 40 <= ti_S I \/ ti_S I + 16 <= ti_NB I;
  c_Snf : shad (ti_NB I) + 5 <= ti_f I \/ ti_f I + 128 <= shad (ti_NB I);
  c_SnS : shad (ti_NB I) + 5 <= ti_S I \/ ti_S I + 16 <= shad (ti_NB I);
  c_Snhi : shad (ti_NB I) + 5 <= ti_lo I;
  c_nbSn : ti_NB I + 40 <= shad (ti_NB I) \/ shad (ti_NB I) + 5 <= ti_NB I;
  c_q16 : ti_q I mod 16 = 0 }.

Definition pz (z : Z) : cell := C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))).
Definition sh_poison : list cell :=
  [pz (-15); pz (-15); pz (-15); pz (-15); pz (-8); pz (-8); pz (-8); pz (-8); pz (-8); pz (-13); pz (-13); pz (-13); pz (-13); pz (-13); pz (-13); pz (-13)].
Definition sh_f5 : list cell :=
  [pz (-11); pz (-11); pz (-11); pz (-11); pz (-11); pz (-11); pz (-11); pz (-11); pz (-11); pz (-11); pz (-11); pz (-11); pz (-11); pz (-11); pz (-11); pz (-11)].

Definition tc_saved (I : tcI) : list cell :=
  [C8 (ti_fs0 I); C8 (ti_s9 I); C8 (ti_s8 I); C8 (ti_s7 I); C8 (ti_s6 I); C8 (ti_s5 I); C8 (ti_s4 I);
   C8 (ti_s3 I); C8 (ti_s2 I); C8 (ti_s1 I); C8 (ti_s0 I); C8 (ti_ra I)].

Definition tc_W (I : tcI) : list (Z * Z) :=
  [(ti_spq I, ti_q I); (ti_NB I, ti_NB I + 40); (ti_f I, ti_f I + 24); (ti_f I + 32, ti_f I + 72); (ti_S I, ti_S I + 16)].

Definition TINV (I : tcI) (shc : list cell) (mb m : mem) : Prop :=
  (exists j7 t17 jd, rw_cells asegs m (ti_spq I) [C8 (Z_to_bv 64 (ti_f I)); CB 7 j7; CB 17 t17; CB (Z.to_nat (ti_d I)) jd]) /\
  rw_cells asegs m (ti_q I + -96) (tc_saved I) /\
  (exists h0 h1 h2, rw_cells asegs m (ti_f I) [C8 h0; C8 h1; C8 h2]) /\
  (exists tmp, u8arr asegs m (ti_f I + 32) tmp /\ length tmp = 40%nat) /\
  rw_cells asegs m (ti_S I) shc /\
  (exists nb, u8arr asegs m (ti_NB I) nb /\ length nb = 40%nat) /\
  mem_inv asegs m /\ munch (tc_W I) mb m /\ wmono asegs mb m /\ stk asegs m (ti_lo I) (ti_spq I).

Ltac ti_open H :=
  let j7 := fresh "j7" in let t17 := fresh "t17" in let jd := fresh "jd" in
  let h0 := fresh "h0" in let h1 := fresh "h1" in let h2 := fresh "h2" in
  let tmp := fresh "tmp" in let nb := fresh "nb" in
  destruct H as ((j7 & t17 & jd & LOC) & SAVED & (h0 & h1 & h2 & HDR) & (tmp & TA & TL) & SH & (nb & NA & NL) & MI & MU & WM & ST).
Ltac ti_close :=
  lazymatch goal with
  | |- TINV _ _ _ _ =>
      split; [do 3 eexists; eassumption|]; split; [eassumption|]; split; [do 3 eexists; eassumption|];
      split; [eexists; split; [eassumption| first [assumption | congruence]]|];
      split; [first [eassumption | unfold sh_poison, sh_f5, pz; eassumption]|];
      split; [eexists; split; [eassumption| first [assumption | congruence]]|];
      split; [eassumption|]; split; [eassumption|]; split; eassumption
  end.

Ltac ti_envX OK :=
  pose proof OK as OK'; destruct OK' as [Cd Clo Croom Cqtop Cnb8 Cnblo Cnbhi Cf64 Cflo Cfhi CfS CShi Cnbf CnbS CSnf CSnS CSnhi CnbSn Cq16];
  unfold ti_spq, ti_S in *; unfold shad, SHB in *.

Ltac ti_env OK :=
  pose proof OK as OK'; destruct OK' as [Cd' Clo Croom Cqtop _ Cnblo Cnbhi _ Cflo Cfhi CfS CShi Cnbf CnbS _ _ _ _ _];
  lazymatch type of Cd' with ?d = 0 \/ _ => let Cd := fresh "Cd" in assert (Cd : 0 <= d <= 16) by (clear - Cd'; lia); clear Cd' end;
  unfold ti_spq, ti_S in *; unfold shad, SHB in *.

Definition nb_shz (I : tcI) (mb : mem) : Prop := forall m', munch (tc_W I) mb m' -> wmono asegs mb m' -> shz m' (ti_NB I) 40.
Definition dig_shz (I : tcI) (mb : mem) : Prop := forall m', munch (tc_W I) mb m' -> wmono asegs mb m' -> shz m' 0x29df0 200.

Lemma tc_f8 : forall I, tc_ok I -> ti_f I mod 8 = 0.
Proof. intros I OK. pose proof (c_f64 I OK). Z.div_mod_to_equations. lia. Qed.
