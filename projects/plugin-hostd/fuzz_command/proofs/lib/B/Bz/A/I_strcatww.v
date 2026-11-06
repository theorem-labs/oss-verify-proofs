(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtRtA/I_strcpyw.v, with its module paths, addresses and numbers changed; 111 of its 156 lines of code are new or changed and 377 lines of the source are left out. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A Require Import Shadow IcptSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A Require Import R_small R_m2s R_thread I_consts I_qck X_atexit D_kit I_ikit I_pck I_strncmpw.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A Require I_strcatw I_strlen I_strnlenw I_strcpyw I_tramp I_musl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Module BzCat := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A.I_strcatw.
Module BzS := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A.I_strlen.
Module BzN := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A.I_strnlenw.
Module BzC := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A.I_strcpyw.
Module BzT := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A.I_tramp.
Module BzU := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A.I_musl.

Lemma ro_hd1 : forall m A c cs, rw_cells asegs m A (c :: cs) -> ro_cells asegs m A [c].
Proof.
  intros m A c cs [[Hwf Hb] _]. cbn in Hwf. split; [cbn; tauto|].
  cbn [cells_bytes cbytes] in Hb |- *. rewrite app_nil_r. apply bytes_at_app in Hb. exact (proj1 Hb).
Qed.

Local Definition zidle (P : Prop) : Prop := P.
Local Definition parked (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nspz H A SP := lazymatch A with context [SP] => fail | _ => zidle1 H end.
Local Ltac zidle_beginz SP n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(SP - n, SP)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nspz H A SP
    | H : ro_cells segs m ?A _ |- _ => zidle_nspz H A SP
    | H : bytes_at segs m ?A _ |- _ => zidle_nspz H A SP
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.

Section WithRIPSLSC.
Hypothesis RIP : rip_stmt.
Hypothesis SL : BzU.strlen_stmt.
Hypothesis SCP : BzC.strcpy_stmt.

Lemma sc_walk : BzCat.strcat_stmt.
Proof.
  unfold BzCat.strcat_stmt. cbv zeta.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m dstr dslack str slack junk lo.
  intros DS DNZ WR SRC NZ OVL ST LOSP HKS SPH SEPd SEPdk SEPsrc OVL2 DPAD PAD MI KN CKD CKS CKW M2S INITED RSLEN RGCF RCF251 RSCPY RGAF RAF.
  unfold kHighShadowEnd in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (P47 : 2^47 = 140737488355328) by (vm_compute; reflexivity).
  assert (P63 : 2^63 = 9223372036854775808) by (vm_compute; reflexivity).
  pose proof (proj2 (proj2 CKD) ltac:(lia)) as (RIMd & KBd).
  pose proof (proj2 (proj2 CKS) ltac:(lia)) as (RIMs & KBs).
  pose proof (proj2 (proj2 CKW) ltac:(lia)) as (RIMw & KBw).
  unfold region_in_mem, kLowMemEnd, kHighMemEnd, kHighShadowEnd in RIMd, RIMs, RIMw.
  assert (EU32 : bv_unsigned (Z_to_bv 64 (usp + -32)) = usp + -32) by (apply unsigned_lit; lia).
  assert (DLO : 0 <= bv_unsigned a0) by (destruct RIMd as [(?&?&?)|(?&?&?)]; lia).
  assert (DHI : bv_unsigned a0 + (Z.of_nat (length dstr) + 1) <= 2^47) by (destruct RIMd as [(?&?&?)|(?&?&?)]; lia).
  assert (PLO : 0 <= bv_unsigned a1) by (destruct RIMs as [(?&?&?)|(?&?&?)]; lia).
  assert (PHI : bv_unsigned a1 + (Z.of_nat (length str) + 1) <= 2^47) by (destruct RIMs as [(?&?&?)|(?&?&?)]; lia).
  assert (DKLO : 0 <= bv_unsigned a0 + Z.of_nat (length dstr)) by (destruct RIMw as [(?&?&?)|(?&?&?)]; lia).
  assert (DKHI : (bv_unsigned a0 + Z.of_nat (length dstr)) + (Z.of_nat (length str) + 1) <= 2^47) by (destruct RIMw as [(?&?&?)|(?&?&?)]; lia).
  assert (FLd : length (dstr ++ z8 :: dslack) = (length dstr + S (length dslack))%nat) by (rewrite length_app; cbn [length]; lia).
  assert (FLs : length (str ++ z8 :: slack) = (length str + S (length slack))%nat) by (rewrite length_app; cbn [length]; lia).
  pose proof (munch_refl [(usp - 2256, usp)] m) as MUs.
  pose proof (munch_refl [(usp - 2256, usp); (bv_unsigned a0 + Z.of_nat (length dstr), bv_unsigned a0 + Z.of_nat (length dstr) + Z.of_nat (length str) + 1)] m) as MU.
  pose proof (wmono_refl asegs m) as WM0.
  pose proof WR as WRm. change (parked (rw_cells asegs m (bv_unsigned a0 + Z.of_nat (length dstr)) [CB (S (length str)) junk])) in WRm.
  replace (S (length str)) with (length str + 1)%nat in WRm by lia.
  pose proof DS as DSm. change (parked (bytes_at asegs m (bv_unsigned a0) (dstr ++ z8 :: dslack))) in DSm.
  carve_frame 32%nat ST.
  zidle_beginz usp 32%Z MUz1 WMz1.
  xsteps_to 0x4517c%Z.
  zidle_end MUz1 WMz1.
  apply BzT.tramp_strlen.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (AGL : agree_on (fun x => 0 <= x < 0x1000000) m mm) by (apply (agree_of_munch _ _ _ _ MUs); intros y Hy; cbn [outside]; lia);
    assert (AGS : agree_on (fun x => 0x7fff8000 <= x < 0x10007fff8000) m mm) by (apply (agree_of_munch _ _ _ _ MUs); intros y Hy; cbn [outside]; lia);
    pose proof (m2s_cells_agree m mm M2S AGL WM0) as M2S0;
    pose proof (chk_ok_agree m mm (bv_unsigned a0) _ CKD DLO DHI AGS) as CKD0;
    assert (ICSN0 : BzN.icells_sn mm) by
      (destruct M2S0 as (M2a & M2b & M2c); unfold BzN.icells_sn;
       split; [exact RGCF|]; split; [exact (ro_hd1 mm _ _ _ M2a)|];
       split; [exact (ro_hd1 mm _ _ _ M2b)|]; split; [exact INITED| exact RCF251]);
    clear AGL AGS end.

  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (BzS.istrlen_spec RIP SL) with (s := bv_unsigned a0) (str := dstr) (slack := dslack) (lo := lo)
    | post_call segs mm ] end.
  all: rewrite ?EU32; try (unfold kHighShadowEnd in * ).
  all: try exact DS; try exact DNZ; try exact DPAD; try exact CKD0; try exact M2S0; try exact ICSN0; try exact RSLEN; try exact MI; try exact ST.
  all: try (solve [ symmetry; apply Z_to_bv_bv_unsigned ]).
  all: try (solve [ destruct RIMd as [(?&?&?)|(?&?&?)]; lia ]).
  all: try (solve [ destruct SEPd as [HH|HH]; lia ]).
  all: try (solve [ lia ]).
  rewrite ?EU32 in *.
  xsteps_to 0x45224%Z.
  apply BzT.tramp_strcpy.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (AGL2 : agree_on (fun x => 0 <= x < 0x1000000) m mm) by (apply (agree_of_munch _ _ _ _ MUs); intros y Hy; cbn [outside]; lia);
    assert (AGS2 : agree_on (fun x => 0x7fff8000 <= x < 0x10007fff8000) m mm) by (apply (agree_of_munch _ _ _ _ MUs); intros y Hy; cbn [outside]; lia);
    pose proof (m2s_cells_agree m mm M2S AGL2 WM0) as M2S1;
    pose proof (chk_ok_agree m mm (bv_unsigned a1) _ CKS PLO PHI AGS2) as CKS1;
    pose proof (chk_ok_agree m mm (bv_unsigned a0 + Z.of_nat (length dstr)) _ CKW DKLO DKHI AGS2) as CKW1;
    assert (ICCP1 : BzC.icells_cp mm) by (unfold BzC.icells_cp; split; [exact RSCPY| split; [exact RGAF| exact RAF]]);
    pose proof (rw_cells_transport asegs _ m mm _ _ WRm MUs WM0) as WR1; cbn [disjoint_from cells_size csize Nat.add] in WR1;
      specialize (WR1 ltac:(repeat split; solve [ exact I | destruct SEPdk as [HH|HH]; lia ]));
    pose proof (bytes_at_transport asegs _ m mm _ _ DSm MUs) as DS1; cbn [disjoint_from] in DS1;
      specialize (DS1 ltac:(repeat split; solve [ exact I | destruct SEPd as [HH|HH]; lia ]));
    pose proof (proj1 (proj1 (bytes_at_app asegs mm (bv_unsigned a0) dstr (z8 :: dslack)) DS1)) as DSpre; clear DS1;
    clear AGL2 AGS2 end.
  clear MUs.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (BzC.iscpy_spec RIP SCP) with (d := bv_unsigned a0 + Z.of_nat (length dstr)) (s := bv_unsigned a1)
        (str := str) (slack := slack) (junk := junk) (lo := lo)
    | post_call segs mm ] end.
  all: rewrite ?EU32; try (unfold kHighShadowEnd in * ).
  all: try reflexivity.
  all: try exact ST; try exact SRC; try exact NZ; try exact PAD; try exact WR1; try exact CKS1; try exact CKW1; try exact M2S1; try exact INITED; try exact ICCP1; try exact MI.
  all: try (rewrite ?EU32; eassumption).
  all: try (solve [ symmetry; apply Z_to_bv_bv_unsigned ]).
  all: try (solve [ destruct RIMs as [(?&?&?)|(?&?&?)]; lia ]).
  all: try (solve [ destruct RIMw as [(?&?&?)|(?&?&?)]; lia ]).
  all: try (solve [ destruct OVL as [HH|HH]; lia ]).
  all: try (solve [ destruct OVL2 as [HH|HH]; lia ]).
  all: try (solve [ destruct SEPsrc as [HH|HH]; lia ]).
  all: try (solve [ destruct SEPdk as [HH|HH]; lia ]).
  all: try (solve [ lia ]).
  lazymatch goal with H : rw_cells asegs ?mm (bv_unsigned a0 + Z.of_nat (length dstr)) ?cs |- _ =>
    replace (length str + 1)%nat with (S (length str)) in H by lia; rename H into RWres end.
  pose proof (proj1 (u8arr_of_rw_cells asegs _ _ _ _ RWres)) as BYres.
  do 5 lstep.
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 (usp + -32))) |- _ => rewrite EU32 in H; rename H into STf end.
  release_frame FR STf usp.
  lstep.
  unfold BzCat.strcat_post. sys_finish.
  all: try (assert (EUusp : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia); rewrite ?EUusp).
  all: first
    [ exact MU
    | exact RWres
    | solve [ apply bytes_at_app; split; [ exact DSpre | exact BYres ] ]
    | assumption ].
Qed.

End WithRIPSLSC.
