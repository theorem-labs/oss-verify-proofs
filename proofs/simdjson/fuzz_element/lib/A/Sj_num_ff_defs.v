(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjNumber.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_adefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Record ffenv : Type := mkFfEnv {
  f_ra : word; f_sp : word; f_gp : word; f_tp : word;
  f_s0 : word; f_s1 : word; f_s2 : word; f_s3 : word; f_s4 : word; f_s5 : word;
  f_s6 : word; f_s7 : word; f_s8 : word; f_s9 : word; f_s10 : word; f_s11 : word;
  f_A : Z; f_FIRST : Z; f_LAST : Z; f_lo : Z; f_p : Z; f_n : Z; f_txt : list byte }.
Notation f_SP E := (bv_unsigned (f_sp E)).
Notation f_TL E := (Z.of_nat (length (f_txt E))).

Record ff_ok (E : ffenv) : Prop := mkFfOk {
  fo_room : (f_lo E + 128 <= f_SP E)%Z;
  fo_top : (f_SP E + 16 <= USTACK_TOP)%Z;
  fo_tmax : (f_TL E < 2147483648)%Z;
  fo_first : (f_A E <= f_FIRST E <= f_LAST E)%Z;
  fo_last : (f_LAST E <= f_A E + f_TL E)%Z;
  fo_chunk : (0 < f_p E /\ f_p E <= f_A E /\ f_LAST E + 8 <= f_p E + f_n E /\ f_A E + f_TL E <= f_p E + f_n E /\ f_p E + f_n E <= f_lo E)%Z }.

Notation FF_W E := [(f_SP E - 128, f_SP E)]%Z.

Definition ff_saved (E : ffenv) : list cell :=
  [C8 (f_s11 E); C8 (f_s10 E); C8 (f_s9 E); C8 (f_s8 E); C8 (f_s7 E); C8 (f_s6 E); C8 (f_s5 E); C8 (f_s4 E); C8 (f_s3 E); C8 (f_s2 E); C8 (f_s1 E); C8 (f_s0 E); C8 (f_ra E)].

Definition FFINV (E : ffenv) (m0 mm : mem) : Prop :=
  (exists j v vf, rw_cells asegs mm (f_SP E + -128) (CB 8 j :: C8 v :: C8 vf :: ff_saved E)) /\
  bytes_at asegs mm (f_A E) (f_txt E) /\
  mem_inv asegs mm /\ munch (FF_W E) m0 mm /\ wmono asegs m0 mm /\ stk asegs mm (f_lo E) (f_SP E + -128).

Ltac ff_open H :=
  let j := fresh "j" in let v := fresh "v" in let vf := fresh "vf" in
  destruct H as ((j & v & vf & FR) & TXT & MI & MU & WM & ST);
  unfold ff_saved in FR;
  let TXB := fresh "TXB" in pose proof (bytes_at_bound _ _ _ _ TXT) as TXB.
Ltac ff_close :=
  lazymatch goal with
  | |- FFINV _ _ _ =>
      split; [eexists _, _, _; eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption
  end.
Ltac ff_env OK :=
  let ROOM := fresh "ROOM" in let TOP := fresh "TOP" in let TMAX := fresh "TMAX" in
  let HFIRST := fresh "HFIRST" in let HLAST := fresh "HLAST" in let HCH := fresh "HCH" in
  destruct OK as [ROOM TOP TMAX HFIRST HLAST HCH];
  unfold USTACK_TOP in *;
  lazymatch goal with E : ffenv |- _ =>
    let SPR := fresh "SPR" in pose proof (bv_unsigned_in_range 64 (f_sp E)) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    let N8 := fresh "N8" in assert (N8 : (f_n E - 7 <= 8 * (f_n E / 8))%Z) by (Z.div_mod_to_equations; lia) end.

Notation FFS E pc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm :=
  (MS (mkR xra (Z_to_bv 64 (f_SP E + -128)) (f_gp E) (f_tp E) xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6) xF (Z_to_bv 64 pc) xfc None mm (seg_rom asegs)).

Definition ff_post (E : ffenv) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m',
    ms' = MS (mkR (f_ra E) (f_sp E) (f_gp E) (f_tp E) t0 t1 t2 (f_s0 E) (f_s1 E) a0 a1 a2 a3 a4 a5 a6 a7
                  (f_s2 E) (f_s3 E) (f_s4 E) (f_s5 E) (f_s6 E) (f_s7 E) (f_s8 E) (f_s9 E) (f_s10 E) (f_s11 E) t3 t4 t5 t6)
             F' (ret_pc (f_ra E)) fc' None m' (seg_rom asegs)
    /\ frm0 fc' /\ munch (FF_W E) m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m' /\ stk asegs m' (f_lo E) (f_SP E).
Definition ff_atcall (E : ffenv) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F' fc' m',
    ms' = MS (mkR (Z_to_bv 64 0xb9d64) (Z_to_bv 64 (f_SP E + -128)) (f_gp E) (f_tp E) t0 t1 t2 s0 s1
                  (Z_to_bv 64 (f_FIRST E)) (Z_to_bv 64 (f_LAST E)) (Z_to_bv 64 (f_SP E + -120)) (Z_to_bv 64 53) (Z_to_bv 64 0xA0000002E) (Z_to_bv 64 1) a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (Z_to_bv 64 0xe37e0) fc' None m' (seg_rom asegs)
    /\ frm0 fc' /\ FFINV E m0 m' /\ (f_FIRST E < f_LAST E)%Z.
Definition ff_mid (E : ffenv) (m0 : mem) : machine_state -> Prop := fun ms' => ff_post E m0 ms' \/ ff_atcall E m0 ms'.

Section FFDEFS.
  Variable E : ffenv.
  Hypothesis OK : ff_ok E.
  Variable m0 : mem.

  Lemma ff_exit : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E m0 mm -> frm0 xfc ->
    evt asegs (ff_mid E m0) (FFS E 0xb9ca4 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK.
    intros until mm. intros INV FRM. ff_open INV. ff_env OK.
    do 13 zstep. zstep. zstep. zstep.
    release_frame FR ST (f_SP E).
    apply evt_done. left. unfold ff_post. do 17 eexists. exists mm.
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact FRM|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  Qed.

  Lemma ff_cf4 : forall xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E m0 mm -> frm0 xfc -> (f_FIRST E < f_LAST E)%Z ->
    evt asegs (ff_mid E m0) (FFS E 0xb9d44 xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 (f_FIRST E)) (Z_to_bv 64 (f_LAST E)) xa2 xa3 xa4 xa5 xa6 xa7
                                 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK.
    intros until mm. intros INV FRM HLT. pose proof INV as INV0. ff_open INV0. ff_env OK.
    do 8 zstep.
    apply evt_done. right. unfold ff_atcall. do 23 eexists. exists mm.
    split; [cbv delta [mkR]; f_equal; f_equal; try reflexivity|].
    split; [exact FRM|]. split; [exact INV | exact HLT].
  Qed.
End FFDEFS.
