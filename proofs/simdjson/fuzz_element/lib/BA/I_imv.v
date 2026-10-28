(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout R_small R_m2s R_thread I_consts I_qck. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import F_memcpy F_memset. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_kit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import I_memcpyw I_memcpyw2 I_amemcpyw I_amemcpyw2 I_imvw I_imvw2 F_imemmove.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition imv_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (d : Z) (src : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(d, d + Z.of_nat (length src)); (bv_unsigned sp - AMEMCPY_DEPTH, bv_unsigned sp)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ bytes_at asegs m' d src.

Section WithRIP.
Hypothesis RIP : rip_stmt.

Theorem imv_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (d s : Z) (src : list byte) (lo : Z),
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 (Z.of_nat (length src)) ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - AMEMCPY_DEPTH -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp < 2^63 ->
  0 <= d -> 0 <= s -> d + Z.of_nat (length src) <= 2^47 -> s + Z.of_nat (length src) <= 2^47 ->
  (Z.of_nat (length src) = 0 \/ s + Z.of_nat (length src) <= lo \/ bv_unsigned sp <= s) ->
  (Z.of_nat (length src) = 0 \/ d + Z.of_nat (length src) <= lo \/ bv_unsigned sp <= d) ->
  bytes_at asegs m s src -> wr_at asegs m d (Z.of_nat (length src)) ->
  chk_ok m s (Z.of_nat (length src)) -> chk_ok m d (Z.of_nat (length src)) -> m2s_cells m -> icells m -> mem_inv asegs m ->
  evt asegs (imv_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc d src lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x812f0) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until lo. intros -> -> -> ST LO LOLO SPH D0 S0 DH SH SEPS SEPD SRC DWR CS CD M2S IC MI.
  unfold kHighShadowEnd in *.
  set (n := Z.of_nat (length src)) in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(d, d + n); (usp - 2224, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (munch_refl [(usp - 2224, usp)] m) as MUf.
  pose proof IC as (G2 & G1 & RM & SHC & RI).
  assert (SRC0 : keep (bytes_at asegs m s src)) by exact SRC. clear SRC.
  assert (DWR0 : keep (wr_at asegs m d n)) by exact DWR. clear DWR.
  assert (N0 : 0 <= n) by lia.
  assert (RS : n = 0 \/ s + n <= 0x7fff8000 \/ 0x10007fff8007 <= s).
  { destruct (Z.eq_dec n 0) as [E|NE]; [left; exact E| right]. destruct CS as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _).
    unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
  assert (RD : n = 0 \/ d + n <= 0x7fff8000 \/ 0x10007fff8007 <= d).
  { destruct (Z.eq_dec n 0) as [E|NE]; [left; exact E| right]. destruct CD as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _).
    unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }

  assert (OFF : forall p, chk_ok m p n -> 0 <= p -> p + n <= 2^47 ->
            forall m', munch [(d, d + n); (usp - 2224, usp)] m m' -> chk_ok m' p n).
  { intros p CP P0 P1 m' MU'. apply (chk_ok_agree m m' p n CP P0 P1). apply (agree_of_munch _ _ _ _ MU'). intros x Hx.
    cbn [outside]. split; [lia| split; [lia| exact I]]. }
  lstep.
  call (imv_prologue usp d s n); [exact ST| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia| lia| lia
        | exact IC| exact MI|].
  rename PC into FRs. rename PC0 into FR. rename POST into ST1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (OFF s CS S0 SH mm MU) as CS1; pose proof (OFF d CD D0 DH mm MU) as CD1 end.
  assert (IC1 : icells x) by (split; [exact G2| split; [exact G1| split; [exact RM| split; [exact SHC| exact RI]]]]).
  assert (M2S1 : m2s_cells x).
  { destruct M2S as (M1 & M2 & M3). split; [| split].
    - apply (rw_cells_agree asegs m x _ _ M1); [| exact WM]. apply (agree_of_munch _ _ _ _ MUf). intros y Hy. cbn in Hy |- *. lia.
    - apply (rw_cells_agree asegs m x _ _ M2); [| exact WM]. apply (agree_of_munch _ _ _ _ MUf). intros y Hy. cbn in Hy |- *. lia.
    - apply (rw_cells_agree asegs m x _ _ M3); [| exact WM]. apply (agree_of_munch _ _ _ _ MUf). intros y Hy. cbn in Hy |- *. lia. }
  call (imv_src RIP usp d s n); [exact ST1| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia| lia| lia
        | exact CS1| exact M2S1| exact IC1| assumption|].
  lazymatch goal with H : stk asegs _ lo (usp + -2144) |- _ => rename H into ST2 end.
  clear CS1 CD1 IC1 M2S1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (OFF d CD D0 DH mm MU) as CD2;
    assert (IC2 : icells mm) by (split; [exact G2| split; [exact G1| split; [exact RM| split; [exact SHC| exact RI]]]]);
    assert (M2S2 : m2s_cells mm) by (destruct M2S as (M1 & M2 & M3); split; [| split];
      [ apply (rw_cells_agree asegs m mm _ _ M1); [| exact WM]; apply (agree_of_munch _ _ _ _ MUf); intros y Hy; cbn in Hy |- *; lia
      | apply (rw_cells_agree asegs m mm _ _ M2); [| exact WM]; apply (agree_of_munch _ _ _ _ MUf); intros y Hy; cbn in Hy |- *; lia
      | apply (rw_cells_agree asegs m mm _ _ M3); [| exact WM]; apply (agree_of_munch _ _ _ _ MUf); intros y Hy; cbn in Hy |- *; lia ])
  end.
  call (imv_dst RIP usp d s n); [exact ST2| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia| lia| lia
        | exact CD2| exact M2S2| exact IC2| assumption|].
  lazymatch goal with H : stk asegs _ lo (usp + -2144) |- _ => rename H into ST3 end.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (SRC : bytes_at asegs mm s src)
      by (unfold keep in SRC0; apply (bytes_at_agree asegs m mm _ _ SRC0); apply (agree_of_munch _ _ _ _ MUf); intros y Hy;
          cbn [outside]; fold n in Hy; (split; [lia| exact I]));
    assert (DWR : wr_at asegs mm d n) by (unfold keep in DWR0; destruct DWR0 as (W0 & W1 & W2); split; [exact W0 | split; [exact W1 | intros i Hi; exact (WM _ (W2 i Hi))]])
  end.
  clear CD2 IC2 M2S2 MUf SRC0 DWR0.
  assert (EUd : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  lstep.
  destruct (Z.eq_dec n 0) as [NZ0|NNZ].
  -
    eapply evt_cut.
    { eapply (imm_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d s src);
        [ reflexivity | reflexivity | reflexivity | lia | lia | fold n; lia | fold n; lia | exact SRC | exact DWR | assumption ]. }
    intros ms' PO. destruct_exs PO. destruct PO as [E [MUc [WMc [MIc DB]]]]. subst ms'.
    fold n in MUc. rewrite NZ0, Z.add_0_r in MUc.
    lazymatch type of MUc with munch _ ?m1 ?m2 =>
      assert (MUe : munch [] m1 m2) by (eapply munch_weaken; [| exact MUc]; unfold sub_fp; cbn [outside]; intros; lia);
      clear MUc; transport_after_call asegs m1 m2 MUe WMc; clear MUe WMc end.
    replace (ret_pc (Z_to_bv 64 0x8211c)) with (Z_to_bv 64 0x8211c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    do 11 lstep.
    release_frame FR ST3 (usp + -72). release_frame FRs ST3 usp.
    lstep.
    unfold imv_post. sys_finish.
    + rewrite (unsigned_lit usp) by lia.
      eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
    + rewrite (unsigned_lit usp) by lia. assumption.
  - call (imm_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d s src);
      [ reflexivity | reflexivity | reflexivity | lia | lia | fold n; lia | fold n; lia | exact SRC | exact DWR | assumption |].
    do 11 lstep.
    release_frame FR ST3 (usp + -72). release_frame FRs ST3 usp.
    lstep.
    unfold imv_post. sys_finish.
    + rewrite (unsigned_lit usp) by lia.
      eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
    + rewrite (unsigned_lit usp) by lia. assumption.
Qed.

End WithRIP.
