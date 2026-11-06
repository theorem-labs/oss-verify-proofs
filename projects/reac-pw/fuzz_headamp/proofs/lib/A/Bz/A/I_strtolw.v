(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: relocated unchanged from an earlier relocation of this file for fuzz_command, for the image this tree pins (fuzz_command.asan sha256 c0661b96). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Bz/A/I_strcpyw.v, with its addresses and numbers changed; 300 of its 376 lines of code are new or changed and 371 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Bz/A/I_atoiw.v, with its module paths, addresses and numbers changed; 95 of its 182 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/plugin-hostd/fuzz_command/lib/A/Bz/A/I_strtolw.v at 2d2ff01bb6f; module paths changed to reac-pw/fuzz_headamp; 18 numeral(s) moved from fuzz_command.asan to fuzz_headamp.asan by alreloc a5c53bb2bed4. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Bz.A Require Import Shadow IcptSpec R_small R_m2s R_thread I_consts I_qck X_atexit D_kit I_ikit I_init I_strtolfix.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Definition parked (P : Prop) : Prop := P.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition STRTOL : Z := 0x952f8.
Definition STRTOL_SSP_GOT : Z := 0x9cff8.
Definition STRTOL_SSP_GUARD : Z := 0x5f7d90.

Definition strtol_body_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (rv : word) (A Ep Eend : Z) (erw : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 rv a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 368, bv_unsigned sp); (Ep, Ep + 8); (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' Ep [C8 (Z_to_bv 64 (A + Eend))]
    /\ rw_cells asegs m' (bv_unsigned tp + -164) [C4 erw].

Definition strtol_body_stmt (fv : list byte -> word) (fe : list byte -> Z) (fr : list byte -> word -> word) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (A Ep : Z) (str : list byte) (ev can e0 : word) (lo : Z),
    bytes_at asegs m A (str ++ [Z_to_bv 8 0]) -> A + Z.of_nat (length str) + 1 < 2^64 ->
    0 < Ep -> rw_cells asegs m Ep [C8 e0] ->
    rw_cells asegs m (bv_unsigned tp + -164) [C4 ev] ->
    bytes_at asegs m STRTOL_SSP_GOT (le8 (Z_to_bv 64 STRTOL_SSP_GUARD)) -> bytes_at asegs m STRTOL_SSP_GUARD (le8 can) ->
    stk asegs m lo (bv_unsigned sp) -> lo + 368 <= bv_unsigned sp ->
    (A + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= A) ->
    (Ep + 8 <= lo \/ bv_unsigned sp <= Ep) ->
    (bv_unsigned tp + -164 + 4 <= lo \/ bv_unsigned sp <= bv_unsigned tp + -164) ->
    (Ep + 8 <= bv_unsigned tp + -164 \/ bv_unsigned tp + -164 + 4 <= Ep) ->
    (STRTOL_SSP_GOT + 8 <= lo \/ bv_unsigned sp <= STRTOL_SSP_GOT) ->
    (STRTOL_SSP_GUARD + 8 <= lo \/ bv_unsigned sp <= STRTOL_SSP_GUARD) ->
    (STRTOL_SSP_GUARD + 8 <= bv_unsigned tp + -164 \/ bv_unsigned tp + -164 + 4 <= STRTOL_SSP_GUARD) ->
    (STRTOL_SSP_GUARD + 8 <= Ep \/ Ep + 8 <= STRTOL_SSP_GUARD) ->
    mem_inv asegs m -> 0 <= fe str <= Z.of_nat (length str) ->
    evt asegs (strtol_body_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (fv str) A Ep (fe str) (fr str ev) lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 Ep) (Z_to_bv 64 10) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 STRTOL) fc None m (seg_rom asegs)).

Lemma rw_cells_hd8 : forall (m : word -> option byte) (A : Z) (v : word) (cs : list cell),
  rw_cells asegs m A (C8 v :: cs) -> rw_cells asegs m A [C8 v].
Proof.
  intros m A v cs [[Hwf Hby] (Ha & Hn & H)].
  cbn [cells_bytes cbytes] in Hby. apply bytes_at_app in Hby.
  cbn [cells_size csize] in Hn, H.
  split.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact (proj1 Hby).
  - split; [exact Ha|]. cbn [cells_size csize]. split; [lia|]. intros i Hi. apply H. lia.
Qed.

Definition ISTRTOL_DEPTH : Z := 2272.

Definition istrtol_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (rv : word) (A Ep Eend : Z) (erw : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 rv a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - ISTRTOL_DEPTH, bv_unsigned sp); (Ep, Ep + 8); (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' Ep [C8 (Z_to_bv 64 (A + Eend))]
    /\ rw_cells asegs m' (bv_unsigned tp + -164) [C4 erw].

Theorem istrtol_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (A Ep : Z) (str : list byte)
    (fv : list byte -> word) (fe : list byte -> Z) (fr : list byte -> word -> word) (ev can e0 : word) (lo : Z),
  rip_stmt -> strtol_body_stmt fv fe fr ->
  bytes_at asegs m A (str ++ [Z_to_bv 8 0]) -> A + Z.of_nat (length str) + 1 <= 2^47 -> Z.of_nat (length str) + 1 <= 2^40 ->
  0 < Ep -> Ep mod 8 = 0 -> Ep + 8 <= 2^47 -> rw_cells asegs m Ep [C8 e0] -> chk_ok m Ep 8 ->
  rw_cells asegs m (bv_unsigned tp + -164) [C4 ev] ->
  bytes_at asegs m STRTOL_SSP_GOT (le8 (Z_to_bv 64 STRTOL_SSP_GUARD)) -> bytes_at asegs m STRTOL_SSP_GUARD (le8 can) ->
  stk asegs m lo (bv_unsigned sp) -> lo + ISTRTOL_DEPTH <= bv_unsigned sp -> kHighShadowEnd < lo -> bv_unsigned sp <= 2^47 ->
  0 <= A -> (forall nn, 1 <= nn <= Z.of_nat (length str) + 1 -> chk_ok m A nn) ->
  (A + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= A) ->
  (Ep + 8 <= lo \/ bv_unsigned sp <= Ep) ->
  (bv_unsigned tp + -164 + 4 <= lo \/ bv_unsigned sp <= bv_unsigned tp + -164) ->
  (Ep + 8 <= bv_unsigned tp + -164 \/ bv_unsigned tp + -164 + 4 <= Ep) ->
  (STRTOL_SSP_GOT + 8 <= lo \/ bv_unsigned sp <= STRTOL_SSP_GOT) ->
  (STRTOL_SSP_GUARD + 8 <= lo \/ bv_unsigned sp <= STRTOL_SSP_GUARD) ->
  (STRTOL_SSP_GUARD + 8 <= bv_unsigned tp + -164 \/ bv_unsigned tp + -164 + 4 <= STRTOL_SSP_GUARD) ->
  (STRTOL_SSP_GUARD + 8 <= Ep \/ Ep + 8 <= STRTOL_SSP_GUARD) ->
  (Ep + 8 <= A \/ A + Z.of_nat (length str) + 1 <= Ep) ->
  (Ep + 8 <= 0x9c360 \/ 0x1369de <= Ep) ->
  m2s_cells m -> icells_sx m -> rw_cells asegs m 0xa5a98 [C1 (Z_to_bv 8 1)] -> mem_inv asegs m ->
  bytes_at asegs m 0x9e1b0 (le8 (wa STRTOL)) ->
  bytes_at asegs m 0x9c368 (le8 (wa 0xa25b8)) -> bytes_at asegs m (0xa25b8 + 29) [Z_to_bv 8 1] ->
  0 <= fe str <= Z.of_nat (length str) ->
  (bv_unsigned tp + -164 + 4 <= 0x7fff8000 \/ 0x10007fff8000 <= bv_unsigned tp + -164) ->
  (bv_unsigned tp + -164 + 4 <= 0x9c360 \/ 0x1369de <= bv_unsigned tp + -164) ->
  (bv_unsigned tp + -164 + 4 <= A \/ A + Z.of_nat (length str) + 1 <= bv_unsigned tp + -164) ->
  evt asegs (istrtol_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (fv str) A Ep (fe str) (fr str ev) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 Ep) (Z_to_bv 64 10) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x41c28) fc None m (seg_rom asegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A Ep str fv fe fr ev can e0 lo.
  intros RIP SB STR A47 N40 EP0 EPAL EP47 ECELL CHKE ERR GOT CAN ST LO LOLO SPH A0 CHK
    SEPS SEPE SEPT SEPET SEPG SEPGU SEPGT SEPGE SEPEA SEPERT M2S ICX AI MI RSLOT AFSLOT AF29 HEEND TPSH TPMETA SEPTA.
  unfold kHighShadowEnd, ISTRTOL_DEPTH in *.
  pose proof (bv_unsigned_in_range 64 sp) as HSPR. unfold bv_modulus in HSPR. cbn [Z.of_N] in HSPR.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(usp - 2272, usp); (Ep, Ep + 8); (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] m) as MU.
  pose proof (munch_refl [(usp - 2272, usp); (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] m) as MUm.
  pose proof (wmono_refl asegs m) as WM.
  pose proof STR as STRm. change (parked (bytes_at asegs m A (str ++ [Z_to_bv 8 0]))) in STRm.
  lstep.
  carve_frame 40%nat ST. rename FR into FRs. carve_frame 8%nat ST.
  do 10 lstep.
  call asan_init_spec; [exact AI| rewrite EU48; exact ST| lia| lia| assumption|].
  rewrite EU48 in *.
  lazymatch goal with H : stk asegs _ lo (usp + -48) |- _ => rename H into ST1 end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (AF0c : ro_cells asegs mm 0x9c368 [C8 (wa 0xa25b8)]) by (split; [cbn; tauto| cbn [cells_bytes cbytes app]; exact AFSLOT]);
    assert (AF1c : ro_cells asegs mm (bv_unsigned (wa 0xa25b8) + 29) [C1 (Z_to_bv 8 1)]) by (rewrite wa_unsigned by lia; exact (ro_C1_of_bytes _ _ _ AF29));
    assert (RS0c : ro_cells asegs mm 0x9e1b0 [C8 (Z_to_bv 64 0x952f8)]) by (split; [cbn; tauto| cbn [cells_bytes cbytes app]; exact RSLOT])
  end.
  do 6 lstep. if_false. do 7 lstep.
  pose proof (rw_cells_hd8 _ _ _ _ FR) as FRloc.
  pose proof SB as SBs. unfold strtol_body_stmt in SBs.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply SBs with (A:=A)(Ep:=(usp+-48))(str:=str)(lo:=lo)(can:=can)(ev:=ev);
      rewrite ?EU48;
      [exact STR|lia|lia|exact FRloc|exact ERR|exact GOT|exact CAN|exact ST1|lia
      |(destruct SEPS;lia)|lia|(destruct SEPT;lia)|(destruct SEPT;lia)|lia|lia
      |(destruct SEPGT;lia)|lia|assumption|lia]
    | post_call asegs mm ] end.
  rewrite ?EU48 in *.
  lazymatch goal with H : rw_cells asegs _ (usp + -48) [C8 (Z_to_bv 64 (A + fe str))] |- _ => rename H into LE end.
  do 8 lstep.
  lazymatch goal with H : stk asegs _ lo (usp + -48) |- _ => rename H into STq end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (AGS : agree_on (fun x => 0x7fff8000 <= x < 0x10007fff8000) m mm)
      by (apply (agree_of_munch _ _ _ _ MUm); intros y Hy; cbn [outside]; destruct TPSH as [T|T]; lia);
    assert (M2S1 : m2s_cells mm) by (destruct M2S as (M2a & M2b & M2c); split; [| split];
      [ apply (rw_cells_agree asegs m mm _ _ M2a); [| exact WM]; apply (agree_of_munch _ _ _ _ MUm); intros y Hy; cbn in Hy |- *; destruct TPMETA as [T|T]; lia
      | apply (rw_cells_agree asegs m mm _ _ M2b); [| exact WM]; apply (agree_of_munch _ _ _ _ MUm); intros y Hy; cbn in Hy |- *; destruct TPMETA as [T|T]; lia
      | apply (rw_cells_agree asegs m mm _ _ M2c); [| exact WM]; apply (agree_of_munch _ _ _ _ MUm); intros y Hy; cbn in Hy |- *; destruct TPMETA as [T|T]; lia ]);
    pose proof (chk_ok_agree m mm Ep _ CHKE ltac:(lia) ltac:(lia) AGS) as CHKE1;
    assert (CHK1 : forall nn, 1 <= nn <= Z.of_nat (length str) + 1 -> chk_ok mm A nn)
      by (intros nn Hnn; apply (chk_ok_agree m mm A nn (CHK nn Hnn) ltac:(lia) ltac:(lia) AGS));
    assert (ICX1 : icells_sx mm) by (destruct ICX as (ICc1 & ICc2); split;
      [ apply (ro_cells_agree asegs m mm _ _ ICc1); apply (agree_of_munch _ _ _ _ MUm); intros y Hy; cbn in Hy |- *; destruct TPMETA as [T|T]; lia
      | apply (ro_cells_agree asegs m mm _ _ ICc2); apply (agree_of_munch _ _ _ _ MUm); intros y Hy; cbn in Hy |- *; destruct TPMETA as [T|T]; lia ]);
    assert (STR1 : bytes_at asegs mm A (str ++ [Z_to_bv 8 0]))
      by (unfold parked in STRm;
          refine (bytes_at_transport asegs _ m mm _ _ STRm MUm _);
          cbn [disjoint_from]; rewrite length_app; cbn [length Nat.add];
          split; [destruct SEPS; lia| split; [destruct SEPTA; lia| exact I]]);
    clear AGS
  end.
  clear MUm.
  destruct (rw_cells_forget asegs _ Ep _ ECELL) as (ejunk & EJ). cbn [cells_size csize Nat.add] in EJ.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (sfixE_spec RIP) with (A:=A)(E:=Ep)(k:=fe str)(base:=10)(str:=str)(lo:=lo);
      rewrite ?EU48;
      first [ exact EJ | exact STR1 | exact CHK1 | assumption | reflexivity | (left; reflexivity)
            | (destruct SEPS; lia) | (destruct SEPE; lia) | lia ]
    | post_call asegs mm ] end.
  rewrite ?EU48 in *.
  lazymatch goal with H : stk asegs _ lo (usp + -48) |- _ => rename H into STf end.
  lazymatch goal with H : rw_cells asegs _ (usp + -48) [C8 (Z_to_bv 64 (A + fe str))] |- _ => rename H into LE2 end.
  do 6 lstep.
  release_frame LE2 STf (usp + -40). release_frame FRs STf (usp).
  lstep. lstep.
  unfold istrtol_post. sys_finish.
  all: rewrite ?EU; assumption.
Qed.
