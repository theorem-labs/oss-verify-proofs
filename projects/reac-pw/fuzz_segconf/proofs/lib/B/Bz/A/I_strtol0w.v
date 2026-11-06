(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: relocated unchanged from an earlier relocation of this file for fuzz_command, for the image this tree pins (fuzz_command.asan sha256 c0661b96). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Bz/A/I_strcpyw.v, with its addresses and numbers changed; 300 of its 376 lines of code are new or changed and 371 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Bz/A/I_atoiw.v, with its module paths, addresses and numbers changed; 45 of its 128 lines of code are new or changed and 293 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/Bz/A/I_strtol0w.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
(* The strtol interceptor of reac-pw/fuzz_segconf's ASan+UBSan image B called with endptr = NULL: strtol(x, NULL, 10),
   from the trampoline 0x43b44 through the wrapper 0x4b6b8 (196 B), musl's strtol 0x9a9e8 through REAL(strtol)
   (the slot 0xa5080) with the wrapper's own stack slot as its end pointer, and StrtolFixAndCheck 0x554a4 with
   a2 = 0 (I_strtolfix0.v sfix0_spec), to the return.
   Port of pupnp/FuzzHttp lib/A0/ICP/I_strtol.v:172 strtol0_i_spec (origin/ossv/recipes 501c0d516c69), the same
   path at a1 = 0, onto the Bz kit's form of the live-endptr walk, I_strtolw.v istrtol_spec: the same premises
   without the end-pointer cell, and the same answer (the value [fv str] in a0 and the errno word [fr str ev], from
   strtol_body_stmt, which pupnp's post leaves existential) without the end-pointer write. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A Require Import Shadow IcptSpec R_small R_m2s R_thread I_consts I_qck X_atexit D_kit I_ikit I_init I_strtolfix.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A Require Import I_strtolw I_strtolfix0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Definition parked (P : Prop) : Prop := P.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

(* I_strtolw.v istrtol_post without the end-pointer cell *)
Definition istrtol0_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (rv : word) (erw : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 rv a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - ISTRTOL_DEPTH, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (bv_unsigned tp + -164) [C4 erw].

Theorem istrtol0_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (A : Z) (str : list byte)
    (fv : list byte -> word) (fe : list byte -> Z) (fr : list byte -> word -> word) (ev can : word) (lo : Z),
  rip_stmt -> strtol_body_stmt fv fe fr ->
  bytes_at asegs m A (str ++ [Z_to_bv 8 0]) -> A + Z.of_nat (length str) + 1 <= 2^47 -> Z.of_nat (length str) + 1 <= 2^40 ->
  rw_cells asegs m (bv_unsigned tp + -164) [C4 ev] ->
  bytes_at asegs m STRTOL_SSP_GOT (le8 (Z_to_bv 64 STRTOL_SSP_GUARD)) -> bytes_at asegs m STRTOL_SSP_GUARD (le8 can) ->
  stk asegs m lo (bv_unsigned sp) -> lo + ISTRTOL_DEPTH <= bv_unsigned sp -> kHighShadowEnd < lo -> bv_unsigned sp <= 2^47 ->
  0 <= A -> (forall nn, 1 <= nn <= Z.of_nat (length str) + 1 -> chk_ok m A nn) ->
  (A + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= A) ->
  (bv_unsigned tp + -164 + 4 <= lo \/ bv_unsigned sp <= bv_unsigned tp + -164) ->
  (STRTOL_SSP_GOT + 8 <= lo \/ bv_unsigned sp <= STRTOL_SSP_GOT) ->
  (STRTOL_SSP_GUARD + 8 <= lo \/ bv_unsigned sp <= STRTOL_SSP_GUARD) ->
  (STRTOL_SSP_GUARD + 8 <= bv_unsigned tp + -164 \/ bv_unsigned tp + -164 + 4 <= STRTOL_SSP_GUARD) ->
  m2s_cells m -> icells_sx m -> rw_cells asegs m 0xad498 [C1 (Z_to_bv 8 1)] -> mem_inv asegs m ->
  bytes_at asegs m 0xa5080 (le8 (wa STRTOL)) ->
  bytes_at asegs m 0xa3208 (le8 (wa 0xa9fb8)) -> bytes_at asegs m (0xa9fb8 + 29) [Z_to_bv 8 1] ->
  0 <= fe str <= Z.of_nat (length str) ->
  (bv_unsigned tp + -164 + 4 <= 0x7fff8000 \/ 0x10007fff8000 <= bv_unsigned tp + -164) ->
  (bv_unsigned tp + -164 + 4 <= 0xa3200 \/ 0x13e3de <= bv_unsigned tp + -164) ->
  (bv_unsigned tp + -164 + 4 <= A \/ A + Z.of_nat (length str) + 1 <= bv_unsigned tp + -164) ->
  evt asegs (istrtol0_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (fv str) (fr str ev) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 0) (Z_to_bv 64 10) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x43b44) fc None m (seg_rom asegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A str fv fe fr ev can lo.
  intros RIP SB STR A47 N40 ERR GOT CAN ST LO LOLO SPH A0 CHK
    SEPS SEPT SEPG SEPGU SEPGT M2S ICX AI MI RSLOT AFSLOT AF29 HEEND TPSH TPMETA SEPTA.
  unfold kHighShadowEnd, ISTRTOL_DEPTH in *.
  pose proof (bv_unsigned_in_range 64 sp) as HSPR. unfold bv_modulus in HSPR. cbn [Z.of_N] in HSPR.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(usp - 2272, usp); (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof STR as STRm. change (parked (bytes_at asegs m A (str ++ [Z_to_bv 8 0]))) in STRm.
  lstep.
  carve_frame 40%nat ST. rename FR into FRs. carve_frame 8%nat ST.
  do 10 lstep.
  call asan_init_spec; [exact AI| rewrite EU48; exact ST| lia| lia| assumption|].
  rewrite EU48 in *.
  lazymatch goal with H : stk asegs _ lo (usp + -48) |- _ => rename H into ST1 end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (AF0c : ro_cells asegs mm 0xa3208 [C8 (wa 0xa9fb8)]) by (split; [cbn; tauto| cbn [cells_bytes cbytes app]; exact AFSLOT]);
    assert (AF1c : ro_cells asegs mm (bv_unsigned (wa 0xa9fb8) + 29) [C1 (Z_to_bv 8 1)]) by (rewrite wa_unsigned by lia; exact (ro_C1_of_bytes _ _ _ AF29));
    assert (RS0c : ro_cells asegs mm 0xa5080 [C8 (Z_to_bv 64 0x9a9e8)]) by (split; [cbn; tauto| cbn [cells_bytes cbytes app]; exact RSLOT])
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
      by (apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside]; destruct TPSH as [T|T]; lia);
    assert (M2S1 : m2s_cells mm) by (destruct M2S as (M2a & M2b & M2c); split; [| split];
      [ apply (rw_cells_agree asegs m mm _ _ M2a); [| exact WM]; apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn in Hy |- *; destruct TPMETA as [T|T]; lia
      | apply (rw_cells_agree asegs m mm _ _ M2b); [| exact WM]; apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn in Hy |- *; destruct TPMETA as [T|T]; lia
      | apply (rw_cells_agree asegs m mm _ _ M2c); [| exact WM]; apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn in Hy |- *; destruct TPMETA as [T|T]; lia ]);
    assert (CHK1 : forall nn, 1 <= nn <= Z.of_nat (length str) + 1 -> chk_ok mm A nn)
      by (intros nn Hnn; apply (chk_ok_agree m mm A nn (CHK nn Hnn) ltac:(lia) ltac:(lia) AGS));
    assert (ICX1 : icells_sx mm) by (destruct ICX as (ICc1 & ICc2); split;
      [ apply (ro_cells_agree asegs m mm _ _ ICc1); apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn in Hy |- *; destruct TPMETA as [T|T]; lia
      | apply (ro_cells_agree asegs m mm _ _ ICc2); apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn in Hy |- *; destruct TPMETA as [T|T]; lia ]);
    assert (STR1 : bytes_at asegs mm A (str ++ [Z_to_bv 8 0]))
      by (unfold parked in STRm;
          refine (bytes_at_transport asegs _ m mm _ _ STRm MU _);
          cbn [disjoint_from]; rewrite length_app; cbn [length Nat.add];
          split; [destruct SEPS; lia| split; [destruct SEPTA; lia| exact I]]);
    clear AGS
  end.
  clear STRm.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (sfix0_spec RIP) with (A:=A)(k:=fe str)(base:=10)(str:=str)(lo:=lo);
      rewrite ?EU48;
      first [ exact STR1 | exact CHK1 | assumption | reflexivity | (left; reflexivity)
            | (destruct SEPS; lia) | lia ]
    | post_call asegs mm ] end.
  rewrite ?EU48 in *.
  lazymatch goal with H : stk asegs _ lo (usp + -48) |- _ => rename H into STf end.
  lazymatch goal with H : rw_cells asegs _ (usp + -48) [C8 (Z_to_bv 64 (A + fe str))] |- _ => rename H into LE2 end.
  do 6 lstep.
  release_frame LE2 STf (usp + -40). release_frame FRs STf (usp).
  lstep. lstep.
  unfold istrtol0_post. sys_finish.
  all: rewrite ?EU; assumption.
Qed.
