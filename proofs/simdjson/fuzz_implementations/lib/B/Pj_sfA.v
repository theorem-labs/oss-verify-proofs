(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjPjNum SjPjDig SjPjBeta.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit Sj_akit Sj_acps Sj_num_akit Sj_num_amem Pj_defsA
     Pj_sfA_a Pj_sfA_b Pj_sfA_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | num_load_hook | solve_load_image ].
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma signed_litB : forall z, (-2^63 <= z < 2^63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_signed. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64 / 2)%Z with (2^63)%Z. lia.
Qed.

Definition sf_specA (RT : rt_sig) : Prop :=
  forall (Σ : rts RT) (ra gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (EX q lo : Z),
  ART RT Σ m -> mem_inv bsegs m -> (0 <= EX <= 2047)%Z ->
  stk bsegs m lo q -> (lo + 16 <= q)%Z -> (rt_sp0 RT Σ - STACK_WIN <= lo)%Z -> (q + 16 <= USTACK_TOP)%Z ->
  evt bsegs (fun ms' => exists m', sf_postA1 ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m' ms'
                        /\ munch [(q - 16, q)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo q /\ ART RT Σ m')
      (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 EX) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PJ_SF_A) fc None m (seg_rom bsegs)).

Section Body.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (q : Z)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (jlo : list byte).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis QR : (0x10000 <= q - 16 /\ q < 2^47)%Z.
  Hypothesis FR : rw_cells bsegs m (q - 16) [CB 8 jlo; C8 ra].
  Hypothesis SZ : shz m 0x29c80 9904.
  Hypothesis G1 : ro_cells bsegs m 0x17fec8 [C8 (Z_to_bv 64 0x189978)].
  Hypothesis G2 : ro_cells bsegs m 0x189978 [C8 (Z_to_bv 64 2147450880)].
  Hypothesis QI : (0x6e0000 <= q - 16)%Z.

  Notation POST := (sf_postA1 ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m).
  Notation SFS pc xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 :=
    (MS (mkR ra (Z_to_bv 64 (q + -16)) gp tp xt0 xt1 xt2 s0 s1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 pc) fc None m (seg_rom bsegs)).
  Notation MAIN := (sf_main ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 q F fc m jlo MI QR FR SZ).
  Notation SHORT := (sf_short ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 q F fc m jlo MI QR FR SZ).

  Lemma sf_body1 : forall EX xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (0 <= EX <= 2047)%Z ->
    evt bsegs POST (SFS 0xf6004 xt0 xt1 xt2 xa0 (Z_to_bv 64 EX) xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI QR FR SZ G1 G2 QI.
    intros EX xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HE.
    zstep. zstep. zstep. zstep.
    zstep. if_cases K0; zify_cond K0.
    {
      zstep. apply MAIN. lia. }

    zstep.
    rewrite (swrap32_id (EX + -1075)) by lia.
    zstep. if_cases G; zify_cond G.
    { exfalso. rewrite !signed_litB in G by lia. lia. }
    zstep. if_cases K1.
    { apply SHORT. lia. }
    do 4 zstep.
    apply MAIN. lia.
  Qed.
End Body.

Section Top.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Theorem sf_okA : sf_specA RT.
Proof using AF.
  unfold sf_specA. intros until lo. intros ART0 MI HE ST ROOM LOR QT. unfold PJ_SF_A.
  pose proof (af_sp0_range RT AF Σ m ART0) as SPR.
  pose proof (munch_refl [(q - 16, q)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  zstep.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (ART1 : ART RT Σ m1);
    [ apply (art_client_write RT AF Σ m m1 (q - 16) ART0 ltac:(ul)); [| exact WM];
      intros a Ha; apply MU; cbn [outside]; split; [| exact I]; intros Hin; apply Ha; left; ul |]
  end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    pose proof (af_client_consts RT AF Σ m1 ART1) as (G1 & G2 & _ & _);
    assert (SZ : shz m1 0x29c80 9904);
    [ change 9904%Z with (8 * (9904 / 8))%Z; apply shz_of_acc; [| reflexivity| lia];
      apply (acc_lit RT AF Σ m1 0x29c80 9904 ART1); unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) |]
  end.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SHB in G1, G2.
  replace (q + -16)%Z with (q - 16)%Z in FR by lia.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    eapply evt_mono;
    [ eapply (sf_body1 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 q F fc m1 j MI ltac:(ul) FR SZ G1 G2 ltac:(ul)); exact HE |]
  end.
  cbv beta. intros ms' PO. eexists. split; [exact PO|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [| exact ART1].
  replace (q - 16)%Z with (q + -16)%Z in FR by lia.
  release_frame FR ST q. exact ST.
Qed.
End Top.
