(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.World Require Import Src_zlib_zlib_uncompress3_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk Frame RefMemcpyLib AgentLib SumWalkTac
  FuzzLib FuzzZ FuzzCk FuzzMem S8AdlerBase S8Adler_code S8AdlerIface FuzzAdlerLib S8AdlerA S8AdlerB S8Adler.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.cks Require Import CkTables CkModel CkMathAdler CkWalk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.


Definition S8_adler32_apart_stmt : Prop :=
  forall regs m rom (retw : word) (usp a adr v len : Z),
    getr regs 1 = retw -> ret_ok retw -> getr regs 2 = Z_to_bv 64 usp ->
    getr regs 10 = Z_to_bv 64 a -> getr regs 11 = Z_to_bv 64 adr -> getr regs 12 = Z_to_bv 64 v ->
    0 <= v < 2 ^ 64 -> v mod 2 ^ 32 = len ->
    0 <= a < 2 ^ 64 -> 1 <= adr -> adr + len < 2 ^ 64 -> 32 <= usp < 2 ^ 64 ->
    store_ok RSEGS m (Z_to_bv 64 (usp - 32)) 32 = true ->
    (1 <= len -> adr + len <= usp - 32 \/ usp <= adr) ->
    img_ok m ->
    (forall i, 0 <= i < len -> exists b : byte, rdn RSEGS m (Z_to_bv 64 (adr + i)) 1 = Some [b]) ->
    exists r m',
      msteps RSEGS (mkst regs (0x1765c : word) m rom) (mkst r retw m' rom)
      /\ getr r 10 = Z_to_bv 64 (adler32_z_model a (bytes_at RSEGS m adr (Z.to_nat len)))
      /\ keeps_cs regs r
      /\ frame_mod m m' [(Z_to_bv 64 (usp - 32), 32%Z)].

Lemma M1_bytes_apart : forall m usp s0v s1v s2v adr n, 32 <= usp < two64 -> 0 <= adr ->
  adr + Z.of_nat n <= two64 -> (adr + Z.of_nat n <= usp - 32 \/ usp <= adr) ->
  bytes_at RSEGS (M1 m usp s0v s1v s2v) adr n = bytes_at RSEGS m adr n.
Proof.
  intros m usp s0v s1v s2v adr n Husp Ha Hn Hd. unfold M1. pose proof two64_pow as TW.
  rewrite !bytes_at_wbytes; rewrite ?lenW8', ?u64_lit by lia; try (change (Z.of_nat 8) with 8); try lia.
  reflexivity.
Qed.

Section RUN_A.
  Variables (m rom : word -> option byte) (retw : word) (usp a adr len : Z).
  Hypothesis Hret : ret_ok retw.
  Hypothesis Ha : 0 <= a < two64.
  Hypothesis Hadr : 1 <= adr.
  Hypothesis Hlen : 0 <= len.
  Hypothesis Hnw : adr + len < two64.
  Hypothesis Husp : 32 <= usp < two64.
  Hypothesis Hstk : store_ok RSEGS m (Z_to_bv 64 (usp - 32)) 32 = true.
  Hypothesis Hbelow : 1 <= len -> adr + len <= usp - 32 \/ usp <= adr.
  Hypothesis Himg : img_ok m.
  Hypothesis Hrd : forall i, 0 <= i < len -> exists b : byte, rdn RSEGS m (Z_to_bv 64 (adr + i)) 1 = Some [b].

  Ltac zbv := apply (f_equal (fun z : Z => Z_to_bv 64 z)); lia.
  Ltac solve_ka := first [ assumption | apply lkeeps_refl | solve_lkeeps ].
  Ltac post := repeat split; gres; rwR; first [ reflexivity | assumption | zbv | lia | solve_ka ].

  Ltac sd_z F D az oktac :=
    chain_step;
    [ reflexivity
    | eapply step_sd_at with (a := Z_to_bv 64 az);
      [ exact F | reflexivity | exact D
      | gres; imm_norm; rwR; rewrite ?zv_addi; zbv
      | gres; rwR; reflexivity
      | oktac ]
    | step_simpl ].

  Ltac ld_z F D vv az R :=
    chain_step;
    [ reflexivity
    | eapply step_ld with (v := vv);
      [ exact F | reflexivity | exact D
      | gres; imm_norm; rwR; rewrite ?zv_addi;
        match goal with |- rdn _ _ (Z_to_bv 64 ?x) _ = _ => replace x with az by lia end; exact R
      | apply bytes_le_to_Z_8 ]
    | step_simpl; gres ].

  Lemma pro_run_a : forall regs,
    getr regs 2 = Z_to_bv 64 usp -> getr regs 10 = Z_to_bv 64 a ->
    getr regs 11 = Z_to_bv 64 adr -> getr regs 12 = Z_to_bv 64 len -> len <> 1 ->
    exists r, msteps RSEGS (mkst regs (0x17298 : word) m rom)
                           (mkst r (0x17310 : word) (M1 m usp (getr regs 8) (getr regs 9) (getr regs 18)) rom)
      /\ getr r 2 = Z_to_bv 64 (usp - 32) /\ getr r 11 = Z_to_bv 64 adr /\ getr r 12 = Z_to_bv 64 len
      /\ getr r 14 = Z_to_bv 64 (lo16 a) /\ getr r 13 = Z_to_bv 64 (hi16 a)
      /\ lkeeps LPRO regs r.
  Proof.
    intros regs R2 R10 R11 R12 H1.
    eexists. split.
    - stepz F_17194 D_17194. rewrite (hi16_machine a) by lia.
      stepz F_17198 D_17198.
      stepz F_1719c D_1719c.
      stepi F_171a0 D_171a0; znorm. rewrite (zv_srli_mod (a * 2 ^ 48) 48), (lo16_machine a) by lia.
      stepb_tk F_171a4 D_171a4 ltac:(condZ).
      stepb_ft F_171f8 D_171f8 ltac:(condZ).
      stepz F_171fc D_171fc.
      sd_z F_17200 D_17200 (usp - 8) ltac:(apply (stk_slot m usp Husp Hstk); [apply mem_grows_refl | lia | lia]).
      sd_z F_17204 D_17204 (usp - 16) ltac:(apply (stk_slot m usp Husp Hstk); [apply grows_w, mem_grows_refl | lia | lia]).
      sd_z F_17208 D_17208 (usp - 24) ltac:(apply (stk_slot m usp Husp Hstk); [apply grows_w, grows_w, mem_grows_refl | lia | lia]).
      apply mst_refl.
    - post.
  Qed.

  Lemma epi_short_a : forall regs s0v s1v s2v,
    getr regs 1 = retw -> getr regs 2 = Z_to_bv 64 (usp - 32) ->
    exists r, msteps RSEGS (mkst regs (0x17388 : word) (M1 m usp s0v s1v s2v) rom)
                           (mkst r retw (M1 m usp s0v s1v s2v) rom)
      /\ getr r 2 = Z_to_bv 64 usp /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v
      /\ lkeeps LEPI regs r.
  Proof.
    intros regs s0v s1v s2v R1 R2.
    pose proof (M1_rd_s0 m usp s0v s1v s2v Husp) as E0.
    pose proof (M1_rd_s1 m usp s0v s1v s2v Husp) as E1.
    pose proof (M1_rd_s2 m usp s0v s1v s2v Husp) as E2.
    eexists. split.
    - ld_z F_17284 D_17284 s0v (usp - 8) E0.
      ld_z F_17288 D_17288 s1v (usp - 16) E1.
      ld_z F_1728c D_1728c s2v (usp - 24) E2.
      stepz F_17290 D_17290.
      stepret F_17294 D_17294 retw ltac:(rwR; reflexivity).
      apply mst_refl.
    - post.
  Qed.

  Lemma epi_long_a : forall regs s0v s1v s2v,
    getr regs 1 = retw -> getr regs 2 = Z_to_bv 64 (usp - 32) ->
    exists r, msteps RSEGS (mkst regs (0x17648 : word) (M1 m usp s0v s1v s2v) rom)
                           (mkst r retw (M1 m usp s0v s1v s2v) rom)
      /\ getr r 2 = Z_to_bv 64 usp /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v
      /\ lkeeps LEPI regs r.
  Proof.
    intros regs s0v s1v s2v R1 R2.
    pose proof (M1_rd_s0 m usp s0v s1v s2v Husp) as E0.
    pose proof (M1_rd_s1 m usp s0v s1v s2v Husp) as E1.
    pose proof (M1_rd_s2 m usp s0v s1v s2v Husp) as E2.
    eexists. split.
    - ld_z F_17544 D_17544 s0v (usp - 8) E0.
      ld_z F_17548 D_17548 s1v (usp - 16) E1.
      ld_z F_1754c D_1754c s2v (usp - 24) E2.
      stepz F_17550 D_17550.
      stepret F_17554 D_17554 retw ltac:(rwR; reflexivity).
      apply mst_refl.
    - post.
  Qed.

  Theorem adler32_z_run_a : forall regs,
    getr regs 1 = retw -> getr regs 2 = Z_to_bv 64 usp -> getr regs 10 = Z_to_bv 64 a ->
    getr regs 11 = Z_to_bv 64 adr -> getr regs 12 = Z_to_bv 64 len ->
    exists r m',
      msteps RSEGS (mkst regs (0x17298 : word) m rom) (mkst r retw m' rom)
      /\ getr r 10 = Z_to_bv 64 (adler32_z_model a (bytes_at RSEGS m adr (Z.to_nat len)))
      /\ keeps_cs regs r
      /\ frame_mod m m' [(Z_to_bv 64 (usp - 32), 32%Z)].
  Proof.
    intros regs R1 R2 R10 R11 R12.
    destruct (Z.eq_dec len 1) as [H1 | H1].
    -
      subst len.
      destruct (a1_run m rom adr 1 Hrd regs retw a Hret R1 R10 R11 R12 Ha ltac:(lia)) as (r & M & V & K).
      exists r, m. split; [exact M|]. split; [|split; [exact K | apply frame_mod_refl]].
      rewrite V. change (Z.to_nat 1) with 1%nat. reflexivity.
    - set (MM := M1 m usp (getr regs 8) (getr regs 9) (getr regs 18)).
      pose proof (M1_img m usp (getr regs 8) (getr regs 9) (getr regs 18) Husp Hstk Himg) as HimgM.
      pose proof (M1_readable m usp (getr regs 8) (getr regs 9) (getr regs 18) adr len Hrd) as HrdM.
      assert (EB : bytes_at RSEGS MM adr (Z.to_nat len) = bytes_at RSEGS m adr (Z.to_nat len)).
      { destruct (Z.eq_dec len 0) as [-> | Hz]; [reflexivity|].
        apply (M1_bytes_apart m usp); lia. }
      destruct (pro_run_a regs R2 R10 R11 R12 H1) as (r1 & M1' & S2 & S11 & S12 & S14 & S13 & K1).
      destruct (body_run MM rom adr len HimgM HrdM Hnw ltac:(lia) Hlen r1 a S11 S12 S14 S13 H1)
        as (r2 & pc' & M2 & Hpc & V2 & K2).
      assert (T1 : getr r2 1 = retw) by (rewrite (K2 (1%bv : reg)), (K1 (1%bv : reg)) by (cbv; tauto); exact R1).
      assert (T2 : getr r2 2 = Z_to_bv 64 (usp - 32)) by (rewrite (K2 (2%bv : reg)) by (cbv; tauto); exact S2).
      assert (EPI : exists r3, msteps RSEGS (mkst r2 pc' MM rom) (mkst r3 retw MM rom)
                 /\ getr r3 2 = Z_to_bv 64 usp /\ getr r3 8 = getr regs 8 /\ getr r3 9 = getr regs 9
                 /\ getr r3 18 = getr regs 18 /\ lkeeps LEPI r2 r3).
      { destruct Hpc as [-> | ->].
        - exact (epi_short_a r2 _ _ _ T1 T2).
        - exact (epi_long_a r2 _ _ _ T1 T2). }
      destruct EPI as (r3 & M3 & U2 & U8 & U9 & U18 & K3).
      exists r3, MM. split; [|split; [|split]].
      + eapply msteps_trans; [exact M1'|]. eapply msteps_trans; [exact M2 | exact M3].
      + rewrite (K3 (10%bv : reg)) by (cbv; tauto). rewrite V2, EB. reflexivity.
      + intros x Hx. cbv [callee_saved In] in Hx.
        repeat (destruct Hx as [<- | Hx];
          [ first [ rewrite U2, R2; reflexivity
                  | exact U8 | exact U9 | exact U18
                  | rewrite (K3 _), (K2 _), (K1 _) by (cbv; tauto); reflexivity ] |]).
        destruct Hx.
      + apply M1_frame; assumption.
  Qed.
End RUN_A.


Theorem s8_adler32_apart : S8_adler32_apart_stmt.
Proof.
  intros regs m rom retw usp a adr v len R1 Hret R2 R10 R11 R12 Hv Hvl Ha Hadr Hnw Husp Hstk Hbelow Himg Hrd.
  destruct (wrap_run regs m rom v R12 Hv) as (r0 & M0 & S12 & Er0).
  assert (Hlen : 0 <= len) by (subst len; apply Z.mod_pos_bound; lia).
  rewrite Hvl in S12.
  assert (G : forall x : reg, x <> 12%bv -> getr r0 x = getr regs x).
  { intros x Hx. subst r0. rewrite !getr_other by (exact Hx). reflexivity. }
  destruct (adler32_z_run_a m rom retw usp a adr len Hret Ha Hadr Hlen Hnw Husp Hstk Hbelow Himg Hrd r0
              ltac:(rewrite G by (intros E; discriminate E); exact R1)
              ltac:(rewrite G by (intros E; discriminate E); exact R2)
              ltac:(rewrite G by (intros E; discriminate E); exact R10)
              ltac:(rewrite G by (intros E; discriminate E); exact R11) S12)
    as (r & m' & M & V & K & Fm).
  exists r, m'. split; [|split; [exact V | split; [|exact Fm]]].
  - eapply msteps_trans; [exact M0 | exact M].
  - intros x Hx. rewrite (K x Hx). apply G. intros ->. cbv in Hx. intuition discriminate.
Qed.

End FXG.
