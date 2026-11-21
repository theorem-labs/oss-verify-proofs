(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.World Require Import Src_zlib_zlib_uncompress2_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk Frame RefMemcpyLib AgentLib SumWalkTac
  FuzzLib FuzzZ FuzzCk FuzzMem S7AdlerBase S7Adler_code S7AdlerIface FuzzAdlerLib S7AdlerA S7AdlerB.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit Require Import LiaFast.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.cks Require Import CkTables CkModel CkMathAdler CkWalk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Opaque adler32_z_model lo16 hi16 byte_at.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.PropExec.FPState}.

Definition W8 (v : word) : list byte := word_to_le_bytes 8 v.
Definition M1 (m : word -> option byte) (usp : Z) (s0v s1v s2v : word) : word -> option byte :=
  wbytes (wbytes (wbytes m (Z_to_bv 64 (usp - 8)) (W8 s0v)) (Z_to_bv 64 (usp - 16)) (W8 s1v))
         (Z_to_bv 64 (usp - 24)) (W8 s2v).

Lemma lenW8' : forall v, length (W8 v) = 8%nat.
Proof. intros. apply lenW8. Qed.

Section FRAME.
  Variables (m : word -> option byte) (usp : Z) (s0v s1v s2v : word).
  Hypothesis Husp : 32 <= usp < two64.
  Hypothesis Hstk : store_ok RSEGS m (Z_to_bv 64 (usp - 32)) 32 = true.
  Hypothesis Himg : img_ok m.

  #[local] Abbreviation MM := (M1 m usp s0v s1v s2v).

  Lemma stk_slot : forall m' z, mem_grows m m' -> usp - 32 <= z -> z + 8 <= usp ->
    store_ok RSEGS m' (Z_to_bv 64 z) 8 = true.
  Proof.
    intros m' z Hg Hlo Hhi. eapply store_ok_mono; [exact Hg|].
    eapply (store_ok_sub RSEGS m (Z_to_bv 64 (usp - 32)) _ 32 8);
      [ rewrite u64_lit by lia; change (Z.of_nat 32) with 32; lia | exact Hstk
      | rewrite !u64_lit by lia; lia | rewrite !u64_lit by lia; change (Z.of_nat 8) with 8; change (Z.of_nat 32) with 32; lia ].
  Qed.

  Lemma grows_w : forall m0 (a : word) bs, mem_grows m m0 -> mem_grows m (wbytes m0 a bs).
  Proof. intros. eapply mem_grows_trans; [eassumption | apply wbytes_grows]. Qed.

  Lemma frame_off_ro32 : RO_HI <= usp - 32 \/ usp <= RO_LO.
  Proof.
    destruct (store_ok_off_ro m (usp - 32) 32 Hstk ltac:(lia) ltac:(change (Z.of_nat 32) with 32; lia)
                ltac:(change (Z.of_nat 32) with 32; lia) Himg); change (Z.of_nat 32) with 32 in *; lia.
  Qed.

  Lemma M1_img : img_ok MM.
  Proof.
    pose proof frame_off_ro32 as Hro. unfold M1.
    repeat (apply img_ok_wbytes; [| rewrite lenW8', u64_lit by lia; change (Z.of_nat 8) with 8; unfold RO_LO, RO_HI in *; lia
                                  | rewrite lenW8', u64_lit by lia; change (Z.of_nat 8) with 8; lia ]).
    exact Himg.
  Qed.

  Lemma M1_frame : frame_mod m MM [(Z_to_bv 64 (usp - 32), 32%Z)].
  Proof.
    unfold M1.
    assert (G : forall m0 z v, frame_mod m m0 [(Z_to_bv 64 (usp - 32), 32%Z)] -> usp - 32 <= z -> z + 8 <= usp ->
                 frame_mod m (wbytes m0 (Z_to_bv 64 z) (W8 v)) [(Z_to_bv 64 (usp - 32), 32%Z)]).
    { intros m0 z v Hf Hlo Hhi. eapply frame_mod_trans_same; [exact Hf|].
      eapply frame_mod_weaken; [| apply frame_mod_wbytes; rewrite lenW8', u64_lit by lia; change (Z.of_nat 8) with 8; lia].
      intros a [Ha _]. split; [|exact I]. rewrite lenW8'. change (Z.of_nat 8) with 8.
      intros Hin. apply Ha. unfold in_rng in *. rewrite !u64_lit in * by lia. lia. }
    apply G; [apply G; [apply G; [apply frame_mod_refl| lia | lia] | lia | lia] | lia | lia].
  Qed.

  Lemma M1_bytes : forall adr n, 0 <= adr -> adr + Z.of_nat n <= usp - 32 ->
    bytes_at RSEGS MM adr n = bytes_at RSEGS m adr n.
  Proof.
    intros adr n Ha Hn. unfold M1.
    rewrite !bytes_at_wbytes; rewrite ?lenW8', ?u64_lit by lia; try (change (Z.of_nat 8) with 8); try lia.
    reflexivity.
  Qed.

  Lemma M1_readable : forall adr len,
    (forall i, 0 <= i < len -> exists b : byte, rdn RSEGS m (Z_to_bv 64 (adr + i)) 1 = Some [b]) ->
    (forall i, 0 <= i < len -> exists b : byte, rdn RSEGS MM (Z_to_bv 64 (adr + i)) 1 = Some [b]).
  Proof.
    intros adr len H i Hi. destruct (H i Hi) as [b Hb]. unfold M1.
    edestruct (rdn1_wbytes RSEGS) as [b1 Hb1]; [exact Hb|].
    edestruct (rdn1_wbytes RSEGS) as [b2 Hb2]; [exact Hb1|].
    edestruct (rdn1_wbytes RSEGS) as [b3 Hb3]; [exact Hb2|].
    exists b3. exact Hb3.
  Qed.

  Lemma M1_rd_s0 : rdn RSEGS MM (Z_to_bv 64 (usp - 8)) 8 = Some (W8 s0v).
  Proof.
    unfold M1. rewrite !rdn_wbytes_out_Z by (rewrite ?lenW8'; change (Z.of_nat 8) with 8; lia).
    apply rdn_wbytes_hit8. rewrite u64_lit by lia. lia.
  Qed.
  Lemma M1_rd_s1 : rdn RSEGS MM (Z_to_bv 64 (usp - 16)) 8 = Some (W8 s1v).
  Proof.
    unfold M1. rewrite rdn_wbytes_out_Z by (rewrite ?lenW8'; change (Z.of_nat 8) with 8; lia).
    apply rdn_wbytes_hit8. rewrite u64_lit by lia. lia.
  Qed.
  Lemma M1_rd_s2 : rdn RSEGS MM (Z_to_bv 64 (usp - 24)) 8 = Some (W8 s2v).
  Proof. unfold M1. apply rdn_wbytes_hit8. rewrite u64_lit by lia. lia. Qed.
End FRAME.

Definition LPRO : list reg := [1; 3; 4; 5; 6; 7; 8; 9; 11; 12; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition LEPI : list reg := [1; 3; 4; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

Section RUN.
  Variables (m rom : word -> option byte) (retw : word) (usp a adr len : Z).
  Hypothesis Hret : ret_ok retw.
  Hypothesis Ha : 0 <= a < two64.
  Hypothesis Hadr : 1 <= adr.
  Hypothesis Hlen : 0 <= len.
  Hypothesis Hnw : adr + len < two64.
  Hypothesis Husp : 32 <= usp < two64.
  Hypothesis Hstk : store_ok RSEGS m (Z_to_bv 64 (usp - 32)) 32 = true.
  Hypothesis Hbelow : 1 <= len -> adr + len <= usp - 32.
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

  Lemma pro_run : forall regs,
    getr regs 2 = Z_to_bv 64 usp -> getr regs 10 = Z_to_bv 64 a ->
    getr regs 11 = Z_to_bv 64 adr -> getr regs 12 = Z_to_bv 64 len -> len <> 1 ->
    exists r, msteps RSEGS (mkst regs (0x17230 : word) m rom)
                           (mkst r (0x172a8 : word) (M1 m usp (getr regs 8) (getr regs 9) (getr regs 18)) rom)
      /\ getr r 2 = Z_to_bv 64 (usp - 32) /\ getr r 11 = Z_to_bv 64 adr /\ getr r 12 = Z_to_bv 64 len
      /\ getr r 14 = Z_to_bv 64 (lo16 a) /\ getr r 13 = Z_to_bv 64 (hi16 a)
      /\ lkeeps LPRO regs r.
  Proof.
    intros regs R2 R10 R11 R12 H1.
    eexists. split.
    - stepz F_1712c D_1712c. rewrite (hi16_machine a) by lia.
      stepz F_17130 D_17130.
      stepz F_17134 D_17134.
      stepi F_17138 D_17138; znorm. rewrite (zv_srli_mod (a * 2 ^ 48) 48), (lo16_machine a) by lia.
      stepb_tk F_1713c D_1713c ltac:(condZ).
      stepb_ft F_17190 D_17190 ltac:(condZ).
      stepz F_17194 D_17194.
      sd_z F_17198 D_17198 (usp - 8) ltac:(apply (stk_slot m usp Husp Hstk); [apply mem_grows_refl | lia | lia]).
      sd_z F_1719c D_1719c (usp - 16) ltac:(apply (stk_slot m usp Husp Hstk); [apply grows_w, mem_grows_refl | lia | lia]).
      sd_z F_171a0 D_171a0 (usp - 24) ltac:(apply (stk_slot m usp Husp Hstk); [apply grows_w, grows_w, mem_grows_refl | lia | lia]).
      apply mst_refl.
    - post.
  Qed.

  Lemma epi_short : forall regs s0v s1v s2v,
    getr regs 1 = retw -> getr regs 2 = Z_to_bv 64 (usp - 32) ->
    exists r, msteps RSEGS (mkst regs (0x17320 : word) (M1 m usp s0v s1v s2v) rom)
                           (mkst r retw (M1 m usp s0v s1v s2v) rom)
      /\ getr r 2 = Z_to_bv 64 usp /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v
      /\ lkeeps LEPI regs r.
  Proof.
    intros regs s0v s1v s2v R1 R2.
    pose proof (M1_rd_s0 m usp s0v s1v s2v Husp) as E0.
    pose proof (M1_rd_s1 m usp s0v s1v s2v Husp) as E1.
    pose proof (M1_rd_s2 m usp s0v s1v s2v Husp) as E2.
    eexists. split.
    - ld_z F_1721c D_1721c s0v (usp - 8) E0.
      ld_z F_17220 D_17220 s1v (usp - 16) E1.
      ld_z F_17224 D_17224 s2v (usp - 24) E2.
      stepz F_17228 D_17228.
      stepret F_1722c D_1722c retw ltac:(rwR; reflexivity).
      apply mst_refl.
    - post.
  Qed.

  Lemma epi_long : forall regs s0v s1v s2v,
    getr regs 1 = retw -> getr regs 2 = Z_to_bv 64 (usp - 32) ->
    exists r, msteps RSEGS (mkst regs (0x175e0 : word) (M1 m usp s0v s1v s2v) rom)
                           (mkst r retw (M1 m usp s0v s1v s2v) rom)
      /\ getr r 2 = Z_to_bv 64 usp /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v
      /\ lkeeps LEPI regs r.
  Proof.
    intros regs s0v s1v s2v R1 R2.
    pose proof (M1_rd_s0 m usp s0v s1v s2v Husp) as E0.
    pose proof (M1_rd_s1 m usp s0v s1v s2v Husp) as E1.
    pose proof (M1_rd_s2 m usp s0v s1v s2v Husp) as E2.
    eexists. split.
    - ld_z F_174dc D_174dc s0v (usp - 8) E0.
      ld_z F_174e0 D_174e0 s1v (usp - 16) E1.
      ld_z F_174e4 D_174e4 s2v (usp - 24) E2.
      stepz F_174e8 D_174e8.
      stepret F_174ec D_174ec retw ltac:(rwR; reflexivity).
      apply mst_refl.
    - post.
  Qed.

  Theorem adler32_z_run : forall regs,
    getr regs 1 = retw -> getr regs 2 = Z_to_bv 64 usp -> getr regs 10 = Z_to_bv 64 a ->
    getr regs 11 = Z_to_bv 64 adr -> getr regs 12 = Z_to_bv 64 len ->
    exists r m',
      msteps RSEGS (mkst regs (0x17230 : word) m rom) (mkst r retw m' rom)
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
        apply (M1_bytes m usp); lia. }
      destruct (pro_run regs R2 R10 R11 R12 H1) as (r1 & M1' & S2 & S11 & S12 & S14 & S13 & K1).
      destruct (body_run MM rom adr len HimgM HrdM Hnw ltac:(lia) Hlen r1 a S11 S12 S14 S13 H1)
        as (r2 & pc' & M2 & Hpc & V2 & K2).
      assert (T1 : getr r2 1 = retw) by (rewrite (K2 (1%bv : reg)), (K1 (1%bv : reg)) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])); exact R1).
      assert (T2 : getr r2 2 = Z_to_bv 64 (usp - 32)) by (rewrite (K2 (2%bv : reg)) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])); exact S2).
      assert (EPI : exists r3, msteps RSEGS (mkst r2 pc' MM rom) (mkst r3 retw MM rom)
                 /\ getr r3 2 = Z_to_bv 64 usp /\ getr r3 8 = getr regs 8 /\ getr r3 9 = getr regs 9
                 /\ getr r3 18 = getr regs 18 /\ lkeeps LEPI r2 r3).
      { destruct Hpc as [-> | ->].
        - exact (epi_short r2 _ _ _ T1 T2).
        - exact (epi_long r2 _ _ _ T1 T2). }
      destruct EPI as (r3 & M3 & U2 & U8 & U9 & U18 & K3).
      exists r3, MM. split; [|split; [|split]].
      + eapply msteps_trans; [exact M1'|]. eapply msteps_trans; [exact M2 | exact M3].
      + rewrite (K3 (10%bv : reg)) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])). rewrite V2, EB. reflexivity.
      + intros x Hx. cbv [callee_saved In] in Hx.
        repeat (destruct Hx as [<- | Hx];
          [ first [ rewrite U2, R2; reflexivity
                  | exact U8 | exact U9 | exact U18
                  | rewrite (K3 _), (K2 _), (K1 _) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])); reflexivity ] |]).
        destruct Hx.
      + apply M1_frame; assumption.
  Qed.
End RUN.



Theorem s7_adler32_z_null : S7_adler32_z_null_stmt.
Proof.
  intros regs m rom retw R1 Hret R11 R12.
  eexists. split; [|split].
  - stepz F_1712c D_1712c.
    stepz F_17130 D_17130.
    stepz F_17134 D_17134.
    stepi F_17138 D_17138; znorm.
    stepb_tk F_1713c D_1713c ltac:(condZ).
    stepb_tk F_17190 D_17190 ltac:(condZ).
    stepret F_1718c D_1718c retw ltac:(rwR; reflexivity).
    apply mst_refl.
  - gres. reflexivity.
  - apply (proj2 (keeps_cs_lkeeps _ _)). solve_lkeeps.
Qed.

Lemma wrap_run : forall regs m rom (v : Z),
  getr regs 12 = Z_to_bv 64 v -> 0 <= v < two64 ->
  exists r, msteps RSEGS (mkst regs (0x175f4 : word) m rom) (mkst r (0x17230 : word) m rom)
    /\ getr r 12 = Z_to_bv 64 (v mod 2 ^ 32)
    /\ r = regupd (regupd regs 12 (Z_to_bv 64 (v * 2 ^ 32))) 12 (Z_to_bv 64 (v mod two32)).
Proof.
  intros regs m rom v R12 Hv.
  eexists. split; [|split].
  - stepz F_174f0 D_174f0. stepz F_174f4 D_174f4. stepz F_174f8 D_174f8. apply mst_refl.
  - gres. change (2 ^ 32) with two32. reflexivity.
  - reflexivity.
Qed.

Theorem s7_adler32 : S7_adler32_stmt.
Proof.
  intros regs m rom retw usp a adr v len R1 Hret R2 R10 R11 R12 Hv Hvl Ha Hadr Hnw Husp Hstk Hbelow Himg Hrd.
  destruct (wrap_run regs m rom v R12 Hv) as (r0 & M0 & S12 & Er0).
  assert (Hlen : 0 <= len) by (subst len; apply Z.mod_pos_bound; lia).
  rewrite Hvl in S12.
  assert (G : forall x : reg, x <> 12%bv -> getr r0 x = getr regs x).
  { intros x Hx. subst r0. rewrite !getr_other by (exact Hx). reflexivity. }
  destruct (adler32_z_run m rom retw usp a adr len Hret Ha Hadr Hlen Hnw Husp Hstk Hbelow Himg Hrd r0
              ltac:(rewrite G by (intros E; discriminate E); exact R1)
              ltac:(rewrite G by (intros E; discriminate E); exact R2)
              ltac:(rewrite G by (intros E; discriminate E); exact R10)
              ltac:(rewrite G by (intros E; discriminate E); exact R11) S12)
    as (r & m' & M & V & K & Fm).
  exists r, m'. split; [|split; [exact V | split; [|exact Fm]]].
  - eapply msteps_trans; [exact M0 | exact M].
  - intros x Hx. rewrite (K x Hx). apply G. intros ->. cbv in Hx. intuition discriminate.
Qed.

Theorem s7_adler32_null : S7_adler32_null_stmt.
Proof.
  intros regs m rom retw R1 Hret R11 R12.
  destruct (wrap_run regs m rom 0 R12 ltac:(lia)) as (r0 & M0 & S12 & Er0).
  assert (G : forall x : reg, x <> 12%bv -> getr r0 x = getr regs x).
  { intros x Hx. subst r0. rewrite !getr_other by (exact Hx). reflexivity. }
  destruct (s7_adler32_z_null r0 m rom retw ltac:(rewrite G by (intros E; discriminate E); exact R1) Hret
              ltac:(rewrite G by (intros E; discriminate E); exact R11) S12) as (r & M & V & K).
  exists r. split; [|split; [exact V|]].
  - eapply msteps_trans; [exact M0 | exact M].
  - intros x Hx. rewrite (K x Hx). apply G. intros ->. cbv in Hx. intuition discriminate.
Qed.
End FXG.
