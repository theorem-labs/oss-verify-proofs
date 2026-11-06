(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_pop_arg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require BImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_leaves_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcleaf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcdefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_scommon_lg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RTW_sec_snp1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcleaf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcdefs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_scommon_lg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition A_APPNUM : Z := 0x68f1c.

(* [comment removed for export] *)
Definition hq (v : Z) (i : Z) : Z := v / 16 ^ i.
Definition hd (v : Z) (i : Z) : Z := (v / 16 ^ i) mod 16.

Lemma hq_facts : forall v i, 0 <= i -> 2^44 <= v < 2^48 ->
  hq v (i + 1) = hq v i / 16 /\ hd v i = hq v i - 16 * hq v (i + 1) /\ 0 <= hd v i < 16 /\ 0 <= hq v i
  /\ (i <= 10 -> 16 <= hq v i) /\ (i <= 11 -> hq v i < 16 ^ (12 - i)) /\ (i = 11 -> 1 <= hq v i < 16).
Proof.
  intros v i Hi Hv. unfold hq, hd. rewrite Z.pow_add_r, Z.pow_1_r by lia. rewrite <- Z.div_div by (try apply Z.pow_nonneg; try apply Z.lt_gt; try apply Z.pow_pos_nonneg; lia).
  assert (P0 : 0 < 16 ^ i) by (apply Z.pow_pos_nonneg; lia).
  split; [reflexivity|]. split; [Z.div_mod_to_equations; nia|]. split; [Z.div_mod_to_equations; nia|].
  split; [apply Z.div_pos; lia|].
  split; [| split].
  - intros Hle. apply Z.div_le_lower_bound; [lia|].
    assert (16 ^ i * 16 <= 2^44); [| lia]. replace (2^44) with (16 ^ 10 * 16) by reflexivity.
    apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.pow_le_mono_r; lia.
  - intros Hle. apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. replace (i + (12 - i)) with 12 by lia.
    change (16 ^ 12) with (2^48). lia.
  - intros ->. change (16 ^ 11) with (2^44). split; [apply Z.div_le_lower_bound; lia| apply Z.div_lt_upper_bound; lia].
Qed.

(* [comment removed for export] *)
Lemma an_divu_lit : forall a b, (0 <= a < 2^64)%Z -> (0 < b < 2^64)%Z ->
  mul_div M_DIVU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a / b).
Proof.
  intros a b Ha Hb. unfold mul_div. rewrite (unsigned_lit b) by lia.
  replace (b =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
  assert (R : (0 <= a / b <= a)%Z). { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. nia. }
  apply bv_eq. rewrite bv_divu_unsigned. rewrite !unsigned_lit by lia. reflexivity.
Qed.

Section AN.
  Variables (sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (BP bcur bend v lo : Z).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + 336 <= bv_unsigned sp.
  Hypothesis HV : 2^44 <= v < 2^48.
  Hypothesis HBP : bv_unsigned sp <= BP /\ BP + 8 <= bcur.
  Hypothesis HB : bcur + 12 <= bend /\ bend + 1 < 2^64.

  Let NB : Z := bv_unsigned sp + -328.   (* [comment removed for export] *)

  Ltac gi := lstep; lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => if_lia | _ => idtac end.

  (* [comment removed for export] *)
  Lemma ims240 : forall ra' sp' t0 t1 t2 s0' s1' a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' t3 t4 t5 t6 (m0 : word -> option byte) (P : Z) (junk : list byte),
    rw_cells bsegs m0 P [CB 240 junk] -> mem_inv bsegs m0 -> 0 <= P -> P + 240 < 2^64 ->
    evt bsegs (fun ms' => exists (a1' a2' a3' : word) m' junk',
                 ms' = MS (mkR ra' sp' gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 P) a1' a2' a3' a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra') fc None m' (seg_rom bsegs)
                 /\ munch [(P, P + 240)] m0 m' /\ wmono bsegs m0 m' /\ mem_inv bsegs m' /\ rw_cells bsegs m' P [CB 240 junk'])
      (MS (mkR ra' sp' gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 P) (Z_to_bv 64 170) (Z_to_bv 64 240) a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AIMEMSET) fc None m0 (seg_rom bsegs)).
  Proof.
    intros until junk. intros DST MI0 H1 H2.
    destruct (Z.eq_dec (Z.land (Z.lor 240 P) 15) 0) as [AL|NAL].
    2:{ eapply evt_mono; [eapply imemset_call; eauto; lia|]. cbv beta. unfold imemset_post.
        intros ms' nelH_; (nelim nelH_ 8%nat; intros a2' a3' m' -> MU WM MI' DST'). exists (Z_to_bv 64 170), a2', a3', m'. eexists. split; [reflexivity|]. eauto. }
    assert (P16 : P mod 16 = 0).
    { rewrite Z.land_lor_distr_l in AL. apply Z.lor_eq_0_iff in AL. destruct AL as [_ AL].
      change 15 with (Z.ones 4) in AL. rewrite Z.land_ones in AL by lia. exact AL. }
    unfold AIMEMSET.
    pose proof (munch_refl [(P, P + 240)] m0) as MU. pose proof (wmono_refl bsegs m0) as WM.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in DST; [| reflexivity]. cbn [mk_CB_cells app] in DST.
    zstep. zstep.
    zstep. if_cases K0; zify_cond K0; try (exfalso; apply K0; first [exact AL | rewrite Z.lor_comm; exact AL]).
    zstep. if_cases K1; zify_cond K1; try (exfalso; revert K1; rewrite ?unsigned_lit by lia; lia).
    do 8 zstep. fl.
    do 14 (gs; gs; gs; zstep; if_cases K2; zify_cond K2; [| exfalso; revert K2; rewrite ?unsigned_lit by lia; lia]; clear K2).
    gs. gs. gs. zstep. if_cases K3; zify_cond K3; [exfalso; revert K3; rewrite ?unsigned_lit by lia; lia|]. clear K3.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch type of DST with rw_cells _ _ _ ?cs =>
        pose proof (rw_cells_merge bsegs mm P [] cs []) as MG; cbn [app] in MG; rewrite ?app_nil_r in MG; specialize (MG DST); rewrite ?app_nil_r in MG
      end end.
    match type of MG with rw_cells _ _ _ [CB ?sz ?bs] => replace sz with 240%nat in MG by (cbn; lia) end.
    apply evt_done. nexists 4%nat. eexists. split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MG].
  Qed.

  (* [comment removed for export] *)
  Definition an_hi (ra s0 s1 : word) (m1 : word -> option byte) : Prop :=
    rw_cells bsegs m1 (bv_unsigned sp + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Lemma an_A : forall (ra t0 t1 t2 s0 s1 t3 t4 t5 t6 : word) (POST : machine_state -> Prop),
    (forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m1 : word -> option byte) (j8 j240 : list byte),
       munch [(bv_unsigned sp + -336, bv_unsigned sp)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
       stk bsegs m1 lo (bv_unsigned sp + -336) -> an_hi ra s0 s1 m1 ->
       rw_cells bsegs m1 (bv_unsigned sp + -336) [CB 8 j8] -> rw_cells bsegs m1 NB [CB 240 j240] ->
       evt bsegs POST
         (MS (mkR (wz 0x68fdc) (Z_to_bv 64 (bv_unsigned sp + -336)) gp tp x5 x6 x7 (wz bend) (wz BP) (wz NB) x11 x12 x13 x14 x15 x16 x17
                  (wz 0) (wz 1) (wz 16) (wz v) (wz NB) (wz 0) (wz 1) (wz 12) s10 s11 x28 x29 x30 x31)
             F (wz 0x68fdc) fc None m1 (seg_rom bsegs))) ->
    evt bsegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz BP) (wz bend) (wz v) (wz 16) (wz 12) (wz 1) (wz 0) (wz 0) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz A_APPNUM) fc None m (seg_rom bsegs)).
  Proof.
    intros until POST. intros K.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof CEIL as CEIL'. idtac.
    pose proof (munch_refl [(bv_unsigned sp + -336, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    unfold A_APPNUM. cbv beta delta [wz] in *.
    carve_frame 336%nat ST.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 240; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 12 lstep. (* [comment removed for export] *)
    do 7 gi. (* [comment removed for export] *)
    gi. gi. gi. gi. gi. gi. (* [comment removed for export] *)
    gi. gi. (* [comment removed for export] *)
    gi. gi. gi. gi. fl. (* [comment removed for export] *)
    gi. gi. (* [comment removed for export] *)
    gi. gi. gi. gi. gi. fl. (* [comment removed for export] *)
    replace (bv_unsigned sp + -336 + 8) with NB by (unfold NB; lia).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) =>
        pose proof (proj1 (RT_kit.rw_cells_app mm (bv_unsigned sp + -336) [c0] (c1 :: rest)) FR) as [FR8 FRa];
        pose proof (proj1 (RT_kit.rw_cells_app mm _ [c1] rest) FRa) as [FRnb FRhi]; clear FR FRa;
        cbn [cells_size Cells.csize Nat.add] in FRnb, FRhi
      end end.
    replace (bv_unsigned sp + -336 + Z.of_nat 8) with NB in FRnb, FRhi by (unfold NB; lia).
    replace (NB + Z.of_nat 240) with (bv_unsigned sp + -88) in FRhi by (unfold NB; lia).
    lstep. (* [comment removed for export] *)
    eapply evt_cut; [eapply (ims240 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ NB); [exact FRnb| assumption| unfold NB; lia| unfold NB; lia]|].
    cbv beta. intros ms1 nelH_; (nelim nelH_ 10%nat; intros a1' a2' a3' m1 j240 -> MU1 WM1 MI1 FRnb1).
    replace (ret_pc (Z_to_bv 64 0x68fdc)) with (Z_to_bv 64 0x68fdc : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply K.
    - eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU1]. unfold NB, sub_fp. cbn. intros; lia.
    - exact (wmono_trans bsegs _ _ _ WM WM1).
    - exact MI1.
    - eapply stk_transport_disjoint; [exact ST| exact MU1| exact WM1| unfold NB; cbn; lia].
    - unfold an_hi. eapply rw_cells_transport; [exact FRhi| exact MU1| exact WM1| unfold NB; cbn; lia].
    - eapply rw_cells_transport; [exact FR8| exact MU1| exact WM1| unfold NB; cbn; lia].
    - exact FRnb1.
  Qed.

  (* [comment removed for export] *)
  Lemma an_B : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m1 : word -> option byte) (j240 : list byte) (POST : machine_state -> Prop),
    mem_inv bsegs m1 -> rw_cells bsegs m1 NB [CB 240 j240] ->
    (forall (m2 : word -> option byte) (y14 : word) (j144 : list byte),
       munch [(NB, NB + 96)] m1 m2 -> wmono bsegs m1 m2 -> mem_inv bsegs m2 ->
       rw_cells bsegs m2 NB [C8 (wz (hd v 0)); C8 (wz (hd v 1)); C8 (wz (hd v 2)); C8 (wz (hd v 3)); C8 (wz (hd v 4)); C8 (wz (hd v 5));
                            C8 (wz (hd v 6)); C8 (wz (hd v 7)); C8 (wz (hd v 8)); C8 (wz (hd v 9)); C8 (wz (hd v 10)); C8 (wz (hd v 11)); CB 144 j144] ->
       evt bsegs POST
         (MS (mkR (wz 0x68fdc) (Z_to_bv 64 (bv_unsigned sp + -336)) gp tp x5 x6 x7 (wz bend) (wz BP) (wz (-12)) (wz 18) (wz 0) (wz (hq v 11)) y14 x15 x16 x17
                  (wz 0) (wz 1) (wz 16) (wz 0) (wz (NB + 96)) (wz 0) (wz 1) (wz 12) s10 s11 x28 x29 x30 x31)
             F (wz 0x69018) fc None m2 (seg_rom bsegs))) ->
    evt bsegs POST
      (MS (mkR (wz 0x68fdc) (Z_to_bv 64 (bv_unsigned sp + -336)) gp tp x5 x6 x7 (wz bend) (wz BP) (wz NB) x11 x12 x13 x14 x15 x16 x17
               (wz 0) (wz 1) (wz 16) (wz v) (wz NB) (wz 0) (wz 1) (wz 12) s10 s11 x28 x29 x30 x31)
          F (wz 0x68fdc) fc None m1 (seg_rom bsegs)).
  Proof.
    intros until POST. intros MI1 FRnb K.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof CEIL as CEIL'. idtac.
    pose proof (munch_refl [(NB, NB + 96)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
    assert (ENB : NB = bv_unsigned sp + -328) by reflexivity. clearbody NB.
    cbv beta delta [wz] in *.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [8;8;8;8;8;8;8;8;8;8;8;8;144]%nat) in FRnb; [| reflexivity]. cbn [mk_CB_cells app] in FRnb.
    gi. gi. gi. gi. fl. (* [comment removed for export] *)
    replace (Z_to_bv 64 v) with (Z_to_bv 64 (hq v 0) : word) by (unfold hq; rewrite Z.pow_0_r, Z.div_1_r; reflexivity).
    (* [comment removed for export] *)
    Ltac dl i :=
      let Q1 := fresh "Q1" in let Q2 := fresh "Q2" in let Q3 := fresh "Q3" in let Q4 := fresh "Q4" in let Q5 := fresh "Q5" in let Q6 := fresh "Q6" in let Q7 := fresh "Q7" in
      let QB := fresh "QB" in let QB1 := fresh "QB1" in
      (nelimp (hq_facts v i ltac:(lia) HV) 7%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7);
      let i1 := eval vm_compute in (i + 1)%Z in
      change (i + 1)%Z with i1 in Q1, Q2;
      let e := eval vm_compute in (16 ^ (12 - i))%Z in
      change (16 ^ (12 - i))%Z with e in Q6;
      assert (QB : 0 <= hq v i < 2^48) by lia;
      assert (QB1 : 0 <= hq v i1 < 2^48) by (rewrite Q1; Z.div_mod_to_equations; lia);
      gi; gi; lstep; rewrite an_divu_lit by lia; rewrite <- Q1; gi; fl; gi; gi; gi;
      replace (hq v i - hq v i1 * 16) with (hd v i) by lia;
      lstep; gi; gi; fl; gi;
      clear Q1 Q2 Q4 Q5 Q6 Q7 QB QB1.
    dl 0. dl 1. dl 2. dl 3. dl 4. dl 5. dl 6. dl 7. dl 8. dl 9. dl 10. dl 11.
    replace (hq v 12) with 0 by (unfold hq; symmetry; apply Z.div_small; change (16 ^ 12) with (2^48); lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch type of FRnb with rw_cells _ _ _ [_;_;_;_;_;_;_;_;_;_;_;_; CB 144 ?j] => eapply (K mm _ j) end end;
      [exact MU| exact WM| assumption| exact FRnb].
  Qed.

End AN.


End CeilWrap.
End RTW_sec_snp1.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_kit.
Module RTW_sec_snp2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcleaf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcdefs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_scommon_lg RTW_sec_snp1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma digit_view : forall m A (w : word), rw_cells bsegs m A [C8 w] -> rw_cells bsegs m A [CB 4 (firstn 4 (le8 w)); CB 4 (skipn 4 (le8 w))].
Proof.
  intros m A w H. eapply rw_cells_recast; [exact H| |].
  - cbn [cells_wf cell_wf]. split; [rewrite length_firstn, length_le8; reflexivity|]. split; [rewrite length_skipn, length_le8; reflexivity| exact I].
  - cbn [cells_bytes cbytes app]. rewrite app_nil_r. apply firstn_skipn.
Qed.
Lemma C1_view : forall m A (bs : list byte), rw_cells bsegs m A [CB 1 bs] -> exists b, rw_cells bsegs m A [C1 b].
Proof.
  intros m A bs H. pose proof H as H'. destruct H' as [[W _] _]. cbn in W. destruct W as [L _].
  destruct bs as [|b [|]]; cbn in L; try lia. exists b. eapply rw_cells_recast; [exact H| cbn; tauto| reflexivity].
Qed.

Section AN2.
  Variables (sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (BP bcur bend v lo : Z).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + 336 <= bv_unsigned sp.
  Hypothesis HV : 2^44 <= v < 2^48.
  Hypothesis HBP : bv_unsigned sp <= BP /\ BP + 8 <= bcur.
  Hypothesis HB : bcur + 12 <= bend /\ bend + 1 < 2^64.
  Let NB : Z := bv_unsigned sp + -328.

  Ltac gi := lstep; lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => if_lia | _ => idtac end.

  (* [comment removed for export] *)
  Lemma an_C : forall (x5 x6 x7 y14 x15 x16 x17 x28 x29 x30 x31 : word) (m2 : word -> option byte) (j144 : list byte) (POST : machine_state -> Prop),
    mem_inv bsegs m2 ->
    rw_cells bsegs m2 NB [C8 (wz (hd v 0)); C8 (wz (hd v 1)); C8 (wz (hd v 2)); C8 (wz (hd v 3)); C8 (wz (hd v 4)); C8 (wz (hd v 5));
                         C8 (wz (hd v 6)); C8 (wz (hd v 7)); C8 (wz (hd v 8)); C8 (wz (hd v 9)); C8 (wz (hd v 10)); C8 (wz (hd v 11)); CB 144 j144] ->
    rw_cells bsegs m2 BP [C8 (wz bcur)] ->
    evt bsegs POST
      (MS (mkR (wz 0x68fdc) (Z_to_bv 64 (bv_unsigned sp + -336)) gp tp x5 x6 x7 (wz bend) (wz BP) (wz 11) (wz 12) (wz 87) (wz bcur) (wz (NB + 88)) (wz 10) x16 x17
               (wz 0) (wz 1) (wz 12) (wz 0) (wz (NB + 96)) (wz 0) (wz 1) (wz 12) s10 s11 x28 x29 x30 x31)
          F (wz 0x6917c) fc None m2 (seg_rom bsegs)) ->
    evt bsegs POST
      (MS (mkR (wz 0x68fdc) (Z_to_bv 64 (bv_unsigned sp + -336)) gp tp x5 x6 x7 (wz bend) (wz BP) (wz (-12)) (wz 18) (wz 0) (wz (hq v 11)) y14 x15 x16 x17
               (wz 0) (wz 1) (wz 16) (wz 0) (wz (NB + 96)) (wz 0) (wz 1) (wz 12) s10 s11 x28 x29 x30 x31)
          F (wz 0x69018) fc None m2 (seg_rom bsegs)).
  Proof.
    intros until POST. intros MI2 FRnb HPC K.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof CEIL as CEIL'. idtac.
    pose proof (hq_facts v 11 ltac:(lia) HV) as (_ & Q2 & Q3 & _ & _ & _ & Q7). specialize (Q7 eq_refl).
    assert (D11 : hd v 11 = hq v 11) by (unfold hd, hq in *; rewrite Z.mod_small; lia).
    assert (ENB : NB = bv_unsigned sp + -328) by reflexivity. clearbody NB.
    cbv beta delta [wz] in *.
    gi. fl.
    gi. gi. fl. gi. gi. gi. fl. gi. replace (bv_unsigned sp + -328) with NB by lia. gi.   (* [comment removed for export] *)
    gi. gi. replace (NB + Z.shiftl 11 3) with (NB + 88) by reflexivity. gi. gi.          (* [comment removed for export] *)
    gi. gi. gi. gi.                                                                       (* [comment removed for export] *)
    gi. gi. gi. gi. gi.                                                                   (* [comment removed for export] *)
    gi. gi. fl. gi. replace (bv_unsigned sp + -328) with NB by lia. gi. fl. gi. fl. gi. fl. gi. gi. gi. (* [comment removed for export] *)
    replace (bv_unsigned sp + -240) with (NB + 88) by lia. exact K.
  Qed.

  (* [comment removed for export] *)
  Lemma lb_iter : forall (j : Z) (x5 x6 x7 x16 x17 x28 x29 x30 x31 : word) (mj : word -> option byte) (dlo dhi : list byte) (ob : byte) (POST : machine_state -> Prop),
    0 <= j <= 11 -> mem_inv bsegs mj ->
    rw_cells bsegs mj (NB + 88 - 8 * j) [CB 4 dlo; CB 4 dhi] ->
    rw_cells bsegs mj (bcur + j) [C1 ob] ->
    rw_cells bsegs mj BP [C8 (wz (bcur + j))] ->
    (forall (mj' : word -> option byte) (ob' : byte) (y16 y17 : word),
       munch [(bcur + j, bcur + j + 1); (BP, BP + 8)] mj mj' -> wmono bsegs mj mj' -> mem_inv bsegs mj' ->
       rw_cells bsegs mj' (bcur + j) [C1 ob'] -> rw_cells bsegs mj' BP [C8 (wz (bcur + j + 1))] ->
       rw_cells bsegs mj' (NB + 88 - 8 * j) [CB 4 dlo; CB 4 dhi] ->
       evt bsegs POST
         (MS (mkR (wz 0x68fdc) (Z_to_bv 64 (bv_unsigned sp + -336)) gp tp x5 x6 x7 (wz bend) (wz BP) (wz 11) (wz (12 - (j + 1))) (wz 87) (wz (bcur + j + 1)) (wz (NB + 88 - 8 * (j + 1))) (wz 10) y16 y17
                  (wz 0) (wz 1) (wz 12) (wz 0) (wz (NB + 96)) (wz 0) (wz 1) (wz 12) s10 s11 x28 x29 x30 x31)
             F (wz 0x69178) fc None mj' (seg_rom bsegs))) ->
    evt bsegs POST
      (MS (mkR (wz 0x68fdc) (Z_to_bv 64 (bv_unsigned sp + -336)) gp tp x5 x6 x7 (wz bend) (wz BP) (wz 11) (wz (12 - j)) (wz 87) (wz (bcur + j)) (wz (NB + 88 - 8 * j)) (wz 10) x16 x17
               (wz 0) (wz 1) (wz 12) (wz 0) (wz (NB + 96)) (wz 0) (wz 1) (wz 12) s10 s11 x28 x29 x30 x31)
          F (wz 0x6917c) fc None mj (seg_rom bsegs)).
  Proof.
    intros until POST. intros Hj MIj DIG OUT HPC K.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof CEIL as CEIL'. idtac.
    pose proof (munch_refl [(bcur + j, bcur + j + 1); (BP, BP + 8)] mj) as MU. pose proof (wmono_refl bsegs mj) as WM.
    assert (ENB : NB = bv_unsigned sp + -328) by reflexivity. clearbody NB.
    cbv beta delta [wz] in *.
    set (oj := bcur + j) in *.
    gi. (* [comment removed for export] *)
    lstep. gi. (* [comment removed for export] *)
    set (dw := sext 64 (bv_extract 0 32 (le_bytes_to_word dlo))). clearbody dw.
    (* [comment removed for export] *)
    lstep. if_cases Kc.
    - gi. set (cv := (Z_to_bv 64 (87 + bv_unsigned dw) : word)). clearbody cv.
      lstep. change (le1 cv) with [Z_to_bv 8 (bv_unsigned cv)]. mem_after_store_opt.
      gi. gi. lstep. gi. gi.
      replace (NB + 88 - 8 * j + -8) with (NB + 88 - 8 * (j + 1)) by lia. replace (12 - j + -1) with (12 - (j + 1)) by lia.
      eapply K; [exact MU| exact WM| assumption| eassumption| eassumption| eassumption].
    - gi. set (cv := (Z_to_bv 64 (Z.lor (bv_unsigned dw) 48) : word)). clearbody cv. gi.
      lstep. change (le1 cv) with [Z_to_bv 8 (bv_unsigned cv)]. mem_after_store_opt.
      gi. gi. lstep. gi. gi.
      replace (NB + 88 - 8 * j + -8) with (NB + 88 - 8 * (j + 1)) by lia. replace (12 - j + -1) with (12 - (j + 1)) by lia.
      eapply K; [exact MU| exact WM| assumption| eassumption| eassumption| eassumption].
  Qed.

  (* [comment removed for export] *)
  Lemma an_D : forall (ra s0 s1 x5 x6 x7 x16 x17 x28 x29 x30 x31 : word) (m2 : word -> option byte) (j144 : list byte) (obs : list byte) (POST : machine_state -> Prop),
    mem_inv bsegs m2 -> length obs = 12%nat ->
    rw_cells bsegs m2 NB [C8 (wz (hd v 0)); C8 (wz (hd v 1)); C8 (wz (hd v 2)); C8 (wz (hd v 3)); C8 (wz (hd v 4)); C8 (wz (hd v 5));
                         C8 (wz (hd v 6)); C8 (wz (hd v 7)); C8 (wz (hd v 8)); C8 (wz (hd v 9)); C8 (wz (hd v 10)); C8 (wz (hd v 11)); CB 144 j144] ->
    rw_cells bsegs m2 BP [C8 (wz bcur)] -> rw_cells bsegs m2 bcur [CB 12 obs] ->
    an_hi sp s2 s3 s4 s5 s6 s7 s8 s9 ra s0 s1 m2 -> stk bsegs m2 lo (bv_unsigned sp + -336) ->
    (exists j8, rw_cells bsegs m2 (bv_unsigned sp + -336) [CB 8 j8]) ->
    (forall (m3 : word -> option byte) (obs' : list byte) (z11 z12 z13 z14 z15 z16 z17 : word),
       munch [(bcur, bcur + 12); (BP, BP + 8)] m2 m3 -> wmono bsegs m2 m3 -> mem_inv bsegs m3 ->
       rw_cells bsegs m3 BP [C8 (wz (bcur + 12))] -> rw_cells bsegs m3 bcur [CB 12 obs'] -> stk bsegs m3 lo (bv_unsigned sp) ->
       evt bsegs POST
         (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (wz 12) z11 z12 z13 z14 z15 z16 z17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (ret_pc ra) fc None m3 (seg_rom bsegs))) ->
    evt bsegs POST
      (MS (mkR (wz 0x68fdc) (Z_to_bv 64 (bv_unsigned sp + -336)) gp tp x5 x6 x7 (wz bend) (wz BP) (wz 11) (wz 12) (wz 87) (wz bcur) (wz (NB + 88)) (wz 10) x16 x17
               (wz 0) (wz 1) (wz 12) (wz 0) (wz (NB + 96)) (wz 0) (wz 1) (wz 12) s10 s11 x28 x29 x30 x31)
          F (wz 0x6917c) fc None m2 (seg_rom bsegs)).
  Proof.
    intros until POST. intros MI2 LOBS FRnb HPC OUT FRhi ST2 [j8 FR8] K.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof CEIL as CEIL'. idtac.
    pose proof (munch_refl [(bcur, bcur + 12); (BP, BP + 8)] m2) as MU. pose proof (wmono_refl bsegs m2) as WM.
    assert (ENB : NB = bv_unsigned sp + -328) by reflexivity. clearbody NB.
    unfold an_hi in FRhi. cbv beta delta [wz] in *.
    (* [comment removed for export] *)
    Ltac dview k Dk FRnb :=
      lazymatch type of FRnb with rw_cells _ ?mm ?A ?cs =>
        let pre := eval cbn [firstn] in (firstn k cs) in let c := eval cbn [nth] in (nth k cs (CB 0 [])) in let post := eval cbn [skipn] in (skipn (S k) cs) in
        pose proof (digit_view mm _ _ (rw_cells_mid mm A pre [c] post FRnb)) as Dk; cbn [cells_size Cells.csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Dk
      end.
    dview 0%nat D0 FRnb. dview 1%nat D1 FRnb. dview 2%nat D2 FRnb. dview 3%nat D3 FRnb. dview 4%nat D4 FRnb. dview 5%nat D5 FRnb.
    dview 6%nat D6 FRnb. dview 7%nat D7 FRnb. dview 8%nat D8 FRnb. dview 9%nat D9 FRnb. dview 10%nat D10 FRnb. dview 11%nat D11 FRnb.
    rewrite Z.add_0_r in D0.
    change (Z.of_nat 8) with 8 in D1. change (Z.of_nat 16) with 16 in D2. change (Z.of_nat 24) with 24 in D3. change (Z.of_nat 32) with 32 in D4.
    change (Z.of_nat 40) with 40 in D5. change (Z.of_nat 48) with 48 in D6. change (Z.of_nat 56) with 56 in D7. change (Z.of_nat 64) with 64 in D8.
    change (Z.of_nat 72) with 72 in D9. change (Z.of_nat 80) with 80 in D10. change (Z.of_nat 88) with 88 in D11.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [1;1;1;1;1;1;1;1;1;1;1;1]%nat) in OUT; [| cbn; lia]. cbn [mk_CB_cells app] in OUT.
    pose proof (rw_cells_take m2 bcur [] _ OUT) as DONE.
    replace bcur with (bcur + 0) in OUT at 1 by lia.
    (* [comment removed for export] *)
    Ltac lb1 j Dp :=
      lazymatch type of Dp with rw_cells _ ?m2 _ _ =>
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mj _) =>
      lazymatch goal with MU : munch _ m2 mj, WM : wmono _ m2 mj, OUT : rw_cells _ mj (bcur + _) _, HPC : rw_cells _ mj BP _ |- _ =>
        let DG := fresh "DG" in let O1 := fresh "O1" in let OUT' := fresh "OUT" in let ob := fresh "ob" in let O1c := fresh "O1c" in
        pose proof Dp as DG; eapply (rw_cells_transport bsegs _ m2 mj) in DG; [| exact MU| exact WM| cbn; lia];
        lazymatch type of DG with rw_cells _ _ ?a _ => replace a with (NB + 88 - 8 * j) in DG by lia end;
        lazymatch type of OUT with rw_cells _ _ ?a (?c :: ?rest) =>
          pose proof (proj1 (RT_kit.rw_cells_app mj a [c] rest) OUT) as [O1 OUT']; clear OUT; cbn [cells_size Cells.csize Nat.add] in OUT';
          change (Z.of_nat 1) with 1 in OUT'; lazymatch type of OUT' with rw_cells _ _ ?a' _ => replace a' with (bcur + (j + 1)) in OUT' by lia end; rename OUT' into OUT
        end;
        destruct (C1_view _ _ _ O1) as [ob O1c]; clear O1;
        (* [comment removed for export] *)
        tryif constr_eq j 0%Z then
              (replace (Z_to_bv 64 bcur : word) with (Z_to_bv 64 (bcur + 0) : word) by (f_equal; lia);
               replace (Z_to_bv 64 bcur : word) with (Z_to_bv 64 (bcur + 0) : word) in HPC by (f_equal; lia);
               replace (Z_to_bv 64 (NB + 88) : word) with (Z_to_bv 64 (NB + 88 - 8 * 0) : word) by (f_equal; lia))
        else (let jp := eval vm_compute in (j - 1)%Z in
               replace (bcur + jp + 1) with (bcur + j) by lia; replace (bcur + jp + 1) with (bcur + j) in HPC by lia);
        eapply (lb_iter j); [lia| assumption| exact DG| exact O1c| exact HPC|];
        clear DG O1c HPC
      end end end.
    Ltac lb2 j :=
      lazymatch goal with MU : munch _ ?m2 ?mj, WM : wmono _ _ _, OUT : rw_cells _ _ (bcur + _) _, DONE : rw_cells _ _ bcur _ |- _ =>
        let mj' := fresh "mj" in let ob' := fresh "ob" in let MU' := fresh "MUi" in let WM' := fresh "WMi" in let O1' := fresh "O1n" in
        let MI' := fresh "MIn" in let DONE2 := fresh "DONE" in let MU2 := fresh "MU" in let WM2 := fresh "WM" in let SFP := fresh "SFP" in
        intros mj' ob' ? ? MU' WM' MI' O1' HPC _; cbv beta delta [wz];
        eapply (rw_cells_transport bsegs _ mj mj') in OUT; [| exact MU'| exact WM'| cbn; lia];
        eapply (rw_cells_transport bsegs _ mj mj') in DONE; [| exact MU'| exact WM'| cbn; lia];
        pose proof (proj2 (RT_kit.rw_cells_app mj' bcur _ _) (conj DONE ltac:(cbn [cells_size Cells.csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?Z.add_0_r; exact O1'))) as DONE2;
        clear DONE O1'; cbn [app] in DONE2; rename DONE2 into DONE;
        assert (SFP : sub_fp [(bcur + j, bcur + j + 1); (BP, BP + 8)] [(bcur, bcur + 12); (BP, BP + 8)]) by (unfold sub_fp; cbn; intros; lia);
        pose proof (munch_trans _ _ _ _ MU (munch_weaken _ _ mj mj' SFP MU')) as MU2; clear MU MU' SFP; rename MU2 into MU;
        pose proof (wmono_trans bsegs _ _ _ WM WM') as WM2; clear WM WM'; rename WM2 into WM;
        try match goal with H : mem_inv _ mj |- _ => clear H end
      end.
    Ltac lb j Dp := lb1 j Dp; lb2 j; lstep; if_lit.   (* [comment removed for export] *)
    lb 0%Z D11. lb 1%Z D10. lb 2%Z D9. lb 3%Z D8. lb 4%Z D7. lb 5%Z D6. lb 6%Z D5. lb 7%Z D4. lb 8%Z D3. lb 9%Z D2. lb 10%Z D1. lb 11%Z D0.
    (* [comment removed for export] *)
    gi. fl.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mj _) =>
      eapply (rw_cells_transport bsegs _ m2 mj) in FRhi; [| exact MU| exact WM| cbn; lia];
      eapply (rw_cells_transport bsegs _ m2 mj) in FRnb; [| exact MU| exact WM| cbn; lia];
      eapply (rw_cells_transport bsegs _ m2 mj) in FR8; [| exact MU| exact WM| cbn; lia];
      eapply (stk_transport_disjoint bsegs _ m2 mj) in ST2; [| exact MU| exact WM| cbn; lia]
    end.
    do 11 gi. gi. (* [comment removed for export] *)
    (* [comment removed for export] *)
    rewrite ENB in FRnb. replace (bv_unsigned sp + -328) with (bv_unsigned sp + -336 + 8) in FRnb by lia.
    replace (bv_unsigned sp + -88) with (bv_unsigned sp + -336 + 248) in FRhi by lia.
    glue FR8 FRnb. glue FR8 FRhi. rename FR8 into FR.
    release_frame FR ST2 (bv_unsigned sp).
    gi. (* [comment removed for export] *)
    replace (bcur + 11 + 1) with (bcur + 12) in HPC by lia.
    lazymatch type of DONE with rw_cells _ ?mm _ [C1 ?b0; C1 ?b1; C1 ?b2; C1 ?b3; C1 ?b4; C1 ?b5; C1 ?b6; C1 ?b7; C1 ?b8; C1 ?b9; C1 ?b10; C1 ?b11] =>
      apply (rw_cells_recast bsegs mm bcur _ [CB 12 [b0; b1; b2; b3; b4; b5; b6; b7; b8; b9; b10; b11]]) in DONE; [| cbn; split; [reflexivity| exact I]| reflexivity]
    end.
    eapply K; [exact MU| exact WM| assumption| exact HPC| exact DONE| exact ST2].
  Qed.

  (* [comment removed for export] *)
  Definition appnum_post (ra s0 s1 : word) (obs' : list byte) : machine_state -> Prop :=
    fun ms' => exists (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m' : word -> option byte) (obs' : list byte),
      ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (wz 12) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - 336, bv_unsigned sp); (bcur, bcur + 12); (BP, BP + 8)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp) /\ rw_cells bsegs m' BP [C8 (wz (bcur + 12))] /\ rw_cells bsegs m' bcur [CB 12 obs'].

  Lemma appnum_ok : forall (ra t0 t1 t2 s0 s1 t3 t4 t5 t6 : word) (obs : list byte),
    length obs = 12%nat -> rw_cells bsegs m BP [C8 (wz bcur)] -> rw_cells bsegs m bcur [CB 12 obs] ->
    evt bsegs (appnum_post ra s0 s1 obs)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz BP) (wz bend) (wz v) (wz 16) (wz 12) (wz 1) (wz 0) (wz 0) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz A_APPNUM) fc None m (seg_rom bsegs)).
  Proof.
    intros until obs. intros LOBS HPC OUT.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof CEIL as CEIL'. idtac.
    eapply (an_A sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m BP bend v lo MI ST CEIL LO HV).
    intros x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1 j8 j240 MU01 WM01 MI1 ST1 FRhi1 FR81 FRnb1.
    eapply (an_B sp gp tp s10 s11 F fc BP bend v lo CEIL HV); [exact MI1| exact FRnb1|].
    intros m2 y14 j144 MU12 WM12 MI2 FRnb2.
    assert (MU02 : munch [(bv_unsigned sp - 336, bv_unsigned sp)] m m2).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU01]; unfold sub_fp; cbn; intros; lia|]. eapply munch_weaken; [| exact MU12]; unfold sub_fp; cbn; intros; lia. }
    pose proof (wmono_trans bsegs _ _ _ WM01 WM12) as WM02.
    pose proof HPC as HPC2. eapply (rw_cells_transport bsegs _ m m2) in HPC2; [| exact MU02| exact WM02| cbn; lia].
    pose proof OUT as OUT2. eapply (rw_cells_transport bsegs _ m m2) in OUT2; [| exact MU02| exact WM02| cbn; lia].
    eapply an_C; [exact MI2| exact FRnb2| exact HPC2|].
    eapply an_D; [exact MI2| exact LOBS| exact FRnb2| exact HPC2| exact OUT2
      | unfold an_hi; eapply rw_cells_transport; [exact FRhi1| exact MU12| exact WM12| cbn; lia]
      | eapply stk_transport_disjoint; [exact ST1| exact MU12| exact WM12| cbn; lia]
      | exists j8; eapply rw_cells_transport; [exact FR81| exact MU12| exact WM12| cbn; lia]|].
    intros m3 obs' z11 z12 z13 z14 z15 z16 z17 MU23 WM23 MI3 HPC3 OUT3 ST3.
    apply evt_done. unfold appnum_post. do 14 eexists. exists m3, obs'. split; [reflexivity|].
    split. { eapply munch_trans; [eapply munch_weaken; [| exact MU02]; unfold sub_fp; cbn; intros; lia|]. eapply munch_weaken; [| exact MU23]; unfold sub_fp; cbn; intros; lia. }
    split; [exact (wmono_trans bsegs _ _ _ WM02 WM23)|]. split; [exact MI3|]. split; [exact ST3|]. split; [exact HPC3| exact OUT3].
  Qed.
End AN2.


End CeilWrap.
End RTW_sec_snp2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Arr Bytes Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_pop_arg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs CJ_iface RT_kit AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import ICPT_pcleaf ICPT_pcdefs ICPT_scommon_lg.
Import RTW_sec_snp1.
Import RTW_sec_snp2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require JunkAbs.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.JunkAbs.split_for_access_raw H segs m A cs kn n.
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition A_VSNPRINTF : Z := 0x68614.
Definition FMTA : Z := 0x1cdb6.   (* [comment removed for export] *)

Lemma fmt_cells : forall m, mem_inv bsegs m ->
  ro_cells bsegs m FMTA [CB 21 (zbs [109; 101; 109; 111; 114; 121; 32; 97; 116; 32; 97; 100; 100; 114; 101; 115; 115; 32; 37; 112; 0])].
Proof.
  intros m MI. apply (ro_cells_image bsegs m FMTA (zbs [109; 101; 109; 111; 114; 121; 32; 97; 116; 32; 97; 100; 100; 114; 101; 115; 115; 32; 37; 112; 0]) MI);
    [vm_compute; reflexivity| unfold FMTA; lia| cbn; unfold FMTA; lia].
Qed.

Lemma jt_cells : forall m, mem_inv bsegs m -> ro_cells bsegs m 0x20be4 [CB 4 (zbs [224; 125; 4; 0])].
Proof. intros m MI. apply (ro_cells_image bsegs m 0x20be4 (zbs [224; 125; 4; 0]) MI); [vm_compute; reflexivity| lia| cbn; lia]. Qed.

Lemma cb_len : forall m A n (bs : list byte) rest, rw_cells bsegs m A (CB n bs :: rest) -> length bs = n.
Proof. intros m A n bs rest [[W _] _]. cbn in W. exact (proj1 W). Qed.

Section VSN.
  Variables (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (B VA v lo : Z).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + 464 <= bv_unsigned sp.
  Hypothesis HV : 2^44 <= v < 2^48.
  Hypothesis HBUF : bv_unsigned sp <= B /\ B + 40 < 2^64.
  Hypothesis HVA : bv_unsigned sp <= VA /\ VA + 8 < 2^64 /\ (VA + 8 <= B \/ B + 40 <= VA).

  Ltac gi := lstep; lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => if_lia | _ => idtac end.

  (* [comment removed for export] *)
  Definition vsn_frame (ra : word) (cur : Z) (m1 : word -> option byte) : Prop :=
    rw_cells bsegs m1 (bv_unsigned sp + -128) [C8 (wz FMTA); C8 (wz (B + 40)); C8 (wz cur); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Lemma vsn_A : forall (ra t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) junk (POST : machine_state -> Prop),
    rw_cells bsegs m B [CB 40 junk] ->
    (forall m1, munch [(bv_unsigned sp + -128, bv_unsigned sp)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 -> stk bsegs m1 lo (bv_unsigned sp + -128) ->
       vsn_frame ra B m1 -> rw_cells bsegs m1 B [CB 40 junk] ->
       evt bsegs POST
         (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (wz 32) (wz 0) (wz (B + 40)) (wz 40) (wz FMTA) (wz VA) a4 a5 a6 a7
                  (wz VA) (wz (B + 39)) (wz 115) (wz 37) (wz 45) (wz 9) (wz 10) (wz 46) (wz FMTA) (wz 108) t3 t4 t5 t6)
             F (wz 0x686a4) fc None m1 (seg_rom bsegs))) ->
    evt bsegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz B) (wz 40) (wz FMTA) (wz VA) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz A_VSNPRINTF) fc None m (seg_rom bsegs)).
  Proof.
    intros until POST. intros OUTB K.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof CEIL as CEIL'. idtac.
    pose proof (munch_refl [(bv_unsigned sp + -128, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    unfold A_VSNPRINTF, FMTA in *. cbv beta delta [wz] in *.
    carve_frame 128%nat ST.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 15 gi. (* [comment removed for export] *)
    gi. lstep. if_lit. (* [comment removed for export] *)
    do 16 (gi; try fl). (* [comment removed for export] *)
    eapply K; [exact MU| exact WM| assumption| exact ST| exact FR| exact OUTB].
  Qed.

  (* [comment removed for export] *)
  Lemma vsn_L : forall (ra t0 t1 t2 x10 x11 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m1 : word -> option byte) junk (POST : machine_state -> Prop),
    mem_inv bsegs m1 -> vsn_frame ra B m1 -> rw_cells bsegs m1 B [CB 40 junk] ->
    (forall (m2 : word -> option byte) (y10 y11 : word) junk', munch [(bv_unsigned sp + -112, bv_unsigned sp + -104); (B, B + 18)] m1 m2 -> wmono bsegs m1 m2 -> mem_inv bsegs m2 ->
       vsn_frame ra (B + 18) m2 -> rw_cells bsegs m2 B [CB 40 junk'] ->
       evt bsegs POST
         (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (wz 32) (wz 18) y10 y11 (wz FMTA) (wz VA) a4 a5 a6 a7
                  (wz VA) (wz (B + 39)) (wz 115) (wz 37) (wz 45) (wz 9) (wz 10) (wz 46) (wz (FMTA + 18)) (wz 108) t3 t4 t5 t6)
             F (wz 0x686a4) fc None m2 (seg_rom bsegs))) ->
    evt bsegs POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (wz 32) (wz 0) x10 x11 (wz FMTA) (wz VA) a4 a5 a6 a7
               (wz VA) (wz (B + 39)) (wz 115) (wz 37) (wz 45) (wz 9) (wz 10) (wz 46) (wz FMTA) (wz 108) t3 t4 t5 t6)
          F (wz 0x686a4) fc None m1 (seg_rom bsegs)).
  Proof.
    intros until POST. intros MI1 FR OUTB K.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof CEIL as CEIL'. idtac.
    pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp + -104); (B, B + 18)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
    pose proof (fmt_cells m1 MI1) as FMTC.
    unfold vsn_frame, FMTA in *. cbv beta delta [wz] in *.
    Ltac lit := lstep; fold_ldb; lstep; if_lit; lstep; if_lit; gi; gi; lstep; gi; gi; gi; gi; fl; gi.
    do 18 lit.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch type of OUTB with rw_cells _ _ _ ?cs =>
        pose proof (rw_cells_merge bsegs mm B [] cs []) as MG; cbn [app] in MG; rewrite ?app_nil_r in MG; specialize (MG OUTB); rewrite ?app_nil_r in MG
      end end.
    match type of MG with rw_cells _ _ _ [CB ?sz ?bs] => replace sz with 40%nat in MG by (cbn; lia) end.
    eapply K; [exact MU| exact WM| assumption| exact FR| exact MG].
  Qed.

  (* [comment removed for export] *)
  Definition vsn_post (ra : word) : machine_state -> Prop :=
    fun ms' => exists (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m' : word -> option byte) (junk' : list byte),
      ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - 464, bv_unsigned sp); (B, B + 40)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp) /\ rw_cells bsegs m' B [CB 40 junk'].

  Lemma vsn_PZ : forall (ra t0 t1 t2 y10 y11 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m2 : word -> option byte) junk,
    munch [(bv_unsigned sp + -128, bv_unsigned sp); (B, B + 40)] m m2 -> wmono bsegs m m2 -> mem_inv bsegs m2 ->
    stk bsegs m2 lo (bv_unsigned sp + -128) -> vsn_frame ra (B + 18) m2 -> rw_cells bsegs m2 B [CB 40 junk] -> rw_cells bsegs m2 VA [C8 (wz v)] ->
    evt bsegs (vsn_post ra)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (wz 32) (wz 18) y10 y11 (wz FMTA) (wz VA) a4 a5 a6 a7
               (wz VA) (wz (B + 39)) (wz 115) (wz 37) (wz 45) (wz 9) (wz 10) (wz 46) (wz (FMTA + 18)) (wz 108) t3 t4 t5 t6)
          F (wz 0x686a4) fc None m2 (seg_rom bsegs)).
  Proof.
    intros until junk. intros MU WM MI2 ST2 FR OUTB VAC.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof CEIL as CEIL'. idtac.
    pose proof (fmt_cells m2 MI2) as FMTC. pose proof (jt_cells m2 MI2) as JT.
    unfold vsn_frame, FMTA in *. cbv beta delta [wz] in *.
    lstep. fold_ldb. lstep. if_lit. (* [comment removed for export] *)
    lstep. fold_ldb. lstep. if_lit. (* [comment removed for export] *)
    gi. gi. fl. gi. fl. gi. fl. (* [comment removed for export] *)
    lstep. fold_ldb. (* [comment removed for export] *)
    gi. gi. fl. lstep. if_lit. (* [comment removed for export] *)
    gi. fl. lstep. if_lit. (* [comment removed for export] *)
    lstep. fold_ldb. gi. fl. gi. fl. gi. fl. lstep. fold_ldb. lstep. if_lit. (* [comment removed for export] *)
    gi. gi. gi. fl. lstep. fold_ldb. gi. fl. gi. fl. lstep. if_lit. lstep. if_lit. (* [comment removed for export] *)
    gi. fl. gi. fl. gi. fl. lstep. if_lit. (* [comment removed for export] *)
    gi. fl. gi. fl. gi. fl. (* [comment removed for export] *)
    gi. fl. lstep. (* [comment removed for export] *)
    replace (sext 64 (bv_extract 0 32 (le_bytes_to_word (zbs [224; 125; 4; 0])))) with (Z_to_bv 64 294368 : word) by (apply bv_eq; vm_compute; reflexivity).
    gi. fl. lstep. (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 428388)) with (Z_to_bv 64 428388 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    lstep. if_lit. gi. gi. gi. lstep. gi. gi. gi. gi. lstep. gi. gi. gi. (* [comment removed for export] *)
    do 8 gi. fl. (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch type of OUTB with rw_cells _ _ _ ?cs =>
        pose proof (rw_cells_merge bsegs mm B [] cs []) as MG; cbn [app] in MG; rewrite ?app_nil_r in MG; specialize (MG OUTB); rewrite ?app_nil_r in MG; clear OUTB
      end end.
    match type of MG with rw_cells _ _ _ [CB ?sz ?bs] => replace sz with 40%nat in MG by (cbn; lia) end.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [20; 12; 8]%nat) in MG; [| reflexivity]. cbn [mk_CB_cells app] in MG.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch type of MG with rw_cells _ _ _ [?c0; ?c1; ?c2] =>
        pose proof (proj1 (RT_kit.rw_cells_app mm B [c0] [c1; c2]) MG) as [OB0 OB12]; cbn [cells_size Cells.csize Nat.add] in OB12;
        pose proof (proj1 (RT_kit.rw_cells_app mm _ [c1] [c2]) OB12) as [OB1 OB2]; cbn [cells_size Cells.csize Nat.add] in OB2; clear MG OB12
      end;
      lazymatch type of FR with rw_cells _ _ _ (?f0 :: ?f1 :: ?f2 :: ?rest) =>
        pose proof (proj1 (RT_kit.rw_cells_app mm _ [f0; f1] (f2 :: rest)) FR) as [FRa FRb]; cbn [cells_size Cells.csize Nat.add] in FRb;
        pose proof (proj1 (RT_kit.rw_cells_app mm _ [f2] rest) FRb) as [CUR FRc]; cbn [cells_size Cells.csize Nat.add] in FRc; clear FR FRb
      end end.
    change (Z.of_nat 20) with 20 in OB1. change (Z.of_nat 12) with 12 in OB2. replace (B + 20 + 12) with (B + 32) in OB2 by lia.
    change (Z.of_nat 16) with 16 in CUR. change (Z.of_nat 8) with 8 in FRc.
    replace (bv_unsigned sp + -128 + 16) with (bv_unsigned sp + -112) in CUR by lia. replace (bv_unsigned sp + -112 + 8) with (bv_unsigned sp + -104) in FRc by lia.
    pose proof (cb_len _ _ _ _ _ OB1) as LOBS.
    lstep. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut; [eapply (appnum_ok (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp _ _ _ _ _ _ _ _ _ _ F fc mm (bv_unsigned sp + -112) (B + 20) (B + 39) v lo);
        [assumption| rewrite unsigned_lit by lia; exact ST2| exact CEIL| rewrite unsigned_lit by lia; lia| exact HV| rewrite unsigned_lit by lia; lia| lia| exact LOBS| exact CUR| exact OB1]|]
    end.
    cbv beta. unfold appnum_post. intros msA nelH_; (nelim nelH_ 23%nat; intros z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 m3 obs' -> MU3 WM3 MI3 ST3 CUR3 OB3).
    rewrite unsigned_lit in MU3, ST3 by lia. cbv beta delta [wz] in CUR3 |- *.
    replace (ret_pc (Z_to_bv 64 0x689bc)) with (Z_to_bv 64 0x689bc : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    assert (MU' : munch [(bv_unsigned sp - 464, bv_unsigned sp); (B, B + 40)] m m3).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn; intros; lia|]. eapply munch_weaken; [| exact MU3]; unfold sub_fp; cbn; intros; lia. }
    pose proof (wmono_trans bsegs _ _ _ WM WM3) as WM'. clear MU WM.
    eapply (rw_cells_transport bsegs _ _ m3) in FRa; [| exact MU3| exact WM3| cbn; lia].
    eapply (rw_cells_transport bsegs _ _ m3) in FRc; [| exact MU3| exact WM3| cbn; lia].
    eapply (rw_cells_transport bsegs _ _ m3) in OB0; [| exact MU3| exact WM3| cbn; lia].
    eapply (rw_cells_transport bsegs _ _ m3) in OB2; [| exact MU3| exact WM3| cbn; lia].
    eapply (rw_cells_transport bsegs _ _ m3) in VAC; [| exact MU3| exact WM3| cbn; lia].
    clear MU3 WM3 FMTC JT MI2 ST2 CUR OB1. pose proof (fmt_cells m3 MI3) as FMTC. unfold FMTA in FMTC.
    replace (B + Z.of_nat 20 + 12) with (B + 32) in OB2 by lia. replace (B + 20 + 12) with (B + 32) in CUR3 by lia.
    replace (bv_unsigned sp + -128 + Z.of_nat 16 + 8) with (bv_unsigned sp + -104) in FRc by lia.
    gi. fl. gi. fl. gi. fl. gi. (* [comment removed for export] *)
    lstep. fold_ldb. lstep. if_lit. lstep. if_lit. (* [comment removed for export] *)
    gi. gi. gi. gi. lstep. gi. (* [comment removed for export] *)
    do 13 gi. gi. (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mZ end.
    replace (bv_unsigned sp + -112) with (bv_unsigned sp + -128 + 16) in CUR3 by lia.
    replace (bv_unsigned sp + -104) with (bv_unsigned sp + -128 + 24) in FRc by lia.
    glue FRa CUR3. glue FRa FRc.
    release_frame FRa ST3 (bv_unsigned sp).
    gi. (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch type of OB0 with rw_cells _ _ _ ?cs0 =>
      replace (B + 20) with (B + Z.of_nat (cells_size cs0)) in OB3 by (cbn; lia);
      pose proof (proj2 (RT_kit.rw_cells_app mZ B cs0 _) (conj OB0 OB3)) as OBa; clear OB0 OB3
    end.
    lazymatch type of OBa with rw_cells _ _ _ ?cs0 =>
      replace (B + 32) with (B + Z.of_nat (cells_size cs0)) in OB2 by (cbn; lia);
      pose proof (proj2 (RT_kit.rw_cells_app mZ B cs0 _) (conj OBa OB2)) as OB; clear OBa OB2; cbn [app] in OB
    end.
    lazymatch type of OB with rw_cells _ _ _ ?cs =>
      pose proof (rw_cells_merge bsegs mZ B [] cs []) as MG; cbn [app] in MG; rewrite ?app_nil_r in MG; specialize (MG OB); rewrite ?app_nil_r in MG; clear OB
    end.
    match type of MG with rw_cells _ _ _ [CB ?sz ?bs] => replace sz with 40%nat in MG by (cbn; lia) end.
    apply evt_done. unfold vsn_post. nexists 15%nat. exists mZ. eexists. split; [reflexivity|].
    split; [exact MU'|]. split; [exact WM'|]. split; [assumption|]. split; [exact ST3| exact MG].
  Qed.

  (* [comment removed for export] *)
  Lemma vsn_ok : forall (ra t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) junk,
    rw_cells bsegs m B [CB 40 junk] -> rw_cells bsegs m VA [C8 (wz v)] ->
    evt bsegs (vsn_post ra)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz B) (wz 40) (wz FMTA) (wz VA) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz A_VSNPRINTF) fc None m (seg_rom bsegs)).
  Proof.
    intros until junk. intros OUTB VAC.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof CEIL as CEIL'. idtac.
    eapply vsn_A; [exact OUTB|]. intros m1 MU01 WM01 MI1 ST1 FR1 OUTB1.
    eapply vsn_L; [exact MI1| exact FR1| exact OUTB1|]. intros m2 y10 y11 junk' MU12 WM12 MI2 FR2 OUTB2.
    eapply vsn_PZ.
    - eapply munch_trans; [eapply munch_weaken; [| exact MU01]; unfold sub_fp; cbn; intros; lia|]. eapply munch_weaken; [| exact MU12]; unfold sub_fp; cbn; intros; lia.
    - exact (wmono_trans bsegs _ _ _ WM01 WM12).
    - exact MI2.
    - eapply stk_transport_disjoint; [exact ST1| exact MU12| exact WM12| cbn; lia].
    - exact FR2.
    - exact OUTB2.
    - eapply rw_cells_transport; [| exact MU12| exact WM12| cbn; lia]. eapply rw_cells_transport; [exact VAC| exact MU01| exact WM01| cbn; lia].
  Qed.
End VSN.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition isnprintf_p_stmt' : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 bufw a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v lo : Z) (junk : list byte),
    mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 528 <= bv_unsigned sp ->
    2^44 <= v < 2^48 -> bv_unsigned sp <= bv_unsigned bufw -> bv_unsigned bufw + 40 < 2^64 ->
    rw_cells bsegs m (bv_unsigned bufw) [CB 40 junk] ->
    evt bsegs (fun ms' => exists (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m' junk',
                 ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                          F (ret_pc ra) fc None m' (seg_rom bsegs)
                 /\ munch [(bv_unsigned sp - 528, bv_unsigned sp); (bv_unsigned bufw, bv_unsigned bufw + 40)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
                 /\ stk bsegs m' lo (bv_unsigned sp) /\ rw_cells bsegs m' (bv_unsigned bufw) [CB 40 junk'])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 bufw (wz 40) (wz 0x1cdb6) (wz v) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x68cd0) fc None m (seg_rom bsegs)).

Theorem isnprintf_p_proof : isnprintf_p_stmt'.
Proof.
  unfold isnprintf_p_stmt'. intros until junk. intros MI ST CEIL LO HV HB1 HB2 OUTB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof CEIL as CEIL'. idtac.
  pose proof (munch_refl [(bv_unsigned sp - 528, bv_unsigned sp); (bv_unsigned bufw, bv_unsigned bufw + 40)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  rewrite <- (Z_to_bv_bv_unsigned bufw). set (B := bv_unsigned bufw) in *. clearbody B.
  cbv beta delta [wz] in *.
  carve_frame 64%nat ST.
  apply (rw_cells_split_CB _ _ _ [] _ _ _ [8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 7 lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. fl. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?rest) =>
    pose proof (proj1 (RT_kit.rw_cells_app m1 _ [c0; c1; c2] (c3 :: rest)) FR) as [FRa FRb]; cbn [cells_size Cells.csize Nat.add] in FRb;
    pose proof (proj1 (RT_kit.rw_cells_app m1 _ [c3] rest) FRb) as [VAC FRc]; cbn [cells_size Cells.csize Nat.add] in FRc; clear FR FRb
  end.
  lazymatch type of FRc with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -32) in FRc by lia end.
  lazymatch type of VAC with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -40) in VAC by lia end.
  eapply evt_cut.
  { eapply (vsn_ok (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m1 B (bv_unsigned sp + -40) v lo);
      [assumption| rewrite unsigned_lit by lia; exact ST| exact CEIL| rewrite unsigned_lit by lia; lia| exact HV| rewrite unsigned_lit by lia; lia
      | rewrite unsigned_lit by lia; lia| exact OUTB| exact VAC]. }
  cbv beta. unfold vsn_post. intros ms2 nelH_; (nelim nelH_ 23%nat; intros x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m2 junk' -> MU2 WM2 MI2 ST2 OUT2).
  rewrite unsigned_lit in MU2, ST2 by lia. cbv beta delta [wz] in *.
  replace (ret_pc (Z_to_bv 64 0x68cfc)) with (Z_to_bv 64 0x68cfc : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  eapply (rw_cells_transport bsegs _ m1 m2) in FRa; [| exact MU2| exact WM2| cbn; lia].
  eapply (rw_cells_transport bsegs _ m1 m2) in VAC; [| exact MU2| exact WM2| cbn; lia].
  eapply (rw_cells_transport bsegs _ m1 m2) in FRc; [| exact MU2| exact WM2| cbn; lia].
  assert (MU' : munch [(bv_unsigned sp - 528, bv_unsigned sp); (B, B + 40)] m m2).
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn; intros; lia. }
  pose proof (wmono_trans bsegs _ _ _ WM WM2) as WM'. clear MU WM MU2 WM2.
  lstep. lstep. (* [comment removed for export] *)
  replace (bv_unsigned sp + -40) with (bv_unsigned sp + -64 + 24) in VAC by lia.
  replace (bv_unsigned sp + -32) with (bv_unsigned sp + -64 + 32) in FRc by lia.
  glue FRa VAC. glue FRa FRc.
  release_frame FRa ST2 (bv_unsigned sp).
  lstep. (* [comment removed for export] *)
  apply evt_done. nexists 15%nat. exists m2, junk'. split; [reflexivity|].
  split; [exact MU'|]. split; [exact WM'|]. split; [assumption|]. split; [exact ST2| exact OUT2].
Qed.


End CeilWrap.
