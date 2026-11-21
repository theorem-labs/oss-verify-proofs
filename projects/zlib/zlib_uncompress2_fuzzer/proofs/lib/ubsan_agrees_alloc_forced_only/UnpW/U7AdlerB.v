(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.  (* a worker (A1) tool *)
From LinuxProcessSemantics.LinuxProcessSem Require State Run. (* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import TgtO_zlib_uncompress2_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk Frame RefMemcpyLib AgentLib SumWalkTac FuzzLib FuzzZ FuzzCk FuzzMem. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require Import U7AdlerBase U7Adler_code. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import FuzzAdlerLib. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require Import U7AdlerA.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import LiaFast.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.cks Require Import CkTables CkModel CkMathCrc CkMathAdler CkWalk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Opaque adler_fold adler_blocks csub lo16 hi16 byte_at.

(* [comment removed for export] *)
Definition UKP : list reg := [2; 3; 4]%bv.
(* [comment removed for export] *)
Definition ULK : list reg := [2; 3; 4; 5; 6; 7; 8; 9; 10; 15; 16; 17; 18; 19; 20; 23; 24; 28; 29; 30; 31]%bv.
(* [comment removed for export] *)
Definition UCK : list reg := [1; 2; 3; 4; 11; 12; 13; 14; 22; 23; 24; 25; 26; 27]%bv.
(* [comment removed for export] *)
Definition ULH1 : list reg := [1; 2; 3; 4; 11; 12; 13; 14; 24; 25; 26; 27]%bv.
(* [comment removed for export] *)
Definition AMAGICv : Z := 4223091239536077.
Definition NEG5552 : Z := 18446744073709546064.   (* [comment removed for export] *)

#[local] Abbreviation W8 v := (word_to_le_bytes 8 v).

(* [comment removed for export] *)
Lemma zv_not : forall a, 0 <= a < two64 -> Z_to_bv 64 (Z.lxor a (-1)) = Z_to_bv 64 (two64 - 1 - a).
Proof.
  intros a Ha. apply zv_eq. rewrite Z.lxor_m1_r. unfold Z.lnot.
  replace (Z.pred (- a)) with ((two64 - 1 - a) + (-1) * two64) by lia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma CKR_ULE : incl CKR ULE. Proof. incl_dec. Qed.
Lemma CKR_ULB' : incl CKR ULB. Proof. incl_dec. Qed.

Section UADLB.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *)
  Variables (m rom : word -> option byte) (adr0 len0 : Z).
  Hypothesis Himg : img_ok m.
  Hypothesis Hrd : forall i, 0 <= i < len0 -> exists b : byte, rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (adr0 + i)) 1 = Some [b].
  Hypothesis Hnw : adr0 + len0 < two64.
  Hypothesis Ha0 : 0 <= adr0.
  Hypothesis Hl0 : 0 <= len0.

  #[local] Abbreviation BA := (byte_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m).
  #[local] Abbreviation BS := (bytes_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m).
  (* [comment removed for export] *)
  #[local] Abbreviation PL := (bytes_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m adr0 (Z.to_nat len0)).

  Ltac solve_ka := first [ assumption | apply lkeeps_refl | solve_lkeeps
                         | eapply lkeeps_trans; [eassumption|]; first [assumption | solve_lkeeps | eapply lkeeps_trans; eassumption] ].
  Ltac zbv := apply (f_equal (fun z : Z => Z_to_bv 64 z)); lia.
  Ltac post := repeat split; gres; rwR; first [ reflexivity | assumption | zbv | lia | solve_ka ].
  Ltac step_auipc F D := stepi F D; znorm;
    try match goal with |- context [regupd _ _ (v_auipc ?p ?i)] => wlit_closed (v_auipc p i) end.
  (* [comment removed for export] *)
  Ltac negz :=
    match goal with |- context [regupd _ _ (Z_to_bv 64 (Zneg ?p))] =>
      let v := eval cbv in (18446744073709551616 - Zpos p) in
      replace (Z_to_bv 64 (Zneg p) : word) with (Z_to_bv 64 v : word) by (apply zv_eq; reflexivity) end.
  Ltac ld_amag F D :=
    chain_step;
    [ reflexivity
    | eapply step_ld with (v := Z_to_bv 64 4223091239536077);
      [ exact F | reflexivity | exact D
      | gres; imm_norm; rwR; rewrite ?zv_addi;
        match goal with |- rdn _ _ (Z_to_bv 64 ?x) _ = _ => replace x with AMAG by (unfold AMAG; lia) end;
        apply rd_amag; exact Himg
      | exact amag_bs_v ]
    | step_simpl; gres ].
  (* [comment removed for export] *)
  Ltac ld_slot F D vv E :=
    chain_step;
    [ reflexivity
    | eapply step_ld with (v := vv);
      [ exact F | reflexivity | exact D
      | gres; imm_norm; rwR; rewrite ?zv_addi;
        match goal with |- rdn _ _ (Z_to_bv 64 ?x) _ = _ =>
          match type of E with rdn _ _ (Z_to_bv 64 ?y) _ = _ => replace x with y by lia end end;
        exact E
      | apply bytes_le_to_Z_8 ]
    | step_simpl; gres ].

  (* [comment removed for export] *)
  Ltac kept K H r := rewrite (K r) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])); exact H.
  Ltac ck16 H := pose proof H as CK; unfold CK16, NEG in CK;
    destruct CK as (C10 & C15 & C16 & C17 & C5 & C6 & C7 & C28 & C29 & C30 & C31 & C8 & C9 & C18 & C19 & C20).

  (* [comment removed for export] *)
  Lemma lkeeps_UKP : forall l r1 r2, lkeeps l r1 r2 -> incl UKP l -> lkeeps UKP r1 r2.
  Proof. intros l r1 r2 H Hi x Hx. apply H, Hi, Hx. Qed.
  Ltac toKP H := apply (lkeeps_UKP _ _ _ H); incl_dec.
  Ltac kp_chain := repeat match goal with
    | |- lkeeps UKP ?a ?a => apply lkeeps_refl
    | |- lkeeps UKP _ (regupd _ _ _) => solve_lkeeps
    | H : lkeeps _ ?a ?b |- lkeeps UKP ?a ?c =>
        first [ constr_eq b c; toKP H
              | apply (lkeeps_trans UKP a b c); [toKP H|] ] end.
  Ltac postK := repeat split; gres; rwR; first [ reflexivity | assumption | zbv | lia | solve_ka | kp_chain ].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma uck_run : forall regs (p c A B : Z),
    getr regs 11 = Z_to_bv 64 p -> getr regs 12 = Z_to_bv 64 c ->
    getr regs 14 = Z_to_bv 64 A -> getr regs 13 = Z_to_bv 64 B ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x180d0 : word) m rom) (mkst r (0x18114 : word) m rom)
      /\ CK16 r /\ getr r 21 = Z_to_bv 64 15
      /\ getr r 11 = Z_to_bv 64 p /\ getr r 12 = Z_to_bv 64 c
      /\ getr r 14 = Z_to_bv 64 A /\ getr r 13 = Z_to_bv 64 B
      /\ lkeeps UCK regs r.
  Proof.
    intros regs p c A B R11 R12 R14 R13.
    eexists. split.
    - stepz F_17fac D_17fac. negz.
      stepz F_17fb0 D_17fb0. negz.
      stepz F_17fb4 D_17fb4. negz.
      stepz F_17fb8 D_17fb8. negz.
      stepz F_17fbc D_17fbc. negz.
      stepz F_17fc0 D_17fc0. negz.
      stepz F_17fc4 D_17fc4. negz.
      stepz F_17fc8 D_17fc8. negz.
      stepz F_17fcc D_17fcc. negz.
      stepz F_17fd0 D_17fd0. negz.
      stepz F_17fd4 D_17fd4. negz.
      stepz F_17fd8 D_17fd8. negz.
      stepz F_17fdc D_17fdc. negz.
      stepz F_17fe0 D_17fe0. negz.
      stepz F_17fe4 D_17fe4. negz.
      stepz F_17fe8 D_17fe8. negz.
      stepz F_17fec D_17fec.
      apply mst_refl.
    - unfold CK16, NEG. post.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Section BLK.
    Variable spv : Z.
    Hypothesis Hspv : 0 <= spv /\ spv + 24 <= two64.
    Hypothesis Hs16 : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (spv + 16)) 8 = Some (W8 (Z_to_bv 64 NEG5552)).
    Hypothesis Hs8 : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (spv + 8)) 8 = Some (W8 (Z_to_bv 64 5552)).

    Lemma ublk_loop : forall (c : nat) regs (i : nat) (ab : Z * Z) (rem : Z),
      CK16 regs -> getr regs 2 = Z_to_bv 64 spv ->
      getr regs 23 = Z_to_bv 64 AMAGICv -> getr regs 24 = Z_to_bv 64 65521 ->
      getr regs 11 = Z_to_bv 64 (adr0 + 5552 * Z.of_nat i) -> getr regs 12 = Z_to_bv 64 rem ->
      getr regs 14 = Z_to_bv 64 (fst (adler_blocks i ab PL)) ->
      getr regs 13 = Z_to_bv 64 (snd (adler_blocks i ab PL)) ->
      0 <= fst ab <= 65535 -> 0 <= snd ab <= 65535 ->
      rem = len0 - 5552 * Z.of_nat i -> 5552 * Z.of_nat (S c) <= rem < 5552 * Z.of_nat (S c) + 5552 ->
      exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x17f5c : word) m rom) (mkst r (0x180c4 : word) m rom)
        /\ getr r 14 = Z_to_bv 64 (fst (adler_blocks (i + S c) ab PL))
        /\ getr r 13 = Z_to_bv 64 (snd (adler_blocks (i + S c) ab PL))
        /\ getr r 11 = Z_to_bv 64 (adr0 + 5552 * Z.of_nat (i + S c))
        /\ getr r 12 = Z_to_bv 64 (rem - 5552 * Z.of_nat (S c))
        /\ lkeeps ULK regs r.
    Proof.
      induction c as [|c IH]; intros regs i ab rem HCK R2 R23 R24 R11 R12 R14 R13 Hab1 Hab2 Hrem Hc; ck16 HCK.
      - (* [comment removed for export] *)
        set (q := adr0 + 5552 * Z.of_nat i) in *.
        set (ab1 := adler_blocks i ab PL) in *.
        pose proof (adler_blocks_bound16 i (fst ab) (snd ab) PL Hab1 Hab2) as Hb16.
        rewrite <- surjective_pairing in Hb16. fold ab1 in Hb16. destruct Hb16 as [HbA HbB].
        (* [comment removed for export] *)
        eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x17f74 : word) m rom)
                 (fun r => getr r 26 = Z_to_bv 64 (q + Z.of_nat 0)
                           /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab1 (BS q 0)))
                           /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab1 (BS q 0)))
                           /\ getr r 27 = Z_to_bv 64 (two64 - Z.of_nat 347)
                           /\ getr r 12 = Z_to_bv 64 (rem - 5552)
                           /\ getr r 11 = Z_to_bv 64 (q + 5552)
                           /\ getr r 2 = Z_to_bv 64 spv /\ getr r 23 = Z_to_bv 64 AMAGICv /\ getr r 24 = Z_to_bv 64 65521
                           /\ CK16 r
                           /\ lkeeps ULK regs r)).
        { eexists. split.
          - stepz F_17e38 D_17e38.
            ld_slot F_17e3c D_17e3c (Z_to_bv 64 NEG5552 : word) Hs16.
            stepz F_17e40 D_17e40.
            match goal with |- context [Z_to_bv 64 (rem + NEG5552)] =>
              replace (Z_to_bv 64 (rem + NEG5552)) with (Z_to_bv 64 (rem - 5552) : word)
                by (apply zv_eq; unfold NEG5552; rewrite <- (Z.mod_add _ 1) by lia; f_equal; lia) end.
            ld_slot F_17e44 D_17e44 (Z_to_bv 64 5552 : word) Hs8.
            stepz F_17e48 D_17e48.
            stepz F_17e4c D_17e4c. negz.
            apply mst_refl.
          - rewrite adler_fold_bytes_0. unfold CK16, NEG. post. }
        cbv beta. intros r1 (S26 & S14 & S13 & S27 & S12 & S11 & S2 & S23 & S24 & HCK1 & K1).
        destruct (ub16_loop m rom adr0 len0 Hrd Hnw Ha0 346 r1 ab1 q 0 HCK1 S26 S14 S13 S27 ltac:(lia) ltac:(lia) ltac:(lia))
          as (r2 & M2 & A2 & B2 & C2 & K2).
        change (0 + 16 * 347)%nat with (Z.to_nat NMAX) in A2, B2.
        pose proof (sums_range64' ab1 (BS q (Z.to_nat NMAX)) HbA HbB (bytes_at_bytes _ _ _ _)
                      ltac:(rewrite Zlen_bytes_at; unfold NMAX; lia)) as [HA HB].
        destruct (ubmod_run m rom r2 _ _ (rem - 5552) A2 B2
                    ltac:(kept K2 S23 (23%bv : reg)) ltac:(kept K2 S24 (24%bv : reg)) ltac:(kept K2 S12 (12%bv : reg))
                    HA HB ltac:(lia))
          as (r3 & M3 & A3 & B3 & T3 & U3 & K3).
        assert (E12 : getr r3 12 = Z_to_bv 64 (rem - 5552)) by (rewrite (K3 (12%bv : reg)), (K2 (12%bv : reg)) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])); exact S12).
        assert (E11 : getr r3 11 = Z_to_bv 64 (q + 5552)) by (rewrite (K3 (11%bv : reg)), (K2 (11%bv : reg)) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])); exact S11).
        assert (Hsh : Z.shiftr (rem - 5552) 4 < 347).
        { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16. apply Z.div_lt_upper_bound; lia. }
        assert (Hsh0 : 0 <= Z.shiftr (rem - 5552) 4) by (apply Z.shiftr_nonneg; lia).
        eexists. split; [|split; [|split; [|split; [|split]]]].
        + eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M3|].
          stepb_ft F_17f9c D_17f9c ltac:(condZ).
          apply mst_refl.
        + gres. rewrite A3. replace (i + 1)%nat with (S i) by lia.
          rewrite (adler_blocks_bytes_S (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m i ab adr0 (Z.to_nat len0)) by lia. reflexivity.
        + gres. rewrite B3. replace (i + 1)%nat with (S i) by lia.
          rewrite (adler_blocks_bytes_S (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m i ab adr0 (Z.to_nat len0)) by lia. reflexivity.
        + gres. rewrite E11. zbv.
        + gres. rewrite E12. zbv.
        + eapply lkeeps_trans; [exact K1|].
          intros x Hx. rewrite (K3 x), (K2 x); [reflexivity| |]; revert Hx; cbv; (first [solve [liafast_keep_section; tauto] | tauto]).
      - (* [comment removed for export] *)
        set (q := adr0 + 5552 * Z.of_nat i) in *.
        set (ab1 := adler_blocks i ab PL) in *.
        pose proof (adler_blocks_bound16 i (fst ab) (snd ab) PL Hab1 Hab2) as Hb16.
        rewrite <- surjective_pairing in Hb16. fold ab1 in Hb16. destruct Hb16 as [HbA HbB].
        eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x17f74 : word) m rom)
                 (fun r => getr r 26 = Z_to_bv 64 (q + Z.of_nat 0)
                           /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab1 (BS q 0)))
                           /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab1 (BS q 0)))
                           /\ getr r 27 = Z_to_bv 64 (two64 - Z.of_nat 347)
                           /\ getr r 12 = Z_to_bv 64 (rem - 5552)
                           /\ getr r 11 = Z_to_bv 64 (q + 5552)
                           /\ getr r 2 = Z_to_bv 64 spv /\ getr r 23 = Z_to_bv 64 AMAGICv /\ getr r 24 = Z_to_bv 64 65521
                           /\ CK16 r
                           /\ lkeeps ULK regs r)).
        { eexists. split.
          - stepz F_17e38 D_17e38.
            ld_slot F_17e3c D_17e3c (Z_to_bv 64 NEG5552 : word) Hs16.
            stepz F_17e40 D_17e40.
            match goal with |- context [Z_to_bv 64 (rem + NEG5552)] =>
              replace (Z_to_bv 64 (rem + NEG5552)) with (Z_to_bv 64 (rem - 5552) : word)
                by (apply zv_eq; unfold NEG5552; rewrite <- (Z.mod_add _ 1) by lia; f_equal; lia) end.
            ld_slot F_17e44 D_17e44 (Z_to_bv 64 5552 : word) Hs8.
            stepz F_17e48 D_17e48.
            stepz F_17e4c D_17e4c. negz.
            apply mst_refl.
          - rewrite adler_fold_bytes_0. unfold CK16, NEG. post. }
        cbv beta. intros r1 (S26 & S14 & S13 & S27 & S12 & S11 & S2 & S23 & S24 & HCK1 & K1).
        destruct (ub16_loop m rom adr0 len0 Hrd Hnw Ha0 346 r1 ab1 q 0 HCK1 S26 S14 S13 S27 ltac:(lia) ltac:(lia) ltac:(lia))
          as (r2 & M2 & A2 & B2 & C2 & K2).
        change (0 + 16 * 347)%nat with (Z.to_nat NMAX) in A2, B2.
        pose proof (sums_range64' ab1 (BS q (Z.to_nat NMAX)) HbA HbB (bytes_at_bytes _ _ _ _)
                      ltac:(rewrite Zlen_bytes_at; unfold NMAX; lia)) as [HA HB].
        destruct (ubmod_run m rom r2 _ _ (rem - 5552) A2 B2
                    ltac:(kept K2 S23 (23%bv : reg)) ltac:(kept K2 S24 (24%bv : reg)) ltac:(kept K2 S12 (12%bv : reg))
                    HA HB ltac:(lia))
          as (r3 & M3 & A3 & B3 & T3 & U3 & K3).
        assert (K13 : lkeeps ULK regs r3).
        { eapply lkeeps_trans; [exact K1|].
          intros x Hx. rewrite (K3 x), (K2 x); [reflexivity| |]; revert Hx; cbv; (first [solve [liafast_keep_section; tauto] | tauto]). }
        assert (E12 : getr r3 12 = Z_to_bv 64 (rem - 5552)) by (rewrite (K3 (12%bv : reg)), (K2 (12%bv : reg)) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])); exact S12).
        assert (E11 : getr r3 11 = Z_to_bv 64 (adr0 + 5552 * Z.of_nat (S i))).
        { rewrite (K3 (11%bv : reg)), (K2 (11%bv : reg)) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])). rewrite S11. zbv. }
        assert (HCK3 : CK16 r3).
        { apply (CK16_kept ULE r2 r3); [| exact K3 | exact CKR_ULE].
          apply (CK16_kept ULB r1 r2); [exact HCK1 | exact K2 | exact CKR_ULB']. }
        assert (Hsh : 347 <= Z.shiftr (rem - 5552) 4).
        { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16. apply Z.div_le_lower_bound; lia. }
        assert (Hsh2 : Z.shiftr (rem - 5552) 4 < two64).
        { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16. apply Z.div_lt_upper_bound; lia. }
        assert (A3' : getr r3 14 = Z_to_bv 64 (fst (adler_blocks (S i) ab PL))).
        { rewrite A3, (adler_blocks_bytes_S (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m i ab adr0 (Z.to_nat len0)) by lia. reflexivity. }
        assert (B3' : getr r3 13 = Z_to_bv 64 (snd (adler_blocks (S i) ab PL))).
        { rewrite B3, (adler_blocks_bytes_S (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m i ab adr0 (Z.to_nat len0)) by lia. reflexivity. }
        destruct (IH r3 (S i) ab (rem - 5552) HCK3
                    ltac:(kept K13 R2 (2%bv : reg)) ltac:(kept K13 R23 (23%bv : reg)) ltac:(kept K13 R24 (24%bv : reg))
                    E11 E12 A3' B3' Hab1 Hab2 ltac:(lia) ltac:(lia))
          as (r4 & M4 & A4 & B4 & C4 & T4 & K4).
        eexists. split; [|split; [|split; [|split; [|split]]]].
        + eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M3|].
          stepb_tk F_17f9c D_17f9c ltac:(condZ).
          exact M4.
        + rewrite A4. replace (i + S (S c))%nat with (S i + S c)%nat by lia. reflexivity.
        + rewrite B4. replace (i + S (S c))%nat with (S i + S c)%nat by lia. reflexivity.
        + rewrite C4. zbv.
        + rewrite T4. zbv.
        + eapply lkeeps_trans; [exact K13 | exact K4].
    Qed.
  End BLK.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma utail8_run : forall regs (ab : Z * Z) (q : Z) (n : nat) (rest : Z),
    getr regs 11 = Z_to_bv 64 (q + Z.of_nat n) -> getr regs 12 = Z_to_bv 64 rest ->
    getr regs 14 = Z_to_bv 64 (fst (adler_fold ab (BS q n))) ->
    getr regs 13 = Z_to_bv 64 (snd (adler_fold ab (BS q n))) ->
    0 < rest < 16 -> adr0 <= q -> q + Z.of_nat n + rest <= adr0 + len0 ->
    0 <= fst ab <= 65535 -> 0 <= snd ab <= 65535 -> Z.of_nat n + rest <= NMAX ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x1822c : word) m rom) (mkst r (0x1829c : word) m rom)
      /\ getr r 10 = Z_to_bv 64 (Z.lor ((snd (adler_fold ab (BS q (n + Z.to_nat rest))) mod BASE) * 2 ^ 16)
                                      (fst (adler_fold ab (BS q (n + Z.to_nat rest))) mod BASE))
      /\ lkeeps UKP regs r.
  Proof.
    intros regs ab q n rest R11 R12 R14 R13 Hrest Hq Hfit Hab1 Hab2 Hn.
    eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x18230 : word) m rom)
             (fun r => getr r 10 = Z_to_bv 64 (NEG 1)
                       /\ getr r 11 = Z_to_bv 64 (q + Z.of_nat n)
                       /\ getr r 12 = Z_to_bv 64 (Z.of_nat (S (Z.to_nat (rest - 1))))
                       /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS q n)))
                       /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS q n)))
                       /\ lkeeps UKP regs r)).
    { eexists. split.
      - stepz F_18108 D_18108. negz. apply mst_refl.
      - unfold NEG. post. }
    cbv beta. intros r1 (S10 & S11 & S12 & S14 & S13 & K1).
    destruct (utb_loop m rom adr0 len0 Hrd Hnw Ha0 (Z.to_nat (rest - 1)) r1 ab q n S10 S11 S12 S14 S13 Hq ltac:(lia))
      as (r2 & M2 & A2 & B2 & K2).
    pose proof (sums_range64' ab (BS q (n + S (Z.to_nat (rest - 1)))) Hab1 Hab2 (bytes_at_bytes _ _ _ _)
                  ltac:(rewrite Zlen_bytes_at; lia)) as [HA HB].
    destruct (utmod_run m rom Himg r2 _ _ A2 B2 HA HB) as (r3 & M3 & A3 & B3 & K3).
    destruct (ucomb_run m rom r3 _ _ A3 B3) as (r4 & M4 & V4 & K4).
    exists r4. split; [|split].
    - eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M3 | exact M4].
    - rewrite V4. replace (n + Z.to_nat rest)%nat with (n + S (Z.to_nat (rest - 1)))%nat by lia. reflexivity.
    - kp_chain.
  Qed.

  (* [comment removed for export] *)
  Lemma utail_run : forall regs (ab : Z * Z) (q : Z) (n : nat) (rest : Z),
    getr regs 22 = Z_to_bv 64 (q + Z.of_nat n) -> getr regs 12 = Z_to_bv 64 rest ->
    getr regs 14 = Z_to_bv 64 (fst (adler_fold ab (BS q n))) ->
    getr regs 13 = Z_to_bv 64 (snd (adler_fold ab (BS q n))) ->
    0 <= rest < 16 -> adr0 <= q -> q + Z.of_nat n + rest <= adr0 + len0 ->
    0 <= fst ab <= 65535 -> 0 <= snd ab <= 65535 -> Z.of_nat n + rest <= NMAX ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x18224 : word) m rom) (mkst r (0x1829c : word) m rom)
      /\ getr r 10 = Z_to_bv 64 (Z.lor ((snd (adler_fold ab (BS q (n + Z.to_nat rest))) mod BASE) * 2 ^ 16)
                                      (fst (adler_fold ab (BS q (n + Z.to_nat rest))) mod BASE))
      /\ lkeeps UKP regs r.
  Proof.
    intros regs ab q n rest R22 R12 R14 R13 Hrest Hq Hfit Hab1 Hab2 Hn.
    destruct (Z.eq_dec rest 0) as [-> | Hne].
    - pose proof (sums_range64' ab (BS q n) Hab1 Hab2 (bytes_at_bytes _ _ _ _)
                    ltac:(rewrite Zlen_bytes_at; lia)) as [HA HB].
      eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x1824c : word) m rom)
               (fun r => getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS q n)))
                         /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS q n))) /\ lkeeps UKP regs r)).
      { eexists. split.
        - stepz F_18100 D_18100.
          stepb_tk F_18104 D_18104 ltac:(condZ). apply mst_refl.
        - post. }
      cbv beta. intros r1 (S14 & S13 & K1).
      destruct (utmod_run m rom Himg r1 _ _ S14 S13 HA HB) as (r3 & M3 & A3 & B3 & K3).
      destruct (ucomb_run m rom r3 _ _ A3 B3) as (r4 & M4 & V4 & K4).
      exists r4. split; [|split].
      + eapply msteps_trans; [exact M3 | exact M4].
      + rewrite V4. replace (n + Z.to_nat 0)%nat with n by lia. reflexivity.
      + kp_chain.
    - eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x1822c : word) m rom)
               (fun r => getr r 11 = Z_to_bv 64 (q + Z.of_nat n)
                         /\ getr r 12 = Z_to_bv 64 rest
                         /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS q n)))
                         /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS q n))) /\ lkeeps UKP regs r)).
      { eexists. split.
        - stepz F_18100 D_18100.
          stepb_ft F_18104 D_18104 ltac:(condZ). apply mst_refl.
        - post. }
      cbv beta. intros r1 (S11 & S12 & S14 & S13 & K1).
      destruct (utail8_run r1 ab q n rest S11 S12 S14 S13 ltac:(lia) Hq Hfit Hab1 Hab2 Hn) as (r2 & M2 & V2 & K2).
      exists r2. split; [exact M2 | split; [exact V2 | kp_chain]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma ushort_run : forall regs (a : Z),
    getr regs 11 = Z_to_bv 64 adr0 -> getr regs 12 = Z_to_bv 64 len0 ->
    getr regs 14 = Z_to_bv 64 (lo16 a) -> getr regs 13 = Z_to_bv 64 (hi16 a) ->
    len0 < 16 -> len0 <> 1 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x17e50 : word) m rom) (mkst r (0x1829c : word) m rom)
      /\ getr r 10 = Z_to_bv 64 (adler32_z_model a PL)
      /\ lkeeps UKP regs r.
  Proof.
    intros regs a R11 R12 R14 R13 H16 H1.
    pose proof (lo16_le a) as Hlo. pose proof (hi16_le a) as Hhi.
    rewrite <- (adler_short_exit a PL) by (rewrite Zlen_bytes_at; lia). cbv zeta.
    pose proof (short_a_range (lo16 a) (hi16 a) PL Hlo (bytes_at_bytes _ _ _ _) ltac:(rewrite Zlen_bytes_at; lia)) as HA.
    pose proof (sums_range64 (lo16 a) (hi16 a) PL Hlo Hhi (bytes_at_bytes _ _ _ _)
                  ltac:(rewrite Zlen_bytes_at; unfold NMAX; lia)) as [_ HB].
    set (ab := (lo16 a, hi16 a)) in *.
    destruct (Z.eq_dec len0 0) as [Hz | Hnz].
    - (* [comment removed for export] *)
      eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x17e94 : word) m rom)
               (fun r => getr r 14 = Z_to_bv 64 (fst (adler_fold ab PL))
                         /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab PL)) /\ lkeeps UKP regs r)).
      { eexists. split.
        - stepz F_17d2c D_17d2c.
          stepb_ft F_17d30 D_17d30 ltac:(condZ).
          stepb_tk F_17d34 D_17d34 ltac:(condZ).
          apply mst_refl.
        - rewrite Hz. change (Z.to_nat 0) with 0%nat. rewrite adler_fold_bytes_0. subst ab. post. }
      cbv beta. intros r1 (S14 & S13 & K1).
      destruct (usmod_run m rom Himg r1 _ _ S14 S13 ltac:(lia) HB) as (r2 & M2 & V2 & K2).
      exists r2. split; [exact M2 | split; [exact V2 | kp_chain]].
    - eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x17e78 : word) m rom)
               (fun r => getr r 12 = Z_to_bv 64 (NEG 1)
                         /\ getr r 11 = Z_to_bv 64 (adr0 + Z.of_nat 0)
                         /\ getr r 10 = Z_to_bv 64 (adr0 + Z.of_nat 0 + Z.of_nat (S (Z.to_nat (len0 - 1))))
                         /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS adr0 0)))
                         /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS adr0 0))) /\ lkeeps UKP regs r)).
      { eexists. split.
        - stepz F_17d2c D_17d2c.
          stepb_ft F_17d30 D_17d30 ltac:(condZ).
          stepb_ft F_17d34 D_17d34 ltac:(condZ).
          stepz F_17d38 D_17d38. rewrite (zv_not adr0) by lia.
          stepz F_17d3c D_17d3c.
          stepb_ft F_17d40 D_17d40 ltac:(condZ).
          stepz F_17d44 D_17d44.
          stepz F_17d48 D_17d48.
          stepz F_17d4c D_17d4c.
          stepz F_17d50 D_17d50. negz.
          apply mst_refl.
        - rewrite adler_fold_bytes_0. subst ab. unfold NEG. post. }
      cbv beta. intros r1 (S12 & S11 & S10 & S14 & S13 & K1).
      destruct (usb_loop m rom adr0 len0 Hrd Hnw Ha0 (Z.to_nat (len0 - 1)) r1 ab adr0 0 S12 S11 S10 S14 S13 ltac:(lia) ltac:(lia))
        as (r2 & M2 & A2 & B2 & K2).
      replace (0 + S (Z.to_nat (len0 - 1)))%nat with (Z.to_nat len0) in A2, B2 by lia.
      destruct (usmod_run m rom Himg r2 _ _ A2 B2 ltac:(lia) HB) as (r3 & M3 & V3 & K3).
      exists r3. split; [|split].
      + eapply msteps_trans; [exact M2 | exact M3].
      + exact V3.
      + kp_chain.
  Qed.

  (* [comment removed for export] *)
  Lemma umid_run : forall regs (a : Z),
    getr regs 11 = Z_to_bv 64 adr0 -> getr regs 12 = Z_to_bv 64 len0 ->
    getr regs 14 = Z_to_bv 64 (lo16 a) -> getr regs 13 = Z_to_bv 64 (hi16 a) ->
    16 <= len0 < NMAX ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x17e50 : word) m rom) (mkst r (0x1829c : word) m rom)
      /\ getr r 10 = Z_to_bv 64 (adler32_z_model a PL)
      /\ lkeeps UKP regs r.
  Proof.
    intros regs a R11 R12 R14 R13 Hlen. unfold NMAX in Hlen.
    pose proof (lo16_le a) as Hlo. pose proof (hi16_le a) as Hhi.
    assert (Hnil : PL <> []).
    { intros E. apply (f_equal (@length Z)) in E. rewrite bytes_at_length in E. cbn in E. lia. }
    rewrite <- (adler_long_exit_cons a PL PL); cycle 1.
    { rewrite Zlen_bytes_at. lia. }
    { rewrite Zlen_bytes_at. replace (Z.of_nat (Z.to_nat len0) / NMAX) with 0 by (unfold NMAX; symmetry; apply Z.div_small; lia).
      reflexivity. }
    { exact Hnil. }
    cbv zeta. rewrite Zlen_bytes_at.
    replace (Z.of_nat (Z.to_nat len0) / NMAX) with 0 by (unfold NMAX; symmetry; apply Z.div_small; lia).
    change (Z.to_nat 0) with 0%nat. rewrite adler_blocks_0.
    set (ab := (lo16 a, hi16 a)).
    pose proof (Z.div_mod len0 16 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound len0 16 ltac:(lia)) as Hmb.
    assert (Hq : 1 <= len0 / 16) by (apply Z.div_le_lower_bound; lia).
    set (k := Z.to_nat (len0 / 16 - 1)).
    assert (Hk : Z.of_nat (S k) = len0 / 16) by (subst k; lia).
    assert (Hsh : Z.shiftr len0 4 < 347).
    { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16. apply Z.div_lt_upper_bound; lia. }
    assert (Hsh0 : 0 <= Z.shiftr len0 4) by (apply Z.shiftr_nonneg; lia).
    (* [comment removed for export] *)
    eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x180d0 : word) m rom)
             (fun r => getr r 11 = Z_to_bv 64 (adr0 + Z.of_nat 0)
                       /\ getr r 12 = Z_to_bv 64 (16 * Z.of_nat (S k) + len0 mod 16)
                       /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS adr0 0)))
                       /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS adr0 0)))
                       /\ lkeeps UKP regs r)).
    { eexists. split.
      - stepz F_17d2c D_17d2c.
        stepb_tk F_17d30 D_17d30 ltac:(condZ).
        stepi F_17dc4 D_17dc4; znorm. rewrite (zv_srli len0 4) by lia.
        stepz F_17dc8 D_17dc8.
        stepb_tk F_17dcc D_17dcc ltac:(condZ).
        apply mst_refl.
      - rewrite adler_fold_bytes_0. subst ab. post. }
    cbv beta. intros r0 (T11 & T12 & T14 & T13 & K0).
    destruct (uck_run r0 _ _ _ _ T11 T12 T14 T13) as (r1 & M1 & HCK1 & S21 & S11 & S12 & S14 & S13 & K1).
    destruct (ud16_loop m rom adr0 len0 Hrd Hnw Ha0 k r1 ab adr0 0 (len0 mod 16) HCK1 S11 S14 S13 S12 S21
                ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & M2 & A2 & B2 & C2 & D2 & N2 & E2 & K2).
    destruct (utail_run r2 ab adr0 (0 + 16 * S k) (len0 mod 16)
                ltac:(rewrite D2; zbv) N2 A2 B2 ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(subst ab; cbn [fst]; lia) ltac:(subst ab; cbn [snd]; lia) ltac:(unfold NMAX; lia))
      as (r3 & M3 & V3 & K3).
    exists r3. split; [|split].
    - eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2 | exact M3].
    - rewrite V3. replace (0 + 16 * S k + Z.to_nat (len0 mod 16))%nat with (Z.to_nat len0) by lia. reflexivity.
    - kp_chain.
  Qed.

  (* [comment removed for export] *)
  Theorem ubody_run : forall regs (a : Z),
    getr regs 11 = Z_to_bv 64 adr0 -> getr regs 12 = Z_to_bv 64 len0 ->
    getr regs 14 = Z_to_bv 64 (lo16 a) -> getr regs 13 = Z_to_bv 64 (hi16 a) ->
    len0 <> 1 -> len0 < NMAX ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x17e50 : word) m rom) (mkst r (0x1829c : word) m rom)
      /\ getr r 10 = Z_to_bv 64 (adler32_z_model a PL)
      /\ lkeeps UKP regs r.
  Proof.
    intros regs a R11 R12 R14 R13 H1 Hn.
    destruct (Z.lt_ge_cases len0 16) as [Hs | Hl].
    - exact (ushort_run regs a R11 R12 R14 R13 Hs H1).
    - exact (umid_run regs a R11 R12 R14 R13 ltac:(lia)).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma ulong_head : forall regs,
    getr regs 12 = Z_to_bv 64 len0 -> NMAX <= len0 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x17e50 : word) m rom) (mkst r (0x17f44 : word) m rom)
      /\ CK16 r /\ getr r 21 = Z_to_bv 64 NEG5552 /\ getr r 22 = Z_to_bv 64 4096 /\ getr r 23 = Z_to_bv 64 65340
      /\ lkeeps ULH1 regs r.
  Proof.
    intros regs R12 Hlen. unfold NMAX in Hlen.
    assert (Hsh : 347 <= Z.shiftr len0 4).
    { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16. apply Z.div_le_lower_bound; lia. }
    assert (Hsh2 : Z.shiftr len0 4 < two64).
    { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16. apply Z.div_lt_upper_bound; lia. }
    eexists. split.
    - stepz F_17d2c D_17d2c.
      stepb_tk F_17d30 D_17d30 ltac:(condZ).
      stepi F_17dc4 D_17dc4; znorm. rewrite (zv_srli len0 4) by lia.
      stepz F_17dc8 D_17dc8.
      stepb_ft F_17dcc D_17dcc ltac:(condZ).
      stepz F_17dd0 D_17dd0.
      stepz F_17dd4 D_17dd4.
      stepz F_17dd8 D_17dd8. negz.
      stepz F_17ddc D_17ddc. negz.
      stepz F_17de0 D_17de0. negz.
      stepz F_17de4 D_17de4. negz.
      stepz F_17de8 D_17de8. negz.
      stepz F_17dec D_17dec. negz.
      stepz F_17df0 D_17df0. negz.
      stepz F_17df4 D_17df4. negz.
      stepz F_17df8 D_17df8. negz.
      stepz F_17dfc D_17dfc. negz.
      stepz F_17e00 D_17e00. negz.
      stepz F_17e04 D_17e04. negz.
      stepz F_17e08 D_17e08. negz.
      stepz F_17e0c D_17e0c. negz.
      stepz F_17e10 D_17e10. negz.
      stepz F_17e14 D_17e14. negz.
      step_auipc F_17e18 D_17e18.
      stepz F_17e1c D_17e1c.
      apply mst_refl.
    - unfold CK16, NEG, NEG5552. post.
  Qed.

  (* [comment removed for export] *)
  Lemma ulong_body : forall regs (a spv : Z),
    CK16 regs -> getr regs 2 = Z_to_bv 64 spv ->
    0 <= spv /\ spv + 24 <= two64 ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (spv + 16)) 8 = Some (W8 (Z_to_bv 64 NEG5552)) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (spv + 8)) 8 = Some (W8 (Z_to_bv 64 5552)) ->
    getr regs 23 = Z_to_bv 64 65340 ->
    getr regs 11 = Z_to_bv 64 adr0 -> getr regs 12 = Z_to_bv 64 len0 ->
    getr regs 14 = Z_to_bv 64 (lo16 a) -> getr regs 13 = Z_to_bv 64 (hi16 a) ->
    NMAX <= len0 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x17f50 : word) m rom) (mkst r (0x1829c : word) m rom)
      /\ getr r 10 = Z_to_bv 64 (adler32_z_model a PL)
      /\ lkeeps UKP regs r.
  Proof.
    intros regs a spv HCK R2 Hspv Hs16 Hs8 R23 R11 R12 R14 R13 Hlen. unfold NMAX in Hlen.
    ck16 HCK.
    pose proof (lo16_le a) as Hlo. pose proof (hi16_le a) as Hhi.
    set (ab := (lo16 a, hi16 a)).
    pose proof (Z.div_mod len0 5552 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound len0 5552 ltac:(lia)) as Hmb.
    assert (Hq : 1 <= len0 / 5552) by (apply Z.div_le_lower_bound; lia).
    set (nb := len0 / 5552) in *.
    set (c := Z.to_nat (nb - 1)).
    assert (Hc : Z.of_nat (S c) = nb) by (subst c; lia).
    assert (Hnbl : Zlen PL / NMAX = nb) by (rewrite Zlen_bytes_at; unfold NMAX; subst nb; f_equal; lia).
    (* [comment removed for export] *)
    eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x17f5c : word) m rom)
             (fun r => CK16 r /\ getr r 2 = Z_to_bv 64 spv
                       /\ getr r 23 = Z_to_bv 64 AMAGICv /\ getr r 24 = Z_to_bv 64 65521
                       /\ getr r 11 = Z_to_bv 64 (adr0 + 5552 * Z.of_nat 0) /\ getr r 12 = Z_to_bv 64 len0
                       /\ getr r 14 = Z_to_bv 64 (fst (adler_blocks 0 ab PL))
                       /\ getr r 13 = Z_to_bv 64 (snd (adler_blocks 0 ab PL))
                       /\ lkeeps UKP regs r)).
    { eexists. split.
      - ld_amag F_17e2c D_17e2c.
        stepz F_17e30 D_17e30. stepz F_17e34 D_17e34.
        apply mst_refl.
      - rewrite adler_blocks_0. subst ab. unfold CK16, NEG, AMAGICv. post. }
    cbv beta. intros r1 (HCK1 & S2 & S23 & S24 & S11 & S12 & S14 & S13 & K1).
    destruct (ublk_loop spv Hspv Hs16 Hs8 c r1 0 ab len0 HCK1 S2 S23 S24 S11 S12 S14 S13
                ltac:(subst ab; cbn [fst]; lia) ltac:(subst ab; cbn [snd]; lia) ltac:(lia) ltac:(lia))
      as (r2 & M2 & A2 & B2 & C2 & N2 & K2).
    cbn [Nat.add] in A2, B2, C2.
    set (ab1 := adler_blocks (S c) ab PL) in *.
    pose proof (adler_blocks_bound16 (S c) (lo16 a) (hi16 a) PL Hlo Hhi) as Hb16. fold ab ab1 in Hb16.
    destruct Hb16 as [Hb1 Hb2].
    set (p := adr0 + 5552 * Z.of_nat (S c)) in *.
    set (rem := len0 - 5552 * Z.of_nat (S c)) in *.
    assert (Hrem : 0 <= rem < 5552) by (subst rem; lia).
    replace (len0 - 5552 * Z.of_nat (S c)) with rem in N2 by reflexivity.
    assert (Hrest : skipn (Z.to_nat (NMAX * nb)) PL = BS p (Z.to_nat rem)).
    { rewrite <- Hc. rewrite (adler_rest_bytes (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m adr0 (Z.to_nat len0) (S c)) by lia.
      subst p rem. f_equal. unfold NMAX. lia. }
    destruct (Z.eq_dec rem 0) as [Hz | Hnz].
    - (* [comment removed for export] *)
      rewrite <- (adler_long_exit_nil a PL); cycle 1.
      { rewrite Zlen_bytes_at. lia. }
      { rewrite Hnbl, Hrest, Hz. reflexivity. }
      cbv zeta. rewrite Hnbl, <- Hc, Nat2Z.id. fold ab. fold ab1.
      eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x18294 : word) m rom)
               (fun r => getr r 14 = Z_to_bv 64 (fst ab1) /\ getr r 13 = Z_to_bv 64 (snd ab1) /\ lkeeps UKP r1 r)).
      { eexists. split.
        - eapply msteps_trans; [exact M2|].
          stepb_tk F_17fa0 D_17fa0 ltac:(condZ). apply mst_refl.
        - postK. }
      cbv beta. intros r3 (T14 & T13 & K3).
      destruct (ucomb_run m rom r3 _ _ T14 T13) as (r4 & M4 & V4 & K4).
      exists r4. split; [exact M4 | split; [exact V4 | kp_chain]].
    - rewrite <- (adler_long_exit_cons a PL (BS p (Z.to_nat rem))); cycle 1.
      { rewrite Zlen_bytes_at. lia. }
      { rewrite Hnbl. exact Hrest. }
      { intros E. apply (f_equal (@length Z)) in E. rewrite bytes_at_length in E. cbn in E. lia. }
      cbv zeta. rewrite Hnbl, <- Hc, Nat2Z.id. fold ab. fold ab1.
      destruct (Z.lt_ge_cases rem 16) as [Hsmall | Hbig].
      + (* [comment removed for export] *)
        eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x1822c : word) m rom)
                 (fun r => getr r 11 = Z_to_bv 64 (p + Z.of_nat 0)
                           /\ getr r 12 = Z_to_bv 64 rem
                           /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab1 (BS p 0)))
                           /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab1 (BS p 0))) /\ lkeeps UKP r1 r)).
        { eexists. split.
          - eapply msteps_trans; [exact M2|].
            stepb_ft F_17fa0 D_17fa0 ltac:(condZ).
            stepz F_17fa4 D_17fa4.
            stepb_tk F_17fa8 D_17fa8 ltac:(condZ).
            apply mst_refl.
          - rewrite adler_fold_bytes_0. postK. }
        cbv beta. intros r3 (T11 & T12 & T14 & T13 & K3).
        destruct (utail8_run r3 ab1 p 0 rem T11 T12 T14 T13 ltac:(lia) ltac:(lia) ltac:(lia) Hb1 Hb2 ltac:(unfold NMAX; lia))
          as (r4 & M4 & V4 & K4).
        exists r4. split; [exact M4 | split; [rewrite V4; reflexivity | kp_chain]].
      + (* [comment removed for export] *)
        pose proof (Z.div_mod rem 16 ltac:(lia)) as Hdm2. pose proof (Z.mod_pos_bound rem 16 ltac:(lia)) as Hmb2.
        assert (Hq2 : 1 <= rem / 16) by (apply Z.div_le_lower_bound; lia).
        set (k := Z.to_nat (rem / 16 - 1)).
        assert (Hk : Z.of_nat (S k) = rem / 16) by (subst k; lia).
        eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x180d0 : word) m rom)
                 (fun r => getr r 11 = Z_to_bv 64 (p + Z.of_nat 0)
                           /\ getr r 12 = Z_to_bv 64 (16 * Z.of_nat (S k) + rem mod 16)
                           /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab1 (BS p 0)))
                           /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab1 (BS p 0))) /\ lkeeps UKP r1 r)).
        { eexists. split.
          - eapply msteps_trans; [exact M2|].
            stepb_ft F_17fa0 D_17fa0 ltac:(condZ).
            stepz F_17fa4 D_17fa4.
            stepb_ft F_17fa8 D_17fa8 ltac:(condZ).
            apply mst_refl.
          - rewrite adler_fold_bytes_0. postK. }
        cbv beta. intros r3 (T11 & T12 & T14 & T13 & K3).
        destruct (uck_run r3 _ _ _ _ T11 T12 T14 T13) as (r4 & M4 & HCK4 & S21 & U11 & U12 & U14 & U13 & K4).
        destruct (ud16_loop m rom adr0 len0 Hrd Hnw Ha0 k r4 ab1 p 0 (rem mod 16) HCK4 U11 U14 U13 U12 S21
                    ltac:(lia) ltac:(lia) ltac:(lia)) as (r5 & M5 & A5 & B5 & P5 & D5 & N5 & E5 & K5).
        destruct (utail_run r5 ab1 p (0 + 16 * S k) (rem mod 16)
                    ltac:(rewrite D5; zbv) N5 A5 B5 ltac:(lia) ltac:(lia) ltac:(lia) Hb1 Hb2 ltac:(unfold NMAX; lia))
          as (r6 & M6 & V6 & K6).
        exists r6. split; [|split].
        * eapply msteps_trans; [exact M4|]. eapply msteps_trans; [exact M5 | exact M6].
        * rewrite V6. replace (0 + 16 * S k + Z.to_nat (rem mod 16))%nat with (Z.to_nat rem) by lia. reflexivity.
        * kp_chain.
  Qed.
End UADLB.
