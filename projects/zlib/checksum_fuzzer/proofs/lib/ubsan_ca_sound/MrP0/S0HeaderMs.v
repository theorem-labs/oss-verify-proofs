(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import RunCtx.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import ModelAmb.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.World Require Import Src_zlib_checksum_fuzzer_repro.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  S0ReadBase S0TargetPre S0Header_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

#[local] Abbreviation RSEGS := Src_zlib_checksum_fuzzer_repro.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition sr_HA : list expr :=
  [ELit 0; J 1; spx (-128); J 3; J 4; J 5; J 6; J 7;
   J 8; EVar 2; J 10; J 11; J 12; J 13; J 14; J 15;
   J 16; J 17; J 18; EVar 3; J 20; J 21; J 22; J 23;
   J 24; J 25; J 26; J 27; J 28; J 29; J 30; J 31].

Definition kn_HA : list kentry :=
  [KRange (EVar 2) 0x51000 0x7fffff800000; KRange (EVar 3) 6 67108863;
   KWord (SA (EVar 2) 0) 1 (EVar 6); KWord (SA (EVar 2) 1) 1 (EVar 7);
   KRange (EVar 6) 0 255; KRange (EVar 7) 0 255].

Definition hkA' {RCa1 : RunCtx}  := Eval vm_compute in runh scr_fall (SS 0x13e4c sr_HA [] kn_HA NXh).

Lemma hdrA_itinerary_ok {RCa1 : RunCtx}  :
  s_pc (fst (fst hkA')) = 0x14020%Z /\ s_log (fst (fst hkA')) = [] /\ s_next (fst (fst hkA')) = 47%nat
  /\ nth 11 (s_regs (fst (fst hkA'))) (ELit 0) = cfglen_x.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma w2le1_byte : forall (x : byte), word_to_le_bytes 1 (Z_to_bv 64 (bv_unsigned x)) = [x].
Proof.
  intros x. pose proof (bv_unsigned_in_range _ x) as Hx. change (bv_modulus 8) with 256%Z in Hx.
  unfold word_to_le_bytes. cbn [Z_to_le_bytes]. f_equal.
  rewrite u_small by lia. apply Z_to_bv_bv_unsigned.
Qed.

Section HDR.
Context {RCa1 : RunCtx}.
  Variables (R : bvmap 5 word) (M rom : word -> option byte) (sp0 buf : Z) (content : list byte).
  Let L : Z := Z.of_nat (length content).
  Hypothesis R2 : getr R 2 = Z_to_bv 64 (sp0 - 128).
  Hypothesis R9 : getr R 9 = Z_to_bv 64 buf.
  Hypothesis R19 : getr R 19 = Z_to_bv 64 L.
  Hypothesis SP0 : (0x7fff80000000 <= sp0 <= 0x800000000000)%Z.
  Hypothesis HB : (0x51000 <= buf)%Z.
  Hypothesis HBL : (buf + L <= 0x7fffff800000)%Z.
  Hypothesis HL : (6 + hdr_cfglen content <= L < 2 ^ 26)%Z.
  Hypothesis Hcont : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 buf) (length content) = Some content.

  Definition valsA : list word :=
    [Z_to_bv 64 sp0; Z_to_bv 64 0; Z_to_bv 64 buf; Z_to_bv 64 L; Z_to_bv 64 0; Z_to_bv 64 0;
     Z_to_bv 64 (hdr_b0 content); Z_to_bv 64 (hdr_b1 content); Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0] ++ junk_vals R.

  Lemma content_byte : forall j, (j < length content)%nat ->
    rdn (run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (buf + Z.of_nat j)) 1%nat
    = Some (word_to_le_bytes 1 (Z_to_bv 64 (bv_unsigned (nth j content (Z_to_bv 8 0))))).
  Proof.
    intros j Hj. pose proof (rdn_nth (run_segments RSEGS rc_inp rc_sp rc_mb) M (length content) _ content j Hcont Hj) as H.
    rewrite w_add_nat in H. rewrite u_small in H by lia. rewrite w2le1_byte. exact H.
  Qed.

  Lemma hdrA_sym : regs_ok (ENVh content valsA) sr_HA R /\ know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) (ENVh content valsA) M kn_HA.
  Proof.
    set (E := ENVh content valsA).
    assert (E0 : ev E 0 = Z_to_bv 64 sp0) by reflexivity.
    assert (E2 : ev E 2 = Z_to_bv 64 buf) by reflexivity.
    assert (E3 : ev E 3 = Z_to_bv 64 L) by reflexivity.
    assert (E6 : ev E 6 = Z_to_bv 64 (hdr_b0 content)) by reflexivity.
    assert (E7 : ev E 7 = Z_to_bv 64 (hdr_b1 content)) by reflexivity.
    assert (EJ : forall i, (i < 32)%nat -> ev E (11 + i) = getr R (Z_to_bv 5 (Z.of_nat i))).
    { intros i Hi. unfold E, ENVh, valsA. cbn [ev]. unfold vals_ev.
      change (11 + i)%nat with (length [Z_to_bv 64 sp0; Z_to_bv 64 0; Z_to_bv 64 buf; Z_to_bv 64 L; Z_to_bv 64 0; Z_to_bv 64 0;
                                        Z_to_bv 64 (hdr_b0 content); Z_to_bv 64 (hdr_b1 content); Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0] + i)%nat.
      rewrite app_nth2_plus. unfold junk_vals. rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi.
      reflexivity. }
    split.
    - apply S0ReadBase.regs_ok_by_index. intros i Hi.
      destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
        cbn [nth sr_HA S0ReadBase.all_regs].
      all: try (lazymatch goal with |- _ = edenot _ (J ?n) =>
                  unfold J; change (edenot E (EVar (11 + n))) with (ev E (11 + n)%nat); rewrite EJ by lia; reflexivity end).
      all: try (lazymatch goal with |- _ = edenot _ (spx ?z) =>
                  unfold spx; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot]; rewrite E0;
                  rewrite R2; rewrite u_small by lia; f_equal; lia end).
      all: try (change (edenot E (EVar 2)) with (ev E 2); rewrite E2; assumption).
      all: try (change (edenot E (EVar 3)) with (ev E 3); rewrite E3; assumption).
      all: cbn [edenot]; first [assumption | apply getr_zero | reflexivity].
    - pose proof (bv_unsigned_in_range _ (nth 0 content (Z_to_bv 8 0))) as B0.
      pose proof (bv_unsigned_in_range _ (nth 1 content (Z_to_bv 8 0))) as B1.
      change (bv_modulus 8) with 256%Z in B0, B1.
      pose proof (hdr_cfglen_range content) as CR.
      unfold kn_HA. repeat apply Forall_cons; try apply Forall_nil.
      + apply krange_intro. change (edenot E (EVar 2)) with (ev E 2). rewrite E2. rewrite u_small by lia. lia.
      + apply krange_intro. change (edenot E (EVar 3)) with (ev E 3). rewrite E3. rewrite u_small by lia. lia.
      + cbn [kentry_ok]. split; [lia|]. split; [apply flat_intro; change (edenot E (EVar 2)) with (ev E 2); rewrite ?E2; rewrite ?u_small by lia; lia|].
        unfold adenot, v_addi. cbn [a_base a_off edenot]. change (ev E 2) with (Z_to_bv 64 buf).
        change (ev E 6) with (Z_to_bv 64 (hdr_b0 content)). unfold hdr_b0. rewrite u_small by lia.
        replace (buf + 0)%Z with (buf + Z.of_nat 0)%Z by lia.
        apply content_byte. lia.
      + cbn [kentry_ok]. split; [lia|]. split; [apply flat_intro; change (edenot E (EVar 2)) with (ev E 2); rewrite ?E2; rewrite ?u_small by lia; lia|].
        unfold adenot, v_addi. cbn [a_base a_off edenot]. change (ev E 2) with (Z_to_bv 64 buf).
        change (ev E 7) with (Z_to_bv 64 (hdr_b1 content)). unfold hdr_b1. rewrite u_small by lia.
        replace (buf + 1)%Z with (buf + Z.of_nat 1)%Z by lia.
        apply content_byte. lia.
      + apply krange_intro. change (edenot E (EVar 6)) with (ev E 6). rewrite E6. unfold hdr_b0. rewrite u_small by lia. lia.
      + apply krange_intro. change (edenot E (EVar 7)) with (ev E 7). rewrite E7. unfold hdr_b1. rewrite u_small by lia. lia.
  Qed.

  Theorem header_ok_ms :
    exists R',
      msteps (run_segments RSEGS rc_inp rc_sp rc_mb) (mkst R (Z_to_bv 64 0x13e4c) M rom) (mkst R' (Z_to_bv 64 0x14020) M rom)
      /\ getr R' 1 = Z_to_bv 64 0x13ec4 /\ getr R' 2 = Z_to_bv 64 (sp0 - 128)
      /\ getr R' 10 = Z_to_bv 64 (buf + 2) /\ getr R' 11 = Z_to_bv 64 (hdr_cfglen content)
      /\ getr R' 12 = Z_to_bv 64 (buf + 6 + hdr_cfglen content) /\ getr R' 13 = Z_to_bv 64 (hdr_paylen content)
      /\ getr R' 8 = Z_to_bv 64 (buf + 2) /\ getr R' 9 = Z_to_bv 64 buf
      /\ getr R' 18 = Z_to_bv 64 (hdr_cfglen content) /\ getr R' 19 = Z_to_bv 64 (buf + 6 + hdr_cfglen content)
      /\ getr R' 20 = Z_to_bv 64 (hdr_paylen content)
      /\ getr R' 21 = Z_to_bv 64 (if (hdr_b1 content <? 128)%Z then hdr_b1 content else hdr_b1 content - 256 + 2 ^ 64)%Z
      /\ (forall r : reg, In r [3; 4; 22; 23; 24; 25; 26; 27]%bv -> getr R' r = getr R r).
  Proof.
    destruct hdrA_sym as [HR HK].
    pose proof (hdr_cfglen_range content) as CR.
    pose proof (bv_unsigned_in_range _ (nth 1 content (Z_to_bv 8 0))) as B1. change (bv_modulus 8) with 256%Z in B1.
    set (cb := fun i : nat => Z_to_bv 64 (bv_unsigned (nth (Z.to_nat (hdr_cfglen content) + 2 + i) content (Z_to_bv 8 0)))).
    assert (HL0 : length valsA = 43%nat) by (unfold valsA; rewrite length_app, junk_vals_length; reflexivity).
    pose proof (env_app_regs valsA [cb 1%nat; cb 0%nat; cb 2%nat; cb 3%nat] (blobs_ev [content]) sr_HA R
                  ltac:(rewrite HL0; vm_compute; reflexivity) HR) as HR1.
    pose proof (env_app_know (run_segments RSEGS rc_inp rc_sp rc_mb) valsA [cb 1%nat; cb 0%nat; cb 2%nat; cb 3%nat] (blobs_ev [content]) M kn_HA
                  ltac:(rewrite HL0; vm_compute; reflexivity) HK) as HK1.
    clear HR HK.
    set (vals := valsA ++ [cb 1%nat; cb 0%nat; cb 2%nat; cb 3%nat]) in *.
    change (Env (vals_ev vals) (blobs_ev [content])) with (ENVh content vals) in HR1, HK1.
    rename HR1 into HR. rename HK1 into HK.
    assert (P0 : vals_ev vals 0 = Z_to_bv 64 sp0) by reflexivity.
    assert (P2 : vals_ev vals 2 = Z_to_bv 64 buf) by reflexivity.
    assert (P3 : vals_ev vals 3 = Z_to_bv 64 L) by reflexivity.
    assert (P6 : vals_ev vals 6 = Z_to_bv 64 (hdr_b0 content)) by reflexivity.
    assert (P7 : vals_ev vals 7 = Z_to_bv 64 (hdr_b1 content)) by reflexivity.
    assert (PB41 : vals_ev vals 43 = cb 1%nat).
    { unfold vals. replace 43%nat with (length valsA + 0)%nat by (rewrite HL0; reflexivity). rewrite vals_ev_app_r. reflexivity. }
    assert (PB42 : vals_ev vals 44 = cb 0%nat).
    { unfold vals. replace 44%nat with (length valsA + 1)%nat by (rewrite HL0; reflexivity). rewrite vals_ev_app_r. reflexivity. }
    assert (PB43 : vals_ev vals 45 = cb 2%nat).
    { unfold vals. replace 45%nat with (length valsA + 2)%nat by (rewrite HL0; reflexivity). rewrite vals_ev_app_r. reflexivity. }
    assert (PB44 : vals_ev vals 46 = cb 3%nat).
    { unfold vals. replace 46%nat with (length valsA + 3)%nat by (rewrite HL0; reflexivity). rewrite vals_ev_app_r. reflexivity. }
    assert (EJ : forall i, (i < 32)%nat -> vals_ev vals (11 + i) = getr R (Z_to_bv 5 (Z.of_nat i))).
    { intros i Hi. unfold vals. rewrite vals_ev_app_l by (rewrite HL0; lia). unfold valsA, vals_ev.
      change (11 + i)%nat with (length [Z_to_bv 64 sp0; Z_to_bv 64 0; Z_to_bv 64 buf; Z_to_bv 64 L; Z_to_bv 64 0; Z_to_bv 64 0;
                                        Z_to_bv 64 (hdr_b0 content); Z_to_bv 64 (hdr_b1 content); Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0] + i)%nat.
      rewrite app_nth2_plus. unfold junk_vals. rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity. }
    clearbody vals.
    pose proof (cfglen_val content vals P6 P7) as CV.
    assert (CB : forall i, (i < 4)%nat ->
      rdn (run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (buf + hdr_cfglen content + 2 + Z.of_nat i)) 1%nat
      = Some [nth (Z.to_nat (hdr_cfglen content) + 2 + i) content (Z_to_bv 8 0)]).
    { intros i Hi.
      replace (buf + hdr_cfglen content + 2 + Z.of_nat i)%Z
        with (buf + Z.of_nat (Z.to_nat (hdr_cfglen content) + 2 + i))%Z by lia.
      rewrite content_byte by (unfold L in HL; lia). rewrite w2le1_byte. reflexivity. }
    destruct (run_sound (run_segments RSEGS rc_inp rc_sp rc_mb) FUELh STOPSh scr_fall 0x13e4c sr_HA kn_HA NXh (fst (fst hkA')) (snd (fst hkA')) (snd hkA')
                (ENVh content vals) M rom R ltac:(reflexivity) HR HK) as (R' & HR' & _ & HMS).
    { let v := eval vm_compute in (snd (fst hkA')) in change (snd (fst hkA')) with v.
      split_foralls.
      all: try (unfold sc_denot; fold cfglen_x).
      all: try (lazymatch goal with
                | |- branch_taken _ _ _ = false =>
                    cbn [edenot]; rewrite CV; change (ev (ENVh content vals) 3) with (vals_ev vals 3); rewrite P3;
                    rewrite alu_add; unfold v_add; cbn [branch_taken]; unfold bv_ltu;
                    rewrite (u_small (hdr_cfglen content)) by lia; change (bv_unsigned (Z_to_bv 64 6)) with 6%Z;
                    rewrite !u_small by (unfold L in *; lia); apply Z.ltb_ge; unfold L in *; lia
                end).
      all: try (lazymatch goal with
                | |- exists bs, rdn _ _ (adenot _ (SA _ ?o)) 1 = Some bs /\ _ =>
                    let i := eval vm_compute in (Z.to_nat (o - 2)) in
                    eexists; split;
                    [ unfold adenot, v_addi; cbn [a_base a_off edenot]; rewrite CV;
                      change (ev (ENVh content vals) 2) with (vals_ev vals 2); rewrite P2;
                      rewrite alu_add; unfold v_add;
                      rewrite (u_small (hdr_cfglen content)) by lia; rewrite (u_small buf) by lia; rewrite !u_small by (unfold L in *; lia);
                      replace (buf + hdr_cfglen content + o)%Z
                        with (buf + hdr_cfglen content + 2 + Z.of_nat i)%Z by lia;
                      apply (CB i); lia
                    | lazymatch goal with |- _ = edenot _ (EVar ?n) => change (edenot (ENVh content vals) (EVar n)) with (vals_ev vals n) end;
                      first [rewrite PB41 | rewrite PB42 | rewrite PB43 | rewrite PB44];
                      unfold cb, extz; cbn [bytes_le_to_Z Z.shiftl]; rewrite Z.lor_0_r; reflexivity ]
                | |- flat _ (SA _ ?o) _ =>
                    unfold flat, estart, elenZ; cbn [a_base a_off]; fold cfglen_x; cbn [edenot]; rewrite CV;
                    change (ev (ENVh content vals) 2) with (vals_ev vals 2); rewrite P2;
                    rewrite alu_add; unfold v_add; rewrite (u_small (hdr_cfglen content)) by lia; rewrite (u_small buf) by lia;
                    rewrite !u_small by (unfold L in *; lia); unfold L in *; lia
                end). }
    assert (A6 : edenot (ENVh content vals) (EAlu ALU_ADD (EAlu ALU_ADD (EVar 2) cfglen_x) (ELit 6))
                  = Z_to_bv 64 (buf + 6 + hdr_cfglen content)).
    { cbn [edenot]. rewrite CV. change (ev (ENVh content vals) 2) with (vals_ev vals 2); rewrite P2.
      rewrite !alu_add. unfold v_add. rewrite (alu_add (Z_to_bv 64 buf)). unfold v_add.
      rewrite (u_small (hdr_cfglen content)) by lia. rewrite (u_small buf) by lia.
      rewrite (u_small (buf + hdr_cfglen content)) by (unfold L in *; lia). change (bv_unsigned (Z_to_bv 64 6)) with 6%Z.
      f_equal. lia. }
    assert (APL : edenot (ENVh content vals) (EAlu ALU_ADD (EAlu ALU_ADD (EVar 3) (EMd M_MUL (ELit (-1)) cfglen_x)) (ELit (-6)))
                  = Z_to_bv 64 (hdr_paylen content)).
    { cbn [edenot]. rewrite CV. change (ev (ENVh content vals) 3) with (vals_ev vals 3); rewrite P3.
      rewrite !alu_add, m_mul. unfold v_add, v_mul. rewrite ?alu_add. unfold v_add.
      apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
      unfold L in *. rewrite (Z.mod_small (Z.of_nat (length content))), (Z.mod_small (hdr_cfglen content)) by lia.
      change ((-1) mod 2 ^ 64)%Z with 18446744073709551615%Z. change ((-6) mod 2 ^ 64)%Z with 18446744073709551610%Z.
      rewrite Zplus_mod_idemp_l.
      replace (Z.of_nat (length content) + (18446744073709551615 * hdr_cfglen content) mod 2 ^ 64 + 18446744073709551610)%Z
        with (Z.of_nat (length content) + 18446744073709551610 + (18446744073709551615 * hdr_cfglen content) mod 2 ^ 64)%Z by lia.
      rewrite Zplus_mod_idemp_r.
      apply (mod_eq_shift _ _ (hdr_cfglen content + 1)); [lia|]. unfold hdr_paylen. lia. }
    assert (A2 : edenot (ENVh content vals) (EAlu ALU_ADD (EVar 2) (ELit 2)) = Z_to_bv 64 (buf + 2)).
    { rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot]. change (ev (ENVh content vals) 2) with (vals_ev vals 2).
      rewrite P2. rewrite u_small by lia. reflexivity. }
    exists R'.
    destruct hdrA_itinerary_ok as (Epc & Elog & _ & _).
    split. { rewrite Epc, Elog in HMS. cbn [mem_denot] in HMS. exact HMS. }
    repeat split.
    - regv HR' (1 : reg). reflexivity.
    - regv HR' (2 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot]. change (ev (ENVh content vals) 0) with (vals_ev vals 0).
      rewrite P0. rewrite u_small by lia. f_equal; lia.
    - regv HR' (10 : reg). exact A2.
    - regv HR' (11 : reg). exact CV.
    - regv HR' (12 : reg). exact A6.
    - regv HR' (13 : reg). exact APL.
    - regv HR' (8 : reg). exact A2.
    - regv HR' (9 : reg). change (edenot (ENVh content vals) (EVar 2)) with (vals_ev vals 2). rewrite P2. reflexivity.
    - regv HR' (18 : reg). exact CV.
    - regv HR' (19 : reg). exact A6.
    - regv HR' (20 : reg). exact APL.
    - regv HR' (21 : reg). change (edenot (ENVh content vals) (EExt true 0 1 (EVar 7))) with (sx8F (vals_ev vals 7)).
      rewrite P7. apply sx8F_val. unfold hdr_b1. lia.
    - intros r Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<-|Hr];
        [ lazymatch goal with |- getr R' ?rr = _ =>
            regv HR' rr;
            lazymatch goal with |- edenot _ (EVar ?n) = _ =>
              change (edenot (ENVh content vals) (EVar n)) with (vals_ev vals n);
              let k := eval vm_compute in (n - 11)%nat in
              change n with (11 + k)%nat; rewrite EJ by lia; f_equal; apply bv_eq; reflexivity end end |]).
      destruct Hr.
  Qed.
End HDR.
