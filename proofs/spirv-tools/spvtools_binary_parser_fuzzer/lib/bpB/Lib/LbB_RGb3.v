(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsStack0.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_RGl LbB_RGb2.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Lemma rg_b2_c : forall (x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (ff sph D N lo : Z),
  9 <= N <= 36 -> 1 <= D -> D + N <= 2 ^ 47 ->
  ff mod 64 = 0 -> 0x6e8000 <= ff -> ff + 128 <= 2 ^ 47 ->
  (ff + 128 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
  sph mod 32 = 0 -> 2 ^ 45 <= sph <= 2 ^ 47 ->
  wr_at asegs m ff 128 -> wr_at asegs m (sh ff) 16 -> stk asegs m lo sph -> lo <= sph - 2592 -> ff + 128 <= lo ->
  mem_inv asegs m -> ACONST m ->
  exists R' M',
    CatSim.msteps asegs
      (MS (mkR (Z_to_bv 64 CS_SM_RET2) (Z_to_bv 64 (sph - 2592)) x3 x4 x5 x6 x7 (Z_to_bv 64 (sph - 2528)) (Z_to_bv 64 (sph - 2592))
               (Z_to_bv 64 ff) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 N) (Z_to_bv 64 D) (Z_to_bv 64 0x7fff8000)
               x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 CS_SM_RET2) fc None m ro)
      (MS R' F (Z_to_bv 64 LH_HEAD) fc None M' ro)
    /\ getr R' 19 = Z_to_bv 64 (D + (5)) /\ getr R' 15 = Z_to_bv 64 0 /\ getr R' 16 = Z_to_bv 64 (N - 5)
    /\ getr R' 5 = Z_to_bv 64 (2 ^ 64 - 1 - (D + (5)))
    /\ getr R' 20 = Z_to_bv 64 0x7fff8000 /\ getr R' 10 = Z_to_bv 64 ff /\ getr R' 13 = Z_to_bv 64 (sh ff) /\ getr R' 14 = Z_to_bv 64 ff
    /\ getr R' 1 = Z_to_bv 64 CS_SM_RET2 /\ getr R' 2 = Z_to_bv 64 (sph - 2592) /\ getr R' 3 = x3 /\ getr R' 4 = x4
    /\ getr R' 8 = Z_to_bv 64 (sph - 2528) /\ getr R' 9 = Z_to_bv 64 (sph - 2592) /\ getr R' 18 = Z_to_bv 64 N
    /\ getr R' 21 = x21 /\ getr R' 22 = x22 /\ getr R' 23 = x23 /\ getr R' 24 = x24 /\ getr R' 25 = x25 /\ getr R' 26 = x26 /\ getr R' 27 = x27
    /\ munch [(ff, ff + 72); (sh ff, sh ff + 12); (sph - 2584, sph - 2576)] m M' /\ wmono asegs m M' /\ mem_inv asegs M'
    /\ stk asegs M' lo sph.
Proof.
  intros until lo. intros HN HD0 HD1 F64 FLO FHI FB SP32 SPR WF WS ST LO FST MI AC.
  assert (HQ : ff = 64 * (ff / 64)) by (pose proof (Z.div_mod ff 64 ltac:(lia)); lia).
  assert (HSH : sh ff = 8 * (ff / 64) + SHBASE) by (rewrite q8sh by lia; reflexivity).
  pose proof HSH as HSHu. unfold SHBASE in HSHu.
  remember (mkR (Z_to_bv 64 CS_SM_RET2) (Z_to_bv 64 (sph - 2592)) x3 x4 x5 x6 x7 (Z_to_bv 64 (sph - 2528)) (Z_to_bv 64 (sph - 2592)) (Z_to_bv 64 ff) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 N) (Z_to_bv 64 D) (Z_to_bv 64 0x7fff8000) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.
  assert (S2 : getr R 2 = Z_to_bv 64 (sph - 2592)) by (rewrite HR0; reflexivity).
  assert (S8 : getr R 8 = Z_to_bv 64 (sph - 2528)) by (rewrite HR0; reflexivity).
  assert (S9 : getr R 9 = Z_to_bv 64 (sph - 2592)) by (rewrite HR0; reflexivity).
  assert (S10 : getr R 10 = Z_to_bv 64 ff) by (rewrite HR0; reflexivity).
  assert (S18 : getr R 18 = Z_to_bv 64 N) by (rewrite HR0; reflexivity).
  assert (S19 : getr R 19 = Z_to_bv 64 D) by (rewrite HR0; reflexivity).
  assert (S20 : getr R 20 = Z_to_bv 64 SHBASE) by (rewrite HR0; reflexivity).
  pose (E := Eseed R [Z_to_bv 64 sph; Z_to_bv 64 (ff / 64); Z_to_bv 64 D; Z_to_bv 64 N]).
  assert (E32 : bv_unsigned (edenot E (EVar 32)) = sph) by (evs; rewrite u64_of_Z by lia; reflexivity).
  assert (EFF : bv_unsigned (edenot E (EMd M_MUL (ELit 64) (EVar 33))) = ff)
    by (evs; rewrite rg_zmul, <- HQ, u64_of_Z by lia; reflexivity).
  assert (ESH : bv_unsigned (edenot E (EMd M_MUL (ELit 8) (EVar 33))) = 8 * (ff / 64))
    by (evs; rewrite rg_zmul, u64_of_Z by lia; reflexivity).
  assert (HR : regs_ok E (srs sr_id [(2%bv, EAlu ALU_ADD (EVar 32) (ELit (-2592))); (8%bv, EAlu ALU_ADD (EVar 32) (ELit (-2528)));
                                     (9%bv, EAlu ALU_ADD (EVar 32) (ELit (-2592))); (10%bv, EMd M_MUL (ELit 64) (EVar 33));
                                     (18%bv, EVar 35); (19%bv, EVar 34); (20%bv, ELit SHBASE)]) R).
  { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X);
      first [rewrite S2 | rewrite S8 | rewrite S9 | rewrite S10 | rewrite S18 | rewrite S19 | rewrite S20];
      evs; rewrite ?rg_zadd, ?rg_zmul, <- ?HQ; first [reflexivity | f_equal; lia]. }
  assert (HK : know_ok asegs E m
     [ KImg 0x10000 0x91000;
       KWr (SA (EMd M_MUL (ELit 64) (EVar 33)) 0) (ELit 128);
       KWr (SA (EMd M_MUL (ELit 8) (EVar 33)) SHBASE) (ELit 16);
       KWr (SA (EVar 32) (-2592)) (ELit 2592);
       KRange (EVar 32) (2 ^ 45) (2 ^ 47);
       KRange (EVar 33) 1 (2 ^ 41);
       KRange (EVar 34) 1 (2 ^ 47);
       KRange (EVar 35) 9 36;
       KWord (SA (ELit 0) FIVE_SH) 1 (ELit 0) ]).
  { unfold know_ok.
    apply Forall_cons; [apply kimg_of_mem_inv; [exact MI | lia | lia]|].
    apply Forall_cons.
    { eapply kwr_of_wr_at; [exact WF | unfold estart; cbn [a_base a_off]; rewrite EFF; lia
        | unfold estart, elenZ; cbn [a_base a_off]; rewrite EFF; evs; rewrite u64_of_Z by lia; lia
        | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
    apply Forall_cons.
    { eapply kwr_of_wr_at; [exact WS | unfold estart; cbn [a_base a_off]; rewrite ESH; lia
        | unfold estart, elenZ; cbn [a_base a_off]; rewrite ESH; evs; rewrite u64_of_Z by lia; lia
        | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
    apply Forall_cons.
    { eapply kwr_of_stk; [exact ST | unfold estart; cbn [a_base a_off]; rewrite E32; lia
        | unfold estart, elenZ; cbn [a_base a_off]; rewrite E32; evs; rewrite u64_of_Z by lia; lia
        | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
    do 4 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
    apply Forall_cons; [apply five_sh; exact AC|].
    apply Forall_nil. }
  xrun_at (PropExec.mkFP F fc) asegs R CS_SM_RET2 m ro HR HK 120%nat [LH_HEAD] (SCR [] [] []) 36%N.
  { first [apply Forall_nil | split_scs].
    all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; rewrite ?rg_zmul, ?rg_zadd, ?rg_br_ge, ?u64_of_Z by lia;
      cbn [a_off a_base]; first [apply negb_false_iff, Z.ltb_lt; lia | lia]. }
  clear HK.
  lazymatch type of Hlf with log_flat _ ?lg =>
    lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
      change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
  exists R', M1. split; [exact Hms|].
  rreg HR' 19%bv G19.
  rreg HR' 15%bv G15.
  rreg HR' 16%bv G16.
  rreg HR' 5%bv G5.
  rreg HR' 20%bv G20.
  rreg HR' 10%bv G10.
  rreg HR' 13%bv G13.
  rreg HR' 14%bv G14.
  rreg HR' 1%bv G1.
  rreg HR' 2%bv G2.
  rreg HR' 3%bv G3.
  rreg HR' 4%bv G4.
  rreg HR' 8%bv G8.
  rreg HR' 9%bv G9.
  rreg HR' 18%bv G18.
  rreg HR' 21%bv G21.
  rreg HR' 22%bv G22.
  rreg HR' 23%bv G23.
  rreg HR' 24%bv G24.
  rreg HR' 25%bv G25.
  rreg HR' 26%bv G26.
  rreg HR' 27%bv G27.
  split; [rewrite G19; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G15; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G16; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G5; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G20; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G10; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G13; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G14; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G1; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G2; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G3; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G4; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G8; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G9; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G18; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G21; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G22; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G23; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G24; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G25; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G26; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G27; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split.
  { subst M1. apply munch_mem_denot; [exact Hlf|].
    repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; cbn [a_base a_off]; rewrite ?EFF, ?ESH, ?E32;
                                cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
    apply Forall_nil. }
  split; [subst M1; apply wmono_mem_denot|].
  split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
  subst M1; apply stk_mem_denot; exact ST.
Qed.

Lemma rg_b2_d : forall (x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (ff sph D N lo : Z),
  37 <= N <= 2 ^ 26 -> 1 <= D -> D + N <= 2 ^ 47 ->
  ff mod 64 = 0 -> 0x6e8000 <= ff -> ff + 128 <= 2 ^ 47 ->
  (ff + 128 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
  sph mod 32 = 0 -> 2 ^ 45 <= sph <= 2 ^ 47 ->
  wr_at asegs m ff 128 -> wr_at asegs m (sh ff) 16 -> stk asegs m lo sph -> lo <= sph - 2592 -> ff + 128 <= lo ->
  mem_inv asegs m -> ACONST m ->
  exists R' M',
    CatSim.msteps asegs
      (MS (mkR (Z_to_bv 64 CS_SM_RET2) (Z_to_bv 64 (sph - 2592)) x3 x4 x5 x6 x7 (Z_to_bv 64 (sph - 2528)) (Z_to_bv 64 (sph - 2592))
               (Z_to_bv 64 ff) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 N) (Z_to_bv 64 D) (Z_to_bv 64 0x7fff8000)
               x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 CS_SM_RET2) fc None m ro)
      (MS R' F (Z_to_bv 64 LH_HEAD) fc None M' ro)
    /\ getr R' 19 = Z_to_bv 64 (D + (5)) /\ getr R' 15 = Z_to_bv 64 0 /\ getr R' 16 = Z_to_bv 64 (32)
    /\ getr R' 5 = Z_to_bv 64 (2 ^ 64 - 1 - (D + (5)))
    /\ getr R' 20 = Z_to_bv 64 0x7fff8000 /\ getr R' 10 = Z_to_bv 64 ff /\ getr R' 13 = Z_to_bv 64 (sh ff) /\ getr R' 14 = Z_to_bv 64 ff
    /\ getr R' 1 = Z_to_bv 64 CS_SM_RET2 /\ getr R' 2 = Z_to_bv 64 (sph - 2592) /\ getr R' 3 = x3 /\ getr R' 4 = x4
    /\ getr R' 8 = Z_to_bv 64 (sph - 2528) /\ getr R' 9 = Z_to_bv 64 (sph - 2592) /\ getr R' 18 = Z_to_bv 64 37
    /\ getr R' 21 = x21 /\ getr R' 22 = x22 /\ getr R' 23 = x23 /\ getr R' 24 = x24 /\ getr R' 25 = x25 /\ getr R' 26 = x26 /\ getr R' 27 = x27
    /\ munch [(ff, ff + 72); (sh ff, sh ff + 12); (sph - 2584, sph - 2576)] m M' /\ wmono asegs m M' /\ mem_inv asegs M'
    /\ stk asegs M' lo sph.
Proof.
  intros until lo. intros HN HD0 HD1 F64 FLO FHI FB SP32 SPR WF WS ST LO FST MI AC.
  assert (HQ : ff = 64 * (ff / 64)) by (pose proof (Z.div_mod ff 64 ltac:(lia)); lia).
  assert (HSH : sh ff = 8 * (ff / 64) + SHBASE) by (rewrite q8sh by lia; reflexivity).
  pose proof HSH as HSHu. unfold SHBASE in HSHu.
  remember (mkR (Z_to_bv 64 CS_SM_RET2) (Z_to_bv 64 (sph - 2592)) x3 x4 x5 x6 x7 (Z_to_bv 64 (sph - 2528)) (Z_to_bv 64 (sph - 2592)) (Z_to_bv 64 ff) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 N) (Z_to_bv 64 D) (Z_to_bv 64 0x7fff8000) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.
  assert (S2 : getr R 2 = Z_to_bv 64 (sph - 2592)) by (rewrite HR0; reflexivity).
  assert (S8 : getr R 8 = Z_to_bv 64 (sph - 2528)) by (rewrite HR0; reflexivity).
  assert (S9 : getr R 9 = Z_to_bv 64 (sph - 2592)) by (rewrite HR0; reflexivity).
  assert (S10 : getr R 10 = Z_to_bv 64 ff) by (rewrite HR0; reflexivity).
  assert (S18 : getr R 18 = Z_to_bv 64 N) by (rewrite HR0; reflexivity).
  assert (S19 : getr R 19 = Z_to_bv 64 D) by (rewrite HR0; reflexivity).
  assert (S20 : getr R 20 = Z_to_bv 64 SHBASE) by (rewrite HR0; reflexivity).
  pose (E := Eseed R [Z_to_bv 64 sph; Z_to_bv 64 (ff / 64); Z_to_bv 64 D; Z_to_bv 64 N]).
  assert (E32 : bv_unsigned (edenot E (EVar 32)) = sph) by (evs; rewrite u64_of_Z by lia; reflexivity).
  assert (EFF : bv_unsigned (edenot E (EMd M_MUL (ELit 64) (EVar 33))) = ff)
    by (evs; rewrite rg_zmul, <- HQ, u64_of_Z by lia; reflexivity).
  assert (ESH : bv_unsigned (edenot E (EMd M_MUL (ELit 8) (EVar 33))) = 8 * (ff / 64))
    by (evs; rewrite rg_zmul, u64_of_Z by lia; reflexivity).
  assert (HR : regs_ok E (srs sr_id [(2%bv, EAlu ALU_ADD (EVar 32) (ELit (-2592))); (8%bv, EAlu ALU_ADD (EVar 32) (ELit (-2528)));
                                     (9%bv, EAlu ALU_ADD (EVar 32) (ELit (-2592))); (10%bv, EMd M_MUL (ELit 64) (EVar 33));
                                     (18%bv, EVar 35); (19%bv, EVar 34); (20%bv, ELit SHBASE)]) R).
  { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X);
      first [rewrite S2 | rewrite S8 | rewrite S9 | rewrite S10 | rewrite S18 | rewrite S19 | rewrite S20];
      evs; rewrite ?rg_zadd, ?rg_zmul, <- ?HQ; first [reflexivity | f_equal; lia]. }
  assert (HK : know_ok asegs E m
     [ KImg 0x10000 0x91000;
       KWr (SA (EMd M_MUL (ELit 64) (EVar 33)) 0) (ELit 128);
       KWr (SA (EMd M_MUL (ELit 8) (EVar 33)) SHBASE) (ELit 16);
       KWr (SA (EVar 32) (-2592)) (ELit 2592);
       KRange (EVar 32) (2 ^ 45) (2 ^ 47);
       KRange (EVar 33) 1 (2 ^ 41);
       KRange (EVar 34) 1 (2 ^ 47);
       KRange (EVar 35) 37 (2 ^ 26);
       KWord (SA (ELit 0) FIVE_SH) 1 (ELit 0) ]).
  { unfold know_ok.
    apply Forall_cons; [apply kimg_of_mem_inv; [exact MI | lia | lia]|].
    apply Forall_cons.
    { eapply kwr_of_wr_at; [exact WF | unfold estart; cbn [a_base a_off]; rewrite EFF; lia
        | unfold estart, elenZ; cbn [a_base a_off]; rewrite EFF; evs; rewrite u64_of_Z by lia; lia
        | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
    apply Forall_cons.
    { eapply kwr_of_wr_at; [exact WS | unfold estart; cbn [a_base a_off]; rewrite ESH; lia
        | unfold estart, elenZ; cbn [a_base a_off]; rewrite ESH; evs; rewrite u64_of_Z by lia; lia
        | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
    apply Forall_cons.
    { eapply kwr_of_stk; [exact ST | unfold estart; cbn [a_base a_off]; rewrite E32; lia
        | unfold estart, elenZ; cbn [a_base a_off]; rewrite E32; evs; rewrite u64_of_Z by lia; lia
        | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
    do 4 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
    apply Forall_cons; [apply five_sh; exact AC|].
    apply Forall_nil. }
  xrun_at (PropExec.mkFP F fc) asegs R CS_SM_RET2 m ro HR HK 120%nat [LH_HEAD] (SCR [false] [] []) 36%N.
  { first [apply Forall_nil | split_scs].
    all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; rewrite ?rg_zmul, ?rg_zadd, ?rg_br_ge, ?u64_of_Z by lia;
      cbn [a_off a_base]; first [apply negb_false_iff, Z.ltb_lt; lia | lia]. }
  clear HK.
  lazymatch type of Hlf with log_flat _ ?lg =>
    lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
      change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
  exists R', M1. split; [exact Hms|].
  rreg HR' 19%bv G19.
  rreg HR' 15%bv G15.
  rreg HR' 16%bv G16.
  rreg HR' 5%bv G5.
  rreg HR' 20%bv G20.
  rreg HR' 10%bv G10.
  rreg HR' 13%bv G13.
  rreg HR' 14%bv G14.
  rreg HR' 1%bv G1.
  rreg HR' 2%bv G2.
  rreg HR' 3%bv G3.
  rreg HR' 4%bv G4.
  rreg HR' 8%bv G8.
  rreg HR' 9%bv G9.
  rreg HR' 18%bv G18.
  rreg HR' 21%bv G21.
  rreg HR' 22%bv G22.
  rreg HR' 23%bv G23.
  rreg HR' 24%bv G24.
  rreg HR' 25%bv G25.
  rreg HR' 26%bv G26.
  rreg HR' 27%bv G27.
  split; [rewrite G19; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G15; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G16; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G5; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G20; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G10; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G13; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G14; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G1; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G2; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G3; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G4; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G8; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G9; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G18; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G21; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G22; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G23; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G24; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G25; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G26; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G27; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split.
  { subst M1. apply munch_mem_denot; [exact Hlf|].
    repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; cbn [a_base a_off]; rewrite ?EFF, ?ESH, ?E32;
                                cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
    apply Forall_nil. }
  split; [subst M1; apply wmono_mem_denot|].
  split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
  subst M1; apply stk_mem_denot; exact ST.
Qed.
