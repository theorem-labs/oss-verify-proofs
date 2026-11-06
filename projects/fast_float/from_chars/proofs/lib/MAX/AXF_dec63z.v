(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Module AXF_dec63.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_G := EVar 32.
Definition e_idx := EVar 33.
Definition e_W := EVar 34.
Definition e_avail := EVar 35.
Definition e_freed := EVar 36.
Definition e_sp0 := EVar 37.
Definition e_canary := EVar 38.
Definition STK := SA e_sp0 (-1024).
Definition sr_dec63 := (sr_upd (sr_upd (sr_upd sr_id 2 (e_sp0)) 10 (e_G)) 11 (e_idx)).
Definition kn_dec63 : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWr STK (ELit 1024);
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_idx 0 31;
    KRange e_avail 0 (2^32-1);
    KRange e_freed 0 (2^32-1);
    KWord (SA e_G 24) 4 e_avail;
    KWord (SA e_G 28) 4 e_freed;
    KWord (SA e_G 32) 8 e_W;
    KWord (SA (ELit 0) 0x63da0) 8 (ELit 0x95e40);
    KWord (SA (ELit 0) 0x95e40) 8 e_canary;
    KDisj STK (ELit 1024) (SA e_G 0) (ELit 40) ].
Definition scr_dec63 : scripts := SCR [] [] [].
Definition ss_dec63 := SS 0x518d0 sr_dec63 [] kn_dec63 39.
Definition RUN_dec63 := sym_exec SEGS 200 true [0x519e4; 0x51a2c] scr_dec63 ss_dec63 [].

Definition scr_pd63 : scripts := SCR [false; false; true] [] [].
Definition RES_pd63 := Eval vm_compute in sym_exec SEGS 200 true [0x519e4; 0x51a2c] scr_pd63 ss_dec63 [].
Lemma RES_pd63_ok : sym_exec SEGS 200 true [0x519e4; 0x51a2c] scr_pd63 (SS 0x518d0 sr_dec63 [] kn_dec63 39) [] = RES_pd63.
Proof. vm_compute. reflexivity. Qed.
End AXF_dec63.

Import ListNotations AX2 AX2S.

Module AXF_fm0.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_G := EVar 32.
Definition e_sp0 := EVar 33.
Definition e_BASE := EVar 34.
Definition e_LEN := EVar 35.
Definition e_canary := EVar 36.
Definition e_ra := EVar 40.
Definition e_s0 := EVar 41.
Definition e_s1 := EVar 42.
Definition e_s2 := EVar 43.
Definition e_s3 := EVar 44.
Definition STK := SA e_sp0 (-1024).
Definition sr_fm0 := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-96)))) 9 (ELit 0x95e40)) 10 (e_G)) 11 (e_LEN)) 12 (e_BASE)) 18 (ELit 0x95ed8)).
Definition kn_fm0 : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWr STK (ELit 1024);
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KWord (SA (ELit 0) 0x95ee8) 8 (ELit 0);
    KWord (SA e_sp0 (-8)) 8 e_ra;
    KWord (SA e_sp0 (-16)) 8 e_s0;
    KWord (SA e_sp0 (-24)) 8 e_s1;
    KWord (SA e_sp0 (-32)) 8 e_s2;
    KWord (SA e_sp0 (-40)) 8 e_s3;
    KWord (SA e_sp0 (-48)) 8 e_canary;
    KWord (SA (ELit 0) 0x95e40) 8 e_canary;
    KWr (SA e_G 0) (ELit 40);
    KWr (SA (ELit 0) 0x95ee8) (ELit 8);
    KDisj STK (ELit 1024) (SA e_G 0) (ELit 40);
    KDisj STK (ELit 1024) (SA (ELit 0) 0x95ee8) (ELit 8);
    KDisj STK (ELit 1024) (SA (ELit 0) 0x95e40) (ELit 8);
    KDisj (SA e_G 0) (ELit 40) (SA (ELit 0) 0x95ee8) (ELit 8);
    KDisj (SA e_G 0) (ELit 40) (SA (ELit 0) 0x95e40) (ELit 8) ].
Definition scr_fm0 : scripts := SCR [] [] [].
Definition ss_fm0 := SS 0x51bb4 sr_fm0 [] kn_fm0 45.
Definition RUN_fm0 := sym_exec SEGS 100 true [] scr_fm0 ss_fm0 [].

Definition scr_pfm0 : scripts := SCR [] [] [].
Definition RES_pfm0 := Eval vm_compute in sym_exec SEGS 100 true [] scr_pfm0 ss_fm0 [].
Lemma RES_pfm0_ok : sym_exec SEGS 100 true [] scr_pfm0 (SS 0x51bb4 sr_fm0 [] kn_fm0 45) [] = RES_pfm0.
Proof. vm_compute. reflexivity. Qed.
End AXF_fm0.

Module AXF_fm0z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section FM0.
Context {fx : FPState}.

Definition VALS_fm0 (G sp0 BASE LEN canary ra s0 s1 s2 s3 : Z) : list Z := [G; sp0; BASE; LEN; canary; 0; 0; 0; ra; s0; s1; s2; s3].

Record fm0_pre (regs : bvmap 5 word) (m : word -> option byte) (G sp0 BASE LEN canary ra s0 s1 s2 s3 : Z) : Prop := {
  fm0_R2 : getr regs 2 = wa (sp0 + -96) ;
  fm0_R9 : getr regs 9 = wa 613952 ;
  fm0_R10 : getr regs 10 = wa G ;
  fm0_R11 : getr regs 11 = wa LEN ;
  fm0_R12 : getr regs 12 = wa BASE ;
  fm0_R18 : getr regs 18 = wa 614104 ;
  fm0_HSTK : stk_ok SEGS m (wa sp0) 1024 ;
  fm0_rng_G : 1 <= G <= 2^63-1 ;
  fm0_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  fm0_rng_BASE : 0 <= BASE <= 2^64-1 ;
  fm0_rng_LEN : 0 <= LEN <= 2^64-1 ;
  fm0_rng_canary : 0 <= canary <= 2^64-1 ;
  fm0_rng_ra : 0 <= ra <= 2^64-1 ;
  fm0_rng_s0 : 0 <= s0 <= 2^64-1 ;
  fm0_rng_s1 : 0 <= s1 <= 2^64-1 ;
  fm0_rng_s2 : 0 <= s2 <= 2^64-1 ;
  fm0_rng_s3 : 0 <= s3 <= 2^64-1 ;
  fm0_ka1 : sp0 mod 16 = 0 ;
  fm0_ka4 : G mod 8 = 0 ;
  fm0_kw5 : rdn SEGS m (wa (0 + 614120)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  fm0_kw6 : rdn SEGS m (wa (sp0 + -8)) 8 = Some (word_to_le_bytes 8 (wa ra)) ;
  fm0_kw7 : rdn SEGS m (wa (sp0 + -16)) 8 = Some (word_to_le_bytes 8 (wa s0)) ;
  fm0_kw8 : rdn SEGS m (wa (sp0 + -24)) 8 = Some (word_to_le_bytes 8 (wa s1)) ;
  fm0_kw9 : rdn SEGS m (wa (sp0 + -32)) 8 = Some (word_to_le_bytes 8 (wa s2)) ;
  fm0_kw10 : rdn SEGS m (wa (sp0 + -40)) 8 = Some (word_to_le_bytes 8 (wa s3)) ;
  fm0_kw11 : rdn SEGS m (wa (sp0 + -48)) 8 = Some (word_to_le_bytes 8 (wa canary)) ;
  fm0_kw12 : rdn SEGS m (wa (0 + 613952)) 8 = Some (word_to_le_bytes 8 (wa canary)) ;
  fm0_kwr13 : forall d k, 0 <= d -> d + Z.of_nat k <= 40 -> store_ok SEGS m (wa (G + 0 + d)) k = true ;
  fm0_kwr14 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (0 + 614120 + d)) k = true ;
  fm0_kd15 : sp0 + -1024 + 1024 <= G + 0 \/ G + 0 + 40 <= sp0 + -1024 ;
  fm0_kd16 : sp0 + -1024 + 1024 <= 0 + 614120 \/ 0 + 614120 + 8 <= sp0 + -1024 ;
  fm0_kd17 : sp0 + -1024 + 1024 <= 0 + 613952 \/ 0 + 613952 + 8 <= sp0 + -1024 ;
  fm0_kd18 : G + 0 + 40 <= 0 + 614120 \/ 0 + 614120 + 8 <= G + 0 ;
  fm0_kd19 : G + 0 + 40 <= 0 + 613952 \/ 0 + 613952 + 8 <= G + 0
}.


#[using="Type"] Lemma fm0_setup : forall regs m G sp0 BASE LEN canary ra s0 s1 s2 s3, fm0_pre regs m G sp0 BASE LEN canary ra s0 s1 s2 s3 ->
  regs_ok (Ez regs (VALS_fm0 G sp0 BASE LEN canary ra s0 s1 s2 s3)) AXF_fm0.sr_fm0 regs /\ know_ok SEGS (Ez regs (VALS_fm0 G sp0 BASE LEN canary ra s0 s1 s2 s3)) m AXF_fm0.kn_fm0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G sp0 BASE LEN canary ra s0 s1 s2 s3 P. destruct P as [fm0_R2 fm0_R9 fm0_R10 fm0_R11 fm0_R12 fm0_R18 fm0_HSTK fm0_rng_G fm0_rng_sp0 fm0_rng_BASE fm0_rng_LEN fm0_rng_canary fm0_rng_ra fm0_rng_s0 fm0_rng_s1 fm0_rng_s2 fm0_rng_s3 fm0_ka1 fm0_ka4 fm0_kw5 fm0_kw6 fm0_kw7 fm0_kw8 fm0_kw9 fm0_kw10 fm0_kw11 fm0_kw12 fm0_kwr13 fm0_kwr14 fm0_kd15 fm0_kd16 fm0_kd17 fm0_kd18 fm0_kd19].
  set (E := Ez regs (VALS_fm0 G sp0 BASE LEN canary ra s0 s1 s2 s3)).
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = BASE) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = LEN) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = canary) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = ra) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = s0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = s1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = s2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z44 : bv_unsigned (ev E 44) = s3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_fm0.sr_fm0.
    apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|]|]|]|]|]|].
    - rewrite fm0_R2, zeval_sound. cbn [zeval edenot AXF_fm0.e_G AXF_fm0.e_sp0 AXF_fm0.e_BASE AXF_fm0.e_LEN AXF_fm0.e_canary AXF_fm0.e_ra AXF_fm0.e_s0 AXF_fm0.e_s1 AXF_fm0.e_s2 AXF_fm0.e_s3 AXF_fm0.STK]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z40, ?Z41, ?Z42, ?Z43, ?Z44. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite fm0_R9. reflexivity.
    - rewrite fm0_R10. reflexivity.
    - rewrite fm0_R11. reflexivity.
    - rewrite fm0_R12. reflexivity.
    - rewrite fm0_R18. reflexivity. }
  unfold know_ok, AXF_fm0.kn_fm0.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_fm0.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_fm0.e_G AXF_fm0.e_sp0 AXF_fm0.e_BASE AXF_fm0.e_LEN AXF_fm0.e_canary AXF_fm0.e_ra AXF_fm0.e_s0 AXF_fm0.e_s1 AXF_fm0.e_s2 AXF_fm0.e_s3 AXF_fm0.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z40, ?Z41, ?Z42, ?Z43, ?Z44.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range G _ _ fm0_rng_G eq_refl eq_refl), ?(mod64_of_range sp0 _ _ fm0_rng_sp0 eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply fm0_kwr13 | apply fm0_kwr14]; assumption).
  all: try (clear - fm0_rng_G fm0_rng_sp0 fm0_rng_BASE fm0_rng_LEN fm0_rng_canary fm0_rng_ra fm0_rng_s0 fm0_rng_s1 fm0_rng_s2 fm0_rng_s3 fm0_ka1 fm0_ka4; lia).
  all: first [(clear - fm0_rng_G fm0_rng_sp0 fm0_rng_BASE fm0_rng_LEN fm0_rng_canary fm0_rng_ra fm0_rng_s0 fm0_rng_s1 fm0_rng_s2 fm0_rng_s3 fm0_ka1 fm0_ka4 fm0_kd15; lia) | (clear - fm0_rng_G fm0_rng_sp0 fm0_rng_BASE fm0_rng_LEN fm0_rng_canary fm0_rng_ra fm0_rng_s0 fm0_rng_s1 fm0_rng_s2 fm0_rng_s3 fm0_ka1 fm0_ka4 fm0_kd16; lia) | (clear - fm0_rng_G fm0_rng_sp0 fm0_rng_BASE fm0_rng_LEN fm0_rng_canary fm0_rng_ra fm0_rng_s0 fm0_rng_s1 fm0_rng_s2 fm0_rng_s3 fm0_ka1 fm0_ka4 fm0_kd17; lia) | (clear - fm0_rng_G fm0_rng_sp0 fm0_rng_BASE fm0_rng_LEN fm0_rng_canary fm0_rng_ra fm0_rng_s0 fm0_rng_s1 fm0_rng_s2 fm0_rng_s3 fm0_ka1 fm0_ka4 fm0_kd18; lia) | (clear - fm0_rng_G fm0_rng_sp0 fm0_rng_BASE fm0_rng_LEN fm0_rng_canary fm0_rng_ra fm0_rng_s0 fm0_rng_s1 fm0_rng_s2 fm0_rng_s3 fm0_ka1 fm0_ka4 fm0_kd19; lia) | lia].
Qed.


Definition fm0_mem_pfm0 (m : word -> option byte) (regs : bvmap 5 word) (G sp0 BASE LEN canary ra s0 s1 s2 s3 : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (sp0 + -88)) (word_to_le_bytes 8 (wa 0))) (wa (sp0 + -80)) (word_to_le_bytes 8 (wa 0))) (wa (sp0 + -72)) (word_to_le_bytes 8 (wa 0))) (wa (sp0 + -64)) (word_to_le_bytes 8 (wa 0))) (wa (sp0 + -56)) (word_to_le_bytes 8 (wa 0))) (wa (G + 8)) (word_to_le_bytes 8 (wa 0))) (wa (G + 0)) (word_to_le_bytes 8 (wa 0))) (wa (G + 16)) (word_to_le_bytes 8 (wa 0))) (wa (G + 24)) (word_to_le_bytes 8 (wa 0))) (wa (G + 32)) (word_to_le_bytes 8 (wa 0))) (wa (G + 0)) (word_to_le_bytes 8 (wa G))) (wa (G + 8)) (word_to_le_bytes 8 (wa G))) (wa (0 + 614120)) (word_to_le_bytes 8 (wa G)).

#[using="Type"] Theorem fm0_pfm0 : forall regs m rom G sp0 BASE LEN canary ra s0 s1 s2 s3, fm0_pre regs m G sp0 BASE LEN canary ra s0 s1 s2 s3 ->
  scs_denot SEGS m (Ez regs (VALS_fm0 G sp0 BASE LEN canary ra s0 s1 s2 s3)) (snd (fst AXF_fm0.RES_pfm0)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51bb4) m rom) (mkst R (wa 0x51ca0) (fm0_mem_pfm0 m regs G sp0 BASE LEN canary ra s0 s1 s2 s3) rom) /\
    getr R 1 = wa ra /\ getr R 2 = wa sp0 /\ getr R 8 = wa s0 /\ getr R 9 = wa s1 /\ getr R 10 = wa BASE /\ getr R 11 = wa LEN /\ getr R 12 = wa BASE /\ getr R 13 = wa canary /\ getr R 18 = wa s2 /\ getr R 19 = wa s3 /\ (forall k, In k [3; 4; 5; 6; 7; 14; 15; 16; 17; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G sp0 BASE LEN canary ra s0 s1 s2 s3 P Hsc. destruct (fm0_setup regs m G sp0 BASE LEN canary ra s0 s1 s2 s3 P) as [HR HK].
  set (E := Ez regs (VALS_fm0 G sp0 BASE LEN canary ra s0 s1 s2 s3)) in *. destruct P as [fm0_R2 fm0_R9 fm0_R10 fm0_R11 fm0_R12 fm0_R18 fm0_HSTK fm0_rng_G fm0_rng_sp0 fm0_rng_BASE fm0_rng_LEN fm0_rng_canary fm0_rng_ra fm0_rng_s0 fm0_rng_s1 fm0_rng_s2 fm0_rng_s3 fm0_ka1 fm0_ka4 fm0_kw5 fm0_kw6 fm0_kw7 fm0_kw8 fm0_kw9 fm0_kw10 fm0_kw11 fm0_kw12 fm0_kwr13 fm0_kwr14 fm0_kd15 fm0_kd16 fm0_kd17 fm0_kd18 fm0_kd19].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = BASE) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = LEN) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = canary) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = ra) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = s0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = s1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = s2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z44 : bv_unsigned (ev E 44) = s3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [] AXF_fm0.scr_pfm0 0x51bb4 AXF_fm0.sr_fm0 AXF_fm0.kn_fm0 45 _ _ _ E m rom regs AXF_fm0.RES_pfm0_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_fm0.RES_pfm0 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (fm0_mem_pfm0 m regs G sp0 BASE LEN canary ra s0 s1 s2 s3) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold fm0_mem_pfm0. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End FM0.
End AXF_fm0z.

Module AXF_fm1.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_G := EVar 32.
Definition e_sp0 := EVar 33.
Definition e_BASE := EVar 34.
Definition e_LEN := EVar 35.
Definition e_canary := EVar 36.
Definition e_H := EVar 37.
Definition e_HP := EVar 38.
Definition e_ra := EVar 40.
Definition e_s0 := EVar 41.
Definition e_s1 := EVar 42.
Definition e_s2 := EVar 43.
Definition e_s3 := EVar 44.
Definition STK := SA e_sp0 (-1024).
Definition sr_fm1 := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-96)))) 9 (ELit 0x95e40)) 10 (e_G)) 11 (e_LEN)) 12 (e_BASE)) 18 (ELit 0x95ed8)).
Definition kn_fm1 : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWr STK (ELit 1024);
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_H 1 (2^63-1);
    KRange e_HP 1 (2^63-1);
    KWord (SA (ELit 0) 0x95ee8) 8 e_H;
    KWord (SA e_H 0) 8 e_HP;
    KWord (SA e_sp0 (-8)) 8 e_ra;
    KWord (SA e_sp0 (-16)) 8 e_s0;
    KWord (SA e_sp0 (-24)) 8 e_s1;
    KWord (SA e_sp0 (-32)) 8 e_s2;
    KWord (SA e_sp0 (-40)) 8 e_s3;
    KWord (SA e_sp0 (-48)) 8 e_canary;
    KWord (SA (ELit 0) 0x95e40) 8 e_canary;
    KWr (SA e_G 0) (ELit 40);
    KWr (SA e_H 0) (ELit 8);
    KWr (SA e_HP 8) (ELit 8);
    KDisj STK (ELit 1024) (SA e_G 0) (ELit 40);
    KDisj STK (ELit 1024) (SA (ELit 0) 0x95ee8) (ELit 8);
    KDisj STK (ELit 1024) (SA (ELit 0) 0x95e40) (ELit 8);
    KDisj STK (ELit 1024) (SA e_H 0) (ELit 40);
    KDisj STK (ELit 1024) (SA e_HP 0) (ELit 40);
    KDisj (SA e_G 0) (ELit 40) (SA (ELit 0) 0x95ee8) (ELit 8);
    KDisj (SA e_G 0) (ELit 40) (SA (ELit 0) 0x95e40) (ELit 8);
    KDisj (SA e_G 0) (ELit 40) (SA e_H 0) (ELit 40);
    KDisj (SA e_G 0) (ELit 40) (SA e_HP 0) (ELit 40);
    KDisj (SA e_H 0) (ELit 40) (SA (ELit 0) 0x95e40) (ELit 8);
    KDisj (SA e_HP 0) (ELit 40) (SA (ELit 0) 0x95e40) (ELit 8);
    KDisj (SA e_H 0) (ELit 40) (SA (ELit 0) 0x95ee8) (ELit 8);
    KDisj (SA e_HP 0) (ELit 40) (SA (ELit 0) 0x95ee8) (ELit 8) ].
Definition scr_fm1 : scripts := SCR [] [] [].
Definition ss_fm1 := SS 0x51bb4 sr_fm1 [] kn_fm1 45.
Definition RUN_fm1 := sym_exec SEGS 100 true [] scr_fm1 ss_fm1 [].

Definition scr_pfm1 : scripts := SCR [] [] [].
Definition RES_pfm1 := Eval vm_compute in sym_exec SEGS 100 true [] scr_pfm1 ss_fm1 [].
Lemma RES_pfm1_ok : sym_exec SEGS 100 true [] scr_pfm1 (SS 0x51bb4 sr_fm1 [] kn_fm1 45) [] = RES_pfm1.
Proof. vm_compute. reflexivity. Qed.
End AXF_fm1.

Module AXF_fm1z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section FM1.
Context {fx : FPState}.

Definition VALS_fm1 (G sp0 BASE LEN canary H HP ra s0 s1 s2 s3 : Z) : list Z := [G; sp0; BASE; LEN; canary; H; HP; 0; ra; s0; s1; s2; s3].

Record fm1_pre (regs : bvmap 5 word) (m : word -> option byte) (G sp0 BASE LEN canary H HP ra s0 s1 s2 s3 : Z) : Prop := {
  fm1_R2 : getr regs 2 = wa (sp0 + -96) ;
  fm1_R9 : getr regs 9 = wa 613952 ;
  fm1_R10 : getr regs 10 = wa G ;
  fm1_R11 : getr regs 11 = wa LEN ;
  fm1_R12 : getr regs 12 = wa BASE ;
  fm1_R18 : getr regs 18 = wa 614104 ;
  fm1_HSTK : stk_ok SEGS m (wa sp0) 1024 ;
  fm1_rng_G : 1 <= G <= 2^63-1 ;
  fm1_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  fm1_rng_BASE : 0 <= BASE <= 2^64-1 ;
  fm1_rng_LEN : 0 <= LEN <= 2^64-1 ;
  fm1_rng_canary : 0 <= canary <= 2^64-1 ;
  fm1_rng_H : 1 <= H <= 2^63-1 ;
  fm1_rng_HP : 1 <= HP <= 2^63-1 ;
  fm1_rng_ra : 0 <= ra <= 2^64-1 ;
  fm1_rng_s0 : 0 <= s0 <= 2^64-1 ;
  fm1_rng_s1 : 0 <= s1 <= 2^64-1 ;
  fm1_rng_s2 : 0 <= s2 <= 2^64-1 ;
  fm1_rng_s3 : 0 <= s3 <= 2^64-1 ;
  fm1_ka1 : sp0 mod 16 = 0 ;
  fm1_ka4 : G mod 8 = 0 ;
  fm1_kw7 : rdn SEGS m (wa (0 + 614120)) 8 = Some (word_to_le_bytes 8 (wa H)) ;
  fm1_kw8 : rdn SEGS m (wa (H + 0)) 8 = Some (word_to_le_bytes 8 (wa HP)) ;
  fm1_kw9 : rdn SEGS m (wa (sp0 + -8)) 8 = Some (word_to_le_bytes 8 (wa ra)) ;
  fm1_kw10 : rdn SEGS m (wa (sp0 + -16)) 8 = Some (word_to_le_bytes 8 (wa s0)) ;
  fm1_kw11 : rdn SEGS m (wa (sp0 + -24)) 8 = Some (word_to_le_bytes 8 (wa s1)) ;
  fm1_kw12 : rdn SEGS m (wa (sp0 + -32)) 8 = Some (word_to_le_bytes 8 (wa s2)) ;
  fm1_kw13 : rdn SEGS m (wa (sp0 + -40)) 8 = Some (word_to_le_bytes 8 (wa s3)) ;
  fm1_kw14 : rdn SEGS m (wa (sp0 + -48)) 8 = Some (word_to_le_bytes 8 (wa canary)) ;
  fm1_kw15 : rdn SEGS m (wa (0 + 613952)) 8 = Some (word_to_le_bytes 8 (wa canary)) ;
  fm1_kwr16 : forall d k, 0 <= d -> d + Z.of_nat k <= 40 -> store_ok SEGS m (wa (G + 0 + d)) k = true ;
  fm1_kwr17 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (H + 0 + d)) k = true ;
  fm1_kwr18 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (HP + 8 + d)) k = true ;
  fm1_kd19 : sp0 + -1024 + 1024 <= G + 0 \/ G + 0 + 40 <= sp0 + -1024 ;
  fm1_kd20 : sp0 + -1024 + 1024 <= 0 + 614120 \/ 0 + 614120 + 8 <= sp0 + -1024 ;
  fm1_kd21 : sp0 + -1024 + 1024 <= 0 + 613952 \/ 0 + 613952 + 8 <= sp0 + -1024 ;
  fm1_kd22 : sp0 + -1024 + 1024 <= H + 0 \/ H + 0 + 40 <= sp0 + -1024 ;
  fm1_kd23 : sp0 + -1024 + 1024 <= HP + 0 \/ HP + 0 + 40 <= sp0 + -1024 ;
  fm1_kd24 : G + 0 + 40 <= 0 + 614120 \/ 0 + 614120 + 8 <= G + 0 ;
  fm1_kd25 : G + 0 + 40 <= 0 + 613952 \/ 0 + 613952 + 8 <= G + 0 ;
  fm1_kd26 : G + 0 + 40 <= H + 0 \/ H + 0 + 40 <= G + 0 ;
  fm1_kd27 : G + 0 + 40 <= HP + 0 \/ HP + 0 + 40 <= G + 0 ;
  fm1_kd28 : H + 0 + 40 <= 0 + 613952 \/ 0 + 613952 + 8 <= H + 0 ;
  fm1_kd29 : HP + 0 + 40 <= 0 + 613952 \/ 0 + 613952 + 8 <= HP + 0 ;
  fm1_kd30 : H + 0 + 40 <= 0 + 614120 \/ 0 + 614120 + 8 <= H + 0 ;
  fm1_kd31 : HP + 0 + 40 <= 0 + 614120 \/ 0 + 614120 + 8 <= HP + 0
}.


#[using="Type"] Lemma fm1_setup : forall regs m G sp0 BASE LEN canary H HP ra s0 s1 s2 s3, fm1_pre regs m G sp0 BASE LEN canary H HP ra s0 s1 s2 s3 ->
  regs_ok (Ez regs (VALS_fm1 G sp0 BASE LEN canary H HP ra s0 s1 s2 s3)) AXF_fm1.sr_fm1 regs /\ know_ok SEGS (Ez regs (VALS_fm1 G sp0 BASE LEN canary H HP ra s0 s1 s2 s3)) m AXF_fm1.kn_fm1.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G sp0 BASE LEN canary H HP ra s0 s1 s2 s3 P. destruct P as [fm1_R2 fm1_R9 fm1_R10 fm1_R11 fm1_R12 fm1_R18 fm1_HSTK fm1_rng_G fm1_rng_sp0 fm1_rng_BASE fm1_rng_LEN fm1_rng_canary fm1_rng_H fm1_rng_HP fm1_rng_ra fm1_rng_s0 fm1_rng_s1 fm1_rng_s2 fm1_rng_s3 fm1_ka1 fm1_ka4 fm1_kw7 fm1_kw8 fm1_kw9 fm1_kw10 fm1_kw11 fm1_kw12 fm1_kw13 fm1_kw14 fm1_kw15 fm1_kwr16 fm1_kwr17 fm1_kwr18 fm1_kd19 fm1_kd20 fm1_kd21 fm1_kd22 fm1_kd23 fm1_kd24 fm1_kd25 fm1_kd26 fm1_kd27 fm1_kd28 fm1_kd29 fm1_kd30 fm1_kd31].
  set (E := Ez regs (VALS_fm1 G sp0 BASE LEN canary H HP ra s0 s1 s2 s3)).
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = BASE) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = LEN) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = canary) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = H) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = HP) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = ra) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = s0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = s1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = s2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z44 : bv_unsigned (ev E 44) = s3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_fm1.sr_fm1.
    apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|]|]|]|]|]|].
    - rewrite fm1_R2, zeval_sound. cbn [zeval edenot AXF_fm1.e_G AXF_fm1.e_sp0 AXF_fm1.e_BASE AXF_fm1.e_LEN AXF_fm1.e_canary AXF_fm1.e_H AXF_fm1.e_HP AXF_fm1.e_ra AXF_fm1.e_s0 AXF_fm1.e_s1 AXF_fm1.e_s2 AXF_fm1.e_s3 AXF_fm1.STK]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z40, ?Z41, ?Z42, ?Z43, ?Z44. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite fm1_R9. reflexivity.
    - rewrite fm1_R10. reflexivity.
    - rewrite fm1_R11. reflexivity.
    - rewrite fm1_R12. reflexivity.
    - rewrite fm1_R18. reflexivity. }
  unfold know_ok, AXF_fm1.kn_fm1.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_fm1.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_fm1.e_G AXF_fm1.e_sp0 AXF_fm1.e_BASE AXF_fm1.e_LEN AXF_fm1.e_canary AXF_fm1.e_H AXF_fm1.e_HP AXF_fm1.e_ra AXF_fm1.e_s0 AXF_fm1.e_s1 AXF_fm1.e_s2 AXF_fm1.e_s3 AXF_fm1.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z40, ?Z41, ?Z42, ?Z43, ?Z44.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range G _ _ fm1_rng_G eq_refl eq_refl), ?(mod64_of_range sp0 _ _ fm1_rng_sp0 eq_refl eq_refl), ?(mod64_of_range H _ _ fm1_rng_H eq_refl eq_refl), ?(mod64_of_range HP _ _ fm1_rng_HP eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply fm1_kwr16 | apply fm1_kwr17 | apply fm1_kwr18]; assumption).
  all: try (clear - fm1_rng_G fm1_rng_sp0 fm1_rng_BASE fm1_rng_LEN fm1_rng_canary fm1_rng_H fm1_rng_HP fm1_rng_ra fm1_rng_s0 fm1_rng_s1 fm1_rng_s2 fm1_rng_s3 fm1_ka1 fm1_ka4; lia).
  all: first [(clear - fm1_rng_G fm1_rng_sp0 fm1_rng_BASE fm1_rng_LEN fm1_rng_canary fm1_rng_H fm1_rng_HP fm1_rng_ra fm1_rng_s0 fm1_rng_s1 fm1_rng_s2 fm1_rng_s3 fm1_ka1 fm1_ka4 fm1_kd19; lia) | (clear - fm1_rng_G fm1_rng_sp0 fm1_rng_BASE fm1_rng_LEN fm1_rng_canary fm1_rng_H fm1_rng_HP fm1_rng_ra fm1_rng_s0 fm1_rng_s1 fm1_rng_s2 fm1_rng_s3 fm1_ka1 fm1_ka4 fm1_kd20; lia) | (clear - fm1_rng_G fm1_rng_sp0 fm1_rng_BASE fm1_rng_LEN fm1_rng_canary fm1_rng_H fm1_rng_HP fm1_rng_ra fm1_rng_s0 fm1_rng_s1 fm1_rng_s2 fm1_rng_s3 fm1_ka1 fm1_ka4 fm1_kd21; lia) | (clear - fm1_rng_G fm1_rng_sp0 fm1_rng_BASE fm1_rng_LEN fm1_rng_canary fm1_rng_H fm1_rng_HP fm1_rng_ra fm1_rng_s0 fm1_rng_s1 fm1_rng_s2 fm1_rng_s3 fm1_ka1 fm1_ka4 fm1_kd22; lia) | (clear - fm1_rng_G fm1_rng_sp0 fm1_rng_BASE fm1_rng_LEN fm1_rng_canary fm1_rng_H fm1_rng_HP fm1_rng_ra fm1_rng_s0 fm1_rng_s1 fm1_rng_s2 fm1_rng_s3 fm1_ka1 fm1_ka4 fm1_kd23; lia) | (clear - fm1_rng_G fm1_rng_sp0 fm1_rng_BASE fm1_rng_LEN fm1_rng_canary fm1_rng_H fm1_rng_HP fm1_rng_ra fm1_rng_s0 fm1_rng_s1 fm1_rng_s2 fm1_rng_s3 fm1_ka1 fm1_ka4 fm1_kd24; lia) | (clear - fm1_rng_G fm1_rng_sp0 fm1_rng_BASE fm1_rng_LEN fm1_rng_canary fm1_rng_H fm1_rng_HP fm1_rng_ra fm1_rng_s0 fm1_rng_s1 fm1_rng_s2 fm1_rng_s3 fm1_ka1 fm1_ka4 fm1_kd25; lia) | (clear - fm1_rng_G fm1_rng_sp0 fm1_rng_BASE fm1_rng_LEN fm1_rng_canary fm1_rng_H fm1_rng_HP fm1_rng_ra fm1_rng_s0 fm1_rng_s1 fm1_rng_s2 fm1_rng_s3 fm1_ka1 fm1_ka4 fm1_kd26; lia) | (clear - fm1_rng_G fm1_rng_sp0 fm1_rng_BASE fm1_rng_LEN fm1_rng_canary fm1_rng_H fm1_rng_HP fm1_rng_ra fm1_rng_s0 fm1_rng_s1 fm1_rng_s2 fm1_rng_s3 fm1_ka1 fm1_ka4 fm1_kd27; lia) | (clear - fm1_rng_G fm1_rng_sp0 fm1_rng_BASE fm1_rng_LEN fm1_rng_canary fm1_rng_H fm1_rng_HP fm1_rng_ra fm1_rng_s0 fm1_rng_s1 fm1_rng_s2 fm1_rng_s3 fm1_ka1 fm1_ka4 fm1_kd28; lia) | (clear - fm1_rng_G fm1_rng_sp0 fm1_rng_BASE fm1_rng_LEN fm1_rng_canary fm1_rng_H fm1_rng_HP fm1_rng_ra fm1_rng_s0 fm1_rng_s1 fm1_rng_s2 fm1_rng_s3 fm1_ka1 fm1_ka4 fm1_kd29; lia) | (clear - fm1_rng_G fm1_rng_sp0 fm1_rng_BASE fm1_rng_LEN fm1_rng_canary fm1_rng_H fm1_rng_HP fm1_rng_ra fm1_rng_s0 fm1_rng_s1 fm1_rng_s2 fm1_rng_s3 fm1_ka1 fm1_ka4 fm1_kd30; lia) | (clear - fm1_rng_G fm1_rng_sp0 fm1_rng_BASE fm1_rng_LEN fm1_rng_canary fm1_rng_H fm1_rng_HP fm1_rng_ra fm1_rng_s0 fm1_rng_s1 fm1_rng_s2 fm1_rng_s3 fm1_ka1 fm1_ka4 fm1_kd31; lia) | lia].
Qed.


Definition fm1_mem_pfm1 (m : word -> option byte) (regs : bvmap 5 word) (G sp0 BASE LEN canary H HP ra s0 s1 s2 s3 : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (sp0 + -88)) (word_to_le_bytes 8 (wa 0))) (wa (sp0 + -80)) (word_to_le_bytes 8 (wa 0))) (wa (sp0 + -72)) (word_to_le_bytes 8 (wa 0))) (wa (sp0 + -64)) (word_to_le_bytes 8 (wa 0))) (wa (sp0 + -56)) (word_to_le_bytes 8 (wa 0))) (wa (G + 8)) (word_to_le_bytes 8 (wa 0))) (wa (G + 0)) (word_to_le_bytes 8 (wa 0))) (wa (G + 16)) (word_to_le_bytes 8 (wa 0))) (wa (G + 24)) (word_to_le_bytes 8 (wa 0))) (wa (G + 32)) (word_to_le_bytes 8 (wa 0))) (wa (G + 8)) (word_to_le_bytes 8 (wa H))) (wa (G + 0)) (word_to_le_bytes 8 (wa HP))) (wa (HP + 8)) (word_to_le_bytes 8 (wa G))) (wa (H + 0)) (word_to_le_bytes 8 (wa G)).

#[using="Type"] Theorem fm1_pfm1 : forall regs m rom G sp0 BASE LEN canary H HP ra s0 s1 s2 s3, fm1_pre regs m G sp0 BASE LEN canary H HP ra s0 s1 s2 s3 ->
  scs_denot SEGS m (Ez regs (VALS_fm1 G sp0 BASE LEN canary H HP ra s0 s1 s2 s3)) (snd (fst AXF_fm1.RES_pfm1)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51bb4) m rom) (mkst R (wa 0x51ca0) (fm1_mem_pfm1 m regs G sp0 BASE LEN canary H HP ra s0 s1 s2 s3) rom) /\
    getr R 1 = wa ra /\ getr R 2 = wa sp0 /\ getr R 8 = wa s0 /\ getr R 9 = wa s1 /\ getr R 10 = wa BASE /\ getr R 11 = wa LEN /\ getr R 12 = wa BASE /\ getr R 13 = wa canary /\ getr R 18 = wa s2 /\ getr R 19 = wa s3 /\ (forall k, In k [3; 4; 5; 6; 7; 14; 15; 16; 17; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G sp0 BASE LEN canary H HP ra s0 s1 s2 s3 P Hsc. destruct (fm1_setup regs m G sp0 BASE LEN canary H HP ra s0 s1 s2 s3 P) as [HR HK].
  set (E := Ez regs (VALS_fm1 G sp0 BASE LEN canary H HP ra s0 s1 s2 s3)) in *. destruct P as [fm1_R2 fm1_R9 fm1_R10 fm1_R11 fm1_R12 fm1_R18 fm1_HSTK fm1_rng_G fm1_rng_sp0 fm1_rng_BASE fm1_rng_LEN fm1_rng_canary fm1_rng_H fm1_rng_HP fm1_rng_ra fm1_rng_s0 fm1_rng_s1 fm1_rng_s2 fm1_rng_s3 fm1_ka1 fm1_ka4 fm1_kw7 fm1_kw8 fm1_kw9 fm1_kw10 fm1_kw11 fm1_kw12 fm1_kw13 fm1_kw14 fm1_kw15 fm1_kwr16 fm1_kwr17 fm1_kwr18 fm1_kd19 fm1_kd20 fm1_kd21 fm1_kd22 fm1_kd23 fm1_kd24 fm1_kd25 fm1_kd26 fm1_kd27 fm1_kd28 fm1_kd29 fm1_kd30 fm1_kd31].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = BASE) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = LEN) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = canary) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = H) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = HP) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = ra) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = s0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = s1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = s2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z44 : bv_unsigned (ev E 44) = s3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [] AXF_fm1.scr_pfm1 0x51bb4 AXF_fm1.sr_fm1 AXF_fm1.kn_fm1 45 _ _ _ E m rom regs AXF_fm1.RES_pfm1_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_fm1.RES_pfm1 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (fm1_mem_pfm1 m regs G sp0 BASE LEN canary H HP ra s0 s1 s2 s3) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold fm1_mem_pfm1. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End FM1.
End AXF_fm1z.

Module AXF_m1f.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_sc := EVar 32.
Definition e_G1 := EVar 33.
Definition e_freed1 := EVar 34.
Definition e_W1 := EVar 35.
Definition e_nx1 := EVar 36.
Definition e_freed2 := EVar 37.
Definition ACT := SA (EMd M_MUL (ELit 8) e_sc) 614184.
Definition sr_m1f := (sr_upd (sr_upd sr_id 10 (e_G1)) 21 (EAlu ALU_ADD (EMd M_MUL (ELit 8) e_sc) (ELit 614184))).
Definition kn_m1f : list kentry :=
  [ KRange e_sc 0 47;
    KRange e_G1 1 (2^63-1);
    KAlign e_G1 8;
    KRange e_freed1 0 (2^32-1);
    KRange e_W1 0 (2^63-1);
    KRange e_nx1 1 (2^63-1);
    KAlign e_nx1 8;
    KRange e_freed2 0 (2^32-1);
    KWord (SA e_G1 28) 4 e_freed1;
    KWord (SA e_G1 32) 8 e_W1;
    KWord (SA e_G1 8) 8 e_nx1;
    KWord (SA e_nx1 28) 4 e_freed2;
    KWr ACT (ELit 8);
    KDisj ACT (ELit 8) (SA e_nx1 0) (ELit 40) ].
Definition scr_m1f : scripts := SCR [false; false] [] [].
Definition ss_m1f := SS 0x523b8 sr_m1f [] kn_m1f 38.
Definition RUN_m1f := sym_exec SEGS 100 true [0x523e4] scr_m1f ss_m1f [].

Definition scr_pm1f : scripts := SCR [false; false] [] [].
Definition RES_pm1f := Eval vm_compute in sym_exec SEGS 100 true [0x523e4] scr_pm1f ss_m1f [].
Lemma RES_pm1f_ok : sym_exec SEGS 100 true [0x523e4] scr_pm1f (SS 0x523b8 sr_m1f [] kn_m1f 38) [] = RES_pm1f.
Proof. vm_compute. reflexivity. Qed.
End AXF_m1f.

Module AXF_m1fz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section M1F.
Context {fx : FPState}.

Definition VALS_m1f (sc G1 freed1 W1 nx1 freed2 : Z) : list Z := [sc; G1; freed1; W1; nx1; freed2].

Record m1f_pre (regs : bvmap 5 word) (m : word -> option byte) (sc G1 freed1 W1 nx1 freed2 : Z) : Prop := {
  m1f_R10 : getr regs 10 = wa G1 ;
  m1f_R21 : getr regs 21 = wa ((8 * sc) + 614184) ;
  m1f_rng_sc : 0 <= sc <= 47 ;
  m1f_rng_G1 : 1 <= G1 <= 2^63-1 ;
  m1f_rng_freed1 : 0 <= freed1 <= 2^32-1 ;
  m1f_rng_W1 : 0 <= W1 <= 2^63-1 ;
  m1f_rng_nx1 : 1 <= nx1 <= 2^63-1 ;
  m1f_rng_freed2 : 0 <= freed2 <= 2^32-1 ;
  m1f_ka2 : G1 mod 8 = 0 ;
  m1f_ka6 : nx1 mod 8 = 0 ;
  m1f_kw8 : rdn SEGS m (wa (G1 + 28)) 4 = Some (word_to_le_bytes 4 (wa freed1)) ;
  m1f_kw9 : rdn SEGS m (wa (G1 + 32)) 8 = Some (word_to_le_bytes 8 (wa W1)) ;
  m1f_kw10 : rdn SEGS m (wa (G1 + 8)) 8 = Some (word_to_le_bytes 8 (wa nx1)) ;
  m1f_kw11 : rdn SEGS m (wa (nx1 + 28)) 4 = Some (word_to_le_bytes 4 (wa freed2)) ;
  m1f_kwr12 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (8 * sc + 614184 + d)) k = true ;
  m1f_kd13 : 8 * sc + 614184 + 8 <= nx1 + 0 \/ nx1 + 0 + 40 <= 8 * sc + 614184
}.


#[using="Type"] Lemma m1f_setup : forall regs m sc G1 freed1 W1 nx1 freed2, m1f_pre regs m sc G1 freed1 W1 nx1 freed2 ->
  regs_ok (Ez regs (VALS_m1f sc G1 freed1 W1 nx1 freed2)) AXF_m1f.sr_m1f regs /\ know_ok SEGS (Ez regs (VALS_m1f sc G1 freed1 W1 nx1 freed2)) m AXF_m1f.kn_m1f.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sc G1 freed1 W1 nx1 freed2 P. destruct P as [m1f_R10 m1f_R21 m1f_rng_sc m1f_rng_G1 m1f_rng_freed1 m1f_rng_W1 m1f_rng_nx1 m1f_rng_freed2 m1f_ka2 m1f_ka6 m1f_kw8 m1f_kw9 m1f_kw10 m1f_kw11 m1f_kwr12 m1f_kd13].
  set (E := Ez regs (VALS_m1f sc G1 freed1 W1 nx1 freed2)).
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = G1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = freed1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = W1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = nx1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = freed2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_m1f.sr_m1f.
    apply (regs_ok_pin E _ regs 21); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|].
    - rewrite m1f_R10. reflexivity.
    - rewrite m1f_R21, zeval_sound. cbn [zeval edenot AXF_m1f.e_sc AXF_m1f.e_G1 AXF_m1f.e_freed1 AXF_m1f.e_W1 AXF_m1f.e_nx1 AXF_m1f.e_freed2 AXF_m1f.ACT]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)]. }
  unfold know_ok, AXF_m1f.kn_m1f.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_m1f.e_sc AXF_m1f.e_G1 AXF_m1f.e_freed1 AXF_m1f.e_W1 AXF_m1f.e_nx1 AXF_m1f.e_freed2 AXF_m1f.ACT a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sc _ _ m1f_rng_sc eq_refl eq_refl), ?(mod64_of_range G1 _ _ m1f_rng_G1 eq_refl eq_refl), ?(mod64_of_range freed1 _ _ m1f_rng_freed1 eq_refl eq_refl), ?(mod64_of_range W1 _ _ m1f_rng_W1 eq_refl eq_refl), ?(mod64_of_range nx1 _ _ m1f_rng_nx1 eq_refl eq_refl), ?(mod64_of_range freed2 _ _ m1f_rng_freed2 eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply m1f_kwr12]; assumption).
  all: try (clear - m1f_rng_sc m1f_rng_G1 m1f_rng_freed1 m1f_rng_W1 m1f_rng_nx1 m1f_rng_freed2 m1f_ka2 m1f_ka6; lia).
  all: first [(clear - m1f_rng_sc m1f_rng_G1 m1f_rng_freed1 m1f_rng_W1 m1f_rng_nx1 m1f_rng_freed2 m1f_ka2 m1f_ka6 m1f_kd13; lia) | lia].
Qed.


Definition m1f_mem_pm1f (m : word -> option byte) (regs : bvmap 5 word) (sc G1 freed1 W1 nx1 freed2 : Z) : word -> option byte :=
  wbytes (m) (wa (8 * sc + 614184)) (word_to_le_bytes 8 (wa nx1)).

#[using="Type"] Theorem m1f_pm1f : forall regs m rom sc G1 freed1 W1 nx1 freed2, m1f_pre regs m sc G1 freed1 W1 nx1 freed2 ->
  scs_denot SEGS m (Ez regs (VALS_m1f sc G1 freed1 W1 nx1 freed2)) (snd (fst AXF_m1f.RES_pm1f)) ->
  exists R, msteps SEGS (mkst regs (wa 0x523b8) m rom) (mkst R (wa 0x523e4) (m1f_mem_pm1f m regs sc G1 freed1 W1 nx1 freed2) rom) /\
    getr R 10 = wa nx1 /\ getr R 12 = wa (Z.land W1 32) /\ getr R 13 = wa (ext_Z true 0 4 freed2) /\ getr R 14 = wa 2 /\ getr R 21 = wa ((8 * sc) + 614184) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 18; 19; 20; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc G1 freed1 W1 nx1 freed2 P Hsc. destruct (m1f_setup regs m sc G1 freed1 W1 nx1 freed2 P) as [HR HK].
  set (E := Ez regs (VALS_m1f sc G1 freed1 W1 nx1 freed2)) in *. destruct P as [m1f_R10 m1f_R21 m1f_rng_sc m1f_rng_G1 m1f_rng_freed1 m1f_rng_W1 m1f_rng_nx1 m1f_rng_freed2 m1f_ka2 m1f_ka6 m1f_kw8 m1f_kw9 m1f_kw10 m1f_kw11 m1f_kwr12 m1f_kd13].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = G1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = freed1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = W1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = nx1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = freed2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x523e4] AXF_m1f.scr_pm1f 0x523b8 AXF_m1f.sr_m1f AXF_m1f.kn_m1f 38 _ _ _ E m rom regs AXF_m1f.RES_pm1f_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_m1f.RES_pm1f fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (m1f_mem_pm1f m regs sc G1 freed1 W1 nx1 freed2) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold m1f_mem_pm1f. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End M1F.
End AXF_m1fz.

Module AXF_m1n.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_sc := EVar 32.
Definition e_G1 := EVar 33.
Definition e_freed1 := EVar 34.
Definition e_W1 := EVar 35.
Definition ACT := SA (EMd M_MUL (ELit 8) e_sc) 614184.
Definition sr_m1n := (sr_upd (sr_upd sr_id 10 (e_G1)) 21 (EAlu ALU_ADD (EMd M_MUL (ELit 8) e_sc) (ELit 614184))).
Definition kn_m1n : list kentry :=
  [ KRange e_sc 0 47;
    KRange e_G1 1 (2^63-1);
    KAlign e_G1 8;
    KRange e_freed1 0 (2^32-1);
    KRange e_W1 0 (2^63-1);
    KWord (SA e_G1 28) 4 e_freed1;
    KWord (SA e_G1 32) 8 e_W1 ].
Definition scr_m1n : scripts := SCR [false; true] [] [].
Definition ss_m1n := SS 0x523b8 sr_m1n [] kn_m1n 36.
Definition RUN_m1n := sym_exec SEGS 100 true [0x523e4] scr_m1n ss_m1n [].

Definition scr_pm1n : scripts := SCR [false; true] [] [].
Definition RES_pm1n := Eval vm_compute in sym_exec SEGS 100 true [0x523e4] scr_pm1n ss_m1n [].
Lemma RES_pm1n_ok : sym_exec SEGS 100 true [0x523e4] scr_pm1n (SS 0x523b8 sr_m1n [] kn_m1n 36) [] = RES_pm1n.
Proof. vm_compute. reflexivity. Qed.
End AXF_m1n.

Module AXF_m1nz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section M1N.
Context {fx : FPState}.

Definition VALS_m1n (sc G1 freed1 W1 : Z) : list Z := [sc; G1; freed1; W1].

Record m1n_pre (regs : bvmap 5 word) (m : word -> option byte) (sc G1 freed1 W1 : Z) : Prop := {
  m1n_R10 : getr regs 10 = wa G1 ;
  m1n_R21 : getr regs 21 = wa ((8 * sc) + 614184) ;
  m1n_rng_sc : 0 <= sc <= 47 ;
  m1n_rng_G1 : 1 <= G1 <= 2^63-1 ;
  m1n_rng_freed1 : 0 <= freed1 <= 2^32-1 ;
  m1n_rng_W1 : 0 <= W1 <= 2^63-1 ;
  m1n_ka2 : G1 mod 8 = 0 ;
  m1n_kw5 : rdn SEGS m (wa (G1 + 28)) 4 = Some (word_to_le_bytes 4 (wa freed1)) ;
  m1n_kw6 : rdn SEGS m (wa (G1 + 32)) 8 = Some (word_to_le_bytes 8 (wa W1))
}.


#[using="Type"] Lemma m1n_setup : forall regs m sc G1 freed1 W1, m1n_pre regs m sc G1 freed1 W1 ->
  regs_ok (Ez regs (VALS_m1n sc G1 freed1 W1)) AXF_m1n.sr_m1n regs /\ know_ok SEGS (Ez regs (VALS_m1n sc G1 freed1 W1)) m AXF_m1n.kn_m1n.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sc G1 freed1 W1 P. destruct P as [m1n_R10 m1n_R21 m1n_rng_sc m1n_rng_G1 m1n_rng_freed1 m1n_rng_W1 m1n_ka2 m1n_kw5 m1n_kw6].
  set (E := Ez regs (VALS_m1n sc G1 freed1 W1)).
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = G1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = freed1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = W1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_m1n.sr_m1n.
    apply (regs_ok_pin E _ regs 21); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|].
    - rewrite m1n_R10. reflexivity.
    - rewrite m1n_R21, zeval_sound. cbn [zeval edenot AXF_m1n.e_sc AXF_m1n.e_G1 AXF_m1n.e_freed1 AXF_m1n.e_W1 AXF_m1n.ACT]. rewrite ?Z32, ?Z33, ?Z34, ?Z35. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)]. }
  unfold know_ok, AXF_m1n.kn_m1n.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_m1n.e_sc AXF_m1n.e_G1 AXF_m1n.e_freed1 AXF_m1n.e_W1 AXF_m1n.ACT a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sc _ _ m1n_rng_sc eq_refl eq_refl), ?(mod64_of_range G1 _ _ m1n_rng_G1 eq_refl eq_refl), ?(mod64_of_range freed1 _ _ m1n_rng_freed1 eq_refl eq_refl), ?(mod64_of_range W1 _ _ m1n_rng_W1 eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - m1n_rng_sc m1n_rng_G1 m1n_rng_freed1 m1n_rng_W1 m1n_ka2; lia).
  all: first [lia].
Qed.


Definition m1n_mem_pm1n (m : word -> option byte) (regs : bvmap 5 word) (sc G1 freed1 W1 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem m1n_pm1n : forall regs m rom sc G1 freed1 W1, m1n_pre regs m sc G1 freed1 W1 ->
  scs_denot SEGS m (Ez regs (VALS_m1n sc G1 freed1 W1)) (snd (fst AXF_m1n.RES_pm1n)) ->
  exists R, msteps SEGS (mkst regs (wa 0x523b8) m rom) (mkst R (wa 0x523e4) (m1n_mem_pm1n m regs sc G1 freed1 W1) rom) /\
    getr R 10 = wa G1 /\ getr R 12 = wa (Z.land W1 32) /\ getr R 13 = wa (ext_Z true 0 4 freed1) /\ getr R 14 = wa 2 /\ getr R 21 = wa ((8 * sc) + 614184) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 18; 19; 20; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc G1 freed1 W1 P Hsc. destruct (m1n_setup regs m sc G1 freed1 W1 P) as [HR HK].
  set (E := Ez regs (VALS_m1n sc G1 freed1 W1)) in *. destruct P as [m1n_R10 m1n_R21 m1n_rng_sc m1n_rng_G1 m1n_rng_freed1 m1n_rng_W1 m1n_ka2 m1n_kw5 m1n_kw6].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = G1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = freed1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = W1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x523e4] AXF_m1n.scr_pm1n 0x523b8 AXF_m1n.sr_m1n AXF_m1n.kn_m1n 36 _ _ _ E m rom regs AXF_m1n.RES_pm1n_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_m1n.RES_pm1n fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (m1n_mem_pm1n m regs sc G1 freed1 W1) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold m1n_mem_pm1n. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End M1N.
End AXF_m1nz.

Module AXF_m2a.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_sc := EVar 32.
Definition e_G2 := EVar 33.
Definition e_freed2 := EVar 34.
Definition e_mem2 := EVar 35.
Definition e_hb := EVar 36.
Definition sr_m2a := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (e_G2)) 13 (EExt true 0 4 e_freed2)) 14 (ELit 2)) 21 (EAlu ALU_ADD (EMd M_MUL (ELit 8) e_sc) (ELit 614184))).
Definition kn_m2a : list kentry :=
  [ KRange e_sc 0 47;
    KRange e_G2 1 (2^63-1);
    KAlign e_G2 8;
    KRange e_freed2 0 (2^32-1);
    KRange e_mem2 1 (2^63-1);
    KRange e_hb 0 255;
    KWord (SA e_G2 16) 8 e_mem2;
    KWord (SA e_mem2 8) 1 e_hb;
    KWord (SA e_G2 24) 4 (ELit 0) ].
Definition scr_m2a : scripts := SCR [true] [] [].
Definition ss_m2a := SS 0x523e4 sr_m2a [] kn_m2a 37.
Definition RUN_m2a := sym_exec SEGS 100 true [0x52418] scr_m2a ss_m2a [].

Definition scr_pm2a : scripts := SCR [true] [] [].
Definition RES_pm2a := Eval vm_compute in sym_exec SEGS 100 true [0x52418] scr_pm2a ss_m2a [].
Lemma RES_pm2a_ok : sym_exec SEGS 100 true [0x52418] scr_pm2a (SS 0x523e4 sr_m2a [] kn_m2a 37) [] = RES_pm2a.
Proof. vm_compute. reflexivity. Qed.
End AXF_m2a.

Module AXF_m2az.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section M2A.
Context {fx : FPState}.

Definition VALS_m2a (sc G2 freed2 mem2 hb : Z) : list Z := [sc; G2; freed2; mem2; hb].

Record m2a_pre (regs : bvmap 5 word) (m : word -> option byte) (sc G2 freed2 mem2 hb : Z) : Prop := {
  m2a_R10 : getr regs 10 = wa G2 ;
  m2a_R13 : getr regs 13 = wa (ext_Z true 0 4 freed2) ;
  m2a_R14 : getr regs 14 = wa 2 ;
  m2a_R21 : getr regs 21 = wa ((8 * sc) + 614184) ;
  m2a_rng_sc : 0 <= sc <= 47 ;
  m2a_rng_G2 : 1 <= G2 <= 2^63-1 ;
  m2a_rng_freed2 : 0 <= freed2 <= 2^32-1 ;
  m2a_rng_mem2 : 1 <= mem2 <= 2^63-1 ;
  m2a_rng_hb : 0 <= hb <= 255 ;
  m2a_ka2 : G2 mod 8 = 0 ;
  m2a_kw6 : rdn SEGS m (wa (G2 + 16)) 8 = Some (word_to_le_bytes 8 (wa mem2)) ;
  m2a_kw7 : rdn SEGS m (wa (mem2 + 8)) 1 = Some (word_to_le_bytes 1 (wa hb)) ;
  m2a_kw8 : rdn SEGS m (wa (G2 + 24)) 4 = Some (word_to_le_bytes 4 (wa 0))
}.


#[using="Type"] Lemma m2a_setup : forall regs m sc G2 freed2 mem2 hb, m2a_pre regs m sc G2 freed2 mem2 hb ->
  regs_ok (Ez regs (VALS_m2a sc G2 freed2 mem2 hb)) AXF_m2a.sr_m2a regs /\ know_ok SEGS (Ez regs (VALS_m2a sc G2 freed2 mem2 hb)) m AXF_m2a.kn_m2a.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sc G2 freed2 mem2 hb P. destruct P as [m2a_R10 m2a_R13 m2a_R14 m2a_R21 m2a_rng_sc m2a_rng_G2 m2a_rng_freed2 m2a_rng_mem2 m2a_rng_hb m2a_ka2 m2a_kw6 m2a_kw7 m2a_kw8].
  set (E := Ez regs (VALS_m2a sc G2 freed2 mem2 hb)).
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = G2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = freed2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = mem2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = hb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_m2a.sr_m2a.
    apply (regs_ok_pin E _ regs 21); [apply (regs_ok_pin E _ regs 14); [apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|]|]|].
    - rewrite m2a_R10. reflexivity.
    - rewrite m2a_R13, zeval_sound. cbn [zeval edenot AXF_m2a.e_sc AXF_m2a.e_G2 AXF_m2a.e_freed2 AXF_m2a.e_mem2 AXF_m2a.e_hb]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite m2a_R14. reflexivity.
    - rewrite m2a_R21, zeval_sound. cbn [zeval edenot AXF_m2a.e_sc AXF_m2a.e_G2 AXF_m2a.e_freed2 AXF_m2a.e_mem2 AXF_m2a.e_hb]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)]. }
  unfold know_ok, AXF_m2a.kn_m2a.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_m2a.e_sc AXF_m2a.e_G2 AXF_m2a.e_freed2 AXF_m2a.e_mem2 AXF_m2a.e_hb a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sc _ _ m2a_rng_sc eq_refl eq_refl), ?(mod64_of_range G2 _ _ m2a_rng_G2 eq_refl eq_refl), ?(mod64_of_range freed2 _ _ m2a_rng_freed2 eq_refl eq_refl), ?(mod64_of_range mem2 _ _ m2a_rng_mem2 eq_refl eq_refl), ?(mod64_of_range hb _ _ m2a_rng_hb eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - m2a_rng_sc m2a_rng_G2 m2a_rng_freed2 m2a_rng_mem2 m2a_rng_hb m2a_ka2; lia).
  all: first [lia].
Qed.


Definition m2a_mem_pm2a (m : word -> option byte) (regs : bvmap 5 word) (sc G2 freed2 mem2 hb : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem m2a_pm2a : forall regs m rom sc G2 freed2 mem2 hb, m2a_pre regs m sc G2 freed2 mem2 hb ->
  scs_denot SEGS m (Ez regs (VALS_m2a sc G2 freed2 mem2 hb)) (snd (fst AXF_m2a.RES_pm2a)) ->
  exists R, msteps SEGS (mkst regs (wa 0x523e4) m rom) (mkst R (wa 0x52418) (m2a_mem_pm2a m regs sc G2 freed2 mem2 hb) rom) /\
    getr R 10 = wa G2 /\ getr R 11 = wa 0 /\ getr R 12 = wa hb /\ getr R 21 = wa ((8 * sc) + 614184) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 18; 19; 20; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc G2 freed2 mem2 hb P Hsc. destruct (m2a_setup regs m sc G2 freed2 mem2 hb P) as [HR HK].
  set (E := Ez regs (VALS_m2a sc G2 freed2 mem2 hb)) in *. destruct P as [m2a_R10 m2a_R13 m2a_R14 m2a_R21 m2a_rng_sc m2a_rng_G2 m2a_rng_freed2 m2a_rng_mem2 m2a_rng_hb m2a_ka2 m2a_kw6 m2a_kw7 m2a_kw8].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = G2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = freed2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = mem2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = hb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x52418] AXF_m2a.scr_pm2a 0x523e4 AXF_m2a.sr_m2a AXF_m2a.kn_m2a 37 _ _ _ E m rom regs AXF_m2a.RES_pm2a_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_m2a.RES_pm2a fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (m2a_mem_pm2a m regs sc G2 freed2 mem2 hb) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold m2a_mem_pm2a. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End M2A.
End AXF_m2az.

Module AXF_m2b.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_sc := EVar 32.
Definition e_G2 := EVar 33.
Definition e_freed2 := EVar 34.
Definition e_mem2 := EVar 35.
Definition e_hb := EVar 36.
Definition e_nx2 := EVar 37.
Definition ACT := SA (EMd M_MUL (ELit 8) e_sc) 614184.
Definition sr_m2b := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (e_G2)) 13 (EExt true 0 4 e_freed2)) 14 (ELit 2)) 21 (EAlu ALU_ADD (EMd M_MUL (ELit 8) e_sc) (ELit 614184))).
Definition kn_m2b : list kentry :=
  [ KRange e_sc 0 47;
    KRange e_G2 1 (2^63-1);
    KAlign e_G2 8;
    KRange e_freed2 0 (2^32-1);
    KRange e_mem2 1 (2^63-1);
    KRange e_hb 0 255;
    KRange e_nx2 1 (2^63-1);
    KAlign e_nx2 8;
    KWord (SA e_G2 16) 8 e_mem2;
    KWord (SA e_mem2 8) 1 e_hb;
    KWord (SA e_G2 8) 8 e_nx2;
    KWord (SA e_nx2 24) 4 (ELit 0);
    KWr ACT (ELit 8);
    KDisj ACT (ELit 8) (SA e_nx2 0) (ELit 40) ].
Definition scr_m2b : scripts := SCR [false; false] [] [].
Definition ss_m2b := SS 0x523e4 sr_m2b [] kn_m2b 38.
Definition RUN_m2b := sym_exec SEGS 100 true [0x52418] scr_m2b ss_m2b [].

Definition scr_pm2b : scripts := SCR [false; false] [] [].
Definition RES_pm2b := Eval vm_compute in sym_exec SEGS 100 true [0x52418] scr_pm2b ss_m2b [].
Lemma RES_pm2b_ok : sym_exec SEGS 100 true [0x52418] scr_pm2b (SS 0x523e4 sr_m2b [] kn_m2b 38) [] = RES_pm2b.
Proof. vm_compute. reflexivity. Qed.
End AXF_m2b.

Module AXF_m2bz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section M2B.
Context {fx : FPState}.

Definition VALS_m2b (sc G2 freed2 mem2 hb nx2 : Z) : list Z := [sc; G2; freed2; mem2; hb; nx2].

Record m2b_pre (regs : bvmap 5 word) (m : word -> option byte) (sc G2 freed2 mem2 hb nx2 : Z) : Prop := {
  m2b_R10 : getr regs 10 = wa G2 ;
  m2b_R13 : getr regs 13 = wa (ext_Z true 0 4 freed2) ;
  m2b_R14 : getr regs 14 = wa 2 ;
  m2b_R21 : getr regs 21 = wa ((8 * sc) + 614184) ;
  m2b_rng_sc : 0 <= sc <= 47 ;
  m2b_rng_G2 : 1 <= G2 <= 2^63-1 ;
  m2b_rng_freed2 : 0 <= freed2 <= 2^32-1 ;
  m2b_rng_mem2 : 1 <= mem2 <= 2^63-1 ;
  m2b_rng_hb : 0 <= hb <= 255 ;
  m2b_rng_nx2 : 1 <= nx2 <= 2^63-1 ;
  m2b_ka2 : G2 mod 8 = 0 ;
  m2b_ka7 : nx2 mod 8 = 0 ;
  m2b_kw8 : rdn SEGS m (wa (G2 + 16)) 8 = Some (word_to_le_bytes 8 (wa mem2)) ;
  m2b_kw9 : rdn SEGS m (wa (mem2 + 8)) 1 = Some (word_to_le_bytes 1 (wa hb)) ;
  m2b_kw10 : rdn SEGS m (wa (G2 + 8)) 8 = Some (word_to_le_bytes 8 (wa nx2)) ;
  m2b_kw11 : rdn SEGS m (wa (nx2 + 24)) 4 = Some (word_to_le_bytes 4 (wa 0)) ;
  m2b_kwr12 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (8 * sc + 614184 + d)) k = true ;
  m2b_kd13 : 8 * sc + 614184 + 8 <= nx2 + 0 \/ nx2 + 0 + 40 <= 8 * sc + 614184
}.


#[using="Type"] Lemma m2b_setup : forall regs m sc G2 freed2 mem2 hb nx2, m2b_pre regs m sc G2 freed2 mem2 hb nx2 ->
  regs_ok (Ez regs (VALS_m2b sc G2 freed2 mem2 hb nx2)) AXF_m2b.sr_m2b regs /\ know_ok SEGS (Ez regs (VALS_m2b sc G2 freed2 mem2 hb nx2)) m AXF_m2b.kn_m2b.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sc G2 freed2 mem2 hb nx2 P. destruct P as [m2b_R10 m2b_R13 m2b_R14 m2b_R21 m2b_rng_sc m2b_rng_G2 m2b_rng_freed2 m2b_rng_mem2 m2b_rng_hb m2b_rng_nx2 m2b_ka2 m2b_ka7 m2b_kw8 m2b_kw9 m2b_kw10 m2b_kw11 m2b_kwr12 m2b_kd13].
  set (E := Ez regs (VALS_m2b sc G2 freed2 mem2 hb nx2)).
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = G2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = freed2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = mem2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = hb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = nx2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_m2b.sr_m2b.
    apply (regs_ok_pin E _ regs 21); [apply (regs_ok_pin E _ regs 14); [apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|]|]|].
    - rewrite m2b_R10. reflexivity.
    - rewrite m2b_R13, zeval_sound. cbn [zeval edenot AXF_m2b.e_sc AXF_m2b.e_G2 AXF_m2b.e_freed2 AXF_m2b.e_mem2 AXF_m2b.e_hb AXF_m2b.e_nx2 AXF_m2b.ACT]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite m2b_R14. reflexivity.
    - rewrite m2b_R21, zeval_sound. cbn [zeval edenot AXF_m2b.e_sc AXF_m2b.e_G2 AXF_m2b.e_freed2 AXF_m2b.e_mem2 AXF_m2b.e_hb AXF_m2b.e_nx2 AXF_m2b.ACT]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)]. }
  unfold know_ok, AXF_m2b.kn_m2b.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_m2b.e_sc AXF_m2b.e_G2 AXF_m2b.e_freed2 AXF_m2b.e_mem2 AXF_m2b.e_hb AXF_m2b.e_nx2 AXF_m2b.ACT a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sc _ _ m2b_rng_sc eq_refl eq_refl), ?(mod64_of_range G2 _ _ m2b_rng_G2 eq_refl eq_refl), ?(mod64_of_range freed2 _ _ m2b_rng_freed2 eq_refl eq_refl), ?(mod64_of_range mem2 _ _ m2b_rng_mem2 eq_refl eq_refl), ?(mod64_of_range hb _ _ m2b_rng_hb eq_refl eq_refl), ?(mod64_of_range nx2 _ _ m2b_rng_nx2 eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply m2b_kwr12]; assumption).
  all: try (clear - m2b_rng_sc m2b_rng_G2 m2b_rng_freed2 m2b_rng_mem2 m2b_rng_hb m2b_rng_nx2 m2b_ka2 m2b_ka7; lia).
  all: first [(clear - m2b_rng_sc m2b_rng_G2 m2b_rng_freed2 m2b_rng_mem2 m2b_rng_hb m2b_rng_nx2 m2b_ka2 m2b_ka7 m2b_kd13; lia) | lia].
Qed.


Definition m2b_mem_pm2b (m : word -> option byte) (regs : bvmap 5 word) (sc G2 freed2 mem2 hb nx2 : Z) : word -> option byte :=
  wbytes (m) (wa (8 * sc + 614184)) (word_to_le_bytes 8 (wa nx2)).

#[using="Type"] Theorem m2b_pm2b : forall regs m rom sc G2 freed2 mem2 hb nx2, m2b_pre regs m sc G2 freed2 mem2 hb nx2 ->
  scs_denot SEGS m (Ez regs (VALS_m2b sc G2 freed2 mem2 hb nx2)) (snd (fst AXF_m2b.RES_pm2b)) ->
  exists R, msteps SEGS (mkst regs (wa 0x523e4) m rom) (mkst R (wa 0x52418) (m2b_mem_pm2b m regs sc G2 freed2 mem2 hb nx2) rom) /\
    getr R 10 = wa nx2 /\ getr R 11 = wa 0 /\ getr R 12 = wa hb /\ getr R 13 = wa nx2 /\ getr R 21 = wa ((8 * sc) + 614184) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 18; 19; 20; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc G2 freed2 mem2 hb nx2 P Hsc. destruct (m2b_setup regs m sc G2 freed2 mem2 hb nx2 P) as [HR HK].
  set (E := Ez regs (VALS_m2b sc G2 freed2 mem2 hb nx2)) in *. destruct P as [m2b_R10 m2b_R13 m2b_R14 m2b_R21 m2b_rng_sc m2b_rng_G2 m2b_rng_freed2 m2b_rng_mem2 m2b_rng_hb m2b_rng_nx2 m2b_ka2 m2b_ka7 m2b_kw8 m2b_kw9 m2b_kw10 m2b_kw11 m2b_kwr12 m2b_kd13].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = G2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = freed2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = mem2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = hb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = nx2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x52418] AXF_m2b.scr_pm2b 0x523e4 AXF_m2b.sr_m2b AXF_m2b.kn_m2b 38 _ _ _ E m rom regs AXF_m2b.RES_pm2b_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_m2b.RES_pm2b fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (m2b_mem_pm2b m regs sc G2 freed2 mem2 hb nx2) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold m2b_mem_pm2b. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End M2B.
End AXF_m2bz.

Module AXF_m2c.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_sc := EVar 32.
Definition e_G2 := EVar 33.
Definition e_freed2 := EVar 34.
Definition e_mem2 := EVar 35.
Definition e_hb := EVar 36.
Definition sr_m2c := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (e_G2)) 13 (EExt true 0 4 e_freed2)) 14 (ELit 2)) 21 (EAlu ALU_ADD (EMd M_MUL (ELit 8) e_sc) (ELit 614184))).
Definition kn_m2c : list kentry :=
  [ KRange e_sc 0 47;
    KRange e_G2 1 (2^63-1);
    KAlign e_G2 8;
    KRange e_freed2 0 (2^32-1);
    KRange e_mem2 1 (2^63-1);
    KRange e_hb 0 255;
    KWord (SA e_G2 16) 8 e_mem2;
    KWord (SA e_mem2 8) 1 e_hb;
    KWord (SA e_G2 8) 8 e_G2 ].
Definition scr_m2c : scripts := SCR [false] [] [].
Definition ss_m2c := SS 0x523e4 sr_m2c [] kn_m2c 37.
Definition RUN_m2c := sym_exec SEGS 100 true [0x527c4] scr_m2c ss_m2c [].

Definition scr_pm2c : scripts := SCR [false] [] [].
Definition RES_pm2c := Eval vm_compute in sym_exec SEGS 100 true [0x527c4] scr_pm2c ss_m2c [].
Lemma RES_pm2c_ok : sym_exec SEGS 100 true [0x527c4] scr_pm2c (SS 0x523e4 sr_m2c [] kn_m2c 37) [] = RES_pm2c.
Proof. vm_compute. reflexivity. Qed.
End AXF_m2c.

Module AXF_m2cz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section M2C.
Context {fx : FPState}.

Definition VALS_m2c (sc G2 freed2 mem2 hb : Z) : list Z := [sc; G2; freed2; mem2; hb].

Record m2c_pre (regs : bvmap 5 word) (m : word -> option byte) (sc G2 freed2 mem2 hb : Z) : Prop := {
  m2c_R10 : getr regs 10 = wa G2 ;
  m2c_R13 : getr regs 13 = wa (ext_Z true 0 4 freed2) ;
  m2c_R14 : getr regs 14 = wa 2 ;
  m2c_R21 : getr regs 21 = wa ((8 * sc) + 614184) ;
  m2c_rng_sc : 0 <= sc <= 47 ;
  m2c_rng_G2 : 1 <= G2 <= 2^63-1 ;
  m2c_rng_freed2 : 0 <= freed2 <= 2^32-1 ;
  m2c_rng_mem2 : 1 <= mem2 <= 2^63-1 ;
  m2c_rng_hb : 0 <= hb <= 255 ;
  m2c_ka2 : G2 mod 8 = 0 ;
  m2c_kw6 : rdn SEGS m (wa (G2 + 16)) 8 = Some (word_to_le_bytes 8 (wa mem2)) ;
  m2c_kw7 : rdn SEGS m (wa (mem2 + 8)) 1 = Some (word_to_le_bytes 1 (wa hb)) ;
  m2c_kw8 : rdn SEGS m (wa (G2 + 8)) 8 = Some (word_to_le_bytes 8 (wa G2))
}.


#[using="Type"] Lemma m2c_setup : forall regs m sc G2 freed2 mem2 hb, m2c_pre regs m sc G2 freed2 mem2 hb ->
  regs_ok (Ez regs (VALS_m2c sc G2 freed2 mem2 hb)) AXF_m2c.sr_m2c regs /\ know_ok SEGS (Ez regs (VALS_m2c sc G2 freed2 mem2 hb)) m AXF_m2c.kn_m2c.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sc G2 freed2 mem2 hb P. destruct P as [m2c_R10 m2c_R13 m2c_R14 m2c_R21 m2c_rng_sc m2c_rng_G2 m2c_rng_freed2 m2c_rng_mem2 m2c_rng_hb m2c_ka2 m2c_kw6 m2c_kw7 m2c_kw8].
  set (E := Ez regs (VALS_m2c sc G2 freed2 mem2 hb)).
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = G2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = freed2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = mem2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = hb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_m2c.sr_m2c.
    apply (regs_ok_pin E _ regs 21); [apply (regs_ok_pin E _ regs 14); [apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|]|]|].
    - rewrite m2c_R10. reflexivity.
    - rewrite m2c_R13, zeval_sound. cbn [zeval edenot AXF_m2c.e_sc AXF_m2c.e_G2 AXF_m2c.e_freed2 AXF_m2c.e_mem2 AXF_m2c.e_hb]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite m2c_R14. reflexivity.
    - rewrite m2c_R21, zeval_sound. cbn [zeval edenot AXF_m2c.e_sc AXF_m2c.e_G2 AXF_m2c.e_freed2 AXF_m2c.e_mem2 AXF_m2c.e_hb]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)]. }
  unfold know_ok, AXF_m2c.kn_m2c.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_m2c.e_sc AXF_m2c.e_G2 AXF_m2c.e_freed2 AXF_m2c.e_mem2 AXF_m2c.e_hb a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sc _ _ m2c_rng_sc eq_refl eq_refl), ?(mod64_of_range G2 _ _ m2c_rng_G2 eq_refl eq_refl), ?(mod64_of_range freed2 _ _ m2c_rng_freed2 eq_refl eq_refl), ?(mod64_of_range mem2 _ _ m2c_rng_mem2 eq_refl eq_refl), ?(mod64_of_range hb _ _ m2c_rng_hb eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - m2c_rng_sc m2c_rng_G2 m2c_rng_freed2 m2c_rng_mem2 m2c_rng_hb m2c_ka2; lia).
  all: first [lia].
Qed.


Definition m2c_mem_pm2c (m : word -> option byte) (regs : bvmap 5 word) (sc G2 freed2 mem2 hb : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem m2c_pm2c : forall regs m rom sc G2 freed2 mem2 hb, m2c_pre regs m sc G2 freed2 mem2 hb ->
  scs_denot SEGS m (Ez regs (VALS_m2c sc G2 freed2 mem2 hb)) (snd (fst AXF_m2c.RES_pm2c)) ->
  exists R, msteps SEGS (mkst regs (wa 0x523e4) m rom) (mkst R (wa 0x527c4) (m2c_mem_pm2c m regs sc G2 freed2 mem2 hb) rom) /\
    getr R 10 = wa G2 /\ getr R 11 = wa mem2 /\ getr R 12 = wa hb /\ getr R 13 = wa G2 /\ getr R 21 = wa ((8 * sc) + 614184) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 18; 19; 20; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc G2 freed2 mem2 hb P Hsc. destruct (m2c_setup regs m sc G2 freed2 mem2 hb P) as [HR HK].
  set (E := Ez regs (VALS_m2c sc G2 freed2 mem2 hb)) in *. destruct P as [m2c_R10 m2c_R13 m2c_R14 m2c_R21 m2c_rng_sc m2c_rng_G2 m2c_rng_freed2 m2c_rng_mem2 m2c_rng_hb m2c_ka2 m2c_kw6 m2c_kw7 m2c_kw8].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = G2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = freed2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = mem2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = hb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x527c4] AXF_m2c.scr_pm2c 0x523e4 AXF_m2c.sr_m2c AXF_m2c.kn_m2c 37 _ _ _ E m rom regs AXF_m2c.RES_pm2c_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_m2c.RES_pm2c fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (m2c_mem_pm2c m regs sc G2 freed2 mem2 hb) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold m2c_mem_pm2c. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End M2C.
End AXF_m2cz.

Module AXF_mas.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_n := EVar 32.
Definition e_sc := EVar 33.
Definition e_idx := EVar 34.
Definition e_G := EVar 35.
Definition ACT := EMd M_MUL (ELit 8) e_sc.
Definition sr_mas := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (e_n)) 9 (ELit 614096)) 10 (e_idx)) 18 (e_sc)) 20 (e_sc)).
Definition kn_mas : list kentry :=
  [ KRange e_n 1 131051;
    KRange e_sc 0 47;
    KRange e_idx 0 31;
    KRange e_G 1 (2^63-1);
    KWord (SA ACT 614184) 8 e_G ].
Definition scr_mas : scripts := SCR [] [] [].
Definition ss_mas := SS 0x52290 sr_mas [] kn_mas 36.
Definition RUN_mas := sym_exec SEGS 100 true [0x522a4; 0x522e0] scr_mas ss_mas [].

Definition scr_pmas : scripts := SCR [false] [] [].
Definition RES_pmas := Eval vm_compute in sym_exec SEGS 100 true [0x522a4; 0x522e0] scr_pmas ss_mas [].
Lemma RES_pmas_ok : sym_exec SEGS 100 true [0x522a4; 0x522e0] scr_pmas (SS 0x52290 sr_mas [] kn_mas 36) [] = RES_pmas.
Proof. vm_compute. reflexivity. Qed.
End AXF_mas.

Module AXF_masz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section MAS.
Context {fx : FPState}.

Definition VALS_mas (n sc idx G : Z) : list Z := [n; sc; idx; G].

Record mas_pre (regs : bvmap 5 word) (m : word -> option byte) (n sc idx G : Z) : Prop := {
  mas_R8 : getr regs 8 = wa n ;
  mas_R9 : getr regs 9 = wa 614096 ;
  mas_R10 : getr regs 10 = wa idx ;
  mas_R18 : getr regs 18 = wa sc ;
  mas_R20 : getr regs 20 = wa sc ;
  mas_rng_n : 1 <= n <= 131051 ;
  mas_rng_sc : 0 <= sc <= 47 ;
  mas_rng_idx : 0 <= idx <= 31 ;
  mas_rng_G : 1 <= G <= 2^63-1 ;
  mas_kw4 : rdn SEGS m (wa (8 * sc + 614184)) 8 = Some (word_to_le_bytes 8 (wa G))
}.


#[using="Type"] Lemma mas_setup : forall regs m n sc idx G, mas_pre regs m n sc idx G ->
  regs_ok (Ez regs (VALS_mas n sc idx G)) AXF_mas.sr_mas regs /\ know_ok SEGS (Ez regs (VALS_mas n sc idx G)) m AXF_mas.kn_mas.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m n sc idx G P. destruct P as [mas_R8 mas_R9 mas_R10 mas_R18 mas_R20 mas_rng_n mas_rng_sc mas_rng_idx mas_rng_G mas_kw4].
  set (E := Ez regs (VALS_mas n sc idx G)).
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = idx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mas.sr_mas.
    apply (regs_ok_pin E _ regs 20); [apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|]|]|].
    - rewrite mas_R8. reflexivity.
    - rewrite mas_R9. reflexivity.
    - rewrite mas_R10. reflexivity.
    - rewrite mas_R18. reflexivity.
    - rewrite mas_R20. reflexivity. }
  unfold know_ok, AXF_mas.kn_mas.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mas.e_n AXF_mas.e_sc AXF_mas.e_idx AXF_mas.e_G AXF_mas.ACT a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range n _ _ mas_rng_n eq_refl eq_refl), ?(mod64_of_range sc _ _ mas_rng_sc eq_refl eq_refl), ?(mod64_of_range idx _ _ mas_rng_idx eq_refl eq_refl), ?(mod64_of_range G _ _ mas_rng_G eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - mas_rng_n mas_rng_sc mas_rng_idx mas_rng_G; lia).
  all: first [lia].
Qed.


Definition mas_mem_pmas (m : word -> option byte) (regs : bvmap 5 word) (n sc idx G : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mas_pmas : forall regs m rom n sc idx G, mas_pre regs m n sc idx G ->
  scs_denot SEGS m (Ez regs (VALS_mas n sc idx G)) (snd (fst AXF_mas.RES_pmas)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52290) m rom) (mkst R (wa 0x522a4) (mas_mem_pmas m regs n sc idx G) rom) /\
    getr R 8 = wa n /\ getr R 9 = wa 614096 /\ getr R 10 = wa idx /\ getr R 18 = wa G /\ getr R 19 = wa idx /\ getr R 20 = wa sc /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n sc idx G P Hsc. destruct (mas_setup regs m n sc idx G P) as [HR HK].
  set (E := Ez regs (VALS_mas n sc idx G)) in *. destruct P as [mas_R8 mas_R9 mas_R10 mas_R18 mas_R20 mas_rng_n mas_rng_sc mas_rng_idx mas_rng_G mas_kw4].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = idx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x522a4; 0x522e0] AXF_mas.scr_pmas 0x52290 AXF_mas.sr_mas AXF_mas.kn_mas 36 _ _ _ E m rom regs AXF_mas.RES_pmas_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mas.RES_pmas fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mas_mem_pmas m regs n sc idx G) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mas_mem_pmas. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MAS.
End AXF_masz.

Module AXF_md1.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_n := EVar 32.
Definition e_res := EVar 33.
Definition e_seq := EVar 34.
Definition sr_md1 := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (e_n)) 9 (ELit 614096)) 10 (e_res)) 18 (ELit 18446744073709551615)) 19 (EAlu ALU_ADD e_n (ELit 20))).
Definition kn_md1 : list kentry :=
  [ KRange e_n 131052 (2^26);
    KRange e_res 4096 (2^47);
    KRange e_seq 0 255;
    KWord (SA (ELit 0) 0x95e63) 1 (ELit 0);
    KWord (SA (ELit 0) 615016) 1 e_seq;
    KWr (SA (ELit 0) 615016) (ELit 1);
    KWr (SA (ELit 0) 614952) (ELit 32) ].
Definition scr_md1 : scripts := SCR [] [] [].
Definition ss_md1 := SS 0x52018 sr_md1 [] kn_md1 35.
Definition RUN_md1 := sym_exec SEGS 100 true [0x51ca8] scr_md1 ss_md1 [].

Definition scr_pmd1i : scripts := SCR [true] [] [].
Definition RES_pmd1i := Eval vm_compute in sym_exec SEGS 100 true [0x51ca8] scr_pmd1i ss_md1 [].
Lemma RES_pmd1i_ok : sym_exec SEGS 100 true [0x51ca8] scr_pmd1i (SS 0x52018 sr_md1 [] kn_md1 35) [] = RES_pmd1i.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmd1w : scripts := SCR [false] [] [].
Definition RES_pmd1w := Eval vm_compute in sym_exec SEGS 100 true [0x51ca8] scr_pmd1w ss_md1 [].
Lemma RES_pmd1w_ok : sym_exec SEGS 100 true [0x51ca8] scr_pmd1w (SS 0x52018 sr_md1 [] kn_md1 35) [] = RES_pmd1w.
Proof. vm_compute. reflexivity. Qed.
End AXF_md1.

Module AXF_md1z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section MD1.
Context {fx : FPState}.

Definition VALS_md1 (n res seq : Z) : list Z := [n; res; seq].

Record md1_pre (regs : bvmap 5 word) (m : word -> option byte) (n res seq : Z) : Prop := {
  md1_R8 : getr regs 8 = wa n ;
  md1_R9 : getr regs 9 = wa 614096 ;
  md1_R10 : getr regs 10 = wa res ;
  md1_R18 : getr regs 18 = wa 18446744073709551615 ;
  md1_R19 : getr regs 19 = wa (n + 20) ;
  md1_rng_n : 131052 <= n <= 2^26 ;
  md1_rng_res : 4096 <= res <= 2^47 ;
  md1_rng_seq : 0 <= seq <= 255 ;
  md1_kw3 : rdn SEGS m (wa (0 + 613987)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  md1_kw4 : rdn SEGS m (wa (0 + 615016)) 1 = Some (word_to_le_bytes 1 (wa seq)) ;
  md1_kwr5 : forall d k, 0 <= d -> d + Z.of_nat k <= 1 -> store_ok SEGS m (wa (0 + 615016 + d)) k = true ;
  md1_kwr6 : forall d k, 0 <= d -> d + Z.of_nat k <= 32 -> store_ok SEGS m (wa (0 + 614952 + d)) k = true
}.


#[using="Type"] Lemma md1_setup : forall regs m n res seq, md1_pre regs m n res seq ->
  regs_ok (Ez regs (VALS_md1 n res seq)) AXF_md1.sr_md1 regs /\ know_ok SEGS (Ez regs (VALS_md1 n res seq)) m AXF_md1.kn_md1.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m n res seq P. destruct P as [md1_R8 md1_R9 md1_R10 md1_R18 md1_R19 md1_rng_n md1_rng_res md1_rng_seq md1_kw3 md1_kw4 md1_kwr5 md1_kwr6].
  set (E := Ez regs (VALS_md1 n res seq)).
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = res) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = seq) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_md1.sr_md1.
    apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|]|]|].
    - rewrite md1_R8. reflexivity.
    - rewrite md1_R9. reflexivity.
    - rewrite md1_R10. reflexivity.
    - rewrite md1_R18. reflexivity.
    - rewrite md1_R19, zeval_sound. cbn [zeval edenot AXF_md1.e_n AXF_md1.e_res AXF_md1.e_seq]. rewrite ?Z32, ?Z33, ?Z34. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)]. }
  unfold know_ok, AXF_md1.kn_md1.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_md1.e_n AXF_md1.e_res AXF_md1.e_seq a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range n _ _ md1_rng_n eq_refl eq_refl), ?(mod64_of_range res _ _ md1_rng_res eq_refl eq_refl), ?(mod64_of_range seq _ _ md1_rng_seq eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply md1_kwr5 | apply md1_kwr6]; assumption).
  all: try (clear - md1_rng_n md1_rng_res md1_rng_seq; lia).
  all: first [lia].
Qed.


Definition md1_mem_pmd1i (m : word -> option byte) (regs : bvmap 5 word) (n res seq : Z) : word -> option byte :=
  wbytes (m) (wa (0 + 615016)) (word_to_le_bytes 1 (wa (seq + 1))).

#[using="Type"] Theorem md1_pmd1i : forall regs m rom n res seq, md1_pre regs m n res seq ->
  scs_denot SEGS m (Ez regs (VALS_md1 n res seq)) (snd (fst AXF_md1.RES_pmd1i)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52018) m rom) (mkst R (wa 0x51ca8) (md1_mem_pmd1i m regs n res seq) rom) /\
    getr R 1 = wa 336140 /\ getr R 8 = wa n /\ getr R 9 = wa 614096 /\ getr R 10 = wa (seq + 1) /\ getr R 11 = wa 255 /\ getr R 18 = wa 18446744073709551615 /\ getr R 19 = wa (n + 20) /\ getr R 20 = wa res /\ (forall k, In k [2; 3; 4; 5; 6; 7; 12; 13; 14; 15; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n res seq P Hsc. destruct (md1_setup regs m n res seq P) as [HR HK].
  set (E := Ez regs (VALS_md1 n res seq)) in *. destruct P as [md1_R8 md1_R9 md1_R10 md1_R18 md1_R19 md1_rng_n md1_rng_res md1_rng_seq md1_kw3 md1_kw4 md1_kwr5 md1_kwr6].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = res) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = seq) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51ca8] AXF_md1.scr_pmd1i 0x52018 AXF_md1.sr_md1 AXF_md1.kn_md1 35 _ _ _ E m rom regs AXF_md1.RES_pmd1i_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_md1.RES_pmd1i fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (md1_mem_pmd1i m regs n res seq) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold md1_mem_pmd1i. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition md1_mem_pmd1w (m : word -> option byte) (regs : bvmap 5 word) (n res seq : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (0 + 614952)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 614960)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 614968)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 614976)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 615016)) (word_to_le_bytes 1 (wa 1)).

#[using="Type"] Theorem md1_pmd1w : forall regs m rom n res seq, md1_pre regs m n res seq ->
  scs_denot SEGS m (Ez regs (VALS_md1 n res seq)) (snd (fst AXF_md1.RES_pmd1w)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52018) m rom) (mkst R (wa 0x51ca8) (md1_mem_pmd1w m regs n res seq) rom) /\
    getr R 1 = wa 336140 /\ getr R 8 = wa n /\ getr R 9 = wa 614096 /\ getr R 10 = wa 1 /\ getr R 11 = wa 255 /\ getr R 18 = wa 18446744073709551615 /\ getr R 19 = wa (n + 20) /\ getr R 20 = wa res /\ (forall k, In k [2; 3; 4; 5; 6; 7; 12; 13; 14; 15; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n res seq P Hsc. destruct (md1_setup regs m n res seq P) as [HR HK].
  set (E := Ez regs (VALS_md1 n res seq)) in *. destruct P as [md1_R8 md1_R9 md1_R10 md1_R18 md1_R19 md1_rng_n md1_rng_res md1_rng_seq md1_kw3 md1_kw4 md1_kwr5 md1_kwr6].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = res) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = seq) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51ca8] AXF_md1.scr_pmd1w 0x52018 AXF_md1.sr_md1 AXF_md1.kn_md1 35 _ _ _ E m rom regs AXF_md1.RES_pmd1w_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_md1.RES_pmd1w fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (md1_mem_pmd1w m regs n res seq) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold md1_mem_pmd1w. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MD1.
End AXF_md1z.

Module AXF_md2.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_n := EVar 32.
Definition e_res := EVar 33.
Definition e_mt := EVar 34.
Definition e_ctr := EVar 35.
Definition sr_md2 := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (e_n)) 9 (ELit 614096)) 10 (e_mt)) 18 (ELit 18446744073709551615)) 19 (EAlu ALU_ADD e_n (ELit 20))) 20 (e_res)).
Definition kn_md2 : list kentry :=
  [ KRange e_n 131052 (2^26);
    KRange e_res 4096 (2^47);
    KAlign e_res 4096;
    KRange e_mt 1 (2^63-1);
    KAlign e_mt 8;
    KRange e_ctr 0 (2^32-1);
    KWr (SA e_mt 16) (ELit 24);
    KWr (SA e_res 0) (ELit 8);
    KDisj (SA e_mt 16) (ELit 24) (SA e_res 0) (ELit 8);
    KWord (SA (ELit 0) 614116) 4 e_ctr;
    KWr (SA (ELit 0) 614116) (ELit 4);
    KDisj (SA e_mt 16) (ELit 24) (SA (ELit 0) 614116) (ELit 4);
    KDisj (SA e_res 0) (ELit 8) (SA (ELit 0) 614116) (ELit 4) ].
Definition scr_md2 : scripts := SCR [] [] [].
Definition ss_md2 := SS 0x5210c sr_md2 [] kn_md2 36.
Definition RUN_md2 := sym_exec SEGS 100 true [0x522a4] scr_md2 ss_md2 [].

Definition scr_pmd2 : scripts := SCR [] [] [].
Definition RES_pmd2 := Eval vm_compute in sym_exec SEGS 100 true [0x522a4] scr_pmd2 ss_md2 [].
Lemma RES_pmd2_ok : sym_exec SEGS 100 true [0x522a4] scr_pmd2 (SS 0x5210c sr_md2 [] kn_md2 36) [] = RES_pmd2.
Proof. vm_compute. reflexivity. Qed.
End AXF_md2.

Module AXF_md2z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section MD2.
Context {fx : FPState}.

Definition VALS_md2 (n res mt ctr : Z) : list Z := [n; res; mt; ctr].

Record md2_pre (regs : bvmap 5 word) (m : word -> option byte) (n res mt ctr : Z) : Prop := {
  md2_R8 : getr regs 8 = wa n ;
  md2_R9 : getr regs 9 = wa 614096 ;
  md2_R10 : getr regs 10 = wa mt ;
  md2_R18 : getr regs 18 = wa 18446744073709551615 ;
  md2_R19 : getr regs 19 = wa (n + 20) ;
  md2_R20 : getr regs 20 = wa res ;
  md2_rng_n : 131052 <= n <= 2^26 ;
  md2_rng_res : 4096 <= res <= 2^47 ;
  md2_rng_mt : 1 <= mt <= 2^63-1 ;
  md2_rng_ctr : 0 <= ctr <= 2^32-1 ;
  md2_ka2 : res mod 4096 = 0 ;
  md2_ka4 : mt mod 8 = 0 ;
  md2_kwr6 : forall d k, 0 <= d -> d + Z.of_nat k <= 24 -> store_ok SEGS m (wa (mt + 16 + d)) k = true ;
  md2_kwr7 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (res + 0 + d)) k = true ;
  md2_kd8 : mt + 16 + 24 <= res + 0 \/ res + 0 + 8 <= mt + 16 ;
  md2_kw9 : rdn SEGS m (wa (0 + 614116)) 4 = Some (word_to_le_bytes 4 (wa ctr)) ;
  md2_kwr10 : forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (0 + 614116 + d)) k = true ;
  md2_kd11 : mt + 16 + 24 <= 0 + 614116 \/ 0 + 614116 + 4 <= mt + 16 ;
  md2_kd12 : res + 0 + 8 <= 0 + 614116 \/ 0 + 614116 + 4 <= res + 0
}.


#[using="Type"] Lemma md2_setup : forall regs m n res mt ctr, md2_pre regs m n res mt ctr ->
  regs_ok (Ez regs (VALS_md2 n res mt ctr)) AXF_md2.sr_md2 regs /\ know_ok SEGS (Ez regs (VALS_md2 n res mt ctr)) m AXF_md2.kn_md2.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m n res mt ctr P. destruct P as [md2_R8 md2_R9 md2_R10 md2_R18 md2_R19 md2_R20 md2_rng_n md2_rng_res md2_rng_mt md2_rng_ctr md2_ka2 md2_ka4 md2_kwr6 md2_kwr7 md2_kd8 md2_kw9 md2_kwr10 md2_kd11 md2_kd12].
  set (E := Ez regs (VALS_md2 n res mt ctr)).
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = res) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = mt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = ctr) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_md2.sr_md2.
    apply (regs_ok_pin E _ regs 20); [apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|]|]|]|].
    - rewrite md2_R8. reflexivity.
    - rewrite md2_R9. reflexivity.
    - rewrite md2_R10. reflexivity.
    - rewrite md2_R18. reflexivity.
    - rewrite md2_R19, zeval_sound. cbn [zeval edenot AXF_md2.e_n AXF_md2.e_res AXF_md2.e_mt AXF_md2.e_ctr]. rewrite ?Z32, ?Z33, ?Z34, ?Z35. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite md2_R20. reflexivity. }
  unfold know_ok, AXF_md2.kn_md2.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_md2.e_n AXF_md2.e_res AXF_md2.e_mt AXF_md2.e_ctr a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range n _ _ md2_rng_n eq_refl eq_refl), ?(mod64_of_range res _ _ md2_rng_res eq_refl eq_refl), ?(mod64_of_range mt _ _ md2_rng_mt eq_refl eq_refl), ?(mod64_of_range ctr _ _ md2_rng_ctr eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply md2_kwr6 | apply md2_kwr7 | apply md2_kwr10]; assumption).
  all: try (clear - md2_rng_n md2_rng_res md2_rng_mt md2_rng_ctr md2_ka2 md2_ka4; lia).
  all: first [(clear - md2_rng_n md2_rng_res md2_rng_mt md2_rng_ctr md2_ka2 md2_ka4 md2_kd8; lia) | (clear - md2_rng_n md2_rng_res md2_rng_mt md2_rng_ctr md2_ka2 md2_ka4 md2_kd11; lia) | (clear - md2_rng_n md2_rng_res md2_rng_mt md2_rng_ctr md2_ka2 md2_ka4 md2_kd12; lia) | lia].
Qed.


Definition md2_mem_pmd2 (m : word -> option byte) (regs : bvmap 5 word) (n res mt ctr : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (mt + 16)) (word_to_le_bytes 8 (wa res))) (wa (res + 0)) (word_to_le_bytes 8 (wa mt))) (wa (mt + 32)) (word_to_le_bytes 8 (wa ((4096 * Z.shiftr (((n + 4115)) mod 2^64) 12) + 4064)))) (wa (mt + 28)) (word_to_le_bytes 4 (wa 0))) (wa (mt + 24)) (word_to_le_bytes 4 (wa 0))) (wa (0 + 614116)) (word_to_le_bytes 4 (wa (ext_Z true 0 4 ctr + 1))).

#[using="Type"] Theorem md2_pmd2 : forall regs m rom n res mt ctr, md2_pre regs m n res mt ctr ->
  scs_denot SEGS m (Ez regs (VALS_md2 n res mt ctr)) (snd (fst AXF_md2.RES_pmd2)) ->
  exists R, msteps SEGS (mkst regs (wa 0x5210c) m rom) (mkst R (wa 0x522a4) (md2_mem_pmd2 m regs n res mt ctr) rom) /\
    getr R 8 = wa n /\ getr R 9 = wa 614096 /\ getr R 10 = wa (ext_Z true 0 4 ctr + 1) /\ getr R 11 = wa (2048 * Z.shiftr (((n + 4115)) mod 2^64) 11) /\ getr R 18 = wa mt /\ getr R 19 = wa 0 /\ getr R 20 = wa res /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 12; 13; 14; 15; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n res mt ctr P Hsc. destruct (md2_setup regs m n res mt ctr P) as [HR HK].
  set (E := Ez regs (VALS_md2 n res mt ctr)) in *. destruct P as [md2_R8 md2_R9 md2_R10 md2_R18 md2_R19 md2_R20 md2_rng_n md2_rng_res md2_rng_mt md2_rng_ctr md2_ka2 md2_ka4 md2_kwr6 md2_kwr7 md2_kd8 md2_kw9 md2_kwr10 md2_kd11 md2_kd12].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = res) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = mt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = ctr) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x522a4] AXF_md2.scr_pmd2 0x5210c AXF_md2.sr_md2 AXF_md2.kn_md2 36 _ _ _ E m rom regs AXF_md2.RES_pmd2_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_md2.RES_pmd2 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (md2_mem_pmd2 m regs n res mt ctr) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold md2_mem_pmd2. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MD2.
End AXF_md2z.

Module AXF_mmrd.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_sp0 := EVar 32.
Definition e_res := EVar 33.
Definition e_ad := EVar 34.
Definition e_s00 := EVar 35.
Definition e_s10 := EVar 36.
Definition e_s20 := EVar 37.
Definition e_s30 := EVar 38.
Definition e_s40 := EVar 39.
Definition e_s50 := EVar 40.
Definition sr_mmrd := (sr_upd (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-64)))) 10 (e_res)) 16 (e_ad)).
Definition kn_mmrd : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KRange e_res 4096 (2^47);
    KRange e_ad 0 (2^63-1);
    KWord (SA e_sp0 (-8)) 8 (ELit 335896);
    KWord (SA e_sp0 (-16)) 8 e_s00;
    KWord (SA e_sp0 (-24)) 8 e_s10;
    KWord (SA e_sp0 (-32)) 8 e_s20;
    KWord (SA e_sp0 (-40)) 8 e_s30;
    KWord (SA e_sp0 (-48)) 8 e_s40;
    KWord (SA e_sp0 (-56)) 8 e_s50;
    KRange e_s00 0 (2^64-1);
    KRange e_s10 0 (2^64-1);
    KRange e_s20 0 (2^64-1);
    KRange e_s30 0 (2^64-1);
    KRange e_s40 0 (2^64-1);
    KRange e_s50 0 (2^64-1) ].
Definition scr_mmrd : scripts := SCR [] [] [].
Definition ss_mmrd := SS 0x533f0 sr_mmrd [] kn_mmrd 41.
Definition RUN_mmrd := sym_exec SEGS 100 true [0x52018] scr_mmrd ss_mmrd [].

Definition scr_pmrd : scripts := SCR [] [] [].
Definition RES_pmrd := Eval vm_compute in sym_exec SEGS 100 true [0x52018] scr_pmrd ss_mmrd [].
Lemma RES_pmrd_ok : sym_exec SEGS 100 true [0x52018] scr_pmrd (SS 0x533f0 sr_mmrd [] kn_mmrd 41) [] = RES_pmrd.
Proof. vm_compute. reflexivity. Qed.
End AXF_mmrd.

Module AXF_mmrdz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section MMRD.
Context {fx : FPState}.

Definition VALS_mmrd (sp0 res ad s00 s10 s20 s30 s40 s50 : Z) : list Z := [sp0; res; ad; s00; s10; s20; s30; s40; s50].

Record mmrd_pre (regs : bvmap 5 word) (m : word -> option byte) (sp0 res ad s00 s10 s20 s30 s40 s50 : Z) : Prop := {
  mmrd_R2 : getr regs 2 = wa (sp0 + -64) ;
  mmrd_R10 : getr regs 10 = wa res ;
  mmrd_R16 : getr regs 16 = wa ad ;
  mmrd_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  mmrd_rng_res : 4096 <= res <= 2^47 ;
  mmrd_rng_ad : 0 <= ad <= 2^63-1 ;
  mmrd_rng_s00 : 0 <= s00 <= 2^64-1 ;
  mmrd_rng_s10 : 0 <= s10 <= 2^64-1 ;
  mmrd_rng_s20 : 0 <= s20 <= 2^64-1 ;
  mmrd_rng_s30 : 0 <= s30 <= 2^64-1 ;
  mmrd_rng_s40 : 0 <= s40 <= 2^64-1 ;
  mmrd_rng_s50 : 0 <= s50 <= 2^64-1 ;
  mmrd_ka1 : sp0 mod 16 = 0 ;
  mmrd_kw4 : rdn SEGS m (wa (sp0 + -8)) 8 = Some (word_to_le_bytes 8 (wa 335896)) ;
  mmrd_kw5 : rdn SEGS m (wa (sp0 + -16)) 8 = Some (word_to_le_bytes 8 (wa s00)) ;
  mmrd_kw6 : rdn SEGS m (wa (sp0 + -24)) 8 = Some (word_to_le_bytes 8 (wa s10)) ;
  mmrd_kw7 : rdn SEGS m (wa (sp0 + -32)) 8 = Some (word_to_le_bytes 8 (wa s20)) ;
  mmrd_kw8 : rdn SEGS m (wa (sp0 + -40)) 8 = Some (word_to_le_bytes 8 (wa s30)) ;
  mmrd_kw9 : rdn SEGS m (wa (sp0 + -48)) 8 = Some (word_to_le_bytes 8 (wa s40)) ;
  mmrd_kw10 : rdn SEGS m (wa (sp0 + -56)) 8 = Some (word_to_le_bytes 8 (wa s50))
}.


#[using="Type"] Lemma mmrd_setup : forall regs m sp0 res ad s00 s10 s20 s30 s40 s50, mmrd_pre regs m sp0 res ad s00 s10 s20 s30 s40 s50 ->
  regs_ok (Ez regs (VALS_mmrd sp0 res ad s00 s10 s20 s30 s40 s50)) AXF_mmrd.sr_mmrd regs /\ know_ok SEGS (Ez regs (VALS_mmrd sp0 res ad s00 s10 s20 s30 s40 s50)) m AXF_mmrd.kn_mmrd.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sp0 res ad s00 s10 s20 s30 s40 s50 P. destruct P as [mmrd_R2 mmrd_R10 mmrd_R16 mmrd_rng_sp0 mmrd_rng_res mmrd_rng_ad mmrd_rng_s00 mmrd_rng_s10 mmrd_rng_s20 mmrd_rng_s30 mmrd_rng_s40 mmrd_rng_s50 mmrd_ka1 mmrd_kw4 mmrd_kw5 mmrd_kw6 mmrd_kw7 mmrd_kw8 mmrd_kw9 mmrd_kw10].
  set (E := Ez regs (VALS_mmrd sp0 res ad s00 s10 s20 s30 s40 s50)).
  assert (Z32 : bv_unsigned (ev E 32) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = res) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = ad) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = s00) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = s10) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = s20) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = s30) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = s40) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = s50) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mmrd.sr_mmrd.
    apply (regs_ok_pin E _ regs 16); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|]|]|].
    - rewrite mmrd_R2, zeval_sound. cbn [zeval edenot AXF_mmrd.e_sp0 AXF_mmrd.e_res AXF_mmrd.e_ad AXF_mmrd.e_s00 AXF_mmrd.e_s10 AXF_mmrd.e_s20 AXF_mmrd.e_s30 AXF_mmrd.e_s40 AXF_mmrd.e_s50]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite mmrd_R10. reflexivity.
    - rewrite mmrd_R16. reflexivity. }
  unfold know_ok, AXF_mmrd.kn_mmrd.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mmrd.e_sp0 AXF_mmrd.e_res AXF_mmrd.e_ad AXF_mmrd.e_s00 AXF_mmrd.e_s10 AXF_mmrd.e_s20 AXF_mmrd.e_s30 AXF_mmrd.e_s40 AXF_mmrd.e_s50 a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sp0 _ _ mmrd_rng_sp0 eq_refl eq_refl), ?(mod64_of_range res _ _ mmrd_rng_res eq_refl eq_refl), ?(mod64_of_range ad _ _ mmrd_rng_ad eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - mmrd_rng_sp0 mmrd_rng_res mmrd_rng_ad mmrd_rng_s00 mmrd_rng_s10 mmrd_rng_s20 mmrd_rng_s30 mmrd_rng_s40 mmrd_rng_s50 mmrd_ka1; lia).
  all: first [lia].
Qed.


Definition mmrd_mem_pmrd (m : word -> option byte) (regs : bvmap 5 word) (sp0 res ad s00 s10 s20 s30 s40 s50 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mmrd_pmrd : forall regs m rom sp0 res ad s00 s10 s20 s30 s40 s50, mmrd_pre regs m sp0 res ad s00 s10 s20 s30 s40 s50 ->
  scs_denot SEGS m (Ez regs (VALS_mmrd sp0 res ad s00 s10 s20 s30 s40 s50)) (snd (fst AXF_mmrd.RES_pmrd)) ->
  exists R, msteps SEGS (mkst regs (wa 0x533f0) m rom) (mkst R (wa 0x52018) (mmrd_mem_pmrd m regs sp0 res ad s00 s10 s20 s30 s40 s50) rom) /\
    getr R 1 = wa 335896 /\ getr R 2 = wa sp0 /\ getr R 8 = wa s00 /\ getr R 9 = wa s10 /\ getr R 10 = wa res /\ getr R 11 = wa 18446744073709547521 /\ getr R 16 = wa ad /\ getr R 18 = wa s20 /\ getr R 19 = wa s30 /\ getr R 20 = wa s40 /\ getr R 21 = wa s50 /\ (forall k, In k [3; 4; 5; 6; 7; 12; 13; 14; 15; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sp0 res ad s00 s10 s20 s30 s40 s50 P Hsc. destruct (mmrd_setup regs m sp0 res ad s00 s10 s20 s30 s40 s50 P) as [HR HK].
  set (E := Ez regs (VALS_mmrd sp0 res ad s00 s10 s20 s30 s40 s50)) in *. destruct P as [mmrd_R2 mmrd_R10 mmrd_R16 mmrd_rng_sp0 mmrd_rng_res mmrd_rng_ad mmrd_rng_s00 mmrd_rng_s10 mmrd_rng_s20 mmrd_rng_s30 mmrd_rng_s40 mmrd_rng_s50 mmrd_ka1 mmrd_kw4 mmrd_kw5 mmrd_kw6 mmrd_kw7 mmrd_kw8 mmrd_kw9 mmrd_kw10].
  assert (Z32 : bv_unsigned (ev E 32) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = res) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = ad) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = s00) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = s10) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = s20) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = s30) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = s40) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = s50) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x52018] AXF_mmrd.scr_pmrd 0x533f0 AXF_mmrd.sr_mmrd AXF_mmrd.kn_mmrd 41 _ _ _ E m rom regs AXF_mmrd.RES_pmrd_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mmrd.RES_pmrd fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mmrd_mem_pmrd m regs sp0 res ad s00 s10 s20 s30 s40 s50) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mmrd_mem_pmrd. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MMRD.
End AXF_mmrdz.

Module AXF_mp63.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_G := EVar 32.
Definition e_sp0 := EVar 33.
Definition e_W := EVar 34.
Definition e_SEQ := EVar 36.
Definition e_MEM := EVar 37.
Definition STK := SA e_sp0 (-1024).
Definition SC := EAlu ALU_SRL (EMd M_MUL (ELit 4503599627370496) e_W) (ELit 58).
Definition sr_mp63 := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-96)))) 9 (ELit 0x95e40)) 10 (e_G)) 18 (ELit 0x95ed8)).
Definition kn_mp63 : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWr STK (ELit 1024);
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange SC 63 63;
    KWord (SA e_G 32) 8 e_W;
    KWord (SA e_G 16) 8 e_MEM;
    KWord (SA (ELit 0) 0x96268) 1 e_SEQ;
    KWr (SA (ELit 0) 0x96228) (ELit 32);
    KWr (SA (ELit 0) 0x96268) (ELit 1);
    KDisj STK (ELit 1024) (SA e_G 0) (ELit 40);
    KDisj STK (ELit 1024) (SA (ELit 0) 0x96228) (ELit 72);
    KDisj (SA e_G 0) (ELit 40) (SA (ELit 0) 0x96228) (ELit 72) ].
Definition scr_mp63 : scripts := SCR [] [] [].
Definition ss_mp63 := SS 0x51af8 sr_mp63 [] kn_mp63 38.
Definition RUN_mp63 := sym_exec SEGS 100 true [0x51bb4] scr_mp63 ss_mp63 [].

Definition scr_pm63a : scripts := SCR [true; true] [] [].
Definition RES_pm63a := Eval vm_compute in sym_exec SEGS 100 true [0x51bb4] scr_pm63a ss_mp63 [].
Lemma RES_pm63a_ok : sym_exec SEGS 100 true [0x51bb4] scr_pm63a (SS 0x51af8 sr_mp63 [] kn_mp63 38) [] = RES_pm63a.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pm63b : scripts := SCR [true; false] [] [].
Definition RES_pm63b := Eval vm_compute in sym_exec SEGS 100 true [0x51bb4] scr_pm63b ss_mp63 [].
Lemma RES_pm63b_ok : sym_exec SEGS 100 true [0x51bb4] scr_pm63b (SS 0x51af8 sr_mp63 [] kn_mp63 38) [] = RES_pm63b.
Proof. vm_compute. reflexivity. Qed.
End AXF_mp63.

Module AXF_mp63z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section MP63.
Context {fx : FPState}.

Definition VALS_mp63 (G sp0 W SEQ MEM : Z) : list Z := [G; sp0; W; 0; SEQ; MEM].

Record mp63_pre (regs : bvmap 5 word) (m : word -> option byte) (G sp0 W SEQ MEM : Z) : Prop := {
  mp63_R2 : getr regs 2 = wa (sp0 + -96) ;
  mp63_R9 : getr regs 9 = wa 613952 ;
  mp63_R10 : getr regs 10 = wa G ;
  mp63_R18 : getr regs 18 = wa 614104 ;
  mp63_HSTK : stk_ok SEGS m (wa sp0) 1024 ;
  mp63_rng_G : 1 <= G <= 2^63-1 ;
  mp63_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  mp63_rng_W : 0 <= W <= 2^64-1 ;
  mp63_rng_SEQ : 0 <= SEQ <= 255 ;
  mp63_rng_MEM : 0 <= MEM <= 2^64-1 ;
  mp63_ka1 : sp0 mod 16 = 0 ;
  mp63_ka4 : G mod 8 = 0 ;
  mp63_kr5 : 63 <= SCW W <= 63 ;
  mp63_kw6 : rdn SEGS m (wa (G + 32)) 8 = Some (word_to_le_bytes 8 (wa W)) ;
  mp63_kw7 : rdn SEGS m (wa (G + 16)) 8 = Some (word_to_le_bytes 8 (wa MEM)) ;
  mp63_kw8 : rdn SEGS m (wa (0 + 615016)) 1 = Some (word_to_le_bytes 1 (wa SEQ)) ;
  mp63_kwr9 : forall d k, 0 <= d -> d + Z.of_nat k <= 32 -> store_ok SEGS m (wa (0 + 614952 + d)) k = true ;
  mp63_kwr10 : forall d k, 0 <= d -> d + Z.of_nat k <= 1 -> store_ok SEGS m (wa (0 + 615016 + d)) k = true ;
  mp63_kd11 : sp0 + -1024 + 1024 <= G + 0 \/ G + 0 + 40 <= sp0 + -1024 ;
  mp63_kd12 : sp0 + -1024 + 1024 <= 0 + 614952 \/ 0 + 614952 + 72 <= sp0 + -1024 ;
  mp63_kd13 : G + 0 + 40 <= 0 + 614952 \/ 0 + 614952 + 72 <= G + 0
}.


#[using="Type"] Lemma mp63_setup : forall regs m G sp0 W SEQ MEM, mp63_pre regs m G sp0 W SEQ MEM ->
  regs_ok (Ez regs (VALS_mp63 G sp0 W SEQ MEM)) AXF_mp63.sr_mp63 regs /\ know_ok SEGS (Ez regs (VALS_mp63 G sp0 W SEQ MEM)) m AXF_mp63.kn_mp63.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G sp0 W SEQ MEM P. destruct P as [mp63_R2 mp63_R9 mp63_R10 mp63_R18 mp63_HSTK mp63_rng_G mp63_rng_sp0 mp63_rng_W mp63_rng_SEQ mp63_rng_MEM mp63_ka1 mp63_ka4 mp63_kr5 mp63_kw6 mp63_kw7 mp63_kw8 mp63_kwr9 mp63_kwr10 mp63_kd11 mp63_kd12 mp63_kd13].
  set (E := Ez regs (VALS_mp63 G sp0 W SEQ MEM)).
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = SEQ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = MEM) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mp63.sr_mp63.
    apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|]|]|]|].
    - rewrite mp63_R2, zeval_sound. cbn [zeval edenot AXF_mp63.e_G AXF_mp63.e_sp0 AXF_mp63.e_W AXF_mp63.e_SEQ AXF_mp63.e_MEM AXF_mp63.STK AXF_mp63.SC]. rewrite ?Z32, ?Z33, ?Z34, ?Z36, ?Z37. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite mp63_R9. reflexivity.
    - rewrite mp63_R10. reflexivity.
    - rewrite mp63_R18. reflexivity. }
  unfold know_ok, AXF_mp63.kn_mp63.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_mp63.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mp63.e_G AXF_mp63.e_sp0 AXF_mp63.e_W AXF_mp63.e_SEQ AXF_mp63.e_MEM AXF_mp63.STK AXF_mp63.SC a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z36, ?Z37.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range G _ _ mp63_rng_G eq_refl eq_refl), ?(mod64_of_range sp0 _ _ mp63_rng_sp0 eq_refl eq_refl), ?(mod64_of_range SEQ _ _ mp63_rng_SEQ eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply mp63_kwr9 | apply mp63_kwr10]; assumption).
  all: try (clear - mp63_rng_G mp63_rng_sp0 mp63_rng_W mp63_rng_SEQ mp63_rng_MEM mp63_ka1 mp63_ka4 mp63_kr5; lia).
  all: first [(clear - mp63_rng_G mp63_rng_sp0 mp63_rng_W mp63_rng_SEQ mp63_rng_MEM mp63_ka1 mp63_ka4 mp63_kr5 mp63_kd11; lia) | (clear - mp63_rng_G mp63_rng_sp0 mp63_rng_W mp63_rng_SEQ mp63_rng_MEM mp63_ka1 mp63_ka4 mp63_kr5 mp63_kd12; lia) | (clear - mp63_rng_G mp63_rng_sp0 mp63_rng_W mp63_rng_SEQ mp63_rng_MEM mp63_ka1 mp63_ka4 mp63_kr5 mp63_kd13; lia) | lia].
Qed.


Definition mp63_mem_pm63a (m : word -> option byte) (regs : bvmap 5 word) (G sp0 W SEQ MEM : Z) : word -> option byte :=
  wbytes (m) (wa (0 + 615016)) (word_to_le_bytes 1 (wa (ext_Z false 0 1 SEQ + 1))).

#[using="Type"] Theorem mp63_pm63a : forall regs m rom G sp0 W SEQ MEM, mp63_pre regs m G sp0 W SEQ MEM ->
  scs_denot SEGS m (Ez regs (VALS_mp63 G sp0 W SEQ MEM)) (snd (fst AXF_mp63.RES_pm63a)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51af8) m rom) (mkst R (wa 0x51bb4) (mp63_mem_pm63a m regs G sp0 W SEQ MEM) rom) /\
    getr R 2 = wa (sp0 + -96) /\ getr R 9 = wa 613952 /\ getr R 10 = wa G /\ getr R 11 = wa (4096 * Z.shiftr W 12) /\ getr R 12 = wa MEM /\ getr R 13 = wa 18446744073709547520 /\ getr R 18 = wa 614104 /\ (forall k, In k [1; 3; 4; 5; 6; 7; 8; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G sp0 W SEQ MEM P Hsc. destruct (mp63_setup regs m G sp0 W SEQ MEM P) as [HR HK].
  set (E := Ez regs (VALS_mp63 G sp0 W SEQ MEM)) in *. destruct P as [mp63_R2 mp63_R9 mp63_R10 mp63_R18 mp63_HSTK mp63_rng_G mp63_rng_sp0 mp63_rng_W mp63_rng_SEQ mp63_rng_MEM mp63_ka1 mp63_ka4 mp63_kr5 mp63_kw6 mp63_kw7 mp63_kw8 mp63_kwr9 mp63_kwr10 mp63_kd11 mp63_kd12 mp63_kd13].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = SEQ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = MEM) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51bb4] AXF_mp63.scr_pm63a 0x51af8 AXF_mp63.sr_mp63 AXF_mp63.kn_mp63 38 _ _ _ E m rom regs AXF_mp63.RES_pm63a_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mp63.RES_pm63a fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mp63_mem_pm63a m regs G sp0 W SEQ MEM) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mp63_mem_pm63a. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition mp63_mem_pm63b (m : word -> option byte) (regs : bvmap 5 word) (G sp0 W SEQ MEM : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (0 + 614952)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 614960)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 614968)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 614976)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 615016)) (word_to_le_bytes 1 (wa 1)).

#[using="Type"] Theorem mp63_pm63b : forall regs m rom G sp0 W SEQ MEM, mp63_pre regs m G sp0 W SEQ MEM ->
  scs_denot SEGS m (Ez regs (VALS_mp63 G sp0 W SEQ MEM)) (snd (fst AXF_mp63.RES_pm63b)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51af8) m rom) (mkst R (wa 0x51bb4) (mp63_mem_pm63b m regs G sp0 W SEQ MEM) rom) /\
    getr R 2 = wa (sp0 + -96) /\ getr R 9 = wa 613952 /\ getr R 10 = wa G /\ getr R 11 = wa (4096 * Z.shiftr W 12) /\ getr R 12 = wa MEM /\ getr R 13 = wa 18446744073709547520 /\ getr R 18 = wa 614104 /\ (forall k, In k [1; 3; 4; 5; 6; 7; 8; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G sp0 W SEQ MEM P Hsc. destruct (mp63_setup regs m G sp0 W SEQ MEM P) as [HR HK].
  set (E := Ez regs (VALS_mp63 G sp0 W SEQ MEM)) in *. destruct P as [mp63_R2 mp63_R9 mp63_R10 mp63_R18 mp63_HSTK mp63_rng_G mp63_rng_sp0 mp63_rng_W mp63_rng_SEQ mp63_rng_MEM mp63_ka1 mp63_ka4 mp63_kr5 mp63_kw6 mp63_kw7 mp63_kw8 mp63_kwr9 mp63_kwr10 mp63_kd11 mp63_kd12 mp63_kd13].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = SEQ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = MEM) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51bb4] AXF_mp63.scr_pm63b 0x51af8 AXF_mp63.sr_mp63 AXF_mp63.kn_mp63 38 _ _ _ E m rom regs AXF_mp63.RES_pm63b_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mp63.RES_pm63b fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mp63_mem_pm63b m regs G sp0 W SEQ MEM) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mp63_mem_pm63b. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MP63.
End AXF_mp63z.

Module AXF_mps.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_G := EVar 32.
Definition e_sp0 := EVar 33.
Definition e_W := EVar 34.
Definition e_USG := EVar 35.
Definition e_SEQ := EVar 36.
Definition e_MEM := EVar 37.
Definition STK := SA e_sp0 (-1024).
Definition SC := EAlu ALU_SRL (EMd M_MUL (ELit 4503599627370496) e_W) (ELit 58).
Definition SC8 := EMd M_MUL (ELit 8) SC.
Definition SCM7 := EAlu ALU_ADD SC (ELit (-7)).
Definition sr_mps := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-96)))) 9 (ELit 0x95e40)) 10 (e_G)) 18 (ELit 0x95ed8)).
Definition kn_mps : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWr STK (ELit 1024);
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange SC 0 47;
    KRange SC8 0 376;
    KWord (SA e_G 32) 8 e_W;
    KWord (SA e_G 16) 8 e_MEM;
    KWord (SA SC8 614568) 8 e_USG;
    KWord (SA (ELit 0) 0x96268) 1 e_SEQ;
    KWr (SA SC8 614568) (ELit 8);
    KWr (SA (ELit 0) 0x96228) (ELit 32);
    KWr (SA (ELit 0) 0x96268) (ELit 1);
    KWr (SA SC 614945) (ELit 1);
    KDisj STK (ELit 1024) (SA SC 614945) (ELit 1);
    KDisj (SA e_G 0) (ELit 40) (SA SC 614945) (ELit 1);
    KDisj STK (ELit 1024) (SA e_G 0) (ELit 40);
    KDisj STK (ELit 1024) (SA SC8 614568) (ELit 8);
    KDisj STK (ELit 1024) (SA (ELit 0) 0x96228) (ELit 72);
    KDisj (SA e_G 0) (ELit 40) (SA SC8 614568) (ELit 8);
    KDisj (SA e_G 0) (ELit 40) (SA (ELit 0) 0x96228) (ELit 72) ].
Definition scr_mps : scripts := SCR [] [] [].
Definition ss_mps := SS 0x51af8 sr_mps [] kn_mps 38.
Definition RUN_mps := sym_exec SEGS 100 true [0x51bb4] scr_mps ss_mps [].

Definition scr_pmpa : scripts := SCR [true; true; false] [] [].
Definition RES_pmpa := Eval vm_compute in sym_exec SEGS 100 true [0x51bb4] scr_pmpa ss_mps [].
Lemma RES_pmpa_ok : sym_exec SEGS 100 true [0x51bb4] scr_pmpa (SS 0x51af8 sr_mps [] kn_mps 38) [] = RES_pmpa.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmpb : scripts := SCR [true; true; true] [] [].
Definition RES_pmpb := Eval vm_compute in sym_exec SEGS 100 true [0x51bb4] scr_pmpb ss_mps [].
Lemma RES_pmpb_ok : sym_exec SEGS 100 true [0x51bb4] scr_pmpb (SS 0x51af8 sr_mps [] kn_mps 38) [] = RES_pmpb.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmpc : scripts := SCR [true; false; false] [] [].
Definition RES_pmpc := Eval vm_compute in sym_exec SEGS 100 true [0x51bb4] scr_pmpc ss_mps [].
Lemma RES_pmpc_ok : sym_exec SEGS 100 true [0x51bb4] scr_pmpc (SS 0x51af8 sr_mps [] kn_mps 38) [] = RES_pmpc.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmpd : scripts := SCR [true; false; true] [] [].
Definition RES_pmpd := Eval vm_compute in sym_exec SEGS 100 true [0x51bb4] scr_pmpd ss_mps [].
Lemma RES_pmpd_ok : sym_exec SEGS 100 true [0x51bb4] scr_pmpd (SS 0x51af8 sr_mps [] kn_mps 38) [] = RES_pmpd.
Proof. vm_compute. reflexivity. Qed.
End AXF_mps.

Module AXF_mpsz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section MPS.
Context {fx : FPState}.

Definition VALS_mps (G sp0 W USG SEQ MEM : Z) : list Z := [G; sp0; W; USG; SEQ; MEM].

Record mps_pre (regs : bvmap 5 word) (m : word -> option byte) (G sp0 W USG SEQ MEM : Z) : Prop := {
  mps_R2 : getr regs 2 = wa (sp0 + -96) ;
  mps_R9 : getr regs 9 = wa 613952 ;
  mps_R10 : getr regs 10 = wa G ;
  mps_R18 : getr regs 18 = wa 614104 ;
  mps_HSTK : stk_ok SEGS m (wa sp0) 1024 ;
  mps_rng_G : 1 <= G <= 2^63-1 ;
  mps_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  mps_rng_W : 0 <= W <= 2^64-1 ;
  mps_rng_USG : 0 <= USG <= 2^64-1 ;
  mps_rng_SEQ : 0 <= SEQ <= 255 ;
  mps_rng_MEM : 0 <= MEM <= 2^64-1 ;
  mps_ka1 : sp0 mod 16 = 0 ;
  mps_ka4 : G mod 8 = 0 ;
  mps_kr5 : 0 <= SCW W <= 47 ;
  mps_kr6 : 0 <= 8 * SCW W <= 376 ;
  mps_kw7 : rdn SEGS m (wa (G + 32)) 8 = Some (word_to_le_bytes 8 (wa W)) ;
  mps_kw8 : rdn SEGS m (wa (G + 16)) 8 = Some (word_to_le_bytes 8 (wa MEM)) ;
  mps_kw9 : rdn SEGS m (wa (8 * SCW W + 614568)) 8 = Some (word_to_le_bytes 8 (wa USG)) ;
  mps_kw10 : rdn SEGS m (wa (0 + 615016)) 1 = Some (word_to_le_bytes 1 (wa SEQ)) ;
  mps_kwr11 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (8 * SCW W + 614568 + d)) k = true ;
  mps_kwr12 : forall d k, 0 <= d -> d + Z.of_nat k <= 32 -> store_ok SEGS m (wa (0 + 614952 + d)) k = true ;
  mps_kwr13 : forall d k, 0 <= d -> d + Z.of_nat k <= 1 -> store_ok SEGS m (wa (0 + 615016 + d)) k = true ;
  mps_kwr14 : forall d k, 0 <= d -> d + Z.of_nat k <= 1 -> store_ok SEGS m (wa (SCW W + 614945 + d)) k = true ;
  mps_kd15 : sp0 + -1024 + 1024 <= SCW W + 614945 \/ SCW W + 614945 + 1 <= sp0 + -1024 ;
  mps_kd16 : G + 0 + 40 <= SCW W + 614945 \/ SCW W + 614945 + 1 <= G + 0 ;
  mps_kd17 : sp0 + -1024 + 1024 <= G + 0 \/ G + 0 + 40 <= sp0 + -1024 ;
  mps_kd18 : sp0 + -1024 + 1024 <= 8 * SCW W + 614568 \/ 8 * SCW W + 614568 + 8 <= sp0 + -1024 ;
  mps_kd19 : sp0 + -1024 + 1024 <= 0 + 614952 \/ 0 + 614952 + 72 <= sp0 + -1024 ;
  mps_kd20 : G + 0 + 40 <= 8 * SCW W + 614568 \/ 8 * SCW W + 614568 + 8 <= G + 0 ;
  mps_kd21 : G + 0 + 40 <= 0 + 614952 \/ 0 + 614952 + 72 <= G + 0
}.


#[using="Type"] Lemma mps_setup : forall regs m G sp0 W USG SEQ MEM, mps_pre regs m G sp0 W USG SEQ MEM ->
  regs_ok (Ez regs (VALS_mps G sp0 W USG SEQ MEM)) AXF_mps.sr_mps regs /\ know_ok SEGS (Ez regs (VALS_mps G sp0 W USG SEQ MEM)) m AXF_mps.kn_mps.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G sp0 W USG SEQ MEM P. destruct P as [mps_R2 mps_R9 mps_R10 mps_R18 mps_HSTK mps_rng_G mps_rng_sp0 mps_rng_W mps_rng_USG mps_rng_SEQ mps_rng_MEM mps_ka1 mps_ka4 mps_kr5 mps_kr6 mps_kw7 mps_kw8 mps_kw9 mps_kw10 mps_kwr11 mps_kwr12 mps_kwr13 mps_kwr14 mps_kd15 mps_kd16 mps_kd17 mps_kd18 mps_kd19 mps_kd20 mps_kd21].
  set (E := Ez regs (VALS_mps G sp0 W USG SEQ MEM)).
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = USG) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = SEQ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = MEM) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mps.sr_mps.
    apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|]|]|]|].
    - rewrite mps_R2, zeval_sound. cbn [zeval edenot AXF_mps.e_G AXF_mps.e_sp0 AXF_mps.e_W AXF_mps.e_USG AXF_mps.e_SEQ AXF_mps.e_MEM AXF_mps.STK AXF_mps.SC AXF_mps.SC8 AXF_mps.SCM7]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite mps_R9. reflexivity.
    - rewrite mps_R10. reflexivity.
    - rewrite mps_R18. reflexivity. }
  unfold know_ok, AXF_mps.kn_mps.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_mps.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mps.e_G AXF_mps.e_sp0 AXF_mps.e_W AXF_mps.e_USG AXF_mps.e_SEQ AXF_mps.e_MEM AXF_mps.STK AXF_mps.SC AXF_mps.SC8 AXF_mps.SCM7 a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range G _ _ mps_rng_G eq_refl eq_refl), ?(mod64_of_range sp0 _ _ mps_rng_sp0 eq_refl eq_refl), ?(mod64_of_range SEQ _ _ mps_rng_SEQ eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply mps_kwr11 | apply mps_kwr12 | apply mps_kwr13 | apply mps_kwr14]; assumption).
  all: try (clear - mps_rng_G mps_rng_sp0 mps_rng_W mps_rng_USG mps_rng_SEQ mps_rng_MEM mps_ka1 mps_ka4 mps_kr5 mps_kr6; lia).
  all: first [(clear - mps_rng_G mps_rng_sp0 mps_rng_W mps_rng_USG mps_rng_SEQ mps_rng_MEM mps_ka1 mps_ka4 mps_kr5 mps_kr6 mps_kd15; lia) | (clear - mps_rng_G mps_rng_sp0 mps_rng_W mps_rng_USG mps_rng_SEQ mps_rng_MEM mps_ka1 mps_ka4 mps_kr5 mps_kr6 mps_kd16; lia) | (clear - mps_rng_G mps_rng_sp0 mps_rng_W mps_rng_USG mps_rng_SEQ mps_rng_MEM mps_ka1 mps_ka4 mps_kr5 mps_kr6 mps_kd17; lia) | (clear - mps_rng_G mps_rng_sp0 mps_rng_W mps_rng_USG mps_rng_SEQ mps_rng_MEM mps_ka1 mps_ka4 mps_kr5 mps_kr6 mps_kd18; lia) | (clear - mps_rng_G mps_rng_sp0 mps_rng_W mps_rng_USG mps_rng_SEQ mps_rng_MEM mps_ka1 mps_ka4 mps_kr5 mps_kr6 mps_kd19; lia) | (clear - mps_rng_G mps_rng_sp0 mps_rng_W mps_rng_USG mps_rng_SEQ mps_rng_MEM mps_ka1 mps_ka4 mps_kr5 mps_kr6 mps_kd20; lia) | (clear - mps_rng_G mps_rng_sp0 mps_rng_W mps_rng_USG mps_rng_SEQ mps_rng_MEM mps_ka1 mps_ka4 mps_kr5 mps_kr6 mps_kd21; lia) | lia].
Qed.


Definition mps_mem_pmpa (m : word -> option byte) (regs : bvmap 5 word) (G sp0 W USG SEQ MEM : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (m) (wa (8 * SCW W + 614568)) (word_to_le_bytes 8 (wa ((USG + Z.land ((((-1 * W) + -1)) mod 2^64) 31) + -32)))) (wa (0 + 615016)) (word_to_le_bytes 1 (wa (ext_Z false 0 1 SEQ + 1)))) (wa (SCW W + 614945)) (word_to_le_bytes 1 (wa (ext_Z false 0 1 SEQ + 1))).

#[using="Type"] Theorem mps_pmpa : forall regs m rom G sp0 W USG SEQ MEM, mps_pre regs m G sp0 W USG SEQ MEM ->
  scs_denot SEGS m (Ez regs (VALS_mps G sp0 W USG SEQ MEM)) (snd (fst AXF_mps.RES_pmpa)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51af8) m rom) (mkst R (wa 0x51bb4) (mps_mem_pmpa m regs G sp0 W USG SEQ MEM) rom) /\
    getr R 2 = wa (sp0 + -96) /\ getr R 9 = wa 613952 /\ getr R 10 = wa G /\ getr R 11 = wa (4096 * Z.shiftr W 12) /\ getr R 12 = wa MEM /\ getr R 13 = wa 18446744073709547520 /\ getr R 14 = wa USG /\ getr R 18 = wa 614104 /\ (forall k, In k [1; 3; 4; 5; 6; 7; 8; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G sp0 W USG SEQ MEM P Hsc. destruct (mps_setup regs m G sp0 W USG SEQ MEM P) as [HR HK].
  set (E := Ez regs (VALS_mps G sp0 W USG SEQ MEM)) in *. destruct P as [mps_R2 mps_R9 mps_R10 mps_R18 mps_HSTK mps_rng_G mps_rng_sp0 mps_rng_W mps_rng_USG mps_rng_SEQ mps_rng_MEM mps_ka1 mps_ka4 mps_kr5 mps_kr6 mps_kw7 mps_kw8 mps_kw9 mps_kw10 mps_kwr11 mps_kwr12 mps_kwr13 mps_kwr14 mps_kd15 mps_kd16 mps_kd17 mps_kd18 mps_kd19 mps_kd20 mps_kd21].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = USG) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = SEQ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = MEM) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51bb4] AXF_mps.scr_pmpa 0x51af8 AXF_mps.sr_mps AXF_mps.kn_mps 38 _ _ _ E m rom regs AXF_mps.RES_pmpa_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mps.RES_pmpa fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mps_mem_pmpa m regs G sp0 W USG SEQ MEM) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mps_mem_pmpa. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition mps_mem_pmpb (m : word -> option byte) (regs : bvmap 5 word) (G sp0 W USG SEQ MEM : Z) : word -> option byte :=
  wbytes (wbytes (m) (wa (8 * SCW W + 614568)) (word_to_le_bytes 8 (wa ((USG + Z.land ((((-1 * W) + -1)) mod 2^64) 31) + -32)))) (wa (0 + 615016)) (word_to_le_bytes 1 (wa (ext_Z false 0 1 SEQ + 1))).

#[using="Type"] Theorem mps_pmpb : forall regs m rom G sp0 W USG SEQ MEM, mps_pre regs m G sp0 W USG SEQ MEM ->
  scs_denot SEGS m (Ez regs (VALS_mps G sp0 W USG SEQ MEM)) (snd (fst AXF_mps.RES_pmpb)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51af8) m rom) (mkst R (wa 0x51bb4) (mps_mem_pmpb m regs G sp0 W USG SEQ MEM) rom) /\
    getr R 2 = wa (sp0 + -96) /\ getr R 9 = wa 613952 /\ getr R 10 = wa G /\ getr R 11 = wa (4096 * Z.shiftr W 12) /\ getr R 12 = wa MEM /\ getr R 13 = wa 18446744073709547520 /\ getr R 14 = wa USG /\ getr R 18 = wa 614104 /\ (forall k, In k [1; 3; 4; 5; 6; 7; 8; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G sp0 W USG SEQ MEM P Hsc. destruct (mps_setup regs m G sp0 W USG SEQ MEM P) as [HR HK].
  set (E := Ez regs (VALS_mps G sp0 W USG SEQ MEM)) in *. destruct P as [mps_R2 mps_R9 mps_R10 mps_R18 mps_HSTK mps_rng_G mps_rng_sp0 mps_rng_W mps_rng_USG mps_rng_SEQ mps_rng_MEM mps_ka1 mps_ka4 mps_kr5 mps_kr6 mps_kw7 mps_kw8 mps_kw9 mps_kw10 mps_kwr11 mps_kwr12 mps_kwr13 mps_kwr14 mps_kd15 mps_kd16 mps_kd17 mps_kd18 mps_kd19 mps_kd20 mps_kd21].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = USG) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = SEQ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = MEM) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51bb4] AXF_mps.scr_pmpb 0x51af8 AXF_mps.sr_mps AXF_mps.kn_mps 38 _ _ _ E m rom regs AXF_mps.RES_pmpb_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mps.RES_pmpb fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mps_mem_pmpb m regs G sp0 W USG SEQ MEM) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mps_mem_pmpb. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition mps_mem_pmpc (m : word -> option byte) (regs : bvmap 5 word) (G sp0 W USG SEQ MEM : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (8 * SCW W + 614568)) (word_to_le_bytes 8 (wa ((USG + Z.land ((((-1 * W) + -1)) mod 2^64) 31) + -32)))) (wa (0 + 614952)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 614960)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 614968)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 614976)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 615016)) (word_to_le_bytes 1 (wa 1))) (wa (SCW W + 614945)) (word_to_le_bytes 1 (wa 1)).

#[using="Type"] Theorem mps_pmpc : forall regs m rom G sp0 W USG SEQ MEM, mps_pre regs m G sp0 W USG SEQ MEM ->
  scs_denot SEGS m (Ez regs (VALS_mps G sp0 W USG SEQ MEM)) (snd (fst AXF_mps.RES_pmpc)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51af8) m rom) (mkst R (wa 0x51bb4) (mps_mem_pmpc m regs G sp0 W USG SEQ MEM) rom) /\
    getr R 2 = wa (sp0 + -96) /\ getr R 9 = wa 613952 /\ getr R 10 = wa G /\ getr R 11 = wa (4096 * Z.shiftr W 12) /\ getr R 12 = wa MEM /\ getr R 13 = wa 18446744073709547520 /\ getr R 14 = wa USG /\ getr R 18 = wa 614104 /\ (forall k, In k [1; 3; 4; 5; 6; 7; 8; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G sp0 W USG SEQ MEM P Hsc. destruct (mps_setup regs m G sp0 W USG SEQ MEM P) as [HR HK].
  set (E := Ez regs (VALS_mps G sp0 W USG SEQ MEM)) in *. destruct P as [mps_R2 mps_R9 mps_R10 mps_R18 mps_HSTK mps_rng_G mps_rng_sp0 mps_rng_W mps_rng_USG mps_rng_SEQ mps_rng_MEM mps_ka1 mps_ka4 mps_kr5 mps_kr6 mps_kw7 mps_kw8 mps_kw9 mps_kw10 mps_kwr11 mps_kwr12 mps_kwr13 mps_kwr14 mps_kd15 mps_kd16 mps_kd17 mps_kd18 mps_kd19 mps_kd20 mps_kd21].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = USG) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = SEQ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = MEM) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51bb4] AXF_mps.scr_pmpc 0x51af8 AXF_mps.sr_mps AXF_mps.kn_mps 38 _ _ _ E m rom regs AXF_mps.RES_pmpc_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mps.RES_pmpc fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mps_mem_pmpc m regs G sp0 W USG SEQ MEM) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mps_mem_pmpc. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition mps_mem_pmpd (m : word -> option byte) (regs : bvmap 5 word) (G sp0 W USG SEQ MEM : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (8 * SCW W + 614568)) (word_to_le_bytes 8 (wa ((USG + Z.land ((((-1 * W) + -1)) mod 2^64) 31) + -32)))) (wa (0 + 614952)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 614960)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 614968)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 614976)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 615016)) (word_to_le_bytes 1 (wa 1)).

#[using="Type"] Theorem mps_pmpd : forall regs m rom G sp0 W USG SEQ MEM, mps_pre regs m G sp0 W USG SEQ MEM ->
  scs_denot SEGS m (Ez regs (VALS_mps G sp0 W USG SEQ MEM)) (snd (fst AXF_mps.RES_pmpd)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51af8) m rom) (mkst R (wa 0x51bb4) (mps_mem_pmpd m regs G sp0 W USG SEQ MEM) rom) /\
    getr R 2 = wa (sp0 + -96) /\ getr R 9 = wa 613952 /\ getr R 10 = wa G /\ getr R 11 = wa (4096 * Z.shiftr W 12) /\ getr R 12 = wa MEM /\ getr R 13 = wa 18446744073709547520 /\ getr R 14 = wa USG /\ getr R 18 = wa 614104 /\ (forall k, In k [1; 3; 4; 5; 6; 7; 8; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G sp0 W USG SEQ MEM P Hsc. destruct (mps_setup regs m G sp0 W USG SEQ MEM P) as [HR HK].
  set (E := Ez regs (VALS_mps G sp0 W USG SEQ MEM)) in *. destruct P as [mps_R2 mps_R9 mps_R10 mps_R18 mps_HSTK mps_rng_G mps_rng_sp0 mps_rng_W mps_rng_USG mps_rng_SEQ mps_rng_MEM mps_ka1 mps_ka4 mps_kr5 mps_kr6 mps_kw7 mps_kw8 mps_kw9 mps_kw10 mps_kwr11 mps_kwr12 mps_kwr13 mps_kwr14 mps_kd15 mps_kd16 mps_kd17 mps_kd18 mps_kd19 mps_kd20 mps_kd21].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = USG) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = SEQ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = MEM) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51bb4] AXF_mps.scr_pmpd 0x51af8 AXF_mps.sr_mps AXF_mps.kn_mps 38 _ _ _ E m rom regs AXF_mps.RES_pmpd_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mps.RES_pmpd fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mps_mem_pmpd m regs G sp0 W USG SEQ MEM) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mps_mem_pmpd. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MPS.
End AXF_mpsz.

Module AXF_mwj.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_d := EVar 32.
Definition sr_mwj := sr_id.
Definition kn_mwj : list kentry :=
  [  ].
Definition scr_mwj : scripts := SCR [] [] [].
Definition ss_mwj := SS 0x5228c sr_mwj [] kn_mwj 33.
Definition RUN_mwj := sym_exec SEGS 10 true [0x522f0] scr_mwj ss_mwj [].

Definition scr_pmwj : scripts := SCR [] [] [].
Definition RES_pmwj := Eval vm_compute in sym_exec SEGS 10 true [0x522f0] scr_pmwj ss_mwj [].
Lemma RES_pmwj_ok : sym_exec SEGS 10 true [0x522f0] scr_pmwj (SS 0x5228c sr_mwj [] kn_mwj 33) [] = RES_pmwj.
Proof. vm_compute. reflexivity. Qed.
End AXF_mwj.

Module AXF_mwjz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section MWJ.
Context {fx : FPState}.

Definition VALS_mwj (d : Z) : list Z := [d].

Record mwj_pre (regs : bvmap 5 word) (m : word -> option byte) (d : Z) : Prop := {
  mwj_rng_d : 0 <= d <= 1
}.


#[using="Type"] Lemma mwj_setup : forall regs m d, mwj_pre regs m d ->
  regs_ok (Ez regs (VALS_mwj d)) AXF_mwj.sr_mwj regs /\ know_ok SEGS (Ez regs (VALS_mwj d)) m AXF_mwj.kn_mwj.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m d P. destruct P as [mwj_rng_d].
  set (E := Ez regs (VALS_mwj d)).
  assert (Z32 : bv_unsigned (ev E 32) = d) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mwj.sr_mwj.
    apply regs_ok_id. }
  unfold know_ok, AXF_mwj.kn_mwj.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mwj.e_d a_base a_off].
  all: rewrite ?Z32.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range d _ _ mwj_rng_d eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - mwj_rng_d; lia).
  all: first [lia].
Qed.


Definition mwj_mem_pmwj (m : word -> option byte) (regs : bvmap 5 word) (d : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mwj_pmwj : forall regs m rom d, mwj_pre regs m d ->
  scs_denot SEGS m (Ez regs (VALS_mwj d)) (snd (fst AXF_mwj.RES_pmwj)) ->
  exists R, msteps SEGS (mkst regs (wa 0x5228c) m rom) (mkst R (wa 0x522f0) (mwj_mem_pmwj m regs d) rom) /\
    getr R 1 = wa 336528 /\ (forall k, In k [2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom d P Hsc. destruct (mwj_setup regs m d P) as [HR HK].
  set (E := Ez regs (VALS_mwj d)) in *. destruct P as [mwj_rng_d].
  assert (Z32 : bv_unsigned (ev E 32) = d) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 10 [0x522f0] AXF_mwj.scr_pmwj 0x5228c AXF_mwj.sr_mwj AXF_mwj.kn_mwj 33 _ _ _ E m rom regs AXF_mwj.RES_pmwj_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mwj.RES_pmwj fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mwj_mem_pmwj m regs d) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mwj_mem_pmwj. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MWJ.
End AXF_mwjz.

Module AXF_mwr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_d := EVar 32.
Definition sr_mwr := (sr_upd sr_id 1 (ELit 336528)).
Definition kn_mwr : list kentry :=
  [  ].
Definition scr_mwr : scripts := SCR [] [] [].
Definition ss_mwr := SS 0x52b8c sr_mwr [] kn_mwr 33.
Definition RUN_mwr := sym_exec SEGS 10 true [0x52290] scr_mwr ss_mwr [].

Definition scr_pmwr : scripts := SCR [] [] [].
Definition RES_pmwr := Eval vm_compute in sym_exec SEGS 10 true [0x52290] scr_pmwr ss_mwr [].
Lemma RES_pmwr_ok : sym_exec SEGS 10 true [0x52290] scr_pmwr (SS 0x52b8c sr_mwr [] kn_mwr 33) [] = RES_pmwr.
Proof. vm_compute. reflexivity. Qed.
End AXF_mwr.

Module AXF_mwrz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section MWR.
Context {fx : FPState}.

Definition VALS_mwr (d : Z) : list Z := [d].

Record mwr_pre (regs : bvmap 5 word) (m : word -> option byte) (d : Z) : Prop := {
  mwr_R1 : getr regs 1 = wa 336528 ;
  mwr_rng_d : 0 <= d <= 1
}.


#[using="Type"] Lemma mwr_setup : forall regs m d, mwr_pre regs m d ->
  regs_ok (Ez regs (VALS_mwr d)) AXF_mwr.sr_mwr regs /\ know_ok SEGS (Ez regs (VALS_mwr d)) m AXF_mwr.kn_mwr.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m d P. destruct P as [mwr_R1 mwr_rng_d].
  set (E := Ez regs (VALS_mwr d)).
  assert (Z32 : bv_unsigned (ev E 32) = d) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mwr.sr_mwr.
    apply (regs_ok_pin E _ regs 1); [apply regs_ok_id|].
    - rewrite mwr_R1. reflexivity. }
  unfold know_ok, AXF_mwr.kn_mwr.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mwr.e_d a_base a_off].
  all: rewrite ?Z32.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range d _ _ mwr_rng_d eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - mwr_rng_d; lia).
  all: first [lia].
Qed.


Definition mwr_mem_pmwr (m : word -> option byte) (regs : bvmap 5 word) (d : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mwr_pmwr : forall regs m rom d, mwr_pre regs m d ->
  scs_denot SEGS m (Ez regs (VALS_mwr d)) (snd (fst AXF_mwr.RES_pmwr)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52b8c) m rom) (mkst R (wa 0x52290) (mwr_mem_pmwr m regs d) rom) /\
    getr R 1 = wa 336528 /\ (forall k, In k [2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom d P Hsc. destruct (mwr_setup regs m d P) as [HR HK].
  set (E := Ez regs (VALS_mwr d)) in *. destruct P as [mwr_R1 mwr_rng_d].
  assert (Z32 : bv_unsigned (ev E 32) = d) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 10 [0x52290] AXF_mwr.scr_pmwr 0x52b8c AXF_mwr.sr_mwr AXF_mwr.kn_mwr 33 _ _ _ E m rom regs AXF_mwr.RES_pmwr_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mwr.RES_pmwr fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mwr_mem_pmwr m regs d) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mwr_mem_pmwr. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MWR.
End AXF_mwrz.

Module AXF_ncall.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_j := EVar 32.
Definition sr_ncall := (sr_upd sr_id 14 (e_j)).
Definition kn_ncall : list kentry :=
  [ KRange e_j 0 47 ].
Definition scr_ncall : scripts := SCR [] [] [].
Definition ss_ncall := SS 0x526c4 sr_ncall [] kn_ncall 33.
Definition RUN_ncall := sym_exec SEGS 100 true [0x522f0] scr_ncall ss_ncall [].

Definition scr_pncall : scripts := SCR [] [] [].
Definition RES_pncall := Eval vm_compute in sym_exec SEGS 100 true [0x522f0] scr_pncall ss_ncall [].
Lemma RES_pncall_ok : sym_exec SEGS 100 true [0x522f0] scr_pncall (SS 0x526c4 sr_ncall [] kn_ncall 33) [] = RES_pncall.
Proof. vm_compute. reflexivity. Qed.
End AXF_ncall.

Module AXF_ncallz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section NCALL.
Context {fx : FPState}.

Definition VALS_ncall (j : Z) : list Z := [j].

Record ncall_pre (regs : bvmap 5 word) (m : word -> option byte) (j : Z) : Prop := {
  ncall_R14 : getr regs 14 = wa j ;
  ncall_rng_j : 0 <= j <= 47
}.


#[using="Type"] Lemma ncall_setup : forall regs m j, ncall_pre regs m j ->
  regs_ok (Ez regs (VALS_ncall j)) AXF_ncall.sr_ncall regs /\ know_ok SEGS (Ez regs (VALS_ncall j)) m AXF_ncall.kn_ncall.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m j P. destruct P as [ncall_R14 ncall_rng_j].
  set (E := Ez regs (VALS_ncall j)).
  assert (Z32 : bv_unsigned (ev E 32) = j) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_ncall.sr_ncall.
    apply (regs_ok_pin E _ regs 14); [apply regs_ok_id|].
    - rewrite ncall_R14. reflexivity. }
  unfold know_ok, AXF_ncall.kn_ncall.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_ncall.e_j a_base a_off].
  all: rewrite ?Z32.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range j _ _ ncall_rng_j eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - ncall_rng_j; lia).
  all: first [lia].
Qed.


Definition ncall_mem_pncall (m : word -> option byte) (regs : bvmap 5 word) (j : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem ncall_pncall : forall regs m rom j, ncall_pre regs m j ->
  scs_denot SEGS m (Ez regs (VALS_ncall j)) (snd (fst AXF_ncall.RES_pncall)) ->
  exists R, msteps SEGS (mkst regs (wa 0x526c4) m rom) (mkst R (wa 0x522f0) (ncall_mem_pncall m regs j) rom) /\
    getr R 1 = wa 337616 /\ getr R 10 = wa j /\ getr R 14 = wa j /\ getr R 18 = wa j /\ (forall k, In k [2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom j P Hsc. destruct (ncall_setup regs m j P) as [HR HK].
  set (E := Ez regs (VALS_ncall j)) in *. destruct P as [ncall_R14 ncall_rng_j].
  assert (Z32 : bv_unsigned (ev E 32) = j) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x522f0] AXF_ncall.scr_pncall 0x526c4 AXF_ncall.sr_ncall AXF_ncall.kn_ncall 33 _ _ _ E m rom regs AXF_ncall.RES_pncall_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_ncall.RES_pncall fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (ncall_mem_pncall m regs j) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold ncall_mem_pncall. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End NCALL.
End AXF_ncallz.

Module AXF_nfin.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_cnt := EVar 32.
Definition sr_nfin := (sr_upd sr_id 19 (e_cnt)).
Definition kn_nfin : list kentry :=
  [ KRange e_cnt 1 32 ].
Definition scr_nfin : scripts := SCR [] [] [].
Definition ss_nfin := SS 0x52738 sr_nfin [] kn_nfin 33.
Definition RUN_nfin := sym_exec SEGS 100 true [0x529f8] scr_nfin ss_nfin [].

Definition scr_pnfin : scripts := SCR [] [] [].
Definition RES_pnfin := Eval vm_compute in sym_exec SEGS 100 true [0x529f8] scr_pnfin ss_nfin [].
Lemma RES_pnfin_ok : sym_exec SEGS 100 true [0x529f8] scr_pnfin (SS 0x52738 sr_nfin [] kn_nfin 33) [] = RES_pnfin.
Proof. vm_compute. reflexivity. Qed.
End AXF_nfin.

Module AXF_nfinz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section NFIN.
Context {fx : FPState}.

Definition VALS_nfin (cnt : Z) : list Z := [cnt].

Record nfin_pre (regs : bvmap 5 word) (m : word -> option byte) (cnt : Z) : Prop := {
  nfin_R19 : getr regs 19 = wa cnt ;
  nfin_rng_cnt : 1 <= cnt <= 32
}.


#[using="Type"] Lemma nfin_setup : forall regs m cnt, nfin_pre regs m cnt ->
  regs_ok (Ez regs (VALS_nfin cnt)) AXF_nfin.sr_nfin regs /\ know_ok SEGS (Ez regs (VALS_nfin cnt)) m AXF_nfin.kn_nfin.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m cnt P. destruct P as [nfin_R19 nfin_rng_cnt].
  set (E := Ez regs (VALS_nfin cnt)).
  assert (Z32 : bv_unsigned (ev E 32) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_nfin.sr_nfin.
    apply (regs_ok_pin E _ regs 19); [apply regs_ok_id|].
    - rewrite nfin_R19. reflexivity. }
  unfold know_ok, AXF_nfin.kn_nfin.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_nfin.e_cnt a_base a_off].
  all: rewrite ?Z32.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range cnt _ _ nfin_rng_cnt eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - nfin_rng_cnt; lia).
  all: first [lia].
Qed.


Definition nfin_mem_pnfin (m : word -> option byte) (regs : bvmap 5 word) (cnt : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem nfin_pnfin : forall regs m rom cnt, nfin_pre regs m cnt ->
  scs_denot SEGS m (Ez regs (VALS_nfin cnt)) (snd (fst AXF_nfin.RES_pnfin)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52738) m rom) (mkst R (wa 0x529f8) (nfin_mem_pnfin m regs cnt) rom) /\
    getr R 11 = wa (cnt + -1) /\ getr R 12 = wa (cnt + -1) /\ getr R 19 = wa cnt /\ getr R 25 = wa cnt /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom cnt P Hsc. destruct (nfin_setup regs m cnt P) as [HR HK].
  set (E := Ez regs (VALS_nfin cnt)) in *. destruct P as [nfin_R19 nfin_rng_cnt].
  assert (Z32 : bv_unsigned (ev E 32) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x529f8] AXF_nfin.scr_pnfin 0x52738 AXF_nfin.sr_nfin AXF_nfin.kn_nfin 33 _ _ _ E m rom regs AXF_nfin.RES_pnfin_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_nfin.RES_pnfin fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (nfin_mem_pnfin m regs cnt) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold nfin_mem_pnfin. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End NFIN.
End AXF_nfinz.

Module AXF_nhdr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_p := EVar 32.
Definition e_mt := EVar 33.
Definition e_W := EVar 34.
Definition e_b3 := EVar 35.
Definition e_cnt := EVar 36.
Definition sr_nhdr := (sr_upd (sr_upd (sr_upd sr_id 9 (e_mt)) 10 (e_p)) 19 (e_cnt)).
Definition kn_nhdr : list kentry :=
  [ KRange e_p 4096 (2^47);
    KRange e_mt 1 (2^63-1);
    KAlign e_mt 8;
    KRange e_W 0 (2^63-1);
    KRange e_b3 0 255;
    KRange e_cnt 1 32;
    KWord (SA e_mt 32) 8 e_W;
    KWord (SA e_p (-3)) 1 e_b3;
    KWr (SA e_mt 32) (ELit 8);
    KWr (SA e_p (-3)) (ELit 1);
    KDisj (SA e_mt 32) (ELit 8) (SA e_p (-3)) (ELit 1) ].
Definition scr_nhdr : scripts := SCR [] [] [].
Definition ss_nhdr := SS 0x52700 sr_nhdr [] kn_nhdr 37.
Definition RUN_nhdr := sym_exec SEGS 100 true [0x52728] scr_nhdr ss_nhdr [].

Definition scr_pnhdr : scripts := SCR [] [] [].
Definition RES_pnhdr := Eval vm_compute in sym_exec SEGS 100 true [0x52728] scr_pnhdr ss_nhdr [].
Lemma RES_pnhdr_ok : sym_exec SEGS 100 true [0x52728] scr_pnhdr (SS 0x52700 sr_nhdr [] kn_nhdr 37) [] = RES_pnhdr.
Proof. vm_compute. reflexivity. Qed.
End AXF_nhdr.

Module AXF_nhdrz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section NHDR.
Context {fx : FPState}.

Definition VALS_nhdr (p mt W b3 cnt : Z) : list Z := [p; mt; W; b3; cnt].

Record nhdr_pre (regs : bvmap 5 word) (m : word -> option byte) (p mt W b3 cnt : Z) : Prop := {
  nhdr_R9 : getr regs 9 = wa mt ;
  nhdr_R10 : getr regs 10 = wa p ;
  nhdr_R19 : getr regs 19 = wa cnt ;
  nhdr_rng_p : 4096 <= p <= 2^47 ;
  nhdr_rng_mt : 1 <= mt <= 2^63-1 ;
  nhdr_rng_W : 0 <= W <= 2^63-1 ;
  nhdr_rng_b3 : 0 <= b3 <= 255 ;
  nhdr_rng_cnt : 1 <= cnt <= 32 ;
  nhdr_ka2 : mt mod 8 = 0 ;
  nhdr_kw6 : rdn SEGS m (wa (mt + 32)) 8 = Some (word_to_le_bytes 8 (wa W)) ;
  nhdr_kw7 : rdn SEGS m (wa (p + -3)) 1 = Some (word_to_le_bytes 1 (wa b3)) ;
  nhdr_kwr8 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (mt + 32 + d)) k = true ;
  nhdr_kwr9 : forall d k, 0 <= d -> d + Z.of_nat k <= 1 -> store_ok SEGS m (wa (p + -3 + d)) k = true ;
  nhdr_kd10 : mt + 32 + 8 <= p + -3 \/ p + -3 + 1 <= mt + 32
}.


#[using="Type"] Lemma nhdr_setup : forall regs m p mt W b3 cnt, nhdr_pre regs m p mt W b3 cnt ->
  regs_ok (Ez regs (VALS_nhdr p mt W b3 cnt)) AXF_nhdr.sr_nhdr regs /\ know_ok SEGS (Ez regs (VALS_nhdr p mt W b3 cnt)) m AXF_nhdr.kn_nhdr.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m p mt W b3 cnt P. destruct P as [nhdr_R9 nhdr_R10 nhdr_R19 nhdr_rng_p nhdr_rng_mt nhdr_rng_W nhdr_rng_b3 nhdr_rng_cnt nhdr_ka2 nhdr_kw6 nhdr_kw7 nhdr_kwr8 nhdr_kwr9 nhdr_kd10].
  set (E := Ez regs (VALS_nhdr p mt W b3 cnt)).
  assert (Z32 : bv_unsigned (ev E 32) = p) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = mt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = b3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_nhdr.sr_nhdr.
    apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply regs_ok_id|]|]|].
    - rewrite nhdr_R9. reflexivity.
    - rewrite nhdr_R10. reflexivity.
    - rewrite nhdr_R19. reflexivity. }
  unfold know_ok, AXF_nhdr.kn_nhdr.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_nhdr.e_p AXF_nhdr.e_mt AXF_nhdr.e_W AXF_nhdr.e_b3 AXF_nhdr.e_cnt a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range p _ _ nhdr_rng_p eq_refl eq_refl), ?(mod64_of_range mt _ _ nhdr_rng_mt eq_refl eq_refl), ?(mod64_of_range W _ _ nhdr_rng_W eq_refl eq_refl), ?(mod64_of_range b3 _ _ nhdr_rng_b3 eq_refl eq_refl), ?(mod64_of_range cnt _ _ nhdr_rng_cnt eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply nhdr_kwr8 | apply nhdr_kwr9]; assumption).
  all: try (clear - nhdr_rng_p nhdr_rng_mt nhdr_rng_W nhdr_rng_b3 nhdr_rng_cnt nhdr_ka2; lia).
  all: first [(clear - nhdr_rng_p nhdr_rng_mt nhdr_rng_W nhdr_rng_b3 nhdr_rng_cnt nhdr_ka2 nhdr_kd10; lia) | lia].
Qed.


Definition nhdr_mem_pnhdr (m : word -> option byte) (regs : bvmap 5 word) (p mt W b3 cnt : Z) : word -> option byte :=
  wbytes (wbytes (m) (wa (mt + 32)) (word_to_le_bytes 8 (wa (Z.shiftr (((4503599627370496 * W)) mod 2^64) 52)))) (wa (p + -3)) (word_to_le_bytes 1 (wa (Z.land b3 31 + 192))).

#[using="Type"] Theorem nhdr_pnhdr : forall regs m rom p mt W b3 cnt, nhdr_pre regs m p mt W b3 cnt ->
  scs_denot SEGS m (Ez regs (VALS_nhdr p mt W b3 cnt)) (snd (fst AXF_nhdr.RES_pnhdr)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52700) m rom) (mkst R (wa 0x52728) (nhdr_mem_pnhdr m regs p mt W b3 cnt) rom) /\
    getr R 9 = wa mt /\ getr R 10 = wa p /\ getr R 11 = wa (cnt + 1) /\ getr R 12 = wa (p + 12) /\ getr R 19 = wa cnt /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom p mt W b3 cnt P Hsc. destruct (nhdr_setup regs m p mt W b3 cnt P) as [HR HK].
  set (E := Ez regs (VALS_nhdr p mt W b3 cnt)) in *. destruct P as [nhdr_R9 nhdr_R10 nhdr_R19 nhdr_rng_p nhdr_rng_mt nhdr_rng_W nhdr_rng_b3 nhdr_rng_cnt nhdr_ka2 nhdr_kw6 nhdr_kw7 nhdr_kwr8 nhdr_kwr9 nhdr_kd10].
  assert (Z32 : bv_unsigned (ev E 32) = p) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = mt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = b3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x52728] AXF_nhdr.scr_pnhdr 0x52700 AXF_nhdr.sr_nhdr AXF_nhdr.kn_nhdr 37 _ _ _ E m rom regs AXF_nhdr.RES_pnhdr_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_nhdr.RES_pnhdr fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (nhdr_mem_pnhdr m regs p mt W b3 cnt) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold nhdr_mem_pnhdr. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End NHDR.
End AXF_nhdrz.

Module AXF_nj0.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_sz := EVar 32.
Definition sr_nj0 := (sr_upd sr_id 14 (e_sz)).
Definition kn_nj0 : list kentry :=
  [ KRange e_sz 16 2032;
    KAlign e_sz 16 ].
Definition scr_nj0 : scripts := SCR [true] [] [].
Definition ss_nj0 := SS 0x52600 sr_nj0 [] kn_nj0 33.
Definition RUN_nj0 := sym_exec SEGS 100 true [0x526c4; 0x52610] scr_nj0 ss_nj0 [].

Definition scr_pnjs : scripts := SCR [true] [] [].
Definition RES_pnjs := Eval vm_compute in sym_exec SEGS 100 true [0x526c4; 0x52610] scr_pnjs ss_nj0 [].
Lemma RES_pnjs_ok : sym_exec SEGS 100 true [0x526c4; 0x52610] scr_pnjs (SS 0x52600 sr_nj0 [] kn_nj0 33) [] = RES_pnjs.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pnjm : scripts := SCR [false] [] [].
Definition RES_pnjm := Eval vm_compute in sym_exec SEGS 100 true [0x526c4; 0x52610] scr_pnjm ss_nj0 [].
Lemma RES_pnjm_ok : sym_exec SEGS 100 true [0x526c4; 0x52610] scr_pnjm (SS 0x52600 sr_nj0 [] kn_nj0 33) [] = RES_pnjm.
Proof. vm_compute. reflexivity. Qed.
End AXF_nj0.

Module AXF_nj0z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section NJ0.
Context {fx : FPState}.

Definition VALS_nj0 (sz : Z) : list Z := [sz].

Record nj0_pre (regs : bvmap 5 word) (m : word -> option byte) (sz : Z) : Prop := {
  nj0_R14 : getr regs 14 = wa sz ;
  nj0_rng_sz : 16 <= sz <= 2032 ;
  nj0_ka1 : sz mod 16 = 0
}.


#[using="Type"] Lemma nj0_setup : forall regs m sz, nj0_pre regs m sz ->
  regs_ok (Ez regs (VALS_nj0 sz)) AXF_nj0.sr_nj0 regs /\ know_ok SEGS (Ez regs (VALS_nj0 sz)) m AXF_nj0.kn_nj0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sz P. destruct P as [nj0_R14 nj0_rng_sz nj0_ka1].
  set (E := Ez regs (VALS_nj0 sz)).
  assert (Z32 : bv_unsigned (ev E 32) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_nj0.sr_nj0.
    apply (regs_ok_pin E _ regs 14); [apply regs_ok_id|].
    - rewrite nj0_R14. reflexivity. }
  unfold know_ok, AXF_nj0.kn_nj0.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_nj0.e_sz a_base a_off].
  all: rewrite ?Z32.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sz _ _ nj0_rng_sz eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - nj0_rng_sz nj0_ka1; lia).
  all: first [lia].
Qed.


Definition nj0_mem_pnjs (m : word -> option byte) (regs : bvmap 5 word) (sz : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem nj0_pnjs : forall regs m rom sz, nj0_pre regs m sz ->
  scs_denot SEGS m (Ez regs (VALS_nj0 sz)) (snd (fst AXF_nj0.RES_pnjs)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52600) m rom) (mkst R (wa 0x526c4) (nj0_mem_pnjs m regs sz) rom) /\
    getr R 10 = wa 157 /\ getr R 11 = wa (sz + 12) /\ getr R 14 = wa (Z.shiftr sz 4) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 12; 13; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sz P Hsc. destruct (nj0_setup regs m sz P) as [HR HK].
  set (E := Ez regs (VALS_nj0 sz)) in *. destruct P as [nj0_R14 nj0_rng_sz nj0_ka1].
  assert (Z32 : bv_unsigned (ev E 32) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x526c4; 0x52610] AXF_nj0.scr_pnjs 0x52600 AXF_nj0.sr_nj0 AXF_nj0.kn_nj0 33 _ _ _ E m rom regs AXF_nj0.RES_pnjs_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_nj0.RES_pnjs fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (nj0_mem_pnjs m regs sz) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold nj0_mem_pnjs. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition nj0_mem_pnjm (m : word -> option byte) (regs : bvmap 5 word) (sz : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem nj0_pnjm : forall regs m rom sz, nj0_pre regs m sz ->
  scs_denot SEGS m (Ez regs (VALS_nj0 sz)) (snd (fst AXF_nj0.RES_pnjm)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52600) m rom) (mkst R (wa 0x52610) (nj0_mem_pnjm m regs sz) rom) /\
    getr R 10 = wa 157 /\ getr R 11 = wa (sz + 12) /\ getr R 14 = wa (Z.shiftr sz 4) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 12; 13; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sz P Hsc. destruct (nj0_setup regs m sz P) as [HR HK].
  set (E := Ez regs (VALS_nj0 sz)) in *. destruct P as [nj0_R14 nj0_rng_sz nj0_ka1].
  assert (Z32 : bv_unsigned (ev E 32) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x526c4; 0x52610] AXF_nj0.scr_pnjm 0x52600 AXF_nj0.sr_nj0 AXF_nj0.kn_nj0 33 _ _ _ E m rom regs AXF_nj0.RES_pnjm_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_nj0.RES_pnjm fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (nj0_mem_pnjm m regs sz) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold nj0_mem_pnjm. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End NJ0.
End AXF_nj0z.

Module AXF_nr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_G := EVar 32.
Definition e_sp0 := EVar 33.
Definition e_BASE := EVar 34.
Definition e_LEN := EVar 35.
Definition sr_nr := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 1 (ELit 0x51b58)) 2 (EAlu ALU_ADD e_sp0 (ELit (-96)))) 9 (ELit 0x95e40)) 10 (e_BASE)) 11 (e_LEN)) 18 (ELit 0x95ed8)) 19 (e_G)).
Definition kn_nr : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KRange e_G 1 (2^63-1) ].
Definition scr_nr : scripts := SCR [] [] [].
Definition ss_nr := SS 0x51ca0 sr_nr [] kn_nr 36.
Definition RUN_nr := sym_exec SEGS 20 true [0x51bb4] scr_nr ss_nr [].

Definition scr_pnr : scripts := SCR [] [] [].
Definition RES_pnr := Eval vm_compute in sym_exec SEGS 20 true [0x51bb4] scr_pnr ss_nr [].
Lemma RES_pnr_ok : sym_exec SEGS 20 true [0x51bb4] scr_pnr (SS 0x51ca0 sr_nr [] kn_nr 36) [] = RES_pnr.
Proof. vm_compute. reflexivity. Qed.
End AXF_nr.

Module AXF_nrz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section NR.
Context {fx : FPState}.

Definition VALS_nr (G sp0 BASE LEN : Z) : list Z := [G; sp0; BASE; LEN].

Record nr_pre (regs : bvmap 5 word) (m : word -> option byte) (G sp0 BASE LEN : Z) : Prop := {
  nr_R1 : getr regs 1 = wa 334680 ;
  nr_R2 : getr regs 2 = wa (sp0 + -96) ;
  nr_R9 : getr regs 9 = wa 613952 ;
  nr_R10 : getr regs 10 = wa BASE ;
  nr_R11 : getr regs 11 = wa LEN ;
  nr_R18 : getr regs 18 = wa 614104 ;
  nr_R19 : getr regs 19 = wa G ;
  nr_rng_G : 1 <= G <= 2^63-1 ;
  nr_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  nr_rng_BASE : 0 <= BASE <= 2^64-1 ;
  nr_rng_LEN : 0 <= LEN <= 2^64-1 ;
  nr_ka1 : sp0 mod 16 = 0
}.


#[using="Type"] Lemma nr_setup : forall regs m G sp0 BASE LEN, nr_pre regs m G sp0 BASE LEN ->
  regs_ok (Ez regs (VALS_nr G sp0 BASE LEN)) AXF_nr.sr_nr regs /\ know_ok SEGS (Ez regs (VALS_nr G sp0 BASE LEN)) m AXF_nr.kn_nr.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G sp0 BASE LEN P. destruct P as [nr_R1 nr_R2 nr_R9 nr_R10 nr_R11 nr_R18 nr_R19 nr_rng_G nr_rng_sp0 nr_rng_BASE nr_rng_LEN nr_ka1].
  set (E := Ez regs (VALS_nr G sp0 BASE LEN)).
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = BASE) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = LEN) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_nr.sr_nr.
    apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 2); [apply (regs_ok_pin E _ regs 1); [apply regs_ok_id|]|]|]|]|]|]|].
    - rewrite nr_R1. reflexivity.
    - rewrite nr_R2, zeval_sound. cbn [zeval edenot AXF_nr.e_G AXF_nr.e_sp0 AXF_nr.e_BASE AXF_nr.e_LEN]. rewrite ?Z32, ?Z33, ?Z34, ?Z35. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite nr_R9. reflexivity.
    - rewrite nr_R10. reflexivity.
    - rewrite nr_R11. reflexivity.
    - rewrite nr_R18. reflexivity.
    - rewrite nr_R19. reflexivity. }
  unfold know_ok, AXF_nr.kn_nr.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_nr.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_nr.e_G AXF_nr.e_sp0 AXF_nr.e_BASE AXF_nr.e_LEN a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range G _ _ nr_rng_G eq_refl eq_refl), ?(mod64_of_range sp0 _ _ nr_rng_sp0 eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - nr_rng_G nr_rng_sp0 nr_rng_BASE nr_rng_LEN nr_ka1; lia).
  all: first [lia].
Qed.


Definition nr_mem_pnr (m : word -> option byte) (regs : bvmap 5 word) (G sp0 BASE LEN : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem nr_pnr : forall regs m rom G sp0 BASE LEN, nr_pre regs m G sp0 BASE LEN ->
  scs_denot SEGS m (Ez regs (VALS_nr G sp0 BASE LEN)) (snd (fst AXF_nr.RES_pnr)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51ca0) m rom) (mkst R (wa 0x51bb4) (nr_mem_pnr m regs G sp0 BASE LEN) rom) /\
    getr R 1 = wa 334680 /\ getr R 2 = wa (sp0 + -96) /\ getr R 9 = wa 613952 /\ getr R 10 = wa G /\ getr R 11 = wa LEN /\ getr R 12 = wa BASE /\ getr R 18 = wa 614104 /\ getr R 19 = wa G /\ (forall k, In k [3; 4; 5; 6; 7; 8; 13; 14; 15; 16; 17; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G sp0 BASE LEN P Hsc. destruct (nr_setup regs m G sp0 BASE LEN P) as [HR HK].
  set (E := Ez regs (VALS_nr G sp0 BASE LEN)) in *. destruct P as [nr_R1 nr_R2 nr_R9 nr_R10 nr_R11 nr_R18 nr_R19 nr_rng_G nr_rng_sp0 nr_rng_BASE nr_rng_LEN nr_ka1].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = BASE) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = LEN) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 20 [0x51bb4] AXF_nr.scr_pnr 0x51ca0 AXF_nr.sr_nr AXF_nr.kn_nr 36 _ _ _ E m rom regs AXF_nr.RES_pnr_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_nr.RES_pnr fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (nr_mem_pnr m regs G sp0 BASE LEN) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold nr_mem_pnr. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End NR.
End AXF_nrz.

Module AXF_ns.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_G := EVar 32.
Definition e_sp0 := EVar 33.
Definition e_W := EVar 34.
Definition e_USG := EVar 35.
Definition e_MEM := EVar 36.
Definition e_H3 := EVar 37.
Definition e_OFF := EVar 38.
Definition e_PG := EVar 39.
Definition e_PW := EVar 40.
Definition e_PAV := EVar 41.
Definition e_PFR := EVar 42.
Definition e_SEC := EVar 43.
Definition e_PCSZ := EVar 44.
Definition STK := SA e_sp0 (-1024).
Definition SC := EAlu ALU_SRL (EMd M_MUL (ELit 4503599627370496) e_W) (ELit 58).
Definition SC8 := EMd M_MUL (ELit 8) SC.
Definition BASE := EAlu ALU_ADD e_MEM (EMd M_MUL (ELit (-16)) (EExt false 0 2 e_OFF)).
Definition PSC := EAlu ALU_SRL (EMd M_MUL (ELit 4503599627370496) e_PW) (ELit 58).
Definition PSC2 := EMd M_MUL (ELit 2) PSC.
Definition AREA := EMd M_MUL (ELit 4096) (EAlu ALU_SRL e_PG (ELit 12)).
Definition sr_ns := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-96)))) 9 (ELit 0x95e40)) 10 (e_G)) 18 (ELit 0x95ed8)).
Definition kn_ns : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWr STK (ELit 1024);
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange SC 0 47;
    KRange SC8 0 376;
    KRange e_MEM 16 (2^63-1);
    KAlign e_MEM 16;
    KRange e_PG 1 (2^63-1);
    KAlign e_PG 8;
    KRange BASE 16 (2^63-1);
    KRange PSC 0 47;
    KRange PSC2 0 94;
    KRange AREA 1 (2^63-1);
    KWord (SA e_G 32) 8 e_W;
    KWord (SA e_G 16) 8 e_MEM;
    KWord (SA SC8 614568) 8 e_USG;
    KWord (SA e_MEM (-4)) 1 (ELit 0);
    KWord (SA e_MEM (-3)) 1 e_H3;
    KWord (SA e_MEM (-2)) 2 e_OFF;
    KWord (SA BASE (-16)) 8 e_PG;
    KWord (SA e_PG 16) 8 (EAlu ALU_ADD BASE (ELit (-16)));
    KWord (SA e_PG 32) 8 e_PW;
    KWord (SA e_PG 24) 4 e_PAV;
    KWord (SA e_PG 28) 4 e_PFR;
    KWord (SA AREA 0) 8 e_SEC;
    KWord (SA (ELit 0) 614104) 8 e_SEC;
    KWord (SA PSC2 98984) 2 e_PCSZ;
    KWr (SA SC8 614568) (ELit 8);
    KWr (SA e_MEM 0) (ELit 8);
    KDisj STK (ELit 1024) (SA e_G 0) (ELit 40);
    KDisj STK (ELit 1024) (SA SC8 614568) (ELit 8);
    KDisj STK (ELit 1024) (SA e_MEM (-4)) (ELit 12);
    KDisj (SA e_G 0) (ELit 40) (SA SC8 614568) (ELit 8);
    KDisj (SA e_MEM (-4)) (ELit 12) (SA SC8 614568) (ELit 8);
    KDisj (SA BASE (-16)) (ELit 8) (SA SC8 614568) (ELit 8);
    KDisj (SA e_PG 0) (ELit 40) (SA SC8 614568) (ELit 8);
    KDisj (SA AREA 0) (ELit 8) (SA SC8 614568) (ELit 8);
    KDisj (SA (ELit 0) 614104) (ELit 8) (SA SC8 614568) (ELit 8);
    KDisj (SA PSC2 98984) (ELit 2) (SA SC8 614568) (ELit 8) ].
Definition scr_ns : scripts := SCR [false; true; true; true; true; false; false; true] [] [].
Definition ss_ns := SS 0x51af8 sr_ns [] kn_ns 45.
Definition RUN_ns := sym_exec SEGS 150 true [0x518d0] scr_ns ss_ns [].

Definition scr_pns1 : scripts := SCR [false; true; true; true; true; false; false; true] [] [].
Definition RES_pns1 := Eval vm_compute in sym_exec SEGS 150 true [0x518d0] scr_pns1 ss_ns [].
Lemma RES_pns1_ok : sym_exec SEGS 150 true [0x518d0] scr_pns1 (SS 0x51af8 sr_ns [] kn_ns 45) [] = RES_pns1.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pns0 : scripts := SCR [false; true; true; true; true; false; true] [] [].
Definition RES_pns0 := Eval vm_compute in sym_exec SEGS 150 true [0x518d0] scr_pns0 ss_ns [].
Lemma RES_pns0_ok : sym_exec SEGS 150 true [0x518d0] scr_pns0 (SS 0x51af8 sr_ns [] kn_ns 45) [] = RES_pns0.
Proof. vm_compute. reflexivity. Qed.
End AXF_ns.

Module AXF_nsz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section NS.
Context {fx : FPState}.

Definition VALS_ns (G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ : Z) : list Z := [G; sp0; W; USG; MEM; H3; OFF; PG; PW; PAV; PFR; SEC; PCSZ].

Record ns_pre (regs : bvmap 5 word) (m : word -> option byte) (G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ : Z) : Prop := {
  ns_R2 : getr regs 2 = wa (sp0 + -96) ;
  ns_R9 : getr regs 9 = wa 613952 ;
  ns_R10 : getr regs 10 = wa G ;
  ns_R18 : getr regs 18 = wa 614104 ;
  ns_HSTK : stk_ok SEGS m (wa sp0) 1024 ;
  ns_rng_G : 1 <= G <= 2^63-1 ;
  ns_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  ns_rng_W : 0 <= W <= 2^64-1 ;
  ns_rng_USG : 0 <= USG <= 2^64-1 ;
  ns_rng_MEM : 1 <= MEM <= 2^63-1 ;
  ns_rng_H3 : 0 <= H3 <= 255 ;
  ns_rng_OFF : 0 <= OFF <= 65535 ;
  ns_rng_PG : 1 <= PG <= 2^63-1 ;
  ns_rng_PW : 0 <= PW <= 2^64-1 ;
  ns_rng_PAV : 0 <= PAV <= 2^32-1 ;
  ns_rng_PFR : 0 <= PFR <= 2^32-1 ;
  ns_rng_SEC : 0 <= SEC <= 2^64-1 ;
  ns_rng_PCSZ : 0 <= PCSZ <= 65535 ;
  ns_ka1 : sp0 mod 16 = 0 ;
  ns_ka4 : G mod 8 = 0 ;
  ns_kr5 : 0 <= SCW W <= 47 ;
  ns_kr6 : 0 <= 8 * SCW W <= 376 ;
  ns_ka8 : MEM mod 16 = 0 ;
  ns_ka10 : PG mod 8 = 0 ;
  ns_kr11 : 16 <= MEM + -16 * ext_Z false 0 2 OFF <= (2^63-1) ;
  ns_kr12 : 0 <= SCW PW <= 47 ;
  ns_kr13 : 0 <= 2 * SCW PW <= 94 ;
  ns_kr14 : 1 <= 4096 * Z.shiftr PG 12 <= (2^63-1) ;
  ns_kw15 : rdn SEGS m (wa (G + 32)) 8 = Some (word_to_le_bytes 8 (wa W)) ;
  ns_kw16 : rdn SEGS m (wa (G + 16)) 8 = Some (word_to_le_bytes 8 (wa MEM)) ;
  ns_kw17 : rdn SEGS m (wa (8 * SCW W + 614568)) 8 = Some (word_to_le_bytes 8 (wa USG)) ;
  ns_kw18 : rdn SEGS m (wa (MEM + -4)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  ns_kw19 : rdn SEGS m (wa (MEM + -3)) 1 = Some (word_to_le_bytes 1 (wa H3)) ;
  ns_kw20 : rdn SEGS m (wa (MEM + -2)) 2 = Some (word_to_le_bytes 2 (wa OFF)) ;
  ns_kw21 : rdn SEGS m (wa (MEM + -16 * ext_Z false 0 2 OFF + -16)) 8 = Some (word_to_le_bytes 8 (wa PG)) ;
  ns_kw22 : rdn SEGS m (wa (PG + 16)) 8 = Some (word_to_le_bytes 8 (wa (MEM + -16 * ext_Z false 0 2 OFF + -16))) ;
  ns_kw23 : rdn SEGS m (wa (PG + 32)) 8 = Some (word_to_le_bytes 8 (wa PW)) ;
  ns_kw24 : rdn SEGS m (wa (PG + 24)) 4 = Some (word_to_le_bytes 4 (wa PAV)) ;
  ns_kw25 : rdn SEGS m (wa (PG + 28)) 4 = Some (word_to_le_bytes 4 (wa PFR)) ;
  ns_kw26 : rdn SEGS m (wa (4096 * Z.shiftr PG 12 + 0)) 8 = Some (word_to_le_bytes 8 (wa SEC)) ;
  ns_kw27 : rdn SEGS m (wa (0 + 614104)) 8 = Some (word_to_le_bytes 8 (wa SEC)) ;
  ns_kw28 : rdn SEGS m (wa (2 * SCW PW + 98984)) 2 = Some (word_to_le_bytes 2 (wa PCSZ)) ;
  ns_kwr29 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (8 * SCW W + 614568 + d)) k = true ;
  ns_kwr30 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (MEM + 0 + d)) k = true ;
  ns_kd31 : sp0 + -1024 + 1024 <= G + 0 \/ G + 0 + 40 <= sp0 + -1024 ;
  ns_kd32 : sp0 + -1024 + 1024 <= 8 * SCW W + 614568 \/ 8 * SCW W + 614568 + 8 <= sp0 + -1024 ;
  ns_kd33 : sp0 + -1024 + 1024 <= MEM + -4 \/ MEM + -4 + 12 <= sp0 + -1024 ;
  ns_kd34 : G + 0 + 40 <= 8 * SCW W + 614568 \/ 8 * SCW W + 614568 + 8 <= G + 0 ;
  ns_kd35 : MEM + -4 + 12 <= 8 * SCW W + 614568 \/ 8 * SCW W + 614568 + 8 <= MEM + -4 ;
  ns_kd36 : MEM + -16 * ext_Z false 0 2 OFF + -16 + 8 <= 8 * SCW W + 614568 \/ 8 * SCW W + 614568 + 8 <= MEM + -16 * ext_Z false 0 2 OFF + -16 ;
  ns_kd37 : PG + 0 + 40 <= 8 * SCW W + 614568 \/ 8 * SCW W + 614568 + 8 <= PG + 0 ;
  ns_kd38 : 4096 * Z.shiftr PG 12 + 0 + 8 <= 8 * SCW W + 614568 \/ 8 * SCW W + 614568 + 8 <= 4096 * Z.shiftr PG 12 + 0 ;
  ns_kd39 : 0 + 614104 + 8 <= 8 * SCW W + 614568 \/ 8 * SCW W + 614568 + 8 <= 0 + 614104 ;
  ns_kd40 : 2 * SCW PW + 98984 + 2 <= 8 * SCW W + 614568 \/ 8 * SCW W + 614568 + 8 <= 2 * SCW PW + 98984
}.


#[using="Type"] Lemma ns_setup : forall regs m G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ, ns_pre regs m G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ ->
  regs_ok (Ez regs (VALS_ns G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ)) AXF_ns.sr_ns regs /\ know_ok SEGS (Ez regs (VALS_ns G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ)) m AXF_ns.kn_ns.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ P. destruct P as [ns_R2 ns_R9 ns_R10 ns_R18 ns_HSTK ns_rng_G ns_rng_sp0 ns_rng_W ns_rng_USG ns_rng_MEM ns_rng_H3 ns_rng_OFF ns_rng_PG ns_rng_PW ns_rng_PAV ns_rng_PFR ns_rng_SEC ns_rng_PCSZ ns_ka1 ns_ka4 ns_kr5 ns_kr6 ns_ka8 ns_ka10 ns_kr11 ns_kr12 ns_kr13 ns_kr14 ns_kw15 ns_kw16 ns_kw17 ns_kw18 ns_kw19 ns_kw20 ns_kw21 ns_kw22 ns_kw23 ns_kw24 ns_kw25 ns_kw26 ns_kw27 ns_kw28 ns_kwr29 ns_kwr30 ns_kd31 ns_kd32 ns_kd33 ns_kd34 ns_kd35 ns_kd36 ns_kd37 ns_kd38 ns_kd39 ns_kd40].
  set (E := Ez regs (VALS_ns G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ)).
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = USG) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = MEM) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = H3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = OFF) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = PG) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = PW) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = PAV) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = PFR) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = SEC) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z44 : bv_unsigned (ev E 44) = PCSZ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_ns.sr_ns.
    apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|]|]|]|].
    - rewrite ns_R2, zeval_sound. cbn [zeval edenot AXF_ns.e_G AXF_ns.e_sp0 AXF_ns.e_W AXF_ns.e_USG AXF_ns.e_MEM AXF_ns.e_H3 AXF_ns.e_OFF AXF_ns.e_PG AXF_ns.e_PW AXF_ns.e_PAV AXF_ns.e_PFR AXF_ns.e_SEC AXF_ns.e_PCSZ AXF_ns.STK AXF_ns.SC AXF_ns.SC8 AXF_ns.BASE AXF_ns.PSC AXF_ns.PSC2 AXF_ns.AREA]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42, ?Z43, ?Z44. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite ns_R9. reflexivity.
    - rewrite ns_R10. reflexivity.
    - rewrite ns_R18. reflexivity. }
  unfold know_ok, AXF_ns.kn_ns.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_ns.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia]) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_ns.e_G AXF_ns.e_sp0 AXF_ns.e_W AXF_ns.e_USG AXF_ns.e_MEM AXF_ns.e_H3 AXF_ns.e_OFF AXF_ns.e_PG AXF_ns.e_PW AXF_ns.e_PAV AXF_ns.e_PFR AXF_ns.e_SEC AXF_ns.e_PCSZ AXF_ns.STK AXF_ns.SC AXF_ns.SC8 AXF_ns.BASE AXF_ns.PSC AXF_ns.PSC2 AXF_ns.AREA a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42, ?Z43, ?Z44.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range G _ _ ns_rng_G eq_refl eq_refl), ?(mod64_of_range sp0 _ _ ns_rng_sp0 eq_refl eq_refl), ?(mod64_of_range MEM _ _ ns_rng_MEM eq_refl eq_refl), ?(mod64_of_range H3 _ _ ns_rng_H3 eq_refl eq_refl), ?(mod64_of_range OFF _ _ ns_rng_OFF eq_refl eq_refl), ?(mod64_of_range PG _ _ ns_rng_PG eq_refl eq_refl), ?(mod64_of_range PAV _ _ ns_rng_PAV eq_refl eq_refl), ?(mod64_of_range PFR _ _ ns_rng_PFR eq_refl eq_refl), ?(mod64_of_range PCSZ _ _ ns_rng_PCSZ eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply ns_kwr29 | apply ns_kwr30]; assumption).
  all: try (clear - ns_rng_G ns_rng_sp0 ns_rng_W ns_rng_USG ns_rng_MEM ns_rng_H3 ns_rng_OFF ns_rng_PG ns_rng_PW ns_rng_PAV ns_rng_PFR ns_rng_SEC ns_rng_PCSZ ns_ka1 ns_ka4 ns_kr5 ns_kr6 ns_ka8 ns_ka10 ns_kr11 ns_kr12 ns_kr13 ns_kr14; lia).
  all: first [(clear - ns_rng_G ns_rng_sp0 ns_rng_W ns_rng_USG ns_rng_MEM ns_rng_H3 ns_rng_OFF ns_rng_PG ns_rng_PW ns_rng_PAV ns_rng_PFR ns_rng_SEC ns_rng_PCSZ ns_ka1 ns_ka4 ns_kr5 ns_kr6 ns_ka8 ns_ka10 ns_kr11 ns_kr12 ns_kr13 ns_kr14 ns_kd31; lia) | (clear - ns_rng_G ns_rng_sp0 ns_rng_W ns_rng_USG ns_rng_MEM ns_rng_H3 ns_rng_OFF ns_rng_PG ns_rng_PW ns_rng_PAV ns_rng_PFR ns_rng_SEC ns_rng_PCSZ ns_ka1 ns_ka4 ns_kr5 ns_kr6 ns_ka8 ns_ka10 ns_kr11 ns_kr12 ns_kr13 ns_kr14 ns_kd32; lia) | (clear - ns_rng_G ns_rng_sp0 ns_rng_W ns_rng_USG ns_rng_MEM ns_rng_H3 ns_rng_OFF ns_rng_PG ns_rng_PW ns_rng_PAV ns_rng_PFR ns_rng_SEC ns_rng_PCSZ ns_ka1 ns_ka4 ns_kr5 ns_kr6 ns_ka8 ns_ka10 ns_kr11 ns_kr12 ns_kr13 ns_kr14 ns_kd33; lia) | (clear - ns_rng_G ns_rng_sp0 ns_rng_W ns_rng_USG ns_rng_MEM ns_rng_H3 ns_rng_OFF ns_rng_PG ns_rng_PW ns_rng_PAV ns_rng_PFR ns_rng_SEC ns_rng_PCSZ ns_ka1 ns_ka4 ns_kr5 ns_kr6 ns_ka8 ns_ka10 ns_kr11 ns_kr12 ns_kr13 ns_kr14 ns_kd34; lia) | (clear - ns_rng_G ns_rng_sp0 ns_rng_W ns_rng_USG ns_rng_MEM ns_rng_H3 ns_rng_OFF ns_rng_PG ns_rng_PW ns_rng_PAV ns_rng_PFR ns_rng_SEC ns_rng_PCSZ ns_ka1 ns_ka4 ns_kr5 ns_kr6 ns_ka8 ns_ka10 ns_kr11 ns_kr12 ns_kr13 ns_kr14 ns_kd35; lia) | (clear - ns_rng_G ns_rng_sp0 ns_rng_W ns_rng_USG ns_rng_MEM ns_rng_H3 ns_rng_OFF ns_rng_PG ns_rng_PW ns_rng_PAV ns_rng_PFR ns_rng_SEC ns_rng_PCSZ ns_ka1 ns_ka4 ns_kr5 ns_kr6 ns_ka8 ns_ka10 ns_kr11 ns_kr12 ns_kr13 ns_kr14 ns_kd36; lia) | (clear - ns_rng_G ns_rng_sp0 ns_rng_W ns_rng_USG ns_rng_MEM ns_rng_H3 ns_rng_OFF ns_rng_PG ns_rng_PW ns_rng_PAV ns_rng_PFR ns_rng_SEC ns_rng_PCSZ ns_ka1 ns_ka4 ns_kr5 ns_kr6 ns_ka8 ns_ka10 ns_kr11 ns_kr12 ns_kr13 ns_kr14 ns_kd37; lia) | (clear - ns_rng_G ns_rng_sp0 ns_rng_W ns_rng_USG ns_rng_MEM ns_rng_H3 ns_rng_OFF ns_rng_PG ns_rng_PW ns_rng_PAV ns_rng_PFR ns_rng_SEC ns_rng_PCSZ ns_ka1 ns_ka4 ns_kr5 ns_kr6 ns_ka8 ns_ka10 ns_kr11 ns_kr12 ns_kr13 ns_kr14 ns_kd38; lia) | (clear - ns_rng_G ns_rng_sp0 ns_rng_W ns_rng_USG ns_rng_MEM ns_rng_H3 ns_rng_OFF ns_rng_PG ns_rng_PW ns_rng_PAV ns_rng_PFR ns_rng_SEC ns_rng_PCSZ ns_ka1 ns_ka4 ns_kr5 ns_kr6 ns_ka8 ns_ka10 ns_kr11 ns_kr12 ns_kr13 ns_kr14 ns_kd39; lia) | (clear - ns_rng_G ns_rng_sp0 ns_rng_W ns_rng_USG ns_rng_MEM ns_rng_H3 ns_rng_OFF ns_rng_PG ns_rng_PW ns_rng_PAV ns_rng_PFR ns_rng_SEC ns_rng_PCSZ ns_ka1 ns_ka4 ns_kr5 ns_kr6 ns_ka8 ns_ka10 ns_kr11 ns_kr12 ns_kr13 ns_kr14 ns_kd40; lia) | lia].
Qed.


Definition ns_mem_pns1 (m : word -> option byte) (regs : bvmap 5 word) (G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ : Z) : word -> option byte :=
  wbytes (wbytes (m) (wa (8 * SCW W + 614568)) (word_to_le_bytes 8 (wa ((USG + Z.land ((((-1 * W) + -1)) mod 2^64) 31) + -32)))) (wa (MEM + 0)) (word_to_le_bytes 8 (wa 0)).

#[using="Type"] Theorem ns_pns1 : forall regs m rom G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ, ns_pre regs m G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ ->
  scs_denot SEGS m (Ez regs (VALS_ns G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ)) (snd (fst AXF_ns.RES_pns1)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51af8) m rom) (mkst R (wa 0x518d0) (ns_mem_pns1 m regs G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ) rom) /\
    getr R 1 = wa 334680 /\ getr R 2 = wa (sp0 + -96) /\ getr R 8 = wa MEM /\ getr R 9 = wa 613952 /\ getr R 10 = wa PG /\ getr R 11 = wa (Z.land ((ext_Z false 0 1 H3) mod 2^64) 31) /\ getr R 12 = wa (ext_Z false 0 1 H3) /\ getr R 13 = wa ((Z.land ((ext_Z false 0 1 H3) mod 2^64) 31 + 1) * ext_Z false 0 2 PCSZ) /\ getr R 14 = wa (ext_Z false 0 2 PCSZ) /\ getr R 15 = wa (ext_Z false 0 2 PCSZ * Z.land ((ext_Z false 0 1 H3) mod 2^64) 31) /\ getr R 18 = wa 614104 /\ getr R 19 = wa G /\ (forall k, In k [3; 4; 5; 6; 7; 16; 17; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ P Hsc. destruct (ns_setup regs m G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ P) as [HR HK].
  set (E := Ez regs (VALS_ns G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ)) in *. destruct P as [ns_R2 ns_R9 ns_R10 ns_R18 ns_HSTK ns_rng_G ns_rng_sp0 ns_rng_W ns_rng_USG ns_rng_MEM ns_rng_H3 ns_rng_OFF ns_rng_PG ns_rng_PW ns_rng_PAV ns_rng_PFR ns_rng_SEC ns_rng_PCSZ ns_ka1 ns_ka4 ns_kr5 ns_kr6 ns_ka8 ns_ka10 ns_kr11 ns_kr12 ns_kr13 ns_kr14 ns_kw15 ns_kw16 ns_kw17 ns_kw18 ns_kw19 ns_kw20 ns_kw21 ns_kw22 ns_kw23 ns_kw24 ns_kw25 ns_kw26 ns_kw27 ns_kw28 ns_kwr29 ns_kwr30 ns_kd31 ns_kd32 ns_kd33 ns_kd34 ns_kd35 ns_kd36 ns_kd37 ns_kd38 ns_kd39 ns_kd40].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = USG) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = MEM) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = H3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = OFF) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = PG) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = PW) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = PAV) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = PFR) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = SEC) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z44 : bv_unsigned (ev E 44) = PCSZ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 150 [0x518d0] AXF_ns.scr_pns1 0x51af8 AXF_ns.sr_ns AXF_ns.kn_ns 45 _ _ _ E m rom regs AXF_ns.RES_pns1_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_ns.RES_pns1 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (ns_mem_pns1 m regs G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold ns_mem_pns1. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition ns_mem_pns0 (m : word -> option byte) (regs : bvmap 5 word) (G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ : Z) : word -> option byte :=
  wbytes (wbytes (m) (wa (8 * SCW W + 614568)) (word_to_le_bytes 8 (wa ((USG + Z.land ((((-1 * W) + -1)) mod 2^64) 31) + -32)))) (wa (MEM + 0)) (word_to_le_bytes 8 (wa 0)).

#[using="Type"] Theorem ns_pns0 : forall regs m rom G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ, ns_pre regs m G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ ->
  scs_denot SEGS m (Ez regs (VALS_ns G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ)) (snd (fst AXF_ns.RES_pns0)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51af8) m rom) (mkst R (wa 0x518d0) (ns_mem_pns0 m regs G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ) rom) /\
    getr R 1 = wa 334680 /\ getr R 2 = wa (sp0 + -96) /\ getr R 8 = wa MEM /\ getr R 9 = wa 613952 /\ getr R 10 = wa PG /\ getr R 11 = wa (Z.land ((ext_Z false 0 1 H3) mod 2^64) 31) /\ getr R 12 = wa (ext_Z false 0 1 H3) /\ getr R 13 = wa ((Z.land ((ext_Z false 0 1 H3) mod 2^64) 31 + 1) * ext_Z false 0 2 PCSZ) /\ getr R 14 = wa (ext_Z false 0 2 PCSZ) /\ getr R 15 = wa (ext_Z false 0 2 PCSZ * Z.land ((ext_Z false 0 1 H3) mod 2^64) 31) /\ getr R 18 = wa 614104 /\ getr R 19 = wa G /\ (forall k, In k [3; 4; 5; 6; 7; 16; 17; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ P Hsc. destruct (ns_setup regs m G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ P) as [HR HK].
  set (E := Ez regs (VALS_ns G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ)) in *. destruct P as [ns_R2 ns_R9 ns_R10 ns_R18 ns_HSTK ns_rng_G ns_rng_sp0 ns_rng_W ns_rng_USG ns_rng_MEM ns_rng_H3 ns_rng_OFF ns_rng_PG ns_rng_PW ns_rng_PAV ns_rng_PFR ns_rng_SEC ns_rng_PCSZ ns_ka1 ns_ka4 ns_kr5 ns_kr6 ns_ka8 ns_ka10 ns_kr11 ns_kr12 ns_kr13 ns_kr14 ns_kw15 ns_kw16 ns_kw17 ns_kw18 ns_kw19 ns_kw20 ns_kw21 ns_kw22 ns_kw23 ns_kw24 ns_kw25 ns_kw26 ns_kw27 ns_kw28 ns_kwr29 ns_kwr30 ns_kd31 ns_kd32 ns_kd33 ns_kd34 ns_kd35 ns_kd36 ns_kd37 ns_kd38 ns_kd39 ns_kd40].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = USG) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = MEM) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = H3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = OFF) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = PG) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = PW) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = PAV) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = PFR) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = SEC) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z44 : bv_unsigned (ev E 44) = PCSZ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 150 [0x518d0] AXF_ns.scr_pns0 0x51af8 AXF_ns.sr_ns AXF_ns.kn_ns 45 _ _ _ E m rom regs AXF_ns.RES_pns0_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_ns.RES_pns0 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (ns_mem_pns0 m regs G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold ns_mem_pns0. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End NS.
End AXF_nsz.

Module AXF_nzl.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_c := EVar 32.
Definition e_a := EVar 33.
Definition e_size := EVar 34.
Definition sr_nzl := (sr_upd (sr_upd (sr_upd sr_id 11 (e_c)) 12 (e_a)) 24 (e_size)).
Definition kn_nzl : list kentry :=
  [ KRange e_c 1 33;
    KRange e_a 4096 (2^47);
    KRange e_size 16 2032;
    KWr (SA e_a 0) (ELit 1) ].
Definition scr_nzl : scripts := SCR [true] [] [].
Definition ss_nzl := SS 0x52728 sr_nzl [] kn_nzl 35.
Definition RUN_nzl := sym_exec SEGS 100 true [0x52728; 0x52738] scr_nzl ss_nzl [].

Definition scr_pnzc : scripts := SCR [true] [] [].
Definition RES_pnzc := Eval vm_compute in sym_exec SEGS 100 true [0x52728; 0x52738] scr_pnzc ss_nzl [].
Lemma RES_pnzc_ok : sym_exec SEGS 100 true [0x52728; 0x52738] scr_pnzc (SS 0x52728 sr_nzl [] kn_nzl 35) [] = RES_pnzc.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pnzx : scripts := SCR [false] [] [].
Definition RES_pnzx := Eval vm_compute in sym_exec SEGS 100 true [0x52728; 0x52738] scr_pnzx ss_nzl [].
Lemma RES_pnzx_ok : sym_exec SEGS 100 true [0x52728; 0x52738] scr_pnzx (SS 0x52728 sr_nzl [] kn_nzl 35) [] = RES_pnzx.
Proof. vm_compute. reflexivity. Qed.
End AXF_nzl.

Module AXF_nzlz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section NZL.
Context {fx : FPState}.

Definition VALS_nzl (c a size : Z) : list Z := [c; a; size].

Record nzl_pre (regs : bvmap 5 word) (m : word -> option byte) (c a size : Z) : Prop := {
  nzl_R11 : getr regs 11 = wa c ;
  nzl_R12 : getr regs 12 = wa a ;
  nzl_R24 : getr regs 24 = wa size ;
  nzl_rng_c : 1 <= c <= 33 ;
  nzl_rng_a : 4096 <= a <= 2^47 ;
  nzl_rng_size : 16 <= size <= 2032 ;
  nzl_kwr3 : forall d k, 0 <= d -> d + Z.of_nat k <= 1 -> store_ok SEGS m (wa (a + 0 + d)) k = true
}.


#[using="Type"] Lemma nzl_setup : forall regs m c a size, nzl_pre regs m c a size ->
  regs_ok (Ez regs (VALS_nzl c a size)) AXF_nzl.sr_nzl regs /\ know_ok SEGS (Ez regs (VALS_nzl c a size)) m AXF_nzl.kn_nzl.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m c a size P. destruct P as [nzl_R11 nzl_R12 nzl_R24 nzl_rng_c nzl_rng_a nzl_rng_size nzl_kwr3].
  set (E := Ez regs (VALS_nzl c a size)).
  assert (Z32 : bv_unsigned (ev E 32) = c) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = a) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = size) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_nzl.sr_nzl.
    apply (regs_ok_pin E _ regs 24); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply regs_ok_id|]|]|].
    - rewrite nzl_R11. reflexivity.
    - rewrite nzl_R12. reflexivity.
    - rewrite nzl_R24. reflexivity. }
  unfold know_ok, AXF_nzl.kn_nzl.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_nzl.e_c AXF_nzl.e_a AXF_nzl.e_size a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range c _ _ nzl_rng_c eq_refl eq_refl), ?(mod64_of_range a _ _ nzl_rng_a eq_refl eq_refl), ?(mod64_of_range size _ _ nzl_rng_size eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply nzl_kwr3]; assumption).
  all: try (clear - nzl_rng_c nzl_rng_a nzl_rng_size; lia).
  all: first [lia].
Qed.


Definition nzl_mem_pnzc (m : word -> option byte) (regs : bvmap 5 word) (c a size : Z) : word -> option byte :=
  wbytes (m) (wa (a + 0)) (word_to_le_bytes 1 (wa 0)).

#[using="Type"] Theorem nzl_pnzc : forall regs m rom c a size, nzl_pre regs m c a size ->
  scs_denot SEGS m (Ez regs (VALS_nzl c a size)) (snd (fst AXF_nzl.RES_pnzc)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52728) m rom) (mkst R (wa 0x52728) (nzl_mem_pnzc m regs c a size) rom) /\
    getr R 11 = wa (c + -1) /\ getr R 12 = wa (a + size) /\ getr R 24 = wa size /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom c a size P Hsc. destruct (nzl_setup regs m c a size P) as [HR HK].
  set (E := Ez regs (VALS_nzl c a size)) in *. destruct P as [nzl_R11 nzl_R12 nzl_R24 nzl_rng_c nzl_rng_a nzl_rng_size nzl_kwr3].
  assert (Z32 : bv_unsigned (ev E 32) = c) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = a) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = size) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x52728; 0x52738] AXF_nzl.scr_pnzc 0x52728 AXF_nzl.sr_nzl AXF_nzl.kn_nzl 35 _ _ _ E m rom regs AXF_nzl.RES_pnzc_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_nzl.RES_pnzc fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (nzl_mem_pnzc m regs c a size) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold nzl_mem_pnzc. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition nzl_mem_pnzx (m : word -> option byte) (regs : bvmap 5 word) (c a size : Z) : word -> option byte :=
  wbytes (m) (wa (a + 0)) (word_to_le_bytes 1 (wa 0)).

#[using="Type"] Theorem nzl_pnzx : forall regs m rom c a size, nzl_pre regs m c a size ->
  scs_denot SEGS m (Ez regs (VALS_nzl c a size)) (snd (fst AXF_nzl.RES_pnzx)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52728) m rom) (mkst R (wa 0x52738) (nzl_mem_pnzx m regs c a size) rom) /\
    getr R 11 = wa (c + -1) /\ getr R 12 = wa (a + size) /\ getr R 24 = wa size /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom c a size P Hsc. destruct (nzl_setup regs m c a size P) as [HR HK].
  set (E := Ez regs (VALS_nzl c a size)) in *. destruct P as [nzl_R11 nzl_R12 nzl_R24 nzl_rng_c nzl_rng_a nzl_rng_size nzl_kwr3].
  assert (Z32 : bv_unsigned (ev E 32) = c) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = a) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = size) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x52728; 0x52738] AXF_nzl.scr_pnzx 0x52728 AXF_nzl.sr_nzl AXF_nzl.kn_nzl 35 _ _ _ E m rom regs AXF_nzl.RES_pnzx_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_nzl.RES_pnzx fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (nzl_mem_pnzx m regs c a size) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold nzl_mem_pnzx. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End NZL.
End AXF_nzlz.

Module AXF_spe.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_G2 := EVar 32.
Definition e_mem2 := EVar 33.
Definition e_hb := EVar 34.
Definition e_W2 := EVar 35.
Definition e_cnt := EVar 36.
Definition sr_spe := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (e_G2)) 11 (e_mem2)) 12 (e_hb)) 13 (e_W2)) 14 (e_cnt)).
Definition kn_spe : list kentry :=
  [ KRange e_G2 1 (2^63-1);
    KAlign e_G2 8;
    KRange e_mem2 1 (2^63-1);
    KRange e_hb 0 255;
    KRange e_W2 0 (2^63-1);
    KRange e_cnt 1 (2^28);
    KWord (SA e_G2 24) 4 (ELit 0);
    KWr (SA e_mem2 8) (ELit 1);
    KDisj (SA e_mem2 8) (ELit 1) (SA e_G2 24) (ELit 4) ].
Definition scr_spe : scripts := SCR [true; false] [] [].
Definition ss_spe := SS 0x52820 sr_spe [] kn_spe 37.
Definition RUN_spe := sym_exec SEGS 100 true [0x52418] scr_spe ss_spe [].

Definition scr_pspt : scripts := SCR [true; false] [] [].
Definition RES_pspt := Eval vm_compute in sym_exec SEGS 100 true [0x52418] scr_pspt ss_spe [].
Lemma RES_pspt_ok : sym_exec SEGS 100 true [0x52418] scr_pspt (SS 0x52820 sr_spe [] kn_spe 37) [] = RES_pspt.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pspf : scripts := SCR [false; false] [] [].
Definition RES_pspf := Eval vm_compute in sym_exec SEGS 100 true [0x52418] scr_pspf ss_spe [].
Lemma RES_pspf_ok : sym_exec SEGS 100 true [0x52418] scr_pspf (SS 0x52820 sr_spe [] kn_spe 37) [] = RES_pspf.
Proof. vm_compute. reflexivity. Qed.
End AXF_spe.

Module AXF_spez.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section SPE.
Context {fx : FPState}.

Definition VALS_spe (G2 mem2 hb W2 cnt : Z) : list Z := [G2; mem2; hb; W2; cnt].

Record spe_pre (regs : bvmap 5 word) (m : word -> option byte) (G2 mem2 hb W2 cnt : Z) : Prop := {
  spe_R10 : getr regs 10 = wa G2 ;
  spe_R11 : getr regs 11 = wa mem2 ;
  spe_R12 : getr regs 12 = wa hb ;
  spe_R13 : getr regs 13 = wa W2 ;
  spe_R14 : getr regs 14 = wa cnt ;
  spe_rng_G2 : 1 <= G2 <= 2^63-1 ;
  spe_rng_mem2 : 1 <= mem2 <= 2^63-1 ;
  spe_rng_hb : 0 <= hb <= 255 ;
  spe_rng_W2 : 0 <= W2 <= 2^63-1 ;
  spe_rng_cnt : 1 <= cnt <= 2^28 ;
  spe_ka1 : G2 mod 8 = 0 ;
  spe_kw6 : rdn SEGS m (wa (G2 + 24)) 4 = Some (word_to_le_bytes 4 (wa 0)) ;
  spe_kwr7 : forall d k, 0 <= d -> d + Z.of_nat k <= 1 -> store_ok SEGS m (wa (mem2 + 8 + d)) k = true ;
  spe_kd8 : mem2 + 8 + 1 <= G2 + 24 \/ G2 + 24 + 4 <= mem2 + 8
}.


#[using="Type"] Lemma spe_setup : forall regs m G2 mem2 hb W2 cnt, spe_pre regs m G2 mem2 hb W2 cnt ->
  regs_ok (Ez regs (VALS_spe G2 mem2 hb W2 cnt)) AXF_spe.sr_spe regs /\ know_ok SEGS (Ez regs (VALS_spe G2 mem2 hb W2 cnt)) m AXF_spe.kn_spe.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G2 mem2 hb W2 cnt P. destruct P as [spe_R10 spe_R11 spe_R12 spe_R13 spe_R14 spe_rng_G2 spe_rng_mem2 spe_rng_hb spe_rng_W2 spe_rng_cnt spe_ka1 spe_kw6 spe_kwr7 spe_kd8].
  set (E := Ez regs (VALS_spe G2 mem2 hb W2 cnt)).
  assert (Z32 : bv_unsigned (ev E 32) = G2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = mem2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = hb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = W2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_spe.sr_spe.
    apply (regs_ok_pin E _ regs 14); [apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|]|]|]|].
    - rewrite spe_R10. reflexivity.
    - rewrite spe_R11. reflexivity.
    - rewrite spe_R12. reflexivity.
    - rewrite spe_R13. reflexivity.
    - rewrite spe_R14. reflexivity. }
  unfold know_ok, AXF_spe.kn_spe.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_spe.e_G2 AXF_spe.e_mem2 AXF_spe.e_hb AXF_spe.e_W2 AXF_spe.e_cnt a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range G2 _ _ spe_rng_G2 eq_refl eq_refl), ?(mod64_of_range mem2 _ _ spe_rng_mem2 eq_refl eq_refl), ?(mod64_of_range hb _ _ spe_rng_hb eq_refl eq_refl), ?(mod64_of_range W2 _ _ spe_rng_W2 eq_refl eq_refl), ?(mod64_of_range cnt _ _ spe_rng_cnt eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply spe_kwr7]; assumption).
  all: try (clear - spe_rng_G2 spe_rng_mem2 spe_rng_hb spe_rng_W2 spe_rng_cnt spe_ka1; lia).
  all: first [(clear - spe_rng_G2 spe_rng_mem2 spe_rng_hb spe_rng_W2 spe_rng_cnt spe_ka1 spe_kd8; lia) | lia].
Qed.


Definition spe_mem_pspt (m : word -> option byte) (regs : bvmap 5 word) (G2 mem2 hb W2 cnt : Z) : word -> option byte :=
  wbytes (m) (wa (mem2 + 8)) (word_to_le_bytes 1 (wa ((32 * Z.shiftr hb 5) + Z.land (((cnt + -1)) mod 2^64) 31))).

#[using="Type"] Theorem spe_pspt : forall regs m rom G2 mem2 hb W2 cnt, spe_pre regs m G2 mem2 hb W2 cnt ->
  scs_denot SEGS m (Ez regs (VALS_spe G2 mem2 hb W2 cnt)) (snd (fst AXF_spe.RES_pspt)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52820) m rom) (mkst R (wa 0x52418) (spe_mem_pspt m regs G2 mem2 hb W2 cnt) rom) /\
    getr R 10 = wa G2 /\ getr R 11 = wa 0 /\ getr R 12 = wa ((32 * Z.shiftr hb 5) + Z.land (((cnt + -1)) mod 2^64) 31) /\ getr R 13 = wa (Z.land W2 31 + 1) /\ getr R 14 = wa (Z.land (((cnt + -1)) mod 2^64) 31) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G2 mem2 hb W2 cnt P Hsc. destruct (spe_setup regs m G2 mem2 hb W2 cnt P) as [HR HK].
  set (E := Ez regs (VALS_spe G2 mem2 hb W2 cnt)) in *. destruct P as [spe_R10 spe_R11 spe_R12 spe_R13 spe_R14 spe_rng_G2 spe_rng_mem2 spe_rng_hb spe_rng_W2 spe_rng_cnt spe_ka1 spe_kw6 spe_kwr7 spe_kd8].
  assert (Z32 : bv_unsigned (ev E 32) = G2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = mem2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = hb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = W2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x52418] AXF_spe.scr_pspt 0x52820 AXF_spe.sr_spe AXF_spe.kn_spe 37 _ _ _ E m rom regs AXF_spe.RES_pspt_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_spe.RES_pspt fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (spe_mem_pspt m regs G2 mem2 hb W2 cnt) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold spe_mem_pspt. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition spe_mem_pspf (m : word -> option byte) (regs : bvmap 5 word) (G2 mem2 hb W2 cnt : Z) : word -> option byte :=
  wbytes (m) (wa (mem2 + 8)) (word_to_le_bytes 1 (wa ((32 * Z.shiftr hb 5) + Z.land W2 31))).

#[using="Type"] Theorem spe_pspf : forall regs m rom G2 mem2 hb W2 cnt, spe_pre regs m G2 mem2 hb W2 cnt ->
  scs_denot SEGS m (Ez regs (VALS_spe G2 mem2 hb W2 cnt)) (snd (fst AXF_spe.RES_pspf)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52820) m rom) (mkst R (wa 0x52418) (spe_mem_pspf m regs G2 mem2 hb W2 cnt) rom) /\
    getr R 10 = wa G2 /\ getr R 11 = wa 0 /\ getr R 12 = wa ((32 * Z.shiftr hb 5) + Z.land W2 31) /\ getr R 13 = wa (Z.land W2 31 + 1) /\ getr R 14 = wa (Z.land W2 31) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G2 mem2 hb W2 cnt P Hsc. destruct (spe_setup regs m G2 mem2 hb W2 cnt P) as [HR HK].
  set (E := Ez regs (VALS_spe G2 mem2 hb W2 cnt)) in *. destruct P as [spe_R10 spe_R11 spe_R12 spe_R13 spe_R14 spe_rng_G2 spe_rng_mem2 spe_rng_hb spe_rng_W2 spe_rng_cnt spe_ka1 spe_kw6 spe_kwr7 spe_kd8].
  assert (Z32 : bv_unsigned (ev E 32) = G2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = mem2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = hb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = W2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x52418] AXF_spe.scr_pspf 0x52820 AXF_spe.sr_spe AXF_spe.kn_spe 37 _ _ _ E m rom regs AXF_spe.RES_pspf_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_spe.RES_pspf fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (spe_mem_pspf m regs G2 mem2 hb W2 cnt) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold spe_mem_pspf. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End SPE.
End AXF_spez.

Module AXF_spi.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_t0 := EVar 32.
Definition e_a4 := EVar 33.
Definition e_a5 := EVar 34.
Definition e_a6 := EVar 35.
Definition sr_spi := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 5 (e_t0)) 14 (e_a4)) 15 (e_a5)) 16 (e_a6)) 17 (ELit 4096)).
Definition kn_spi : list kentry :=
  [ KRange e_t0 0 (2^28);
    KRange e_a4 0 (2^28);
    KRange e_a5 16 (2^20);
    KRange e_a6 0 (2^28) ].
Definition scr_spi : scripts := SCR [true] [] [].
Definition ss_spi := SS 0x5280c sr_spi [] kn_spi 36.
Definition RUN_spi := sym_exec SEGS 100 true [0x5280c; 0x52820] scr_spi ss_spi [].

Definition scr_pspl : scripts := SCR [true] [] [].
Definition RES_pspl := Eval vm_compute in sym_exec SEGS 100 true [0x5280c; 0x52820] scr_pspl ss_spi [].
Lemma RES_pspl_ok : sym_exec SEGS 100 true [0x5280c; 0x52820] scr_pspl (SS 0x5280c sr_spi [] kn_spi 36) [] = RES_pspl.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pspx : scripts := SCR [false] [] [].
Definition RES_pspx := Eval vm_compute in sym_exec SEGS 100 true [0x5280c; 0x52820] scr_pspx ss_spi [].
Lemma RES_pspx_ok : sym_exec SEGS 100 true [0x5280c; 0x52820] scr_pspx (SS 0x5280c sr_spi [] kn_spi 36) [] = RES_pspx.
Proof. vm_compute. reflexivity. Qed.
End AXF_spi.

Module AXF_spiz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section SPI.
Context {fx : FPState}.

Definition VALS_spi (t0 a4 a5 a6 : Z) : list Z := [t0; a4; a5; a6].

Record spi_pre (regs : bvmap 5 word) (m : word -> option byte) (t0 a4 a5 a6 : Z) : Prop := {
  spi_R5 : getr regs 5 = wa t0 ;
  spi_R14 : getr regs 14 = wa a4 ;
  spi_R15 : getr regs 15 = wa a5 ;
  spi_R16 : getr regs 16 = wa a6 ;
  spi_R17 : getr regs 17 = wa 4096 ;
  spi_rng_t0 : 0 <= t0 <= 2^28 ;
  spi_rng_a4 : 0 <= a4 <= 2^28 ;
  spi_rng_a5 : 16 <= a5 <= 2^20 ;
  spi_rng_a6 : 0 <= a6 <= 2^28
}.


#[using="Type"] Lemma spi_setup : forall regs m t0 a4 a5 a6, spi_pre regs m t0 a4 a5 a6 ->
  regs_ok (Ez regs (VALS_spi t0 a4 a5 a6)) AXF_spi.sr_spi regs /\ know_ok SEGS (Ez regs (VALS_spi t0 a4 a5 a6)) m AXF_spi.kn_spi.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m t0 a4 a5 a6 P. destruct P as [spi_R5 spi_R14 spi_R15 spi_R16 spi_R17 spi_rng_t0 spi_rng_a4 spi_rng_a5 spi_rng_a6].
  set (E := Ez regs (VALS_spi t0 a4 a5 a6)).
  assert (Z32 : bv_unsigned (ev E 32) = t0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = a4) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = a5) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = a6) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_spi.sr_spi.
    apply (regs_ok_pin E _ regs 17); [apply (regs_ok_pin E _ regs 16); [apply (regs_ok_pin E _ regs 15); [apply (regs_ok_pin E _ regs 14); [apply (regs_ok_pin E _ regs 5); [apply regs_ok_id|]|]|]|]|].
    - rewrite spi_R5. reflexivity.
    - rewrite spi_R14. reflexivity.
    - rewrite spi_R15. reflexivity.
    - rewrite spi_R16. reflexivity.
    - rewrite spi_R17. reflexivity. }
  unfold know_ok, AXF_spi.kn_spi.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_spi.e_t0 AXF_spi.e_a4 AXF_spi.e_a5 AXF_spi.e_a6 a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range t0 _ _ spi_rng_t0 eq_refl eq_refl), ?(mod64_of_range a4 _ _ spi_rng_a4 eq_refl eq_refl), ?(mod64_of_range a5 _ _ spi_rng_a5 eq_refl eq_refl), ?(mod64_of_range a6 _ _ spi_rng_a6 eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - spi_rng_t0 spi_rng_a4 spi_rng_a5 spi_rng_a6; lia).
  all: first [lia].
Qed.


Definition spi_mem_pspl (m : word -> option byte) (regs : bvmap 5 word) (t0 a4 a5 a6 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem spi_pspl : forall regs m rom t0 a4 a5 a6, spi_pre regs m t0 a4 a5 a6 ->
  scs_denot SEGS m (Ez regs (VALS_spi t0 a4 a5 a6)) (snd (fst AXF_spi.RES_pspl)) ->
  exists R, msteps SEGS (mkst regs (wa 0x5280c) m rom) (mkst R (wa 0x5280c) (spi_mem_pspl m regs t0 a4 a5 a6) rom) /\
    getr R 5 = wa (t0 + a5) /\ getr R 14 = wa (a4 + 1) /\ getr R 15 = wa a5 /\ getr R 16 = wa (a5 + a6) /\ getr R 17 = wa 4096 /\ (forall k, In k [1; 2; 3; 4; 7; 8; 9; 10; 11; 12; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom t0 a4 a5 a6 P Hsc. destruct (spi_setup regs m t0 a4 a5 a6 P) as [HR HK].
  set (E := Ez regs (VALS_spi t0 a4 a5 a6)) in *. destruct P as [spi_R5 spi_R14 spi_R15 spi_R16 spi_R17 spi_rng_t0 spi_rng_a4 spi_rng_a5 spi_rng_a6].
  assert (Z32 : bv_unsigned (ev E 32) = t0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = a4) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = a5) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = a6) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x5280c; 0x52820] AXF_spi.scr_pspl 0x5280c AXF_spi.sr_spi AXF_spi.kn_spi 36 _ _ _ E m rom regs AXF_spi.RES_pspl_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_spi.RES_pspl fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (spi_mem_pspl m regs t0 a4 a5 a6) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold spi_mem_pspl. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition spi_mem_pspx (m : word -> option byte) (regs : bvmap 5 word) (t0 a4 a5 a6 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem spi_pspx : forall regs m rom t0 a4 a5 a6, spi_pre regs m t0 a4 a5 a6 ->
  scs_denot SEGS m (Ez regs (VALS_spi t0 a4 a5 a6)) (snd (fst AXF_spi.RES_pspx)) ->
  exists R, msteps SEGS (mkst regs (wa 0x5280c) m rom) (mkst R (wa 0x52820) (spi_mem_pspx m regs t0 a4 a5 a6) rom) /\
    getr R 5 = wa (t0 + a5) /\ getr R 14 = wa (a4 + 1) /\ getr R 15 = wa a5 /\ getr R 16 = wa (a5 + a6) /\ getr R 17 = wa 4096 /\ (forall k, In k [1; 2; 3; 4; 7; 8; 9; 10; 11; 12; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom t0 a4 a5 a6 P Hsc. destruct (spi_setup regs m t0 a4 a5 a6 P) as [HR HK].
  set (E := Ez regs (VALS_spi t0 a4 a5 a6)) in *. destruct P as [spi_R5 spi_R14 spi_R15 spi_R16 spi_R17 spi_rng_t0 spi_rng_a4 spi_rng_a5 spi_rng_a6].
  assert (Z32 : bv_unsigned (ev E 32) = t0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = a4) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = a5) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = a6) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x5280c; 0x52820] AXF_spi.scr_pspx 0x5280c AXF_spi.sr_spi AXF_spi.kn_spi 36 _ _ _ E m rom regs AXF_spi.RES_pspx_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_spi.RES_pspx fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (spi_mem_pspx m regs t0 a4 a5 a6) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold spi_mem_pspx. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End SPI.
End AXF_spiz.

Module AXF_t1.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_sp0 := EVar 33.
Definition e_BASE := EVar 34.
Definition e_LEN := EVar 35.
Definition e_ERR := EVar 36.
Definition e_ra := EVar 38.
Definition e_s0 := EVar 39.
Definition e_s1 := EVar 40.
Definition e_s2 := EVar 41.
Definition e_s3 := EVar 42.
Definition STK := SA e_sp0 (-1024).
Definition sr_t1 := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 1 (ELit 0x51768)) 2 (EAlu ALU_ADD e_sp0 (ELit (-48)))) 4 (ELit 0x75bd0)) 10 (e_BASE)) 11 (e_LEN)).
Definition kn_t1 : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWr STK (ELit 1024);
    KWord (SA (ELit 0) 0x95ed0) 4 (ELit 0);
    KWord (SA (ELit 0) 0x75b2c) 4 e_ERR;
    KWord (SA e_sp0 (-8)) 8 e_ra;
    KWord (SA e_sp0 (-16)) 8 e_s0;
    KWord (SA e_sp0 (-24)) 8 e_s1;
    KWord (SA e_sp0 (-32)) 8 e_s2;
    KWord (SA e_sp0 (-40)) 8 e_s3;
    KDisj STK (ELit 1024) (SA (ELit 0) 0x95ed0) (ELit 4);
    KDisj STK (ELit 1024) (SA (ELit 0) 0x75b2c) (ELit 4) ].
Definition scr_t1 : scripts := SCR [true] [] [].
Definition ss_t1 := SS 0x51ca0 sr_t1 [] kn_t1 43.
Definition RUN_t1 := sym_exec SEGS 120 true [0x53558] scr_t1 ss_t1 [].

Definition scr_pt1a : scripts := SCR [true] [] [].
Definition RES_pt1a := Eval vm_compute in sym_exec SEGS 120 true [0x53558] scr_pt1a ss_t1 [].
Lemma RES_pt1a_ok : sym_exec SEGS 120 true [0x53558] scr_pt1a (SS 0x51ca0 sr_t1 [] kn_t1 43) [] = RES_pt1a.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pt1b : scripts := SCR [false] [] [].
Definition RES_pt1b := Eval vm_compute in sym_exec SEGS 120 true [0x53558] scr_pt1b ss_t1 [].
Lemma RES_pt1b_ok : sym_exec SEGS 120 true [0x53558] scr_pt1b (SS 0x51ca0 sr_t1 [] kn_t1 43) [] = RES_pt1b.
Proof. vm_compute. reflexivity. Qed.
End AXF_t1.

Module AXF_t1z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section T1.
Context {fx : FPState}.

Definition VALS_t1 (sp0 BASE LEN ERR ra s0 s1 s2 s3 : Z) : list Z := [0; sp0; BASE; LEN; ERR; 0; ra; s0; s1; s2; s3].

Record t1_pre (regs : bvmap 5 word) (m : word -> option byte) (sp0 BASE LEN ERR ra s0 s1 s2 s3 : Z) : Prop := {
  t1_R1 : getr regs 1 = wa 333672 ;
  t1_R2 : getr regs 2 = wa (sp0 + -48) ;
  t1_R4 : getr regs 4 = wa 482256 ;
  t1_R10 : getr regs 10 = wa BASE ;
  t1_R11 : getr regs 11 = wa LEN ;
  t1_HSTK : stk_ok SEGS m (wa sp0) 1024 ;
  t1_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  t1_rng_BASE : 0 <= BASE <= 2^64-1 ;
  t1_rng_LEN : 0 <= LEN <= 2^64-1 ;
  t1_rng_ERR : 0 <= ERR <= 2^32-1 ;
  t1_rng_ra : 0 <= ra <= 2^64-1 ;
  t1_rng_s0 : 0 <= s0 <= 2^64-1 ;
  t1_rng_s1 : 0 <= s1 <= 2^64-1 ;
  t1_rng_s2 : 0 <= s2 <= 2^64-1 ;
  t1_rng_s3 : 0 <= s3 <= 2^64-1 ;
  t1_ka1 : sp0 mod 16 = 0 ;
  t1_kw3 : rdn SEGS m (wa (0 + 614096)) 4 = Some (word_to_le_bytes 4 (wa 0)) ;
  t1_kw4 : rdn SEGS m (wa (0 + 482092)) 4 = Some (word_to_le_bytes 4 (wa ERR)) ;
  t1_kw5 : rdn SEGS m (wa (sp0 + -8)) 8 = Some (word_to_le_bytes 8 (wa ra)) ;
  t1_kw6 : rdn SEGS m (wa (sp0 + -16)) 8 = Some (word_to_le_bytes 8 (wa s0)) ;
  t1_kw7 : rdn SEGS m (wa (sp0 + -24)) 8 = Some (word_to_le_bytes 8 (wa s1)) ;
  t1_kw8 : rdn SEGS m (wa (sp0 + -32)) 8 = Some (word_to_le_bytes 8 (wa s2)) ;
  t1_kw9 : rdn SEGS m (wa (sp0 + -40)) 8 = Some (word_to_le_bytes 8 (wa s3)) ;
  t1_kd10 : sp0 + -1024 + 1024 <= 0 + 614096 \/ 0 + 614096 + 4 <= sp0 + -1024 ;
  t1_kd11 : sp0 + -1024 + 1024 <= 0 + 482092 \/ 0 + 482092 + 4 <= sp0 + -1024
}.


#[using="Type"] Lemma t1_setup : forall regs m sp0 BASE LEN ERR ra s0 s1 s2 s3, t1_pre regs m sp0 BASE LEN ERR ra s0 s1 s2 s3 ->
  regs_ok (Ez regs (VALS_t1 sp0 BASE LEN ERR ra s0 s1 s2 s3)) AXF_t1.sr_t1 regs /\ know_ok SEGS (Ez regs (VALS_t1 sp0 BASE LEN ERR ra s0 s1 s2 s3)) m AXF_t1.kn_t1.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sp0 BASE LEN ERR ra s0 s1 s2 s3 P. destruct P as [t1_R1 t1_R2 t1_R4 t1_R10 t1_R11 t1_HSTK t1_rng_sp0 t1_rng_BASE t1_rng_LEN t1_rng_ERR t1_rng_ra t1_rng_s0 t1_rng_s1 t1_rng_s2 t1_rng_s3 t1_ka1 t1_kw3 t1_kw4 t1_kw5 t1_kw6 t1_kw7 t1_kw8 t1_kw9 t1_kd10 t1_kd11].
  set (E := Ez regs (VALS_t1 sp0 BASE LEN ERR ra s0 s1 s2 s3)).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = BASE) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = LEN) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = ERR) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = ra) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = s0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = s1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = s2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = s3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_t1.sr_t1.
    apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 4); [apply (regs_ok_pin E _ regs 2); [apply (regs_ok_pin E _ regs 1); [apply regs_ok_id|]|]|]|]|].
    - rewrite t1_R1. reflexivity.
    - rewrite t1_R2, zeval_sound. cbn [zeval edenot AXF_t1.e_sp0 AXF_t1.e_BASE AXF_t1.e_LEN AXF_t1.e_ERR AXF_t1.e_ra AXF_t1.e_s0 AXF_t1.e_s1 AXF_t1.e_s2 AXF_t1.e_s3 AXF_t1.STK]. rewrite ?Z33, ?Z34, ?Z35, ?Z36, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite t1_R4. reflexivity.
    - rewrite t1_R10. reflexivity.
    - rewrite t1_R11. reflexivity. }
  unfold know_ok, AXF_t1.kn_t1.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_t1.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_t1.e_sp0 AXF_t1.e_BASE AXF_t1.e_LEN AXF_t1.e_ERR AXF_t1.e_ra AXF_t1.e_s0 AXF_t1.e_s1 AXF_t1.e_s2 AXF_t1.e_s3 AXF_t1.STK a_base a_off].
  all: rewrite ?Z33, ?Z34, ?Z35, ?Z36, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sp0 _ _ t1_rng_sp0 eq_refl eq_refl), ?(mod64_of_range ERR _ _ t1_rng_ERR eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - t1_rng_sp0 t1_rng_BASE t1_rng_LEN t1_rng_ERR t1_rng_ra t1_rng_s0 t1_rng_s1 t1_rng_s2 t1_rng_s3 t1_ka1; lia).
  all: first [(clear - t1_rng_sp0 t1_rng_BASE t1_rng_LEN t1_rng_ERR t1_rng_ra t1_rng_s0 t1_rng_s1 t1_rng_s2 t1_rng_s3 t1_ka1 t1_kd10; lia) | (clear - t1_rng_sp0 t1_rng_BASE t1_rng_LEN t1_rng_ERR t1_rng_ra t1_rng_s0 t1_rng_s1 t1_rng_s2 t1_rng_s3 t1_ka1 t1_kd11; lia) | lia].
Qed.


Definition t1_mem_pt1a (m : word -> option byte) (regs : bvmap 5 word) (sp0 BASE LEN ERR ra s0 s1 s2 s3 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem t1_pt1a : forall regs m rom sp0 BASE LEN ERR ra s0 s1 s2 s3, t1_pre regs m sp0 BASE LEN ERR ra s0 s1 s2 s3 ->
  scs_denot SEGS m (Ez regs (VALS_t1 sp0 BASE LEN ERR ra s0 s1 s2 s3)) (snd (fst AXF_t1.RES_pt1a)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51ca0) m rom) (mkst R (wa 0x517bc) (t1_mem_pt1a m regs sp0 BASE LEN ERR ra s0 s1 s2 s3) rom) /\
    getr R 1 = wa ra /\ getr R 2 = wa sp0 /\ getr R 4 = wa 482256 /\ getr R 8 = wa s0 /\ getr R 9 = wa s1 /\ getr R 10 = wa 614096 /\ getr R 11 = wa 0 /\ getr R 18 = wa s2 /\ getr R 19 = wa s3 /\ (forall k, In k [3; 5; 6; 7; 12; 13; 14; 15; 16; 17; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sp0 BASE LEN ERR ra s0 s1 s2 s3 P Hsc. destruct (t1_setup regs m sp0 BASE LEN ERR ra s0 s1 s2 s3 P) as [HR HK].
  set (E := Ez regs (VALS_t1 sp0 BASE LEN ERR ra s0 s1 s2 s3)) in *. destruct P as [t1_R1 t1_R2 t1_R4 t1_R10 t1_R11 t1_HSTK t1_rng_sp0 t1_rng_BASE t1_rng_LEN t1_rng_ERR t1_rng_ra t1_rng_s0 t1_rng_s1 t1_rng_s2 t1_rng_s3 t1_ka1 t1_kw3 t1_kw4 t1_kw5 t1_kw6 t1_kw7 t1_kw8 t1_kw9 t1_kd10 t1_kd11].
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = BASE) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = LEN) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = ERR) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = ra) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = s0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = s1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = s2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = s3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 120 [0x53558] AXF_t1.scr_pt1a 0x51ca0 AXF_t1.sr_t1 AXF_t1.kn_t1 43 _ _ _ E m rom regs AXF_t1.RES_pt1a_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_t1.RES_pt1a fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (t1_mem_pt1a m regs sp0 BASE LEN ERR ra s0 s1 s2 s3) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold t1_mem_pt1a. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition t1_mem_pt1b (m : word -> option byte) (regs : bvmap 5 word) (sp0 BASE LEN ERR ra s0 s1 s2 s3 : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (m) (wa (sp0 + -56)) (word_to_le_bytes 8 (wa 333720))) (wa (sp0 + -64)) (word_to_le_bytes 8 (wa BASE))) (wa (sp0 + -72)) (word_to_le_bytes 8 (wa LEN)).

#[using="Type"] Theorem t1_pt1b : forall regs m rom sp0 BASE LEN ERR ra s0 s1 s2 s3, t1_pre regs m sp0 BASE LEN ERR ra s0 s1 s2 s3 ->
  scs_denot SEGS m (Ez regs (VALS_t1 sp0 BASE LEN ERR ra s0 s1 s2 s3)) (snd (fst AXF_t1.RES_pt1b)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51ca0) m rom) (mkst R (wa 0x53558) (t1_mem_pt1b m regs sp0 BASE LEN ERR ra s0 s1 s2 s3) rom) /\
    getr R 1 = wa 341324 /\ getr R 2 = wa (sp0 + -80) /\ getr R 4 = wa 482256 /\ getr R 8 = wa LEN /\ getr R 9 = wa BASE /\ getr R 10 = wa BASE /\ getr R 11 = wa LEN /\ getr R 17 = wa 215 /\ getr R 18 = wa 482092 /\ getr R 19 = wa (ext_Z true 0 4 ERR) /\ (forall k, In k [3; 5; 6; 7; 12; 13; 14; 15; 16; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sp0 BASE LEN ERR ra s0 s1 s2 s3 P Hsc. destruct (t1_setup regs m sp0 BASE LEN ERR ra s0 s1 s2 s3 P) as [HR HK].
  set (E := Ez regs (VALS_t1 sp0 BASE LEN ERR ra s0 s1 s2 s3)) in *. destruct P as [t1_R1 t1_R2 t1_R4 t1_R10 t1_R11 t1_HSTK t1_rng_sp0 t1_rng_BASE t1_rng_LEN t1_rng_ERR t1_rng_ra t1_rng_s0 t1_rng_s1 t1_rng_s2 t1_rng_s3 t1_ka1 t1_kw3 t1_kw4 t1_kw5 t1_kw6 t1_kw7 t1_kw8 t1_kw9 t1_kd10 t1_kd11].
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = BASE) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = LEN) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = ERR) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = ra) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = s0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = s1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = s2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = s3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 120 [0x53558] AXF_t1.scr_pt1b 0x51ca0 AXF_t1.sr_t1 AXF_t1.kn_t1 43 _ _ _ E m rom regs AXF_t1.RES_pt1b_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_t1.RES_pt1b fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (t1_mem_pt1b m regs sp0 BASE LEN ERR ra s0 s1 s2 s3) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold t1_mem_pt1b. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End T1.
End AXF_t1z.

Module AXF_t2.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_sp0 := EVar 33.
Definition e_BASE := EVar 34.
Definition e_LEN := EVar 35.
Definition e_ERR := EVar 36.
Definition e_ra := EVar 38.
Definition e_s0 := EVar 39.
Definition e_s1 := EVar 40.
Definition e_s2 := EVar 41.
Definition e_s3 := EVar 42.
Definition STK := SA e_sp0 (-1024).
Definition sr_t2 := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 1 (ELit 0x5354c)) 2 (EAlu ALU_ADD e_sp0 (ELit (-80)))) 4 (ELit 0x75bd0)) 8 (e_LEN)) 9 (e_BASE)) 10 (ELit 0)) 17 (ELit 215)) 18 (ELit 0x75b2c)) 19 (e_ERR)).
Definition kn_t2 : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWr STK (ELit 1024);
    KWord (SA e_sp0 (-56)) 8 (ELit 0x51798);
    KWord (SA e_sp0 (-64)) 8 e_BASE;
    KWord (SA e_sp0 (-72)) 8 e_LEN;
    KWord (SA e_sp0 (-8)) 8 e_ra;
    KWord (SA e_sp0 (-16)) 8 e_s0;
    KWord (SA e_sp0 (-24)) 8 e_s1;
    KWord (SA e_sp0 (-32)) 8 e_s2;
    KWord (SA e_sp0 (-40)) 8 e_s3;
    KWr (SA (ELit 0) 0x75b2c) (ELit 4);
    KDisj STK (ELit 1024) (SA (ELit 0) 0x75b2c) (ELit 4) ].
Definition scr_t2 : scripts := SCR [true] [] [].
Definition ss_t2 := SS 0x5355c sr_t2 [] kn_t2 43.
Definition RUN_t2 := sym_exec SEGS 100 true [] scr_t2 ss_t2 [].

Definition scr_pt2 : scripts := SCR [true] [] [].
Definition RES_pt2 := Eval vm_compute in sym_exec SEGS 100 true [] scr_pt2 ss_t2 [].
Lemma RES_pt2_ok : sym_exec SEGS 100 true [] scr_pt2 (SS 0x5355c sr_t2 [] kn_t2 43) [] = RES_pt2.
Proof. vm_compute. reflexivity. Qed.
End AXF_t2.

Module AXF_t2z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section T2.
Context {fx : FPState}.

Definition VALS_t2 (sp0 BASE LEN ERR ra s0 s1 s2 s3 : Z) : list Z := [0; sp0; BASE; LEN; ERR; 0; ra; s0; s1; s2; s3].

Record t2_pre (regs : bvmap 5 word) (m : word -> option byte) (sp0 BASE LEN ERR ra s0 s1 s2 s3 : Z) : Prop := {
  t2_R1 : getr regs 1 = wa 341324 ;
  t2_R2 : getr regs 2 = wa (sp0 + -80) ;
  t2_R4 : getr regs 4 = wa 482256 ;
  t2_R8 : getr regs 8 = wa LEN ;
  t2_R9 : getr regs 9 = wa BASE ;
  t2_R10 : getr regs 10 = wa 0 ;
  t2_R17 : getr regs 17 = wa 215 ;
  t2_R18 : getr regs 18 = wa 482092 ;
  t2_R19 : getr regs 19 = wa ERR ;
  t2_HSTK : stk_ok SEGS m (wa sp0) 1024 ;
  t2_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  t2_rng_BASE : 0 <= BASE <= 2^64-1 ;
  t2_rng_LEN : 0 <= LEN <= 2^64-1 ;
  t2_rng_ERR : 0 <= ERR <= 2^64-1 ;
  t2_rng_ra : 0 <= ra <= 2^64-1 ;
  t2_rng_s0 : 0 <= s0 <= 2^64-1 ;
  t2_rng_s1 : 0 <= s1 <= 2^64-1 ;
  t2_rng_s2 : 0 <= s2 <= 2^64-1 ;
  t2_rng_s3 : 0 <= s3 <= 2^64-1 ;
  t2_ka1 : sp0 mod 16 = 0 ;
  t2_kw3 : rdn SEGS m (wa (sp0 + -56)) 8 = Some (word_to_le_bytes 8 (wa 333720)) ;
  t2_kw4 : rdn SEGS m (wa (sp0 + -64)) 8 = Some (word_to_le_bytes 8 (wa BASE)) ;
  t2_kw5 : rdn SEGS m (wa (sp0 + -72)) 8 = Some (word_to_le_bytes 8 (wa LEN)) ;
  t2_kw6 : rdn SEGS m (wa (sp0 + -8)) 8 = Some (word_to_le_bytes 8 (wa ra)) ;
  t2_kw7 : rdn SEGS m (wa (sp0 + -16)) 8 = Some (word_to_le_bytes 8 (wa s0)) ;
  t2_kw8 : rdn SEGS m (wa (sp0 + -24)) 8 = Some (word_to_le_bytes 8 (wa s1)) ;
  t2_kw9 : rdn SEGS m (wa (sp0 + -32)) 8 = Some (word_to_le_bytes 8 (wa s2)) ;
  t2_kw10 : rdn SEGS m (wa (sp0 + -40)) 8 = Some (word_to_le_bytes 8 (wa s3)) ;
  t2_kwr11 : forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (0 + 482092 + d)) k = true ;
  t2_kd12 : sp0 + -1024 + 1024 <= 0 + 482092 \/ 0 + 482092 + 4 <= sp0 + -1024
}.


#[using="Type"] Lemma t2_setup : forall regs m sp0 BASE LEN ERR ra s0 s1 s2 s3, t2_pre regs m sp0 BASE LEN ERR ra s0 s1 s2 s3 ->
  regs_ok (Ez regs (VALS_t2 sp0 BASE LEN ERR ra s0 s1 s2 s3)) AXF_t2.sr_t2 regs /\ know_ok SEGS (Ez regs (VALS_t2 sp0 BASE LEN ERR ra s0 s1 s2 s3)) m AXF_t2.kn_t2.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sp0 BASE LEN ERR ra s0 s1 s2 s3 P. destruct P as [t2_R1 t2_R2 t2_R4 t2_R8 t2_R9 t2_R10 t2_R17 t2_R18 t2_R19 t2_HSTK t2_rng_sp0 t2_rng_BASE t2_rng_LEN t2_rng_ERR t2_rng_ra t2_rng_s0 t2_rng_s1 t2_rng_s2 t2_rng_s3 t2_ka1 t2_kw3 t2_kw4 t2_kw5 t2_kw6 t2_kw7 t2_kw8 t2_kw9 t2_kw10 t2_kwr11 t2_kd12].
  set (E := Ez regs (VALS_t2 sp0 BASE LEN ERR ra s0 s1 s2 s3)).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = BASE) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = LEN) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = ERR) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = ra) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = s0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = s1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = s2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = s3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_t2.sr_t2.
    apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 17); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 8); [apply (regs_ok_pin E _ regs 4); [apply (regs_ok_pin E _ regs 2); [apply (regs_ok_pin E _ regs 1); [apply regs_ok_id|]|]|]|]|]|]|]|]|].
    - rewrite t2_R1. reflexivity.
    - rewrite t2_R2, zeval_sound. cbn [zeval edenot AXF_t2.e_sp0 AXF_t2.e_BASE AXF_t2.e_LEN AXF_t2.e_ERR AXF_t2.e_ra AXF_t2.e_s0 AXF_t2.e_s1 AXF_t2.e_s2 AXF_t2.e_s3 AXF_t2.STK]. rewrite ?Z33, ?Z34, ?Z35, ?Z36, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite t2_R4. reflexivity.
    - rewrite t2_R8. reflexivity.
    - rewrite t2_R9. reflexivity.
    - rewrite t2_R10. reflexivity.
    - rewrite t2_R17. reflexivity.
    - rewrite t2_R18. reflexivity.
    - rewrite t2_R19. reflexivity. }
  unfold know_ok, AXF_t2.kn_t2.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_t2.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_t2.e_sp0 AXF_t2.e_BASE AXF_t2.e_LEN AXF_t2.e_ERR AXF_t2.e_ra AXF_t2.e_s0 AXF_t2.e_s1 AXF_t2.e_s2 AXF_t2.e_s3 AXF_t2.STK a_base a_off].
  all: rewrite ?Z33, ?Z34, ?Z35, ?Z36, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sp0 _ _ t2_rng_sp0 eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply t2_kwr11]; assumption).
  all: try (clear - t2_rng_sp0 t2_rng_BASE t2_rng_LEN t2_rng_ERR t2_rng_ra t2_rng_s0 t2_rng_s1 t2_rng_s2 t2_rng_s3 t2_ka1; lia).
  all: first [(clear - t2_rng_sp0 t2_rng_BASE t2_rng_LEN t2_rng_ERR t2_rng_ra t2_rng_s0 t2_rng_s1 t2_rng_s2 t2_rng_s3 t2_ka1 t2_kd12; lia) | lia].
Qed.


Definition t2_mem_pt2 (m : word -> option byte) (regs : bvmap 5 word) (sp0 BASE LEN ERR ra s0 s1 s2 s3 : Z) : word -> option byte :=
  wbytes (m) (wa (0 + 482092)) (word_to_le_bytes 4 (wa ERR)).

#[using="Type"] Theorem t2_pt2 : forall regs m rom sp0 BASE LEN ERR ra s0 s1 s2 s3, t2_pre regs m sp0 BASE LEN ERR ra s0 s1 s2 s3 ->
  scs_denot SEGS m (Ez regs (VALS_t2 sp0 BASE LEN ERR ra s0 s1 s2 s3)) (snd (fst AXF_t2.RES_pt2)) ->
  exists R, msteps SEGS (mkst regs (wa 0x5355c) m rom) (mkst R (wa 0x517bc) (t2_mem_pt2 m regs sp0 BASE LEN ERR ra s0 s1 s2 s3) rom) /\
    getr R 1 = wa ra /\ getr R 2 = wa sp0 /\ getr R 4 = wa 482256 /\ getr R 8 = wa s0 /\ getr R 9 = wa s1 /\ getr R 10 = wa 0 /\ getr R 11 = wa 18446744073709547521 /\ getr R 17 = wa 215 /\ getr R 18 = wa s2 /\ getr R 19 = wa s3 /\ (forall k, In k [3; 5; 6; 7; 12; 13; 14; 15; 16; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sp0 BASE LEN ERR ra s0 s1 s2 s3 P Hsc. destruct (t2_setup regs m sp0 BASE LEN ERR ra s0 s1 s2 s3 P) as [HR HK].
  set (E := Ez regs (VALS_t2 sp0 BASE LEN ERR ra s0 s1 s2 s3)) in *. destruct P as [t2_R1 t2_R2 t2_R4 t2_R8 t2_R9 t2_R10 t2_R17 t2_R18 t2_R19 t2_HSTK t2_rng_sp0 t2_rng_BASE t2_rng_LEN t2_rng_ERR t2_rng_ra t2_rng_s0 t2_rng_s1 t2_rng_s2 t2_rng_s3 t2_ka1 t2_kw3 t2_kw4 t2_kw5 t2_kw6 t2_kw7 t2_kw8 t2_kw9 t2_kw10 t2_kwr11 t2_kd12].
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = BASE) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = LEN) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = ERR) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = ra) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = s0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = s1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = s2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = s3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [] AXF_t2.scr_pt2 0x5355c AXF_t2.sr_t2 AXF_t2.kn_t2 43 _ _ _ E m rom regs AXF_t2.RES_pt2_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_t2.RES_pt2 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (t2_mem_pt2 m regs sp0 BASE LEN ERR ra s0 s1 s2 s3) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold t2_mem_pt2. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End T2.
End AXF_t2z.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section DEC63.
Context {fx : FPState}.

Definition VALS_dec63 (G idx W avail freed sp0 canary : Z) : list Z := [G; idx; W; avail; freed; sp0; canary].

Record dec63_pre (regs : bvmap 5 word) (m : word -> option byte) (G idx W avail freed sp0 canary : Z) : Prop := {
  dec63_R2 : getr regs 2 = wa sp0 ;
  dec63_R10 : getr regs 10 = wa G ;
  dec63_R11 : getr regs 11 = wa idx ;
  dec63_HSTK : stk_ok SEGS m (wa sp0) 1024 ;
  dec63_rng_G : 1 <= G <= 2^63-1 ;
  dec63_rng_idx : 0 <= idx <= 31 ;
  dec63_rng_W : 0 <= W <= 2^64-1 ;
  dec63_rng_avail : 0 <= avail <= 2^32-1 ;
  dec63_rng_freed : 0 <= freed <= 2^32-1 ;
  dec63_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  dec63_rng_canary : 0 <= canary <= 2^64-1 ;
  dec63_ka1 : sp0 mod 16 = 0 ;
  dec63_ka4 : G mod 8 = 0 ;
  dec63_kw8 : rdn SEGS m (wa (G + 24)) 4 = Some (word_to_le_bytes 4 (wa avail)) ;
  dec63_kw9 : rdn SEGS m (wa (G + 28)) 4 = Some (word_to_le_bytes 4 (wa freed)) ;
  dec63_kw10 : rdn SEGS m (wa (G + 32)) 8 = Some (word_to_le_bytes 8 (wa W)) ;
  dec63_kw11 : rdn SEGS m (wa (0 + 408992)) 8 = Some (word_to_le_bytes 8 (wa 613952)) ;
  dec63_kw12 : rdn SEGS m (wa (0 + 613952)) 8 = Some (word_to_le_bytes 8 (wa canary)) ;
  dec63_kd13 : sp0 + -1024 + 1024 <= G + 0 \/ G + 0 + 40 <= sp0 + -1024
}.


#[using="Type"] Lemma dec63_setup : forall regs m G idx W avail freed sp0 canary, dec63_pre regs m G idx W avail freed sp0 canary ->
  regs_ok (Ez regs (VALS_dec63 G idx W avail freed sp0 canary)) AXF_dec63.sr_dec63 regs /\ know_ok SEGS (Ez regs (VALS_dec63 G idx W avail freed sp0 canary)) m AXF_dec63.kn_dec63.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G idx W avail freed sp0 canary P. destruct P as [dec63_R2 dec63_R10 dec63_R11 dec63_HSTK dec63_rng_G dec63_rng_idx dec63_rng_W dec63_rng_avail dec63_rng_freed dec63_rng_sp0 dec63_rng_canary dec63_ka1 dec63_ka4 dec63_kw8 dec63_kw9 dec63_kw10 dec63_kw11 dec63_kw12 dec63_kd13].
  set (E := Ez regs (VALS_dec63 G idx W avail freed sp0 canary)).
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = idx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = avail) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = freed) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = canary) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_dec63.sr_dec63.
    apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|]|]|].
    - rewrite dec63_R2. reflexivity.
    - rewrite dec63_R10. reflexivity.
    - rewrite dec63_R11. reflexivity. }
  unfold know_ok, AXF_dec63.kn_dec63.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_dec63.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_dec63.e_G AXF_dec63.e_idx AXF_dec63.e_W AXF_dec63.e_avail AXF_dec63.e_freed AXF_dec63.e_sp0 AXF_dec63.e_canary AXF_dec63.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range G _ _ dec63_rng_G eq_refl eq_refl), ?(mod64_of_range idx _ _ dec63_rng_idx eq_refl eq_refl), ?(mod64_of_range avail _ _ dec63_rng_avail eq_refl eq_refl), ?(mod64_of_range freed _ _ dec63_rng_freed eq_refl eq_refl), ?(mod64_of_range sp0 _ _ dec63_rng_sp0 eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - dec63_rng_G dec63_rng_idx dec63_rng_W dec63_rng_avail dec63_rng_freed dec63_rng_sp0 dec63_rng_canary dec63_ka1 dec63_ka4; lia).
  all: first [(clear - dec63_rng_G dec63_rng_idx dec63_rng_W dec63_rng_avail dec63_rng_freed dec63_rng_sp0 dec63_rng_canary dec63_ka1 dec63_ka4 dec63_kd13; lia) | lia].
Qed.


Definition dec63_mem_pd63 (m : word -> option byte) (regs : bvmap 5 word) (G idx W avail freed sp0 canary : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (sp0 + -8)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1))))))) (wa (sp0 + -16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))))) (wa (sp0 + -24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))))))) (wa (sp0 + -32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))))))) (wa (sp0 + -40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))))) (wa (sp0 + -48)) (word_to_le_bytes 8 (wa canary)).

#[using="Type"] Theorem dec63_pd63 : forall regs m rom G idx W avail freed sp0 canary, dec63_pre regs m G idx W avail freed sp0 canary ->
  scs_denot SEGS m (Ez regs (VALS_dec63 G idx W avail freed sp0 canary)) (snd (fst AXF_dec63.RES_pd63)) ->
  exists R, msteps SEGS (mkst regs (wa 0x518d0) m rom) (mkst R (wa 0x519e4) (dec63_mem_pd63 m regs G idx W avail freed sp0 canary) rom) /\
    getr R 2 = wa (sp0 + -96) /\ getr R 9 = wa 613952 /\ getr R 10 = wa G /\ getr R 12 = wa (Z.shiftr (((4503599627370496 * W)) mod 2^64) 58) /\ getr R 14 = wa 47 /\ getr R 15 = wa W /\ getr R 16 = wa 612664 /\ getr R 18 = wa 614104 /\ (forall k, In k [1; 3; 4; 5; 6; 7; 8; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G idx W avail freed sp0 canary P Hsc. destruct (dec63_setup regs m G idx W avail freed sp0 canary P) as [HR HK].
  set (E := Ez regs (VALS_dec63 G idx W avail freed sp0 canary)) in *. destruct P as [dec63_R2 dec63_R10 dec63_R11 dec63_HSTK dec63_rng_G dec63_rng_idx dec63_rng_W dec63_rng_avail dec63_rng_freed dec63_rng_sp0 dec63_rng_canary dec63_ka1 dec63_ka4 dec63_kw8 dec63_kw9 dec63_kw10 dec63_kw11 dec63_kw12 dec63_kd13].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = idx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = avail) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = freed) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = canary) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 200 [0x519e4; 0x51a2c] AXF_dec63.scr_pd63 0x518d0 AXF_dec63.sr_dec63 AXF_dec63.kn_dec63 39 _ _ _ E m rom regs AXF_dec63.RES_pd63_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_dec63.RES_pd63 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (dec63_mem_pd63 m regs G idx W avail freed sp0 canary) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold dec63_mem_pd63. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End DEC63.
