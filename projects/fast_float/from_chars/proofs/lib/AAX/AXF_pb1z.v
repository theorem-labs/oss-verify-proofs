(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_pb1.

Import ListNotations AX2 AX2S.

Module AXF_rt1.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Definition e_DUM := EVar 32.
Definition sr_rt1 := (sr_upd sr_id 1 (ELit 280956)).
Definition kn_rt1 : list kentry :=
  [  ].
Definition scr_rt1 : scripts := SCR [] [] [].
Definition ss_rt1 := SS 0xd317c sr_rt1 [] kn_rt1 33.
Definition RUN_rt1 := sym_exec SEGS 4 true [0x4497c] scr_rt1 ss_rt1 [].

Definition scr_prt1 : scripts := SCR [] [] [].
Definition RES_prt1 := Eval vm_compute in sym_exec SEGS 4 true [0x4497c] scr_prt1 ss_rt1 [].
Lemma RES_prt1_ok : sym_exec SEGS 4 true [0x4497c] scr_prt1 (SS 0xd317c sr_rt1 [] kn_rt1 33) [] = RES_prt1.
Proof. vm_compute. reflexivity. Qed.
End AXF_rt1.

Module AXF_rt1z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .


Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Section RT1.
Context {fx : FPState}.

Definition VALS_rt1 (DUM : Z) : list Z := [DUM].

Record rt1_pre (regs : bvmap 5 word) (m : word -> option byte) (DUM : Z) : Prop := {
  rt1_R1 : getr regs 1 = wa 280956 ;
  rt1_rng_DUM : 0 <= DUM <= 1
}.


#[using="Type"] Lemma rt1_setup : forall regs m DUM, rt1_pre regs m DUM ->
  regs_ok (Ez regs (VALS_rt1 DUM)) AXF_rt1.sr_rt1 regs /\ know_ok SEGS (Ez regs (VALS_rt1 DUM)) m AXF_rt1.kn_rt1.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m DUM P. destruct P as [rt1_R1 rt1_rng_DUM].
  set (E := Ez regs (VALS_rt1 DUM)).
  assert (Z32 : bv_unsigned (ev E 32) = DUM) by (apply zatom; [reflexivity | reflexivity | zrange]).

  split.
  { unfold AXF_rt1.sr_rt1.
    apply (regs_ok_pin E _ regs 1); [apply regs_ok_id|].
    - rewrite rt1_R1. reflexivity. }
  unfold know_ok, AXF_rt1.kn_rt1.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_rt1.e_DUM a_base a_off].
  all: rewrite ?Z32.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range DUM _ _ rt1_rng_DUM eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - rt1_rng_DUM; lia).
  all: first [lia].
Qed.


Definition rt1_mem_prt1 (m : word -> option byte) (regs : bvmap 5 word) (DUM : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem rt1_prt1 : forall regs m rom DUM, rt1_pre regs m DUM ->
  scs_denot SEGS m (Ez regs (VALS_rt1 DUM)) (snd (fst AXF_rt1.RES_prt1)) ->
  exists R, msteps SEGS (mkst regs (wa 0xd317c) m rom) (mkst R (wa 0x4497c) (rt1_mem_prt1 m regs DUM) rom) /\
    getr R 1 = wa 280956 /\ (forall k, In k [2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom DUM P Hsc. destruct (rt1_setup regs m DUM P) as [HR HK].
  set (E := Ez regs (VALS_rt1 DUM)) in *. destruct P as [rt1_R1 rt1_rng_DUM].
  assert (Z32 : bv_unsigned (ev E 32) = DUM) by (apply zatom; [reflexivity | reflexivity | zrange]).

  destruct (run_sound SEGS 4 [0x4497c] AXF_rt1.scr_prt1 0xd317c AXF_rt1.sr_rt1 AXF_rt1.kn_rt1 33 _ _ _ E m rom regs AXF_rt1.RES_prt1_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_rt1.RES_prt1 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (rt1_mem_prt1 m regs DUM) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold rt1_mem_prt1. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End RT1.
End AXF_rt1z.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Section PB1.
Context {fx : FPState}.

Definition VALS_pb1 (AD SZ S0 S1 S2 : Z) : list Z := [AD; SZ; S0; S1; S2].

Record pb1_pre (regs : bvmap 5 word) (m : word -> option byte) (AD SZ S0 S1 S2 : Z) : Prop := {
  pb1_R1 : getr regs 1 = wa 515004 ;
  pb1_R10 : getr regs 10 = wa AD ;
  pb1_R19 : getr regs 19 = wa SZ ;
  pb1_R20 : getr regs 20 = wa AD ;
  pb1_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  pb1_rng_AD : 17594333495296 <= AD <= 2^47-2^20 ;
  pb1_rng_SZ : 4096 <= SZ <= 2^20 ;
  pb1_rng_S0 : 0 <= S0 <= 2^64-1 ;
  pb1_rng_S1 : 0 <= S1 <= 2^64-1 ;
  pb1_rng_S2 : 0 <= S2 <= 2^64-1 ;
  pb1_ka1 : AD mod 4096 = 0 ;
  pb1_ka3 : SZ mod 4096 = 0 ;
  pb1_kr4 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  pb1_kw5 : rdn SEGS m (wa (0 + 935452)) 1 = Some (word_to_le_bytes 1 (wa 1)) ;
  pb1_kw6 : rdn SEGS m (wa (0 + 904208)) 8 = Some (word_to_le_bytes 8 (wa 937400)) ;
  pb1_kw7 : rdn SEGS m (wa (0 + 937400)) 8 = Some (word_to_le_bytes 8 (wa 2147450880)) ;
  pb1_kw8 : rdn SEGS m (wa (0 + 904216)) 8 = Some (word_to_le_bytes 8 (wa 940712)) ;
  pb1_kw9 : rdn SEGS m (wa (0 + 940712)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  pb1_kw10 : rdn SEGS m (wa (0 + 904224)) 8 = Some (word_to_le_bytes 8 (wa 940720)) ;
  pb1_kw11 : rdn SEGS m (wa (0 + 940720)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  pb1_kw12 : rdn SEGS m (wa (0 + 904232)) 8 = Some (word_to_le_bytes 8 (wa 940704)) ;
  pb1_kw13 : rdn SEGS m (wa (0 + 940704)) 8 = Some (word_to_le_bytes 8 (wa 140737488355327)) ;
  pb1_kw14 : rdn SEGS m (wa (0 + 904240)) 8 = Some (word_to_le_bytes 8 (wa 912208)) ;
  pb1_kw15 : rdn SEGS m (wa (0 + 912208)) 8 = Some (word_to_le_bytes 8 (wa 864392)) ;
  pb1_kw16 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 24)) 8 = Some (word_to_le_bytes 8 (wa 280928)) ;
  pb1_kw17 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 16)) 8 = Some (word_to_le_bytes 8 (wa S0)) ;
  pb1_kw18 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 8)) 8 = Some (word_to_le_bytes 8 (wa S1)) ;
  pb1_kw19 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 0)) 8 = Some (word_to_le_bytes 8 (wa S2)) ;
  pb1_kwr20 : forall d k, 0 <= d -> d + Z.of_nat k <= 32 -> store_ok SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 0 + d)) k = true
}.


#[using="Type"] Lemma pb1_setup : forall regs m AD SZ S0 S1 S2, pb1_pre regs m AD SZ S0 S1 S2 ->
  regs_ok (Ez regs (VALS_pb1 AD SZ S0 S1 S2)) AXF_pb1.sr_pb1 regs /\ know_ok SEGS (Ez regs (VALS_pb1 AD SZ S0 S1 S2)) m AXF_pb1.kn_pb1.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m AD SZ S0 S1 S2 P. destruct P as [pb1_R1 pb1_R10 pb1_R19 pb1_R20 pb1_HSTK pb1_rng_AD pb1_rng_SZ pb1_rng_S0 pb1_rng_S1 pb1_rng_S2 pb1_ka1 pb1_ka3 pb1_kr4 pb1_kw5 pb1_kw6 pb1_kw7 pb1_kw8 pb1_kw9 pb1_kw10 pb1_kw11 pb1_kw12 pb1_kw13 pb1_kw14 pb1_kw15 pb1_kw16 pb1_kw17 pb1_kw18 pb1_kw19 pb1_kwr20].
  set (E := Ez regs (VALS_pb1 AD SZ S0 S1 S2)).
  assert (Z32 : bv_unsigned (ev E 32) = AD) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = SZ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = S0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = S1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = S2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  split.
  { unfold AXF_pb1.sr_pb1.
    apply (regs_ok_pin E _ regs 20); [apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 1); [apply regs_ok_id|]|]|]|].
    - rewrite pb1_R1. reflexivity.
    - rewrite pb1_R10. reflexivity.
    - rewrite pb1_R19. reflexivity.
    - rewrite pb1_R20. reflexivity. }
  unfold know_ok, AXF_pb1.kn_pb1.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_pb1.e_AD AXF_pb1.e_SZ AXF_pb1.e_S0 AXF_pb1.e_S1 AXF_pb1.e_S2 AXF_pb1.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range AD _ _ pb1_rng_AD eq_refl eq_refl), ?(mod64_of_range SZ _ _ pb1_rng_SZ eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply pb1_kwr20]; assumption).
  all: try (clear - pb1_rng_AD pb1_rng_SZ pb1_rng_S0 pb1_rng_S1 pb1_rng_S2 pb1_ka1 pb1_ka3 pb1_kr4; lia).
  all: first [lia].
Qed.


Definition pb1_mem_ppb1 (m : word -> option byte) (regs : bvmap 5 word) (AD SZ S0 S1 S2 : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 24)) (word_to_le_bytes 8 (wa 280956))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 16)) (word_to_le_bytes 8 (wa S0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 8)) (word_to_le_bytes 8 (wa S1))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 0)) (word_to_le_bytes 8 (wa S2))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa SZ))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -16)) (word_to_le_bytes 8 (wa AD))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))))).

#[using="Type"] Theorem pb1_ppb1 : forall regs m rom AD SZ S0 S1 S2, pb1_pre regs m AD SZ S0 S1 S2 ->
  scs_denot SEGS m (Ez regs (VALS_pb1 AD SZ S0 S1 S2)) (snd (fst AXF_pb1.RES_ppb1)) ->
  exists R, msteps SEGS (mkst regs (wa 0x75a54) m rom) (mkst R (wa 0xd3088) (pb1_mem_ppb1 m regs AD SZ S0 S1 S2) rom) /\
    getr R 1 = wa 280956 /\ getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 32) /\ getr R 5 = wa 17594333495295 /\ getr R 6 = wa 864392 /\ getr R 7 = wa 140737488355327 /\ getr R 8 = wa S0 /\ getr R 9 = wa S1 /\ getr R 10 = wa (Z.shiftr AD 3 + 2147450880) /\ getr R 11 = wa 250 /\ getr R 12 = wa (((-1 * Z.shiftr AD 3) + Z.shiftr ((((AD + SZ) + -8)) mod 2^64) 3) + 1) /\ getr R 13 = wa (Z.shiftr AD 3) /\ getr R 14 = wa 0 /\ getr R 15 = wa 17592186044415 /\ getr R 16 = wa 18446744073709551615 /\ getr R 17 = wa 0 /\ getr R 18 = wa S2 /\ getr R 19 = wa SZ /\ getr R 20 = wa AD /\ getr R 28 = wa 140737488355327 /\ (forall k, In k [3; 4; 21; 22; 23; 24; 25; 26; 27; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom AD SZ S0 S1 S2 P Hsc. destruct (pb1_setup regs m AD SZ S0 S1 S2 P) as [HR HK].
  set (E := Ez regs (VALS_pb1 AD SZ S0 S1 S2)) in *. destruct P as [pb1_R1 pb1_R10 pb1_R19 pb1_R20 pb1_HSTK pb1_rng_AD pb1_rng_SZ pb1_rng_S0 pb1_rng_S1 pb1_rng_S2 pb1_ka1 pb1_ka3 pb1_kr4 pb1_kw5 pb1_kw6 pb1_kw7 pb1_kw8 pb1_kw9 pb1_kw10 pb1_kw11 pb1_kw12 pb1_kw13 pb1_kw14 pb1_kw15 pb1_kw16 pb1_kw17 pb1_kw18 pb1_kw19 pb1_kwr20].
  assert (Z32 : bv_unsigned (ev E 32) = AD) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = SZ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = S0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = S1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = S2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  destruct (run_sound SEGS 200 [0xd3088] AXF_pb1.scr_ppb1 0x75a54 AXF_pb1.sr_pb1 AXF_pb1.kn_pb1 37 _ _ _ E m rom regs AXF_pb1.RES_ppb1_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_pb1.RES_ppb1 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (pb1_mem_ppb1 m regs AD SZ S0 S1 S2) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold pb1_mem_ppb1. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End PB1.
