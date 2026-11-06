(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXF_pc1a.

Import ListNotations AX2 AX2S.

Module AXF_rt2.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Definition e_DUM := EVar 32.
Definition sr_rt2 := (sr_upd sr_id 1 (ELit 272604)).
Definition kn_rt2 : list kentry :=
  [  ].
Definition scr_rt2 : scripts := SCR [] [] [].
Definition ss_rt2 := SS 0xd49f8 sr_rt2 [] kn_rt2 33.
Definition RUN_rt2 := sym_exec SEGS 4 true [0x428dc] scr_rt2 ss_rt2 [].

Definition scr_prt2 : scripts := SCR [] [] [].
Definition RES_prt2 := Eval vm_compute in sym_exec SEGS 4 true [0x428dc] scr_prt2 ss_rt2 [].
Lemma RES_prt2_ok : sym_exec SEGS 4 true [0x428dc] scr_prt2 (SS 0xd49f8 sr_rt2 [] kn_rt2 33) [] = RES_prt2.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
End AXF_rt2.

Module AXF_rt2z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .


Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Section RT2.
Context {fx : FPState}.

Definition VALS_rt2 (DUM : Z) : list Z := [DUM].

Record rt2_pre (regs : bvmap 5 word) (m : word -> option byte) (DUM : Z) : Prop := {
  rt2_R1 : getr regs 1 = wa 272604 ;
  rt2_rng_DUM : 0 <= DUM <= 1
}.


#[using="Type"] Lemma rt2_setup : forall regs m DUM, rt2_pre regs m DUM ->
  regs_ok (Ez regs (VALS_rt2 DUM)) AXF_rt2.sr_rt2 regs /\ know_ok SEGS (Ez regs (VALS_rt2 DUM)) m AXF_rt2.kn_rt2.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m DUM P. destruct P as [rt2_R1 rt2_rng_DUM].
  set (E := Ez regs (VALS_rt2 DUM)).
  assert (Z32 : bv_unsigned (ev E 32) = DUM) by (apply zatom; [reflexivity | reflexivity | zrange]).

  split.
  { unfold AXF_rt2.sr_rt2.
    apply (regs_ok_pin E _ regs 1); [apply regs_ok_id|].
    - rewrite rt2_R1. reflexivity. }
  unfold know_ok, AXF_rt2.kn_rt2.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_rt2.e_DUM a_base a_off].
  all: rewrite ?Z32.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range DUM _ _ rt2_rng_DUM eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - rt2_rng_DUM; lia).
  all: first [lia].
Qed.


Definition rt2_mem_prt2 (m : word -> option byte) (regs : bvmap 5 word) (DUM : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem rt2_prt2 : forall regs m rom DUM, rt2_pre regs m DUM ->
  scs_denot SEGS m (Ez regs (VALS_rt2 DUM)) (snd (fst AXF_rt2.RES_prt2)) ->
  exists R, msteps SEGS (mkst regs (wa 0xd49f8) m rom) (mkst R (wa 0x428dc) (rt2_mem_prt2 m regs DUM) rom) /\
    getr R 1 = wa 272604 /\ (forall k, In k [2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom DUM P Hsc. destruct (rt2_setup regs m DUM P) as [HR HK].
  set (E := Ez regs (VALS_rt2 DUM)) in *. destruct P as [rt2_R1 rt2_rng_DUM].
  assert (Z32 : bv_unsigned (ev E 32) = DUM) by (apply zatom; [reflexivity | reflexivity | zrange]).

  destruct (run_sound SEGS 4 [0x428dc] AXF_rt2.scr_prt2 0xd49f8 AXF_rt2.sr_rt2 AXF_rt2.kn_rt2 33 _ _ _ E m rom regs AXF_rt2.RES_prt2_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_rt2.RES_prt2 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (rt2_mem_prt2 m regs DUM) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold rt2_mem_prt2. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End RT2.
(* [comment removed for export] *)
End AXF_rt2z.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Section PC1A.
Context {fx : FPState}.

Definition VALS_pc1a (AD SZ S0 : Z) : list Z := [AD; SZ; S0].

Record pc1a_pre (regs : bvmap 5 word) (m : word -> option byte) (AD SZ S0 : Z) : Prop := {
  pc1a_R1 : getr regs 1 = wa 514992 ;
  pc1a_R10 : getr regs 10 = wa AD ;
  pc1a_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  pc1a_rng_AD : 17594333495296 <= AD <= 2^47-2^20 ;
  pc1a_rng_SZ : 4096 <= SZ <= 2^20 ;
  pc1a_rng_S0 : 0 <= S0 <= 2^64-1 ;
  pc1a_ka1 : AD mod 4096 = 0 ;
  pc1a_ka3 : SZ mod 4096 = 0 ;
  pc1a_kr4 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  pc1a_kw5 : rdn SEGS m (wa (0 + 941788)) 1 = Some (word_to_le_bytes 1 (wa 1)) ;
  pc1a_kw6 : rdn SEGS m (wa (0 + 910480)) 8 = Some (word_to_le_bytes 8 (wa 943736)) ;
  pc1a_kw7 : rdn SEGS m (wa (0 + 943736)) 8 = Some (word_to_le_bytes 8 (wa 2147450880)) ;
  pc1a_kw8 : rdn SEGS m (wa (0 + 910488)) 8 = Some (word_to_le_bytes 8 (wa 947048)) ;
  pc1a_kw9 : rdn SEGS m (wa (0 + 947048)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  pc1a_kw10 : rdn SEGS m (wa (0 + 910496)) 8 = Some (word_to_le_bytes 8 (wa 947056)) ;
  pc1a_kw11 : rdn SEGS m (wa (0 + 947056)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  pc1a_kw12 : rdn SEGS m (wa (0 + 910504)) 8 = Some (word_to_le_bytes 8 (wa 947040)) ;
  pc1a_kw13 : rdn SEGS m (wa (0 + 947040)) 8 = Some (word_to_le_bytes 8 (wa 140737488355327)) ;
  pc1a_kw14 : rdn SEGS m (wa (0 + 910512)) 8 = Some (word_to_le_bytes 8 (wa 918480)) ;
  pc1a_kw15 : rdn SEGS m (wa (0 + 918480)) 8 = Some (word_to_le_bytes 8 (wa 870660)) ;
  pc1a_kw16 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 24)) 8 = Some (word_to_le_bytes 8 (wa 272576)) ;
  pc1a_kw17 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 16)) 8 = Some (word_to_le_bytes 8 (wa S0)) ;
  pc1a_kw18 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 8)) 8 = Some (word_to_le_bytes 8 (wa AD)) ;
  pc1a_kw19 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 0)) 8 = Some (word_to_le_bytes 8 (wa SZ)) ;
  pc1a_kwr20 : forall d k, 0 <= d -> d + Z.of_nat k <= 32 -> store_ok SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 0 + d)) k = true
}.


#[using="Type"] Lemma pc1a_setup : forall regs m AD SZ S0, pc1a_pre regs m AD SZ S0 ->
  regs_ok (Ez regs (VALS_pc1a AD SZ S0)) AXF_pc1a.sr_pc1a regs /\ know_ok SEGS (Ez regs (VALS_pc1a AD SZ S0)) m AXF_pc1a.kn_pc1a.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m AD SZ S0 P. destruct P as [pc1a_R1 pc1a_R10 pc1a_HSTK pc1a_rng_AD pc1a_rng_SZ pc1a_rng_S0 pc1a_ka1 pc1a_ka3 pc1a_kr4 pc1a_kw5 pc1a_kw6 pc1a_kw7 pc1a_kw8 pc1a_kw9 pc1a_kw10 pc1a_kw11 pc1a_kw12 pc1a_kw13 pc1a_kw14 pc1a_kw15 pc1a_kw16 pc1a_kw17 pc1a_kw18 pc1a_kw19 pc1a_kwr20].
  set (E := Ez regs (VALS_pc1a AD SZ S0)).
  assert (Z32 : bv_unsigned (ev E 32) = AD) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = SZ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = S0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  split.
  { unfold AXF_pc1a.sr_pc1a.
    apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 1); [apply regs_ok_id|]|].
    - rewrite pc1a_R1. reflexivity.
    - rewrite pc1a_R10. reflexivity. }
  unfold know_ok, AXF_pc1a.kn_pc1a.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_pc1a.e_AD AXF_pc1a.e_SZ AXF_pc1a.e_S0 AXF_pc1a.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range AD _ _ pc1a_rng_AD eq_refl eq_refl), ?(mod64_of_range SZ _ _ pc1a_rng_SZ eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply pc1a_kwr20]; assumption).
  all: try (clear - pc1a_rng_AD pc1a_rng_SZ pc1a_rng_S0 pc1a_ka1 pc1a_ka3 pc1a_kr4; lia).
  all: first [lia].
Qed.


Definition pc1a_mem_ppc1a (m : word -> option byte) (regs : bvmap 5 word) (AD SZ S0 : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 24)) (word_to_le_bytes 8 (wa 272604))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 16)) (word_to_le_bytes 8 (wa S0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 8)) (word_to_le_bytes 8 (wa AD))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 0)) (word_to_le_bytes 8 (wa SZ))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))))).

#[using="Type"] Theorem pc1a_ppc1a : forall regs m rom AD SZ S0, pc1a_pre regs m AD SZ S0 ->
  scs_denot SEGS m (Ez regs (VALS_pc1a AD SZ S0)) (snd (fst AXF_pc1a.RES_ppc1a)) ->
  exists R, msteps SEGS (mkst regs (wa 0x75a48) m rom) (mkst R (wa 0xd4904) (pc1a_mem_ppc1a m regs AD SZ S0) rom) /\
    getr R 1 = wa 272604 /\ getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 32) /\ getr R 5 = wa 17594333495295 /\ getr R 6 = wa 870660 /\ getr R 7 = wa 140737488355327 /\ getr R 8 = wa S0 /\ getr R 9 = wa AD /\ getr R 10 = wa (Z.shiftr AD 3 + 2147450880) /\ getr R 11 = wa 250 /\ getr R 12 = wa (((-1 * Z.shiftr AD 3) + Z.shiftr ((((AD + SZ) + -8)) mod 2^64) 3) + 1) /\ getr R 13 = wa (Z.shiftr AD 3) /\ getr R 14 = wa 0 /\ getr R 15 = wa 17592186044415 /\ getr R 16 = wa 18446744073709551615 /\ getr R 17 = wa 0 /\ getr R 18 = wa SZ /\ getr R 28 = wa 140737488355327 /\ (forall k, In k [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom AD SZ S0 P Hsc. destruct (pc1a_setup regs m AD SZ S0 P) as [HR HK].
  set (E := Ez regs (VALS_pc1a AD SZ S0)) in *. destruct P as [pc1a_R1 pc1a_R10 pc1a_HSTK pc1a_rng_AD pc1a_rng_SZ pc1a_rng_S0 pc1a_ka1 pc1a_ka3 pc1a_kr4 pc1a_kw5 pc1a_kw6 pc1a_kw7 pc1a_kw8 pc1a_kw9 pc1a_kw10 pc1a_kw11 pc1a_kw12 pc1a_kw13 pc1a_kw14 pc1a_kw15 pc1a_kw16 pc1a_kw17 pc1a_kw18 pc1a_kw19 pc1a_kwr20].
  assert (Z32 : bv_unsigned (ev E 32) = AD) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = SZ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = S0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  destruct (run_sound SEGS 200 [0xd4904] AXF_pc1a.scr_ppc1a 0x75a48 AXF_pc1a.sr_pc1a AXF_pc1a.kn_pc1a 35 _ _ _ E m rom regs AXF_pc1a.RES_ppc1a_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_pc1a.RES_ppc1a fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (pc1a_mem_ppc1a m regs AD SZ S0) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold pc1a_mem_ppc1a. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End PC1A.
(* [comment removed for export] *)
