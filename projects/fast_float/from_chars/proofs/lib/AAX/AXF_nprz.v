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

Module AXF_npr.
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

Definition e_CA := EVar 32.
Definition e_ND := EVar 33.
Definition e_mc := EVar 34.
Definition CC := EAlu ALU_SRL (EAlu ALU_ADD e_ND (ELit 31)) (ELit 5).
Definition REC := EAlu ALU_ADD e_CA (EMd M_MUL (ELit 80) (EAlu ALU_SRL (EAlu ALU_ADD e_ND (ELit 31)) (ELit 5))).
Definition STK := SA (EVar 2) (-1024).
Definition sr_npr := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (e_CA)) 11 (REC)) 12 (ELit 923480)) 13 (CC)).
Definition kn_npr : list kentry :=
  [ KRange e_CA 1 (2^47);
    KAlign e_CA 16;
    KRange e_ND 33 512;
    KRange (EVar 2) (2^46) (2^47);
    KWord (SA REC 4) 4 e_mc;
    KWr STK (ELit 1024) ].
Definition scr_npr : scripts := SCR [false] [] [].
Definition ss_npr := SS 0x43f94 sr_npr [] kn_npr 35.
Definition RUN_npr := sym_exec SEGS 40 true [0x44474] scr_npr ss_npr [].

Definition scr_pnpr : scripts := SCR [false] [] [].
Definition RES_pnpr := Eval vm_compute in sym_exec SEGS 40 true [0x44474] scr_pnpr ss_npr [].
Lemma RES_pnpr_ok : sym_exec SEGS 40 true [0x44474] scr_pnpr (SS 0x43f94 sr_npr [] kn_npr 35) [] = RES_pnpr.
Proof. vm_compute. reflexivity. Qed.
End AXF_npr.


Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Section NPR.
Context {fx : FPState}.

Definition VALS_npr (CA ND mc : Z) : list Z := [CA; ND; mc].

Record npr_pre (regs : bvmap 5 word) (m : word -> option byte) (CA ND mc : Z) : Prop := {
  npr_R10 : getr regs 10 = wa CA ;
  npr_R11 : getr regs 11 = wa (CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5)) ;
  npr_R12 : getr regs 12 = wa 923480 ;
  npr_R13 : getr regs 13 = wa (Z.shiftr (((ND + 31)) mod 2^64) 5) ;
  npr_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  npr_rng_CA : 1 <= CA <= 2^47 ;
  npr_rng_ND : 33 <= ND <= 512 ;
  npr_rng_mc : 2 <= mc <= 16 ;
  npr_ka1 : CA mod 16 = 0 ;
  npr_kr3 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  npr_kw4 : rdn SEGS m (wa (CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 4)) 4 = Some (word_to_le_bytes 4 (wa mc))
}.


#[using="Type"] Lemma npr_setup : forall regs m CA ND mc, npr_pre regs m CA ND mc ->
  regs_ok (Ez regs (VALS_npr CA ND mc)) AXF_npr.sr_npr regs /\ know_ok SEGS (Ez regs (VALS_npr CA ND mc)) m AXF_npr.kn_npr.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m CA ND mc P. destruct P as [npr_R10 npr_R11 npr_R12 npr_R13 npr_HSTK npr_rng_CA npr_rng_ND npr_rng_mc npr_ka1 npr_kr3 npr_kw4].
  set (E := Ez regs (VALS_npr CA ND mc)).
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ND) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = mc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  assert (HC : 2 <= Z.shiftr ((ND + 31) mod 2^64) 5 <= 16) by (rewrite Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia; change (2^5) with 32; split; [apply Z.div_le_lower_bound; lia | apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia]).
  split.
  { unfold AXF_npr.sr_npr.
    apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|]|]|].
    - rewrite npr_R10. reflexivity.
    - rewrite npr_R11, zeval_sound. cbn [zeval edenot AXF_npr.e_CA AXF_npr.e_ND AXF_npr.e_mc AXF_npr.CC AXF_npr.REC AXF_npr.STK]. rewrite ?Z32, ?Z33, ?Z34, ?Z2. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite npr_R12. reflexivity.
    - rewrite npr_R13, zeval_sound. cbn [zeval edenot AXF_npr.e_CA AXF_npr.e_ND AXF_npr.e_mc AXF_npr.CC AXF_npr.REC AXF_npr.STK]. rewrite ?Z32, ?Z33, ?Z34, ?Z2. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)]. }
  unfold know_ok, AXF_npr.kn_npr.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_npr.e_CA AXF_npr.e_ND AXF_npr.e_mc AXF_npr.CC AXF_npr.REC AXF_npr.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range CA _ _ npr_rng_CA eq_refl eq_refl), ?(mod64_of_range ND _ _ npr_rng_ND eq_refl eq_refl), ?(mod64_of_range mc _ _ npr_rng_mc eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - npr_rng_CA npr_rng_ND npr_rng_mc npr_ka1 npr_kr3 HC; lia).
  all: first [lia].
Qed.


Definition npr_mem_pnpr (m : word -> option byte) (regs : bvmap 5 word) (CA ND mc : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa 278424))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))))).

#[using="Type"] Theorem npr_pnpr : forall regs m rom CA ND mc, npr_pre regs m CA ND mc ->
  scs_denot SEGS m (Ez regs (VALS_npr CA ND mc)) (snd (fst AXF_npr.RES_pnpr)) ->
  exists R, msteps SEGS (mkst regs (wa 0x43f94) m rom) (mkst R (wa 0x44474) (npr_mem_pnpr m regs CA ND mc) rom) /\
    getr R 1 = wa 278424 /\ getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -32) /\ getr R 8 = wa (CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5)) /\ getr R 9 = wa (bv_unsigned (edenot (Ez regs (VALS_npr CA ND mc)) (EAluw ALU_SRL (EExt true 0 4 (EVar 34)) (ELit 1)))) /\ getr R 10 = wa 923480 /\ getr R 11 = wa (CA + 2560) /\ getr R 12 = wa (Z.shiftr (((ND + 31)) mod 2^64) 5) /\ getr R 13 = wa ((CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5)) + 16) /\ getr R 14 = wa (bv_unsigned (edenot (Ez regs (VALS_npr CA ND mc)) (EAluw ALU_SRL (EExt true 0 4 (EVar 34)) (ELit 1)))) /\ (forall k, In k [3; 4; 5; 6; 7; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom CA ND mc P Hsc. destruct (npr_setup regs m CA ND mc P) as [HR HK].
  set (E := Ez regs (VALS_npr CA ND mc)) in *. destruct P as [npr_R10 npr_R11 npr_R12 npr_R13 npr_HSTK npr_rng_CA npr_rng_ND npr_rng_mc npr_ka1 npr_kr3 npr_kw4].
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ND) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = mc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  assert (HC : 2 <= Z.shiftr ((ND + 31) mod 2^64) 5 <= 16) by (rewrite Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia; change (2^5) with 32; split; [apply Z.div_le_lower_bound; lia | apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia]).
  destruct (run_sound SEGS 40 [0x44474] AXF_npr.scr_pnpr 0x43f94 AXF_npr.sr_npr AXF_npr.kn_npr 35 _ _ _ E m rom regs AXF_npr.RES_pnpr_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_npr.RES_pnpr fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (npr_mem_pnpr m regs CA ND mc) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold npr_mem_pnpr. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End NPR.
