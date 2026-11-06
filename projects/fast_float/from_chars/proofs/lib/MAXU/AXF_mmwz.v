(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Module AXF_mmw.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_sp0 := EVar 32.
Definition e_ad := EVar 33.
Definition e_len := EVar 34.
Definition e_prot := EVar 35.
Definition e_flags := EVar 36.
Definition STK := SA e_sp0 (-1024).
Definition sr_mmw := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 2 (e_sp0)) 10 (e_ad)) 11 (e_len)) 12 (e_prot)) 13 (e_flags)) 14 (ELit 18446744073709551615)) 15 (ELit 0)).
Definition kn_mmw : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWr STK (ELit 1024);
    KRange e_ad 0 (2^63-1);
    KRange e_len 0 (2^40);
    KRange e_prot 0 7;
    KRange e_flags 0 255 ].
Definition scr_mmw : scripts := SCR [false] [] [].
Definition ss_mmw := SS 0x550e0 sr_mmw [] kn_mmw 37.
Definition RUN_mmw := sym_exec SEGS 100 true [0x551a4] scr_mmw ss_mmw [].

Definition scr_pnf : scripts := SCR [false] [] [].
Definition RES_pnf := Eval vm_compute in sym_exec SEGS 100 true [0x551a4] scr_pnf ss_mmw [].
Lemma RES_pnf_ok : sym_exec SEGS 100 true [0x551a4] scr_pnf (SS 0x550e0 sr_mmw [] kn_mmw 37) [] = RES_pnf.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pfx : scripts := SCR [true] [] [].
Definition RES_pfx := Eval vm_compute in sym_exec SEGS 100 true [0x551a4] scr_pfx ss_mmw [].
Lemma RES_pfx_ok : sym_exec SEGS 100 true [0x551a4] scr_pfx (SS 0x550e0 sr_mmw [] kn_mmw 37) [] = RES_pfx.
Proof. vm_compute. reflexivity. Qed.
End AXF_mmw.

Import ListNotations AX2 AX2S.

Module AXF_mic2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_auxv := EVar 32.
Definition e_off := EVar 33.
Definition sr_mic2 := (sr_upd (sr_upd sr_id 8 (ELit 621600)) 9 (e_off)).
Definition kn_mic2 : list kentry :=
  [ KRange e_auxv 8 (2^47);
    KRange e_off 0 (2^47);
    KWord (SA (ELit 0) 621608) 8 e_auxv ].
Definition scr_mic2 : scripts := SCR [] [] [].
Definition ss_mic2 := SS 0x53adc sr_mic2 [] kn_mic2 34.
Definition RUN_mic2 := sym_exec SEGS 100 true [0x53ae4] scr_mic2 ss_mic2 [].

Definition scr_pmic : scripts := SCR [] [] [].
Definition RES_pmic := Eval vm_compute in sym_exec SEGS 100 true [0x53ae4] scr_pmic ss_mic2 [].
Lemma RES_pmic_ok : sym_exec SEGS 100 true [0x53ae4] scr_pmic (SS 0x53adc sr_mic2 [] kn_mic2 34) [] = RES_pmic.
Proof. vm_compute. reflexivity. Qed.
End AXF_mic2.

Module AXF_mic2z.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section MIC2.
Context {fx : FPState}.

Definition VALS_mic2 (auxv off : Z) : list Z := [auxv; off].

Record mic2_pre (regs : bvmap 5 word) (m : word -> option byte) (auxv off : Z) : Prop := {
  mic2_R8 : getr regs 8 = wa 621600 ;
  mic2_R9 : getr regs 9 = wa off ;
  mic2_rng_auxv : 8 <= auxv <= 2^47 ;
  mic2_rng_off : 0 <= off <= 2^47 ;
  mic2_kw2 : rdn SEGS m (wa (0 + 621608)) 8 = Some (word_to_le_bytes 8 (wa auxv))
}.


#[using="Type"] Lemma mic2_setup : forall regs m auxv off, mic2_pre regs m auxv off ->
  regs_ok (Ez regs (VALS_mic2 auxv off)) AXF_mic2.sr_mic2 regs /\ know_ok SEGS (Ez regs (VALS_mic2 auxv off)) m AXF_mic2.kn_mic2.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m auxv off P. destruct P as [mic2_R8 mic2_R9 mic2_rng_auxv mic2_rng_off mic2_kw2].
  set (E := Ez regs (VALS_mic2 auxv off)).
  assert (Z32 : bv_unsigned (ev E 32) = auxv) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = off) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mic2.sr_mic2.
    apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|].
    - rewrite mic2_R8. reflexivity.
    - rewrite mic2_R9. reflexivity. }
  unfold know_ok, AXF_mic2.kn_mic2.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mic2.e_auxv AXF_mic2.e_off a_base a_off].
  all: rewrite ?Z32, ?Z33.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range auxv _ _ mic2_rng_auxv eq_refl eq_refl), ?(mod64_of_range off _ _ mic2_rng_off eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - mic2_rng_auxv mic2_rng_off; lia).
  all: first [lia].
Qed.


Definition mic2_mem_pmic (m : word -> option byte) (regs : bvmap 5 word) (auxv off : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mic2_pmic : forall regs m rom auxv off, mic2_pre regs m auxv off ->
  scs_denot SEGS m (Ez regs (VALS_mic2 auxv off)) (snd (fst AXF_mic2.RES_pmic)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53adc) m rom) (mkst R (wa 0x53ae4) (mic2_mem_pmic m regs auxv off) rom) /\
    getr R 8 = wa 621600 /\ getr R 9 = wa (off + 16) /\ getr R 10 = wa auxv /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom auxv off P Hsc. destruct (mic2_setup regs m auxv off P) as [HR HK].
  set (E := Ez regs (VALS_mic2 auxv off)) in *. destruct P as [mic2_R8 mic2_R9 mic2_rng_auxv mic2_rng_off mic2_kw2].
  assert (Z32 : bv_unsigned (ev E 32) = auxv) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = off) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53ae4] AXF_mic2.scr_pmic 0x53adc AXF_mic2.sr_mic2 AXF_mic2.kn_mic2 34 _ _ _ E m rom regs AXF_mic2.RES_pmic_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mic2.RES_pmic fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mic2_mem_pmic m regs auxv off) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mic2_mem_pmic. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MIC2.
End AXF_mic2z.

Module AXF_mil2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_auxv := EVar 32.
Definition e_off := EVar 33.
Definition e_typ := EVar 34.
Definition sr_mil2 := (sr_upd (sr_upd (sr_upd sr_id 9 (e_off)) 10 (e_auxv)) 20 (ELit 25)).
Definition kn_mil2 : list kentry :=
  [ KRange e_auxv 8 (2^47);
    KAlign e_auxv 8;
    KRange e_off 0 (2^47);
    KAlign e_off 16;
    KRange e_typ 0 (2^64-1);
    KWord (SA (EAlu ALU_ADD e_auxv e_off) 0) 8 e_typ ].
Definition scr_mil2 : scripts := SCR [true] [] [].
Definition ss_mil2 := SS 0x53ae4 sr_mil2 [] kn_mil2 35.
Definition RUN_mil2 := sym_exec SEGS 100 true [0x53ac8; 0x53ae4; 0x53af4] scr_mil2 ss_mil2 [].

Definition scr_pmlr : scripts := SCR [true] [] [].
Definition RES_pmlr := Eval vm_compute in sym_exec SEGS 100 true [0x53ac8; 0x53ae4; 0x53af4] scr_pmlr ss_mil2 [].
Lemma RES_pmlr_ok : sym_exec SEGS 100 true [0x53ac8; 0x53ae4; 0x53af4] scr_pmlr (SS 0x53ae4 sr_mil2 [] kn_mil2 35) [] = RES_pmlr.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmlc : scripts := SCR [false; true] [] [].
Definition RES_pmlc := Eval vm_compute in sym_exec SEGS 100 true [0x53ac8; 0x53ae4; 0x53af4] scr_pmlc ss_mil2 [].
Lemma RES_pmlc_ok : sym_exec SEGS 100 true [0x53ac8; 0x53ae4; 0x53af4] scr_pmlc (SS 0x53ae4 sr_mil2 [] kn_mil2 35) [] = RES_pmlc.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmlx : scripts := SCR [false; false] [] [].
Definition RES_pmlx := Eval vm_compute in sym_exec SEGS 100 true [0x53ac8; 0x53ae4; 0x53af4] scr_pmlx ss_mil2 [].
Lemma RES_pmlx_ok : sym_exec SEGS 100 true [0x53ac8; 0x53ae4; 0x53af4] scr_pmlx (SS 0x53ae4 sr_mil2 [] kn_mil2 35) [] = RES_pmlx.
Proof. vm_compute. reflexivity. Qed.
End AXF_mil2.

Module AXF_mil2z.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section MIL2.
Context {fx : FPState}.

Definition VALS_mil2 (auxv off typ : Z) : list Z := [auxv; off; typ].

Record mil2_pre (regs : bvmap 5 word) (m : word -> option byte) (auxv off typ : Z) : Prop := {
  mil2_R9 : getr regs 9 = wa off ;
  mil2_R10 : getr regs 10 = wa auxv ;
  mil2_R20 : getr regs 20 = wa 25 ;
  mil2_rng_auxv : 8 <= auxv <= 2^47 ;
  mil2_rng_off : 0 <= off <= 2^47 ;
  mil2_rng_typ : 0 <= typ <= 2^64-1 ;
  mil2_ka1 : auxv mod 8 = 0 ;
  mil2_ka3 : off mod 16 = 0 ;
  mil2_kw5 : rdn SEGS m (wa (auxv + off + 0)) 8 = Some (word_to_le_bytes 8 (wa typ))
}.


#[using="Type"] Lemma mil2_setup : forall regs m auxv off typ, mil2_pre regs m auxv off typ ->
  regs_ok (Ez regs (VALS_mil2 auxv off typ)) AXF_mil2.sr_mil2 regs /\ know_ok SEGS (Ez regs (VALS_mil2 auxv off typ)) m AXF_mil2.kn_mil2.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m auxv off typ P. destruct P as [mil2_R9 mil2_R10 mil2_R20 mil2_rng_auxv mil2_rng_off mil2_rng_typ mil2_ka1 mil2_ka3 mil2_kw5].
  set (E := Ez regs (VALS_mil2 auxv off typ)).
  assert (Z32 : bv_unsigned (ev E 32) = auxv) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = off) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = typ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mil2.sr_mil2.
    apply (regs_ok_pin E _ regs 20); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply regs_ok_id|]|]|].
    - rewrite mil2_R9. reflexivity.
    - rewrite mil2_R10. reflexivity.
    - rewrite mil2_R20. reflexivity. }
  unfold know_ok, AXF_mil2.kn_mil2.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mil2.e_auxv AXF_mil2.e_off AXF_mil2.e_typ a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range auxv _ _ mil2_rng_auxv eq_refl eq_refl), ?(mod64_of_range off _ _ mil2_rng_off eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - mil2_rng_auxv mil2_rng_off mil2_rng_typ mil2_ka1 mil2_ka3; lia).
  all: first [lia].
Qed.


Definition mil2_mem_pmlr (m : word -> option byte) (regs : bvmap 5 word) (auxv off typ : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mil2_pmlr : forall regs m rom auxv off typ, mil2_pre regs m auxv off typ ->
  scs_denot SEGS m (Ez regs (VALS_mil2 auxv off typ)) (snd (fst AXF_mil2.RES_pmlr)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53ae4) m rom) (mkst R (wa 0x53ac8) (mil2_mem_pmlr m regs auxv off typ) rom) /\
    getr R 9 = wa off /\ getr R 10 = wa auxv /\ getr R 11 = wa typ /\ getr R 12 = wa (auxv + off) /\ getr R 20 = wa 25 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 13; 14; 15; 16; 17; 18; 19; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom auxv off typ P Hsc. destruct (mil2_setup regs m auxv off typ P) as [HR HK].
  set (E := Ez regs (VALS_mil2 auxv off typ)) in *. destruct P as [mil2_R9 mil2_R10 mil2_R20 mil2_rng_auxv mil2_rng_off mil2_rng_typ mil2_ka1 mil2_ka3 mil2_kw5].
  assert (Z32 : bv_unsigned (ev E 32) = auxv) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = off) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = typ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53ac8; 0x53ae4; 0x53af4] AXF_mil2.scr_pmlr 0x53ae4 AXF_mil2.sr_mil2 AXF_mil2.kn_mil2 35 _ _ _ E m rom regs AXF_mil2.RES_pmlr_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mil2.RES_pmlr fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mil2_mem_pmlr m regs auxv off typ) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mil2_mem_pmlr. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition mil2_mem_pmlc (m : word -> option byte) (regs : bvmap 5 word) (auxv off typ : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mil2_pmlc : forall regs m rom auxv off typ, mil2_pre regs m auxv off typ ->
  scs_denot SEGS m (Ez regs (VALS_mil2 auxv off typ)) (snd (fst AXF_mil2.RES_pmlc)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53ae4) m rom) (mkst R (wa 0x53ae4) (mil2_mem_pmlc m regs auxv off typ) rom) /\
    getr R 9 = wa (off + 16) /\ getr R 10 = wa auxv /\ getr R 11 = wa typ /\ getr R 12 = wa (auxv + off) /\ getr R 20 = wa 25 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 13; 14; 15; 16; 17; 18; 19; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom auxv off typ P Hsc. destruct (mil2_setup regs m auxv off typ P) as [HR HK].
  set (E := Ez regs (VALS_mil2 auxv off typ)) in *. destruct P as [mil2_R9 mil2_R10 mil2_R20 mil2_rng_auxv mil2_rng_off mil2_rng_typ mil2_ka1 mil2_ka3 mil2_kw5].
  assert (Z32 : bv_unsigned (ev E 32) = auxv) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = off) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = typ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53ac8; 0x53ae4; 0x53af4] AXF_mil2.scr_pmlc 0x53ae4 AXF_mil2.sr_mil2 AXF_mil2.kn_mil2 35 _ _ _ E m rom regs AXF_mil2.RES_pmlc_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mil2.RES_pmlc fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mil2_mem_pmlc m regs auxv off typ) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mil2_mem_pmlc. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition mil2_mem_pmlx (m : word -> option byte) (regs : bvmap 5 word) (auxv off typ : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mil2_pmlx : forall regs m rom auxv off typ, mil2_pre regs m auxv off typ ->
  scs_denot SEGS m (Ez regs (VALS_mil2 auxv off typ)) (snd (fst AXF_mil2.RES_pmlx)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53ae4) m rom) (mkst R (wa 0x53af4) (mil2_mem_pmlx m regs auxv off typ) rom) /\
    getr R 9 = wa off /\ getr R 10 = wa auxv /\ getr R 11 = wa typ /\ getr R 12 = wa (auxv + off) /\ getr R 20 = wa 25 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 13; 14; 15; 16; 17; 18; 19; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom auxv off typ P Hsc. destruct (mil2_setup regs m auxv off typ P) as [HR HK].
  set (E := Ez regs (VALS_mil2 auxv off typ)) in *. destruct P as [mil2_R9 mil2_R10 mil2_R20 mil2_rng_auxv mil2_rng_off mil2_rng_typ mil2_ka1 mil2_ka3 mil2_kw5].
  assert (Z32 : bv_unsigned (ev E 32) = auxv) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = off) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = typ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53ac8; 0x53ae4; 0x53af4] AXF_mil2.scr_pmlx 0x53ae4 AXF_mil2.sr_mil2 AXF_mil2.kn_mil2 35 _ _ _ E m rom regs AXF_mil2.RES_pmlx_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mil2.RES_pmlx fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mil2_mem_pmlx m regs auxv off typ) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mil2_mem_pmlx. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MIL2.
End AXF_mil2z.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section MMW.
Context {fx : FPState}.

Definition VALS_mmw (sp0 ad len prot flags : Z) : list Z := [sp0; ad; len; prot; flags].

Record mmw_pre (regs : bvmap 5 word) (m : word -> option byte) (sp0 ad len prot flags : Z) : Prop := {
  mmw_R2 : getr regs 2 = wa sp0 ;
  mmw_R10 : getr regs 10 = wa ad ;
  mmw_R11 : getr regs 11 = wa len ;
  mmw_R12 : getr regs 12 = wa prot ;
  mmw_R13 : getr regs 13 = wa flags ;
  mmw_R14 : getr regs 14 = wa 18446744073709551615 ;
  mmw_R15 : getr regs 15 = wa 0 ;
  mmw_HSTK : stk_ok SEGS m (wa sp0) 1024 ;
  mmw_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  mmw_rng_ad : 0 <= ad <= 2^63-1 ;
  mmw_rng_len : 0 <= len <= 2^40 ;
  mmw_rng_prot : 0 <= prot <= 7 ;
  mmw_rng_flags : 0 <= flags <= 255 ;
  mmw_ka1 : sp0 mod 16 = 0
}.


#[using="Type"] Lemma mmw_setup : forall regs m sp0 ad len prot flags, mmw_pre regs m sp0 ad len prot flags ->
  regs_ok (Ez regs (VALS_mmw sp0 ad len prot flags)) AXF_mmw.sr_mmw regs /\ know_ok SEGS (Ez regs (VALS_mmw sp0 ad len prot flags)) m AXF_mmw.kn_mmw.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sp0 ad len prot flags P. destruct P as [mmw_R2 mmw_R10 mmw_R11 mmw_R12 mmw_R13 mmw_R14 mmw_R15 mmw_HSTK mmw_rng_sp0 mmw_rng_ad mmw_rng_len mmw_rng_prot mmw_rng_flags mmw_ka1].
  set (E := Ez regs (VALS_mmw sp0 ad len prot flags)).
  assert (Z32 : bv_unsigned (ev E 32) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ad) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = len) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = prot) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = flags) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mmw.sr_mmw.
    apply (regs_ok_pin E _ regs 15); [apply (regs_ok_pin E _ regs 14); [apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|]|]|]|]|]|]|].
    - rewrite mmw_R2. reflexivity.
    - rewrite mmw_R10. reflexivity.
    - rewrite mmw_R11. reflexivity.
    - rewrite mmw_R12. reflexivity.
    - rewrite mmw_R13. reflexivity.
    - rewrite mmw_R14. reflexivity.
    - rewrite mmw_R15. reflexivity. }
  unfold know_ok, AXF_mmw.kn_mmw.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_mmw.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mmw.e_sp0 AXF_mmw.e_ad AXF_mmw.e_len AXF_mmw.e_prot AXF_mmw.e_flags AXF_mmw.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sp0 _ _ mmw_rng_sp0 eq_refl eq_refl), ?(mod64_of_range ad _ _ mmw_rng_ad eq_refl eq_refl), ?(mod64_of_range len _ _ mmw_rng_len eq_refl eq_refl), ?(mod64_of_range prot _ _ mmw_rng_prot eq_refl eq_refl), ?(mod64_of_range flags _ _ mmw_rng_flags eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - mmw_rng_sp0 mmw_rng_ad mmw_rng_len mmw_rng_prot mmw_rng_flags mmw_ka1; lia).
  all: first [lia].
Qed.


Definition mmw_mem_pnf (m : word -> option byte) (regs : bvmap 5 word) (sp0 ad len prot flags : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (sp0 + -8)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1))))))) (wa (sp0 + -16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))))) (wa (sp0 + -24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))))))) (wa (sp0 + -32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))))))) (wa (sp0 + -40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))))) (wa (sp0 + -48)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))))) (wa (sp0 + -56)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))))).

#[using="Type"] Theorem mmw_pnf : forall regs m rom sp0 ad len prot flags, mmw_pre regs m sp0 ad len prot flags ->
  scs_denot SEGS m (Ez regs (VALS_mmw sp0 ad len prot flags)) (snd (fst AXF_mmw.RES_pnf)) ->
  exists R, msteps SEGS (mkst regs (wa 0x550e0) m rom) (mkst R (wa 0x551a4) (mmw_mem_pnf m regs sp0 ad len prot flags) rom) /\
    getr R 2 = wa (sp0 + -64) /\ getr R 5 = wa 18446744073709551604 /\ getr R 10 = wa ad /\ getr R 11 = wa len /\ getr R 12 = wa prot /\ getr R 13 = wa flags /\ getr R 14 = wa 18446744073709551615 /\ getr R 15 = wa 0 /\ getr R 16 = wa ad /\ getr R 17 = wa 222 /\ (forall k, In k [1; 3; 4; 6; 7; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sp0 ad len prot flags P Hsc. destruct (mmw_setup regs m sp0 ad len prot flags P) as [HR HK].
  set (E := Ez regs (VALS_mmw sp0 ad len prot flags)) in *. destruct P as [mmw_R2 mmw_R10 mmw_R11 mmw_R12 mmw_R13 mmw_R14 mmw_R15 mmw_HSTK mmw_rng_sp0 mmw_rng_ad mmw_rng_len mmw_rng_prot mmw_rng_flags mmw_ka1].
  assert (Z32 : bv_unsigned (ev E 32) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ad) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = len) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = prot) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = flags) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x551a4] AXF_mmw.scr_pnf 0x550e0 AXF_mmw.sr_mmw AXF_mmw.kn_mmw 37 _ _ _ E m rom regs AXF_mmw.RES_pnf_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mmw.RES_pnf fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mmw_mem_pnf m regs sp0 ad len prot flags) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mmw_mem_pnf. repeat (apply (f_equal3 wbytes)); try reflexivity.
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


Definition mmw_mem_pfx (m : word -> option byte) (regs : bvmap 5 word) (sp0 ad len prot flags : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (sp0 + -8)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1))))))) (wa (sp0 + -16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))))) (wa (sp0 + -24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))))))) (wa (sp0 + -32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))))))) (wa (sp0 + -40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))))) (wa (sp0 + -48)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))))) (wa (sp0 + -56)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))))).

#[using="Type"] Theorem mmw_pfx : forall regs m rom sp0 ad len prot flags, mmw_pre regs m sp0 ad len prot flags ->
  scs_denot SEGS m (Ez regs (VALS_mmw sp0 ad len prot flags)) (snd (fst AXF_mmw.RES_pfx)) ->
  exists R, msteps SEGS (mkst regs (wa 0x550e0) m rom) (mkst R (wa 0x551a4) (mmw_mem_pfx m regs sp0 ad len prot flags) rom) /\
    getr R 1 = wa 348544 /\ getr R 2 = wa (sp0 + -64) /\ getr R 5 = wa 18446744073709551615 /\ getr R 8 = wa flags /\ getr R 9 = wa ad /\ getr R 10 = wa ad /\ getr R 11 = wa len /\ getr R 12 = wa prot /\ getr R 13 = wa flags /\ getr R 14 = wa 18446744073709551615 /\ getr R 15 = wa 0 /\ getr R 16 = wa ad /\ getr R 17 = wa 222 /\ getr R 18 = wa prot /\ getr R 19 = wa 0 /\ getr R 20 = wa 18446744073709551615 /\ getr R 21 = wa len /\ (forall k, In k [3; 4; 6; 7; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sp0 ad len prot flags P Hsc. destruct (mmw_setup regs m sp0 ad len prot flags P) as [HR HK].
  set (E := Ez regs (VALS_mmw sp0 ad len prot flags)) in *. destruct P as [mmw_R2 mmw_R10 mmw_R11 mmw_R12 mmw_R13 mmw_R14 mmw_R15 mmw_HSTK mmw_rng_sp0 mmw_rng_ad mmw_rng_len mmw_rng_prot mmw_rng_flags mmw_ka1].
  assert (Z32 : bv_unsigned (ev E 32) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ad) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = len) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = prot) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = flags) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x551a4] AXF_mmw.scr_pfx 0x550e0 AXF_mmw.sr_mmw AXF_mmw.kn_mmw 37 _ _ _ E m rom regs AXF_mmw.RES_pfx_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mmw.RES_pfx fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mmw_mem_pfx m regs sp0 ad len prot flags) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mmw_mem_pfx. repeat (apply (f_equal3 wbytes)); try reflexivity.
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

End MMW.
