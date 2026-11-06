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

Module AXF_nm2.
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

Definition e_u := EVar 32.
Definition e_i1 := EVar 33.
Definition e_t1 := EVar 34.
Definition sr_nm2 := (sr_upd (sr_upd (sr_upd sr_id 10 (EAlu ALU_ADD (ELit 121) (EMd M_MUL (ELit (-1)) e_i1))) 14 (e_u)) 25 (ELit 98984)).
Definition kn_nm2 : list kentry :=
  [ KRange e_u 10 127;
    KRange e_i1 0 47;
    KRange e_t1 0 65535;
    KWord (SA (EMd M_MUL (ELit 2) e_i1) 98984) 2 e_t1 ].
Definition scr_nm2 : scripts := SCR [true] [] [].
Definition ss_nm2 := SS 0x54434 sr_nm2 [] kn_nm2 35.
Definition RUN_nm2 := sym_exec SEGS 100 true [0x54464] scr_nm2 ss_nm2 [].

Definition scr_pnm2l : scripts := SCR [true] [] [].
Definition RES_pnm2l := Eval vm_compute in sym_exec SEGS 100 true [0x54464] scr_pnm2l ss_nm2 [].
Lemma RES_pnm2l_ok : sym_exec SEGS 100 true [0x54464] scr_pnm2l (SS 0x54434 sr_nm2 [] kn_nm2 35) [] = RES_pnm2l.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pnm2g : scripts := SCR [false] [] [].
Definition RES_pnm2g := Eval vm_compute in sym_exec SEGS 100 true [0x54464] scr_pnm2g ss_nm2 [].
Lemma RES_pnm2g_ok : sym_exec SEGS 100 true [0x54464] scr_pnm2g (SS 0x54434 sr_nm2 [] kn_nm2 35) [] = RES_pnm2g.
Proof. vm_compute. reflexivity. Qed.
End AXF_nm2.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section NM2.
Context {fx : FPState}.

Definition VALS_nm2 (u i1 t1 : Z) : list Z := [u; i1; t1].

Record nm2_pre (regs : bvmap 5 word) (m : word -> option byte) (u i1 t1 : Z) : Prop := {
  nm2_R10 : getr regs 10 = wa (121 + (-1 * i1)) ;
  nm2_R14 : getr regs 14 = wa u ;
  nm2_R25 : getr regs 25 = wa 98984 ;
  nm2_rng_u : 10 <= u <= 127 ;
  nm2_rng_i1 : 0 <= i1 <= 47 ;
  nm2_rng_t1 : 0 <= t1 <= 65535 ;
  nm2_kw3 : rdn SEGS m (wa (2 * i1 + 98984)) 2 = Some (word_to_le_bytes 2 (wa t1))
}.


#[using="Type"] Lemma nm2_setup : forall regs m u i1 t1, nm2_pre regs m u i1 t1 ->
  regs_ok (Ez regs (VALS_nm2 u i1 t1)) AXF_nm2.sr_nm2 regs /\ know_ok SEGS (Ez regs (VALS_nm2 u i1 t1)) m AXF_nm2.kn_nm2.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m u i1 t1 P. destruct P as [nm2_R10 nm2_R14 nm2_R25 nm2_rng_u nm2_rng_i1 nm2_rng_t1 nm2_kw3].
  set (E := Ez regs (VALS_nm2 u i1 t1)).
  assert (Z32 : bv_unsigned (ev E 32) = u) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = i1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = t1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_nm2.sr_nm2.
    apply (regs_ok_pin E _ regs 25); [apply (regs_ok_pin E _ regs 14); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|]|].
    - rewrite nm2_R10, zeval_sound. cbn [zeval edenot AXF_nm2.e_u AXF_nm2.e_i1 AXF_nm2.e_t1]. rewrite ?Z32, ?Z33, ?Z34. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite nm2_R14. reflexivity.
    - rewrite nm2_R25. reflexivity. }
  unfold know_ok, AXF_nm2.kn_nm2.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_nm2.e_u AXF_nm2.e_i1 AXF_nm2.e_t1 a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range u _ _ nm2_rng_u eq_refl eq_refl), ?(mod64_of_range i1 _ _ nm2_rng_i1 eq_refl eq_refl), ?(mod64_of_range t1 _ _ nm2_rng_t1 eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - nm2_rng_u nm2_rng_i1 nm2_rng_t1; lia).
  all: first [lia].
Qed.


Definition nm2_mem_pnm2l (m : word -> option byte) (regs : bvmap 5 word) (u i1 t1 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem nm2_pnm2l : forall regs m rom u i1 t1, nm2_pre regs m u i1 t1 ->
  scs_denot SEGS m (Ez regs (VALS_nm2 u i1 t1)) (snd (fst AXF_nm2.RES_pnm2l)) ->
  exists R, msteps SEGS (mkst regs (wa 0x54434) m rom) (mkst R (wa 0x54464) (nm2_mem_pnm2l m regs u i1 t1) rom) /\
    getr R 10 = wa (121 + (-1 * i1)) /\ getr R 12 = wa (i1 + -1) /\ getr R 14 = wa u /\ getr R 25 = wa 98984 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 13; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom u i1 t1 P Hsc. destruct (nm2_setup regs m u i1 t1 P) as [HR HK].
  set (E := Ez regs (VALS_nm2 u i1 t1)) in *. destruct P as [nm2_R10 nm2_R14 nm2_R25 nm2_rng_u nm2_rng_i1 nm2_rng_t1 nm2_kw3].
  assert (Z32 : bv_unsigned (ev E 32) = u) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = i1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = t1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x54464] AXF_nm2.scr_pnm2l 0x54434 AXF_nm2.sr_nm2 AXF_nm2.kn_nm2 35 _ _ _ E m rom regs AXF_nm2.RES_pnm2l_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_nm2.RES_pnm2l fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (nm2_mem_pnm2l m regs u i1 t1) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold nm2_mem_pnm2l. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition nm2_mem_pnm2g (m : word -> option byte) (regs : bvmap 5 word) (u i1 t1 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem nm2_pnm2g : forall regs m rom u i1 t1, nm2_pre regs m u i1 t1 ->
  scs_denot SEGS m (Ez regs (VALS_nm2 u i1 t1)) (snd (fst AXF_nm2.RES_pnm2g)) ->
  exists R, msteps SEGS (mkst regs (wa 0x54434) m rom) (mkst R (wa 0x54464) (nm2_mem_pnm2g m regs u i1 t1) rom) /\
    getr R 10 = wa (121 + (-1 * i1)) /\ getr R 12 = wa (i1 + 1) /\ getr R 14 = wa u /\ getr R 25 = wa 98984 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 13; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom u i1 t1 P Hsc. destruct (nm2_setup regs m u i1 t1 P) as [HR HK].
  set (E := Ez regs (VALS_nm2 u i1 t1)) in *. destruct P as [nm2_R10 nm2_R14 nm2_R25 nm2_rng_u nm2_rng_i1 nm2_rng_t1 nm2_kw3].
  assert (Z32 : bv_unsigned (ev E 32) = u) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = i1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = t1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x54464] AXF_nm2.scr_pnm2g 0x54434 AXF_nm2.sr_nm2 AXF_nm2.kn_nm2 35 _ _ _ E m rom regs AXF_nm2.RES_pnm2g_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_nm2.RES_pnm2g fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (nm2_mem_pnm2g m regs u i1 t1) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold nm2_mem_pnm2g. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End NM2.
