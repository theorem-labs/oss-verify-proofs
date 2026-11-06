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
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ AxTry.

Module AXF_sps.
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

Definition e_G2 := EVar 32.
Definition e_mem2 := EVar 33.
Definition e_hb := EVar 34.
Definition e_W2 := EVar 35.
Definition e_units := EVar 36.
Definition TAB := SA (EAlu ALU_AND (EAlu ALU_SRL e_W2 (ELit 5)) (ELit 126)) 98984.
Definition sr_sps := (sr_upd (sr_upd (sr_upd sr_id 10 (e_G2)) 11 (e_mem2)) 12 (e_hb)).
Definition kn_sps : list kentry :=
  [ KRange e_G2 1 (2^63-1);
    KAlign e_G2 8;
    KRange e_mem2 1 (2^63-1);
    KRange e_hb 0 255;
    KRange e_W2 0 (2^63-1);
    KRange e_units 1 8191;
    KWord (SA e_G2 32) 8 e_W2;
    KWord TAB 2 e_units ].
Definition scr_sps : scripts := SCR [] [] [].
Definition ss_sps := SS 0x5457c sr_sps [] kn_sps 37.
Definition RUN_sps := sym_exec SEGS 100 true [0x545c4] scr_sps ss_sps [].

Definition scr_psps : scripts := SCR [] [] [].
Definition RES_psps := Eval vm_compute in sym_exec SEGS 100 true [0x545c4] scr_psps ss_sps [].
Lemma RES_psps_ok : sym_exec SEGS 100 true [0x545c4] scr_psps (SS 0x5457c sr_sps [] kn_sps 37) [] = RES_psps.
Proof. vm_compute. reflexivity. Qed.
End AXF_sps.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section SPS.
Context {fx : FPState}.

Definition VALS_sps (G2 mem2 hb W2 units : Z) : list Z := [G2; mem2; hb; W2; units].

Record sps_pre (regs : bvmap 5 word) (m : word -> option byte) (G2 mem2 hb W2 units : Z) : Prop := {
  sps_R10 : getr regs 10 = wa G2 ;
  sps_R11 : getr regs 11 = wa mem2 ;
  sps_R12 : getr regs 12 = wa hb ;
  sps_rng_G2 : 1 <= G2 <= 2^63-1 ;
  sps_rng_mem2 : 1 <= mem2 <= 2^63-1 ;
  sps_rng_hb : 0 <= hb <= 255 ;
  sps_rng_W2 : 0 <= W2 <= 2^63-1 ;
  sps_rng_units : 1 <= units <= 8191 ;
  sps_ka1 : G2 mod 8 = 0 ;
  sps_kw6 : rdn SEGS m (wa (G2 + 32)) 8 = Some (word_to_le_bytes 8 (wa W2)) ;
  sps_kw7 : rdn SEGS m (wa (Z.land ((Z.shiftr W2 5) mod 2^64) 126 + 98984)) 2 = Some (word_to_le_bytes 2 (wa units))
}.


#[using="Type"] Lemma sps_setup : forall regs m G2 mem2 hb W2 units, sps_pre regs m G2 mem2 hb W2 units ->
  regs_ok (Ez regs (VALS_sps G2 mem2 hb W2 units)) AXF_sps.sr_sps regs /\ know_ok SEGS (Ez regs (VALS_sps G2 mem2 hb W2 units)) m AXF_sps.kn_sps.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G2 mem2 hb W2 units P. destruct P as [sps_R10 sps_R11 sps_R12 sps_rng_G2 sps_rng_mem2 sps_rng_hb sps_rng_W2 sps_rng_units sps_ka1 sps_kw6 sps_kw7].
  set (E := Ez regs (VALS_sps G2 mem2 hb W2 units)).
  assert (Z32 : bv_unsigned (ev E 32) = G2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = mem2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = hb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = W2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = units) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_sps.sr_sps.
    apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|]|].
    - rewrite sps_R10. reflexivity.
    - rewrite sps_R11. reflexivity.
    - rewrite sps_R12. reflexivity. }
  unfold know_ok, AXF_sps.kn_sps.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_sps.e_G2 AXF_sps.e_mem2 AXF_sps.e_hb AXF_sps.e_W2 AXF_sps.e_units AXF_sps.TAB a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range G2 _ _ sps_rng_G2 eq_refl eq_refl), ?(mod64_of_range mem2 _ _ sps_rng_mem2 eq_refl eq_refl), ?(mod64_of_range hb _ _ sps_rng_hb eq_refl eq_refl), ?(mod64_of_range W2 _ _ sps_rng_W2 eq_refl eq_refl), ?(mod64_of_range units _ _ sps_rng_units eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try (pose proof (land126_bound (Z.shiftr W2 5 mod 2^64)); lia).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - sps_rng_G2 sps_rng_mem2 sps_rng_hb sps_rng_W2 sps_rng_units sps_ka1; lia).
  all: first [lia].
Qed.


Definition sps_mem_psps (m : word -> option byte) (regs : bvmap 5 word) (G2 mem2 hb W2 units : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem sps_psps : forall regs m rom G2 mem2 hb W2 units, sps_pre regs m G2 mem2 hb W2 units ->
  scs_denot SEGS m (Ez regs (VALS_sps G2 mem2 hb W2 units)) (snd (fst AXF_sps.RES_psps)) ->
  exists R, msteps SEGS (mkst regs (wa 0x5457c) m rom) (mkst R (wa 0x545c4) (sps_mem_psps m regs G2 mem2 hb W2 units) rom) /\
    getr R 5 = wa (((16 * units) * (Z.land hb 31 + 2)) + 16) /\ getr R 10 = wa G2 /\ getr R 11 = wa mem2 /\ getr R 12 = wa hb /\ getr R 13 = wa W2 /\ getr R 14 = wa (Z.land hb 31 + 1) /\ getr R 15 = wa (16 * units) /\ getr R 16 = wa ((((16 * Z.land hb 31) + 48) * units) + 15) /\ getr R 17 = wa 4096 /\ (forall k, In k [1; 2; 3; 4; 6; 7; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G2 mem2 hb W2 units P Hsc. destruct (sps_setup regs m G2 mem2 hb W2 units P) as [HR HK].
  set (E := Ez regs (VALS_sps G2 mem2 hb W2 units)) in *. destruct P as [sps_R10 sps_R11 sps_R12 sps_rng_G2 sps_rng_mem2 sps_rng_hb sps_rng_W2 sps_rng_units sps_ka1 sps_kw6 sps_kw7].
  assert (Z32 : bv_unsigned (ev E 32) = G2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = mem2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = hb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = W2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = units) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x545c4] AXF_sps.scr_psps 0x5457c AXF_sps.sr_sps AXF_sps.kn_sps 37 _ _ _ E m rom regs AXF_sps.RES_psps_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_sps.RES_psps fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (sps_mem_psps m regs G2 mem2 hb W2 units) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold sps_mem_psps. repeat (apply (f_equal3 wbytes)); try reflexivity.
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

End SPS.
