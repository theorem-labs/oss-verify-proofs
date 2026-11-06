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

Module AXF_mmw.
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
Definition ss_mmw := SS 0x53328 sr_mmw [] kn_mmw 37.
Definition RUN_mmw := sym_exec SEGS 100 true [0x533ec] scr_mmw ss_mmw [].

Definition scr_pnf : scripts := SCR [false] [] [].
Definition RES_pnf := Eval vm_compute in sym_exec SEGS 100 true [0x533ec] scr_pnf ss_mmw [].
Lemma RES_pnf_ok : sym_exec SEGS 100 true [0x533ec] scr_pnf (SS 0x53328 sr_mmw [] kn_mmw 37) [] = RES_pnf.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pfx : scripts := SCR [true] [] [].
Definition RES_pfx := Eval vm_compute in sym_exec SEGS 100 true [0x533ec] scr_pfx ss_mmw [].
Lemma RES_pfx_ok : sym_exec SEGS 100 true [0x533ec] scr_pfx (SS 0x53328 sr_mmw [] kn_mmw 37) [] = RES_pfx.
Proof. vm_compute. reflexivity. Qed.
End AXF_mmw.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

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
  exists R, msteps SEGS (mkst regs (wa 0x53328) m rom) (mkst R (wa 0x533ec) (mmw_mem_pnf m regs sp0 ad len prot flags) rom) /\
    getr R 2 = wa (sp0 + -64) /\ getr R 5 = wa 18446744073709551604 /\ getr R 10 = wa ad /\ getr R 11 = wa len /\ getr R 12 = wa prot /\ getr R 13 = wa flags /\ getr R 14 = wa 18446744073709551615 /\ getr R 15 = wa 0 /\ getr R 16 = wa ad /\ getr R 17 = wa 222 /\ (forall k, In k [1; 3; 4; 6; 7; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sp0 ad len prot flags P Hsc. destruct (mmw_setup regs m sp0 ad len prot flags P) as [HR HK].
  set (E := Ez regs (VALS_mmw sp0 ad len prot flags)) in *. destruct P as [mmw_R2 mmw_R10 mmw_R11 mmw_R12 mmw_R13 mmw_R14 mmw_R15 mmw_HSTK mmw_rng_sp0 mmw_rng_ad mmw_rng_len mmw_rng_prot mmw_rng_flags mmw_ka1].
  assert (Z32 : bv_unsigned (ev E 32) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ad) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = len) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = prot) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = flags) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x533ec] AXF_mmw.scr_pnf 0x53328 AXF_mmw.sr_mmw AXF_mmw.kn_mmw 37 _ _ _ E m rom regs AXF_mmw.RES_pnf_ok HR HK Hsc) as (R & HR' & _ & Hms).
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
  exists R, msteps SEGS (mkst regs (wa 0x53328) m rom) (mkst R (wa 0x533ec) (mmw_mem_pfx m regs sp0 ad len prot flags) rom) /\
    getr R 1 = wa 340936 /\ getr R 2 = wa (sp0 + -64) /\ getr R 5 = wa 18446744073709551615 /\ getr R 8 = wa flags /\ getr R 9 = wa ad /\ getr R 10 = wa ad /\ getr R 11 = wa len /\ getr R 12 = wa prot /\ getr R 13 = wa flags /\ getr R 14 = wa 18446744073709551615 /\ getr R 15 = wa 0 /\ getr R 16 = wa ad /\ getr R 17 = wa 222 /\ getr R 18 = wa prot /\ getr R 19 = wa 0 /\ getr R 20 = wa 18446744073709551615 /\ getr R 21 = wa len /\ (forall k, In k [3; 4; 6; 7; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sp0 ad len prot flags P Hsc. destruct (mmw_setup regs m sp0 ad len prot flags P) as [HR HK].
  set (E := Ez regs (VALS_mmw sp0 ad len prot flags)) in *. destruct P as [mmw_R2 mmw_R10 mmw_R11 mmw_R12 mmw_R13 mmw_R14 mmw_R15 mmw_HSTK mmw_rng_sp0 mmw_rng_ad mmw_rng_len mmw_rng_prot mmw_rng_flags mmw_ka1].
  assert (Z32 : bv_unsigned (ev E 32) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ad) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = len) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = prot) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = flags) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x533ec] AXF_mmw.scr_pfx 0x53328 AXF_mmw.sr_mmw AXF_mmw.kn_mmw 37 _ _ _ E m rom regs AXF_mmw.RES_pfx_ok HR HK Hsc) as (R & HR' & _ & Hms).
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
