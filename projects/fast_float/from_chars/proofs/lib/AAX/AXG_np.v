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
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require Import AxAsan AXG_put AXG_put2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_np0z.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_np0z.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_np0rz.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_np0rz.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_nprz.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_nprz.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_ng0z.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_ng0z.

Module AXF_ngl.
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

Definition e_FP := EVar 32.
Definition e_CP := EVar 33.
Definition e_EN := EVar 34.
Definition e_w := EVar 35.
Definition sr_ngl := (sr_upd (sr_upd (sr_upd sr_id 11 (e_EN)) 13 (e_CP)) 20 (e_FP)).
Definition kn_ngl : list kentry :=
  [ KRange e_FP 1 (2^47);
    KRange e_CP 1 (2^47);
    KRange e_EN 1 (2^47);
    KWord (SA e_FP 0) 4 e_w;
    KWr (SA e_CP 0) (ELit 4) ].
Definition scr_ngl : scripts := SCR [true] [] [].
Definition ss_ngl := SS 0x446ac sr_ngl [] kn_ngl 36.
Definition RUN_ngl := sym_exec SEGS 10 true [0x446ac; 0x446c0] scr_ngl ss_ngl [].

Definition scr_pnglc : scripts := SCR [true] [] [].
Definition RES_pnglc := Eval vm_compute in sym_exec SEGS 10 true [0x446ac; 0x446c0] scr_pnglc ss_ngl [].
Lemma RES_pnglc_ok : sym_exec SEGS 10 true [0x446ac; 0x446c0] scr_pnglc (SS 0x446ac sr_ngl [] kn_ngl 36) [] = RES_pnglc.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pnglx : scripts := SCR [false] [] [].
Definition RES_pnglx := Eval vm_compute in sym_exec SEGS 10 true [0x446ac; 0x446c0] scr_pnglx ss_ngl [].
Lemma RES_pnglx_ok : sym_exec SEGS 10 true [0x446ac; 0x446c0] scr_pnglx (SS 0x446ac sr_ngl [] kn_ngl 36) [] = RES_pnglx.
Proof. vm_compute. reflexivity. Qed.
End AXF_ngl.


Module AXF_nglz.
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

Section NGL.
Context {fx : FPState}.

Definition VALS_ngl (FP CP EN w : Z) : list Z := [FP; CP; EN; w].

Record ngl_pre (regs : bvmap 5 word) (m : word -> option byte) (FP CP EN w : Z) : Prop := {
  ngl_R11 : getr regs 11 = wa EN ;
  ngl_R13 : getr regs 13 = wa CP ;
  ngl_R20 : getr regs 20 = wa FP ;
  ngl_rng_FP : 1 <= FP <= 2^47 ;
  ngl_rng_CP : 1 <= CP <= 2^47 ;
  ngl_rng_EN : 1 <= EN <= 2^47 ;
  ngl_rng_w : 0 <= w <= 2^32-1 ;
  ngl_kw3 : rdn SEGS m (wa (FP + 0)) 4 = Some (word_to_le_bytes 4 (wa w)) ;
  ngl_kwr4 : forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (CP + 0 + d)) k = true
}.


#[using="Type"] Lemma ngl_setup : forall regs m FP CP EN w, ngl_pre regs m FP CP EN w ->
  regs_ok (Ez regs (VALS_ngl FP CP EN w)) AXF_ngl.sr_ngl regs /\ know_ok SEGS (Ez regs (VALS_ngl FP CP EN w)) m AXF_ngl.kn_ngl.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m FP CP EN w P. destruct P as [ngl_R11 ngl_R13 ngl_R20 ngl_rng_FP ngl_rng_CP ngl_rng_EN ngl_rng_w ngl_kw3 ngl_kwr4].
  set (E := Ez regs (VALS_ngl FP CP EN w)).
  assert (Z32 : bv_unsigned (ev E 32) = FP) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = CP) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = EN) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = w) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_ngl.sr_ngl.
    apply (regs_ok_pin E _ regs 20); [apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 11); [apply regs_ok_id|]|]|].
    - rewrite ngl_R11. reflexivity.
    - rewrite ngl_R13. reflexivity.
    - rewrite ngl_R20. reflexivity. }
  unfold know_ok, AXF_ngl.kn_ngl.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_ngl.e_FP AXF_ngl.e_CP AXF_ngl.e_EN AXF_ngl.e_w a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range FP _ _ ngl_rng_FP eq_refl eq_refl), ?(mod64_of_range CP _ _ ngl_rng_CP eq_refl eq_refl), ?(mod64_of_range EN _ _ ngl_rng_EN eq_refl eq_refl), ?(mod64_of_range w _ _ ngl_rng_w eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply ngl_kwr4]; assumption).
  all: try (clear - ngl_rng_FP ngl_rng_CP ngl_rng_EN ngl_rng_w; lia).
  all: first [lia].
Qed.


Definition ngl_mem_pnglc (m : word -> option byte) (regs : bvmap 5 word) (FP CP EN w : Z) : word -> option byte :=
  wbytes (m) (wa (CP + 0)) (word_to_le_bytes 4 (wa (ext_Z true 0 4 w))).

#[using="Type"] Theorem ngl_pnglc : forall regs m rom FP CP EN w, ngl_pre regs m FP CP EN w ->
  scs_denot SEGS m (Ez regs (VALS_ngl FP CP EN w)) (snd (fst AXF_ngl.RES_pnglc)) ->
  exists R, msteps SEGS (mkst regs (wa 0x446ac) m rom) (mkst R (wa 0x446ac) (ngl_mem_pnglc m regs FP CP EN w) rom) /\
    getr R 11 = wa EN /\ getr R 12 = wa (ext_Z true 0 4 w) /\ getr R 13 = wa (CP + 4) /\ getr R 20 = wa (FP + 4) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 14; 15; 16; 17; 18; 19; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom FP CP EN w P Hsc. destruct (ngl_setup regs m FP CP EN w P) as [HR HK].
  set (E := Ez regs (VALS_ngl FP CP EN w)) in *. destruct P as [ngl_R11 ngl_R13 ngl_R20 ngl_rng_FP ngl_rng_CP ngl_rng_EN ngl_rng_w ngl_kw3 ngl_kwr4].
  assert (Z32 : bv_unsigned (ev E 32) = FP) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = CP) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = EN) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = w) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 10 [0x446ac; 0x446c0] AXF_ngl.scr_pnglc 0x446ac AXF_ngl.sr_ngl AXF_ngl.kn_ngl 36 _ _ _ E m rom regs AXF_ngl.RES_pnglc_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_ngl.RES_pnglc fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (ngl_mem_pnglc m regs FP CP EN w) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold ngl_mem_pnglc. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition ngl_mem_pnglx (m : word -> option byte) (regs : bvmap 5 word) (FP CP EN w : Z) : word -> option byte :=
  wbytes (m) (wa (CP + 0)) (word_to_le_bytes 4 (wa (ext_Z true 0 4 w))).

#[using="Type"] Theorem ngl_pnglx : forall regs m rom FP CP EN w, ngl_pre regs m FP CP EN w ->
  scs_denot SEGS m (Ez regs (VALS_ngl FP CP EN w)) (snd (fst AXF_ngl.RES_pnglx)) ->
  exists R, msteps SEGS (mkst regs (wa 0x446ac) m rom) (mkst R (wa 0x446c0) (ngl_mem_pnglx m regs FP CP EN w) rom) /\
    getr R 11 = wa EN /\ getr R 12 = wa (ext_Z true 0 4 w) /\ getr R 13 = wa (CP + 4) /\ getr R 20 = wa (FP + 4) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 14; 15; 16; 17; 18; 19; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom FP CP EN w P Hsc. destruct (ngl_setup regs m FP CP EN w P) as [HR HK].
  set (E := Ez regs (VALS_ngl FP CP EN w)) in *. destruct P as [ngl_R11 ngl_R13 ngl_R20 ngl_rng_FP ngl_rng_CP ngl_rng_EN ngl_rng_w ngl_kw3 ngl_kwr4].
  assert (Z32 : bv_unsigned (ev E 32) = FP) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = CP) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = EN) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = w) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 10 [0x446ac; 0x446c0] AXF_ngl.scr_pnglx 0x446ac AXF_ngl.sr_ngl AXF_ngl.kn_ngl 36 _ _ _ E m rom regs AXF_ngl.RES_pnglx_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_ngl.RES_pnglx fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (ngl_mem_pnglx m regs FP CP EN w) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold ngl_mem_pnglx. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End NGL.
End AXF_nglz.

From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_ngtz.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_ngtz.
Import ListNotations AX2 AX2S.

Module AXF_ms0.
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

Definition e_dmy := EVar 32.
Definition sr_ms0 := (sr_upd (sr_upd sr_id 11 (ELit 0)) 12 (ELit 0)).
Definition kn_ms0 : list kentry :=
  [ KRange (EVar 10) 1 (2^47) ].
Definition scr_ms0 : scripts := SCR [true] [] [].
Definition ss_ms0 := SS 0xd3088 sr_ms0 [] kn_ms0 33.
Definition RUN_ms0 := sym_exec SEGS 10 true [0xd317c; 0xd3160] scr_ms0 ss_ms0 [].

Definition scr_pms0 : scripts := SCR [true] [] [].
Definition RES_pms0 := Eval vm_compute in sym_exec SEGS 10 true [0xd317c; 0xd3160] scr_pms0 ss_ms0 [].
Lemma RES_pms0_ok : sym_exec SEGS 10 true [0xd317c; 0xd3160] scr_pms0 (SS 0xd3088 sr_ms0 [] kn_ms0 33) [] = RES_pms0.
Proof. vm_compute. reflexivity. Qed.
End AXF_ms0.

Module AXF_ms0z.
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

Section MS0.
Context {fx : FPState}.

Definition VALS_ms0 (dmy : Z) : list Z := [dmy].

Record ms0_pre (regs : bvmap 5 word) (m : word -> option byte) (dmy : Z) : Prop := {
  ms0_R11 : getr regs 11 = wa 0 ;
  ms0_R12 : getr regs 12 = wa 0 ;
  ms0_rng_dmy : 0 <= dmy <= 0 ;
  ms0_kr0 : 1 <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) <= (2^47)
}.


#[using="Type"] Lemma ms0_setup : forall regs m dmy, ms0_pre regs m dmy ->
  regs_ok (Ez regs (VALS_ms0 dmy)) AXF_ms0.sr_ms0 regs /\ know_ok SEGS (Ez regs (VALS_ms0 dmy)) m AXF_ms0.kn_ms0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m dmy P. destruct P as [ms0_R11 ms0_R12 ms0_rng_dmy ms0_kr0].
  set (E := Ez regs (VALS_ms0 dmy)).
  assert (Z32 : bv_unsigned (ev E 32) = dmy) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z10 : bv_unsigned (ev E 10) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10)))) by reflexivity.
  split.
  { unfold AXF_ms0.sr_ms0.
    apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply regs_ok_id|]|].
    - rewrite ms0_R11. reflexivity.
    - rewrite ms0_R12. reflexivity. }
  unfold know_ok, AXF_ms0.kn_ms0.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_ms0.e_dmy a_base a_off].
  all: rewrite ?Z32, ?Z10.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range dmy _ _ ms0_rng_dmy eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - ms0_rng_dmy ms0_kr0; lia).
  all: first [lia].
Qed.


Definition ms0_mem_pms0 (m : word -> option byte) (regs : bvmap 5 word) (dmy : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem ms0_pms0 : forall regs m rom dmy, ms0_pre regs m dmy ->
  scs_denot SEGS m (Ez regs (VALS_ms0 dmy)) (snd (fst AXF_ms0.RES_pms0)) ->
  exists R, msteps SEGS (mkst regs (wa 0xd3088) m rom) (mkst R (wa 0xd317c) (ms0_mem_pms0 m regs dmy) rom) /\
    getr R 11 = wa 0 /\ getr R 12 = wa 0 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom dmy P Hsc. destruct (ms0_setup regs m dmy P) as [HR HK].
  set (E := Ez regs (VALS_ms0 dmy)) in *. destruct P as [ms0_R11 ms0_R12 ms0_rng_dmy ms0_kr0].
  assert (Z32 : bv_unsigned (ev E 32) = dmy) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z10 : bv_unsigned (ev E 10) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10)))) by reflexivity.
  destruct (run_sound SEGS 10 [0xd317c; 0xd3160] AXF_ms0.scr_pms0 0xd3088 AXF_ms0.sr_ms0 AXF_ms0.kn_ms0 33 _ _ _ E m rom regs AXF_ms0.RES_pms0_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_ms0.RES_pms0 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (ms0_mem_pms0 m regs dmy) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold ms0_mem_pms0. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MS0.
End AXF_ms0z.

Module AXF_msA.
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

Definition e_n := EVar 32.
Definition sr_msA := (sr_upd (sr_upd sr_id 11 (ELit 0)) 12 (e_n)).
Definition kn_msA : list kentry :=
  [ KRange (EVar 10) 1 (2^47);
    KWr (SA (EVar 10) 0) e_n ].
Definition scr_msA : scripts := SCR [false; false; false; false] [] [].
Definition ss_msA := SS 0xd3088 sr_msA [] kn_msA 33.
Definition RUN_msA := sym_exec SEGS 40 true [0xd317c; 0xd30d8] scr_msA ss_msA [].

Definition scr_pmsa1 : scripts := SCR [false; true] [] [].
Definition RES_pmsa1 := Eval vm_compute in sym_exec SEGS 40 true [0xd317c; 0xd30d8] scr_pmsa1 ss_msA [].
Lemma RES_pmsa1_ok : sym_exec SEGS 40 true [0xd317c; 0xd30d8] scr_pmsa1 (SS 0xd3088 sr_msA [] kn_msA 33) [] = RES_pmsa1.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmsa2 : scripts := SCR [false; false; true] [] [].
Definition RES_pmsa2 := Eval vm_compute in sym_exec SEGS 40 true [0xd317c; 0xd30d8] scr_pmsa2 ss_msA [].
Lemma RES_pmsa2_ok : sym_exec SEGS 40 true [0xd317c; 0xd30d8] scr_pmsa2 (SS 0xd3088 sr_msA [] kn_msA 33) [] = RES_pmsa2.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmsa3 : scripts := SCR [false; false; false; true] [] [].
Definition RES_pmsa3 := Eval vm_compute in sym_exec SEGS 40 true [0xd317c; 0xd30d8] scr_pmsa3 ss_msA [].
Lemma RES_pmsa3_ok : sym_exec SEGS 40 true [0xd317c; 0xd30d8] scr_pmsa3 (SS 0xd3088 sr_msA [] kn_msA 33) [] = RES_pmsa3.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmsa9 : scripts := SCR [false; false; false; false] [] [].
Definition RES_pmsa9 := Eval vm_compute in sym_exec SEGS 40 true [0xd317c; 0xd30d8] scr_pmsa9 ss_msA [].
Lemma RES_pmsa9_ok : sym_exec SEGS 40 true [0xd317c; 0xd30d8] scr_pmsa9 (SS 0xd3088 sr_msA [] kn_msA 33) [] = RES_pmsa9.
Proof. vm_compute. reflexivity. Qed.
End AXF_msA.

Module AXF_msAz.
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

Section MSA.
Context {fx : FPState}.

Definition VALS_msA (n : Z) : list Z := [n].

Record msA_pre (regs : bvmap 5 word) (m : word -> option byte) (n : Z) : Prop := {
  msA_R11 : getr regs 11 = wa 0 ;
  msA_R12 : getr regs 12 = wa n ;
  msA_rng_n : 1 <= n <= 2^32 ;
  msA_kr0 : 1 <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) <= (2^47) ;
  msA_kwr1 : forall d k, 0 <= d -> d + Z.of_nat k <= n -> store_ok SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + 0 + d)) k = true
}.


#[using="Type"] Lemma msA_setup : forall regs m n, msA_pre regs m n ->
  regs_ok (Ez regs (VALS_msA n)) AXF_msA.sr_msA regs /\ know_ok SEGS (Ez regs (VALS_msA n)) m AXF_msA.kn_msA.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m n P. destruct P as [msA_R11 msA_R12 msA_rng_n msA_kr0 msA_kwr1].
  set (E := Ez regs (VALS_msA n)).
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z10 : bv_unsigned (ev E 10) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10)))) by reflexivity.
  split.
  { unfold AXF_msA.sr_msA.
    apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply regs_ok_id|]|].
    - rewrite msA_R11. reflexivity.
    - rewrite msA_R12. reflexivity. }
  unfold know_ok, AXF_msA.kn_msA.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_msA.e_n a_base a_off].
  all: rewrite ?Z32, ?Z10.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range n _ _ msA_rng_n eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply msA_kwr1]; assumption).
  all: cbn [nth Nat.sub VALS_msA].
  all: rewrite ?(Z.mod_small (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))))) by (pose proof (bv_unsigned_in_range _ (getr regs (Z_to_bv 5 (Z.of_nat 10)))); unfold bv_modulus in *; change (2 ^ Z.of_N 64) with (2^64) in *; lia).
  all: lia.
Qed.


Definition msA_mem_pmsa1 (m : word -> option byte) (regs : bvmap 5 word) (n : Z) : word -> option byte :=
  wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + 0)) (word_to_le_bytes 1 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + n + -1)) (word_to_le_bytes 1 (wa 0)).

#[using="Type"] Theorem msA_pmsa1 : forall regs m rom n, msA_pre regs m n ->
  scs_denot SEGS m (Ez regs (VALS_msA n)) (snd (fst AXF_msA.RES_pmsa1)) ->
  exists R, msteps SEGS (mkst regs (wa 0xd3088) m rom) (mkst R (wa 0xd317c) (msA_mem_pmsa1 m regs n) rom) /\
    getr R 11 = wa 0 /\ getr R 12 = wa n /\ getr R 13 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + n) /\ getr R 14 = wa 3 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n P Hsc. destruct (msA_setup regs m n P) as [HR HK].
  set (E := Ez regs (VALS_msA n)) in *. destruct P as [msA_R11 msA_R12 msA_rng_n msA_kr0 msA_kwr1].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z10 : bv_unsigned (ev E 10) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10)))) by reflexivity.
  destruct (run_sound SEGS 40 [0xd317c; 0xd30d8] AXF_msA.scr_pmsa1 0xd3088 AXF_msA.sr_msA AXF_msA.kn_msA 33 _ _ _ E m rom regs AXF_msA.RES_pmsa1_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_msA.RES_pmsa1 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (msA_mem_pmsa1 m regs n) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold msA_mem_pmsa1. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition msA_mem_pmsa2 (m : word -> option byte) (regs : bvmap 5 word) (n : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + 0)) (word_to_le_bytes 1 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + n + -1)) (word_to_le_bytes 1 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + 1)) (word_to_le_bytes 1 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + 2)) (word_to_le_bytes 1 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + n + -3)) (word_to_le_bytes 1 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + n + -2)) (word_to_le_bytes 1 (wa 0)).

#[using="Type"] Theorem msA_pmsa2 : forall regs m rom n, msA_pre regs m n ->
  scs_denot SEGS m (Ez regs (VALS_msA n)) (snd (fst AXF_msA.RES_pmsa2)) ->
  exists R, msteps SEGS (mkst regs (wa 0xd3088) m rom) (mkst R (wa 0xd317c) (msA_mem_pmsa2 m regs n) rom) /\
    getr R 11 = wa 0 /\ getr R 12 = wa n /\ getr R 13 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + n) /\ getr R 14 = wa 7 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n P Hsc. destruct (msA_setup regs m n P) as [HR HK].
  set (E := Ez regs (VALS_msA n)) in *. destruct P as [msA_R11 msA_R12 msA_rng_n msA_kr0 msA_kwr1].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z10 : bv_unsigned (ev E 10) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10)))) by reflexivity.
  destruct (run_sound SEGS 40 [0xd317c; 0xd30d8] AXF_msA.scr_pmsa2 0xd3088 AXF_msA.sr_msA AXF_msA.kn_msA 33 _ _ _ E m rom regs AXF_msA.RES_pmsa2_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_msA.RES_pmsa2 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (msA_mem_pmsa2 m regs n) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold msA_mem_pmsa2. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition msA_mem_pmsa3 (m : word -> option byte) (regs : bvmap 5 word) (n : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + 0)) (word_to_le_bytes 1 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + n + -1)) (word_to_le_bytes 1 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + 1)) (word_to_le_bytes 1 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + 2)) (word_to_le_bytes 1 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + n + -3)) (word_to_le_bytes 1 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + n + -2)) (word_to_le_bytes 1 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + 3)) (word_to_le_bytes 1 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + n + -4)) (word_to_le_bytes 1 (wa 0)).

#[using="Type"] Theorem msA_pmsa3 : forall regs m rom n, msA_pre regs m n ->
  scs_denot SEGS m (Ez regs (VALS_msA n)) (snd (fst AXF_msA.RES_pmsa3)) ->
  exists R, msteps SEGS (mkst regs (wa 0xd3088) m rom) (mkst R (wa 0xd317c) (msA_mem_pmsa3 m regs n) rom) /\
    getr R 11 = wa 0 /\ getr R 12 = wa n /\ getr R 13 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + n) /\ getr R 14 = wa 7 /\ getr R 15 = wa 9 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n P Hsc. destruct (msA_setup regs m n P) as [HR HK].
  set (E := Ez regs (VALS_msA n)) in *. destruct P as [msA_R11 msA_R12 msA_rng_n msA_kr0 msA_kwr1].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z10 : bv_unsigned (ev E 10) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10)))) by reflexivity.
  destruct (run_sound SEGS 40 [0xd317c; 0xd30d8] AXF_msA.scr_pmsa3 0xd3088 AXF_msA.sr_msA AXF_msA.kn_msA 33 _ _ _ E m rom regs AXF_msA.RES_pmsa3_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_msA.RES_pmsa3 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (msA_mem_pmsa3 m regs n) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold msA_mem_pmsa3. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition msA_mem_pmsa9 (m : word -> option byte) (regs : bvmap 5 word) (n : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + 0)) (word_to_le_bytes 1 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + n + -1)) (word_to_le_bytes 1 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + 1)) (word_to_le_bytes 1 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + 2)) (word_to_le_bytes 1 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + n + -3)) (word_to_le_bytes 1 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + n + -2)) (word_to_le_bytes 1 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + 3)) (word_to_le_bytes 1 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + n + -4)) (word_to_le_bytes 1 (wa 0)).

#[using="Type"] Theorem msA_pmsa9 : forall regs m rom n, msA_pre regs m n ->
  scs_denot SEGS m (Ez regs (VALS_msA n)) (snd (fst AXF_msA.RES_pmsa9)) ->
  exists R, msteps SEGS (mkst regs (wa 0xd3088) m rom) (mkst R (wa 0xd30d8) (msA_mem_pmsa9 m regs n) rom) /\
    getr R 11 = wa 269488128 /\ getr R 12 = wa n /\ getr R 14 = wa 7 /\ getr R 15 = wa 9 /\ getr R 16 = wa 0 /\ 0 <= bv_unsigned (getr R 13) <= 3 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n P Hsc. destruct (msA_setup regs m n P) as [HR HK].
  set (E := Ez regs (VALS_msA n)) in *. destruct P as [msA_R11 msA_R12 msA_rng_n msA_kr0 msA_kwr1].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z10 : bv_unsigned (ev E 10) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10)))) by reflexivity.
  destruct (run_sound SEGS 40 [0xd317c; 0xd30d8] AXF_msA.scr_pmsa9 0xd3088 AXF_msA.sr_msA AXF_msA.kn_msA 33 _ _ _ E m rom regs AXF_msA.RES_pmsa9_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_msA.RES_pmsa9 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (msA_mem_pmsa9 m regs n) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold msA_mem_pmsa9. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split.
    { assert (E13 : getr R 13 = edenot E (EAlu ALU_AND (EAluw ALU_SUB (ELit 0) (EVar 10)) (ELit 3))) by (srg HR'; reflexivity).
      rewrite E13, zeval_sound. cbn [zeval]. rewrite u_wa. change (3 mod 2^64) with (Z.ones 2). rewrite Z.land_ones by lia.
      pose proof (Z.mod_pos_bound (zeval E (EAluw ALU_SUB (ELit 0) (EVar 10)) mod 2^64) (2^2) ltac:(lia)) as U.
      rewrite Z.mod_small by lia. lia. }
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MSA.
End AXF_msAz.

Module AXF_msB.
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

Definition e_n := EVar 32.
Definition e_kq := EVar 33.
Definition sr_msB := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 11 (ELit 269488128)) 12 (e_n)) 13 (e_kq)) 14 (ELit 7)) 15 (ELit 9)) 16 (ELit 0)).
Definition kn_msB : list kentry :=
  [ KRange (EVar 10) 1 (2^47);
    KWr (SA (EVar 10) 0) e_n ].
Definition scr_msB : scripts := SCR [false; false; false] [] [].
Definition ss_msB := SS 0xd30d8 sr_msB [] kn_msB 34.
Definition RUN_msB := sym_exec SEGS 60 true [0xd317c; 0xd3160] scr_msB ss_msB [].

Definition scr_pmsb1 : scripts := SCR [true] [] [].
Definition RES_pmsb1 := Eval vm_compute in sym_exec SEGS 60 true [0xd317c; 0xd3160] scr_pmsb1 ss_msB [].
Lemma RES_pmsb1_ok : sym_exec SEGS 60 true [0xd317c; 0xd3160] scr_pmsb1 (SS 0xd30d8 sr_msB [] kn_msB 34) [] = RES_pmsb1.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmsb2 : scripts := SCR [false; true] [] [].
Definition RES_pmsb2 := Eval vm_compute in sym_exec SEGS 60 true [0xd317c; 0xd3160] scr_pmsb2 ss_msB [].
Lemma RES_pmsb2_ok : sym_exec SEGS 60 true [0xd317c; 0xd3160] scr_pmsb2 (SS 0xd30d8 sr_msB [] kn_msB 34) [] = RES_pmsb2.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmsb3 : scripts := SCR [false; false; true] [] [].
Definition RES_pmsb3 := Eval vm_compute in sym_exec SEGS 60 true [0xd317c; 0xd3160] scr_pmsb3 ss_msB [].
Lemma RES_pmsb3_ok : sym_exec SEGS 60 true [0xd317c; 0xd3160] scr_pmsb3 (SS 0xd30d8 sr_msB [] kn_msB 34) [] = RES_pmsb3.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmsb4 : scripts := SCR [false; false; false] [] [].
Definition RES_pmsb4 := Eval vm_compute in sym_exec SEGS 60 true [0xd317c; 0xd3160] scr_pmsb4 ss_msB [].
Lemma RES_pmsb4_ok : sym_exec SEGS 60 true [0xd317c; 0xd3160] scr_pmsb4 (SS 0xd30d8 sr_msB [] kn_msB 34) [] = RES_pmsb4.
Proof. vm_compute. reflexivity. Qed.
End AXF_msB.

Module AXF_msBz.
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

Section MSB.
Context {fx : FPState}.

Definition VALS_msB (n kq : Z) : list Z := [n; kq].

Record msB_pre (regs : bvmap 5 word) (m : word -> option byte) (n kq : Z) : Prop := {
  msB_R11 : getr regs 11 = wa 269488128 ;
  msB_R12 : getr regs 12 = wa n ;
  msB_R13 : getr regs 13 = wa kq ;
  msB_R14 : getr regs 14 = wa 7 ;
  msB_R15 : getr regs 15 = wa 9 ;
  msB_R16 : getr regs 16 = wa 0 ;
  msB_rng_n : 9 <= n <= 2^32 ;
  msB_rng_kq : 0 <= kq <= 3 ;
  msB_kr0 : 1 <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) <= (2^47) ;
  msB_kwr1 : forall d k, 0 <= d -> d + Z.of_nat k <= n -> store_ok SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + 0 + d)) k = true
}.


#[using="Type"] Lemma msB_setup : forall regs m n kq, msB_pre regs m n kq ->
  regs_ok (Ez regs (VALS_msB n kq)) AXF_msB.sr_msB regs /\ know_ok SEGS (Ez regs (VALS_msB n kq)) m AXF_msB.kn_msB.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m n kq P. destruct P as [msB_R11 msB_R12 msB_R13 msB_R14 msB_R15 msB_R16 msB_rng_n msB_rng_kq msB_kr0 msB_kwr1].
  set (E := Ez regs (VALS_msB n kq)).
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = kq) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z10 : bv_unsigned (ev E 10) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10)))) by reflexivity.
  split.
  { unfold AXF_msB.sr_msB.
    apply (regs_ok_pin E _ regs 16); [apply (regs_ok_pin E _ regs 15); [apply (regs_ok_pin E _ regs 14); [apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply regs_ok_id|]|]|]|]|]|].
    - rewrite msB_R11. reflexivity.
    - rewrite msB_R12. reflexivity.
    - rewrite msB_R13. reflexivity.
    - rewrite msB_R14. reflexivity.
    - rewrite msB_R15. reflexivity.
    - rewrite msB_R16. reflexivity. }
  unfold know_ok, AXF_msB.kn_msB.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_msB.e_n AXF_msB.e_kq a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z10.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range n _ _ msB_rng_n eq_refl eq_refl), ?(mod64_of_range kq _ _ msB_rng_kq eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply msB_kwr1]; assumption).
  all: cbn [nth Nat.sub VALS_msB].
  all: rewrite ?(Z.mod_small (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))))) by (pose proof (bv_unsigned_in_range _ (getr regs (Z_to_bv 5 (Z.of_nat 10)))); unfold bv_modulus in *; change (2 ^ Z.of_N 64) with (2^64) in *; lia).
  all: lia.
Qed.


Definition msB_mem_pmsb1 (m : word -> option byte) (regs : bvmap 5 word) (n kq : Z) : word -> option byte :=
  wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq + 0)) (word_to_le_bytes 4 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)) + -4)) (word_to_le_bytes 4 (wa 0)).

#[using="Type"] Theorem msB_pmsb1 : forall regs m rom n kq, msB_pre regs m n kq ->
  scs_denot SEGS m (Ez regs (VALS_msB n kq)) (snd (fst AXF_msB.RES_pmsb1)) ->
  exists R, msteps SEGS (mkst regs (wa 0xd30d8) m rom) (mkst R (wa 0xd317c) (msB_mem_pmsb1 m regs n kq) rom) /\
    getr R 11 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq) /\ getr R 12 = wa 0 /\ getr R 13 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2))) /\ getr R 14 = wa (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2) /\ getr R 15 = wa 9 /\ getr R 16 = wa 0 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n kq P Hsc. destruct (msB_setup regs m n kq P) as [HR HK].
  set (E := Ez regs (VALS_msB n kq)) in *. destruct P as [msB_R11 msB_R12 msB_R13 msB_R14 msB_R15 msB_R16 msB_rng_n msB_rng_kq msB_kr0 msB_kwr1].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = kq) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z10 : bv_unsigned (ev E 10) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10)))) by reflexivity.
  destruct (run_sound SEGS 60 [0xd317c; 0xd3160] AXF_msB.scr_pmsb1 0xd30d8 AXF_msB.sr_msB AXF_msB.kn_msB 34 _ _ _ E m rom regs AXF_msB.RES_pmsb1_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_msB.RES_pmsb1 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (msB_mem_pmsb1 m regs n kq) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold msB_mem_pmsb1. repeat (apply (f_equal3 wbytes)); try reflexivity.
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


Definition msB_mem_pmsb2 (m : word -> option byte) (regs : bvmap 5 word) (n kq : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq + 0)) (word_to_le_bytes 4 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)) + -4)) (word_to_le_bytes 4 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq + 4)) (word_to_le_bytes 4 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq + 8)) (word_to_le_bytes 4 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)) + -12)) (word_to_le_bytes 4 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)) + -8)) (word_to_le_bytes 4 (wa 0)).

#[using="Type"] Theorem msB_pmsb2 : forall regs m rom n kq, msB_pre regs m n kq ->
  scs_denot SEGS m (Ez regs (VALS_msB n kq)) (snd (fst AXF_msB.RES_pmsb2)) ->
  exists R, msteps SEGS (mkst regs (wa 0xd30d8) m rom) (mkst R (wa 0xd317c) (msB_mem_pmsb2 m regs n kq) rom) /\
    getr R 11 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq) /\ getr R 12 = wa 0 /\ getr R 13 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2))) /\ getr R 14 = wa (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2) /\ getr R 15 = wa 25 /\ getr R 16 = wa 0 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n kq P Hsc. destruct (msB_setup regs m n kq P) as [HR HK].
  set (E := Ez regs (VALS_msB n kq)) in *. destruct P as [msB_R11 msB_R12 msB_R13 msB_R14 msB_R15 msB_R16 msB_rng_n msB_rng_kq msB_kr0 msB_kwr1].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = kq) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z10 : bv_unsigned (ev E 10) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10)))) by reflexivity.
  destruct (run_sound SEGS 60 [0xd317c; 0xd3160] AXF_msB.scr_pmsb2 0xd30d8 AXF_msB.sr_msB AXF_msB.kn_msB 34 _ _ _ E m rom regs AXF_msB.RES_pmsb2_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_msB.RES_pmsb2 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (msB_mem_pmsb2 m regs n kq) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold msB_mem_pmsb2. repeat (apply (f_equal3 wbytes)); try reflexivity.
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


Definition msB_mem_pmsb3 (m : word -> option byte) (regs : bvmap 5 word) (n kq : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq + 0)) (word_to_le_bytes 4 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)) + -4)) (word_to_le_bytes 4 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq + 4)) (word_to_le_bytes 4 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq + 8)) (word_to_le_bytes 4 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)) + -12)) (word_to_le_bytes 4 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)) + -8)) (word_to_le_bytes 4 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq + 12)) (word_to_le_bytes 4 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq + 16)) (word_to_le_bytes 4 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq + 20)) (word_to_le_bytes 4 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq + 24)) (word_to_le_bytes 4 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)) + -28)) (word_to_le_bytes 4 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)) + -24)) (word_to_le_bytes 4 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)) + -20)) (word_to_le_bytes 4 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)) + -16)) (word_to_le_bytes 4 (wa 0)).

#[using="Type"] Theorem msB_pmsb3 : forall regs m rom n kq, msB_pre regs m n kq ->
  scs_denot SEGS m (Ez regs (VALS_msB n kq)) (snd (fst AXF_msB.RES_pmsb3)) ->
  exists R, msteps SEGS (mkst regs (wa 0xd30d8) m rom) (mkst R (wa 0xd317c) (msB_mem_pmsb3 m regs n kq) rom) /\
    getr R 11 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq) /\ getr R 12 = wa 0 /\ getr R 13 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2))) /\ getr R 14 = wa (((4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2) + (-1 * Z.land (((bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq)) mod 2^64) 4)) + -24) /\ getr R 15 = wa (Z.land (((bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq)) mod 2^64) 4 + 24) /\ getr R 16 = wa 32 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n kq P Hsc. destruct (msB_setup regs m n kq P) as [HR HK].
  set (E := Ez regs (VALS_msB n kq)) in *. destruct P as [msB_R11 msB_R12 msB_R13 msB_R14 msB_R15 msB_R16 msB_rng_n msB_rng_kq msB_kr0 msB_kwr1].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = kq) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z10 : bv_unsigned (ev E 10) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10)))) by reflexivity.
  destruct (run_sound SEGS 60 [0xd317c; 0xd3160] AXF_msB.scr_pmsb3 0xd30d8 AXF_msB.sr_msB AXF_msB.kn_msB 34 _ _ _ E m rom regs AXF_msB.RES_pmsb3_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_msB.RES_pmsb3 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (msB_mem_pmsb3 m regs n kq) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold msB_mem_pmsb3. repeat (apply (f_equal3 wbytes)); try reflexivity.
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


Definition msB_mem_pmsb4 (m : word -> option byte) (regs : bvmap 5 word) (n kq : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq + 0)) (word_to_le_bytes 4 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)) + -4)) (word_to_le_bytes 4 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq + 4)) (word_to_le_bytes 4 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq + 8)) (word_to_le_bytes 4 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)) + -12)) (word_to_le_bytes 4 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)) + -8)) (word_to_le_bytes 4 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq + 12)) (word_to_le_bytes 4 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq + 16)) (word_to_le_bytes 4 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq + 20)) (word_to_le_bytes 4 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq + 24)) (word_to_le_bytes 4 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)) + -28)) (word_to_le_bytes 4 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)) + -24)) (word_to_le_bytes 4 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)) + -20)) (word_to_le_bytes 4 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)) + -16)) (word_to_le_bytes 4 (wa 0)).

#[using="Type"] Theorem msB_pmsb4 : forall regs m rom n kq, msB_pre regs m n kq ->
  scs_denot SEGS m (Ez regs (VALS_msB n kq)) (snd (fst AXF_msB.RES_pmsb4)) ->
  exists R, msteps SEGS (mkst regs (wa 0xd30d8) m rom) (mkst R (wa 0xd3160) (msB_mem_pmsb4 m regs n kq) rom) /\
    getr R 11 = wa ((bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + Z.land (((bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq)) mod 2^64) 4)) + 24) /\ getr R 12 = wa 0 /\ getr R 13 = wa 31 /\ getr R 14 = wa (((4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2) + (-1 * Z.land (((bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq)) mod 2^64) 4)) + -24) /\ getr R 15 = wa (Z.land (((bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq)) mod 2^64) 4 + 24) /\ getr R 16 = wa 32 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n kq P Hsc. destruct (msB_setup regs m n kq P) as [HR HK].
  set (E := Ez regs (VALS_msB n kq)) in *. destruct P as [msB_R11 msB_R12 msB_R13 msB_R14 msB_R15 msB_R16 msB_rng_n msB_rng_kq msB_kr0 msB_kwr1].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = kq) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z10 : bv_unsigned (ev E 10) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10)))) by reflexivity.
  destruct (run_sound SEGS 60 [0xd317c; 0xd3160] AXF_msB.scr_pmsb4 0xd30d8 AXF_msB.sr_msB AXF_msB.kn_msB 34 _ _ _ E m rom regs AXF_msB.RES_pmsb4_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_msB.RES_pmsb4 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (msB_mem_pmsb4 m regs n kq) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold msB_mem_pmsb4. repeat (apply (f_equal3 wbytes)); try reflexivity.
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

End MSB.
End AXF_msBz.

Module AXF_msc0.
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

Definition e_c := EVar 32.
Definition sr_msc0 := (sr_upd (sr_upd sr_id 11 (e_c)) 12 (ELit 0)).
Definition kn_msc0 : list kentry :=
  [ KRange (EVar 10) 1 (2^47) ].
Definition scr_msc0 : scripts := SCR [true] [] [].
Definition ss_msc0 := SS 0xd3088 sr_msc0 [] kn_msc0 33.
Definition RUN_msc0 := sym_exec SEGS 10 true [0xd317c; 0xd3160] scr_msc0 ss_msc0 [].

Definition scr_pmsc0 : scripts := SCR [true] [] [].
Definition RES_pmsc0 := Eval vm_compute in sym_exec SEGS 10 true [0xd317c; 0xd3160] scr_pmsc0 ss_msc0 [].
Lemma RES_pmsc0_ok : sym_exec SEGS 10 true [0xd317c; 0xd3160] scr_pmsc0 (SS 0xd3088 sr_msc0 [] kn_msc0 33) [] = RES_pmsc0.
Proof. vm_compute. reflexivity. Qed.
End AXF_msc0.

Module AXF_msc0z.
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

Section MSC0.
Context {fx : FPState}.

Definition VALS_msc0 (c : Z) : list Z := [c].

Record msc0_pre (regs : bvmap 5 word) (m : word -> option byte) (c : Z) : Prop := {
  msc0_R11 : getr regs 11 = wa c ;
  msc0_R12 : getr regs 12 = wa 0 ;
  msc0_rng_c : 0 <= c <= 2^64 - 1 ;
  msc0_kr0 : 1 <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) <= (2^47)
}.


#[using="Type"] Lemma msc0_setup : forall regs m c, msc0_pre regs m c ->
  regs_ok (Ez regs (VALS_msc0 c)) AXF_msc0.sr_msc0 regs /\ know_ok SEGS (Ez regs (VALS_msc0 c)) m AXF_msc0.kn_msc0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m c P. destruct P as [msc0_R11 msc0_R12 msc0_rng_c msc0_kr0].
  set (E := Ez regs (VALS_msc0 c)).
  assert (Z32 : bv_unsigned (ev E 32) = c) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z10 : bv_unsigned (ev E 10) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10)))) by reflexivity.
  split.
  { unfold AXF_msc0.sr_msc0.
    apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply regs_ok_id|]|].
    - rewrite msc0_R11. reflexivity.
    - rewrite msc0_R12. reflexivity. }
  unfold know_ok, AXF_msc0.kn_msc0.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_msc0.e_c a_base a_off].
  all: rewrite ?Z32, ?Z10.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - msc0_rng_c msc0_kr0; lia).
  all: first [lia].
Qed.


Definition msc0_mem_pmsc0 (m : word -> option byte) (regs : bvmap 5 word) (c : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem msc0_pmsc0 : forall regs m rom c, msc0_pre regs m c ->
  scs_denot SEGS m (Ez regs (VALS_msc0 c)) (snd (fst AXF_msc0.RES_pmsc0)) ->
  exists R, msteps SEGS (mkst regs (wa 0xd3088) m rom) (mkst R (wa 0xd317c) (msc0_mem_pmsc0 m regs c) rom) /\
    getr R 11 = wa c /\ getr R 12 = wa 0 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom c P Hsc. destruct (msc0_setup regs m c P) as [HR HK].
  set (E := Ez regs (VALS_msc0 c)) in *. destruct P as [msc0_R11 msc0_R12 msc0_rng_c msc0_kr0].
  assert (Z32 : bv_unsigned (ev E 32) = c) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z10 : bv_unsigned (ev E 10) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10)))) by reflexivity.
  destruct (run_sound SEGS 10 [0xd317c; 0xd3160] AXF_msc0.scr_pmsc0 0xd3088 AXF_msc0.sr_msc0 AXF_msc0.kn_msc0 33 _ _ _ E m rom regs AXF_msc0.RES_pmsc0_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_msc0.RES_pmsc0 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (msc0_mem_pmsc0 m regs c) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold msc0_mem_pmsc0. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.
    all: try (rewrite wa_u; reflexivity).
  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MSC0.
End AXF_msc0z.

Module AXF_mscA.
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

Definition e_n := EVar 32.
Definition e_c := EVar 33.
Definition sr_mscA := (sr_upd (sr_upd sr_id 11 (e_c)) 12 (e_n)).
Definition kn_mscA : list kentry :=
  [ KRange (EVar 10) 1 (2^47);
    KWr (SA (EVar 10) 0) e_n ].
Definition scr_mscA : scripts := SCR [false; false; false; false] [] [].
Definition ss_mscA := SS 0xd3088 sr_mscA [] kn_mscA 34.
Definition RUN_mscA := sym_exec SEGS 40 true [0xd317c; 0xd30d8] scr_mscA ss_mscA [].

Definition scr_pmsca1 : scripts := SCR [false; true] [] [].
Definition RES_pmsca1 := Eval vm_compute in sym_exec SEGS 40 true [0xd317c; 0xd30d8] scr_pmsca1 ss_mscA [].
Lemma RES_pmsca1_ok : sym_exec SEGS 40 true [0xd317c; 0xd30d8] scr_pmsca1 (SS 0xd3088 sr_mscA [] kn_mscA 34) [] = RES_pmsca1.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmsca2 : scripts := SCR [false; false; true] [] [].
Definition RES_pmsca2 := Eval vm_compute in sym_exec SEGS 40 true [0xd317c; 0xd30d8] scr_pmsca2 ss_mscA [].
Lemma RES_pmsca2_ok : sym_exec SEGS 40 true [0xd317c; 0xd30d8] scr_pmsca2 (SS 0xd3088 sr_mscA [] kn_mscA 34) [] = RES_pmsca2.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmsca3 : scripts := SCR [false; false; false; true] [] [].
Definition RES_pmsca3 := Eval vm_compute in sym_exec SEGS 40 true [0xd317c; 0xd30d8] scr_pmsca3 ss_mscA [].
Lemma RES_pmsca3_ok : sym_exec SEGS 40 true [0xd317c; 0xd30d8] scr_pmsca3 (SS 0xd3088 sr_mscA [] kn_mscA 34) [] = RES_pmsca3.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmsca9 : scripts := SCR [false; false; false; false] [] [].
Definition RES_pmsca9 := Eval vm_compute in sym_exec SEGS 40 true [0xd317c; 0xd30d8] scr_pmsca9 ss_mscA [].
Lemma RES_pmsca9_ok : sym_exec SEGS 40 true [0xd317c; 0xd30d8] scr_pmsca9 (SS 0xd3088 sr_mscA [] kn_mscA 34) [] = RES_pmsca9.
Proof. vm_compute. reflexivity. Qed.
End AXF_mscA.

Module AXF_mscAz.
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

Section MSCA.
Context {fx : FPState}.

Definition VALS_mscA (n c : Z) : list Z := [n; c].

Record mscA_pre (regs : bvmap 5 word) (m : word -> option byte) (n c : Z) : Prop := {
  mscA_R11 : getr regs 11 = wa c ;
  mscA_R12 : getr regs 12 = wa n ;
  mscA_rng_n : 1 <= n <= 2^32 ;
  mscA_rng_c : 0 <= c <= 2^64 - 1 ;
  mscA_kr0 : 1 <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) <= (2^47) ;
  mscA_kwr1 : forall d k, 0 <= d -> d + Z.of_nat k <= n -> store_ok SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + 0 + d)) k = true
}.


#[using="Type"] Lemma mscA_setup : forall regs m n c, mscA_pre regs m n c ->
  regs_ok (Ez regs (VALS_mscA n c)) AXF_mscA.sr_mscA regs /\ know_ok SEGS (Ez regs (VALS_mscA n c)) m AXF_mscA.kn_mscA.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m n c P. destruct P as [mscA_R11 mscA_R12 mscA_rng_n mscA_rng_c mscA_kr0 mscA_kwr1].
  set (E := Ez regs (VALS_mscA n c)).
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = c) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z10 : bv_unsigned (ev E 10) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10)))) by reflexivity.
  split.
  { unfold AXF_mscA.sr_mscA.
    apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply regs_ok_id|]|].
    - rewrite mscA_R11. reflexivity.
    - rewrite mscA_R12. reflexivity. }
  unfold know_ok, AXF_mscA.kn_mscA.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_mscA.e_n AXF_mscA.e_c a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z10.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range n _ _ mscA_rng_n eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply mscA_kwr1]; assumption).
  all: cbn [nth Nat.sub VALS_mscA].
  all: rewrite ?(Z.mod_small (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))))) by (pose proof (bv_unsigned_in_range _ (getr regs (Z_to_bv 5 (Z.of_nat 10)))); unfold bv_modulus in *; change (2 ^ Z.of_N 64) with (2^64) in *; lia).
  all: lia.
Qed.


Definition mscA_mem_pmsca1 (m : word -> option byte) (regs : bvmap 5 word) (n c : Z) : word -> option byte :=
  wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + 0)) (word_to_le_bytes 1 (wa c))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + n + -1)) (word_to_le_bytes 1 (wa c)).

#[using="Type"] Theorem mscA_pmsca1 : forall regs m rom n c, mscA_pre regs m n c ->
  scs_denot SEGS m (Ez regs (VALS_mscA n c)) (snd (fst AXF_mscA.RES_pmsca1)) ->
  exists R, msteps SEGS (mkst regs (wa 0xd3088) m rom) (mkst R (wa 0xd317c) (mscA_mem_pmsca1 m regs n c) rom) /\
    getr R 11 = wa c /\ getr R 12 = wa n /\ getr R 13 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + n) /\ getr R 14 = wa 3 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n c P Hsc. destruct (mscA_setup regs m n c P) as [HR HK].
  set (E := Ez regs (VALS_mscA n c)) in *. destruct P as [mscA_R11 mscA_R12 mscA_rng_n mscA_rng_c mscA_kr0 mscA_kwr1].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = c) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z10 : bv_unsigned (ev E 10) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10)))) by reflexivity.
  destruct (run_sound SEGS 40 [0xd317c; 0xd30d8] AXF_mscA.scr_pmsca1 0xd3088 AXF_mscA.sr_mscA AXF_mscA.kn_mscA 34 _ _ _ E m rom regs AXF_mscA.RES_pmsca1_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mscA.RES_pmsca1 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mscA_mem_pmsca1 m regs n c) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mscA_mem_pmsca1. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.
    all: try (rewrite wa_u; reflexivity).
  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition mscA_mem_pmsca2 (m : word -> option byte) (regs : bvmap 5 word) (n c : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + 0)) (word_to_le_bytes 1 (wa c))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + n + -1)) (word_to_le_bytes 1 (wa c))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + 1)) (word_to_le_bytes 1 (wa c))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + 2)) (word_to_le_bytes 1 (wa c))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + n + -3)) (word_to_le_bytes 1 (wa c))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + n + -2)) (word_to_le_bytes 1 (wa c)).

#[using="Type"] Theorem mscA_pmsca2 : forall regs m rom n c, mscA_pre regs m n c ->
  scs_denot SEGS m (Ez regs (VALS_mscA n c)) (snd (fst AXF_mscA.RES_pmsca2)) ->
  exists R, msteps SEGS (mkst regs (wa 0xd3088) m rom) (mkst R (wa 0xd317c) (mscA_mem_pmsca2 m regs n c) rom) /\
    getr R 11 = wa c /\ getr R 12 = wa n /\ getr R 13 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + n) /\ getr R 14 = wa 7 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n c P Hsc. destruct (mscA_setup regs m n c P) as [HR HK].
  set (E := Ez regs (VALS_mscA n c)) in *. destruct P as [mscA_R11 mscA_R12 mscA_rng_n mscA_rng_c mscA_kr0 mscA_kwr1].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = c) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z10 : bv_unsigned (ev E 10) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10)))) by reflexivity.
  destruct (run_sound SEGS 40 [0xd317c; 0xd30d8] AXF_mscA.scr_pmsca2 0xd3088 AXF_mscA.sr_mscA AXF_mscA.kn_mscA 34 _ _ _ E m rom regs AXF_mscA.RES_pmsca2_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mscA.RES_pmsca2 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mscA_mem_pmsca2 m regs n c) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mscA_mem_pmsca2. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.
    all: try (rewrite wa_u; reflexivity).
  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition mscA_mem_pmsca3 (m : word -> option byte) (regs : bvmap 5 word) (n c : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + 0)) (word_to_le_bytes 1 (wa c))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + n + -1)) (word_to_le_bytes 1 (wa c))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + 1)) (word_to_le_bytes 1 (wa c))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + 2)) (word_to_le_bytes 1 (wa c))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + n + -3)) (word_to_le_bytes 1 (wa c))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + n + -2)) (word_to_le_bytes 1 (wa c))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + 3)) (word_to_le_bytes 1 (wa c))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + n + -4)) (word_to_le_bytes 1 (wa c)).

#[using="Type"] Theorem mscA_pmsca3 : forall regs m rom n c, mscA_pre regs m n c ->
  scs_denot SEGS m (Ez regs (VALS_mscA n c)) (snd (fst AXF_mscA.RES_pmsca3)) ->
  exists R, msteps SEGS (mkst regs (wa 0xd3088) m rom) (mkst R (wa 0xd317c) (mscA_mem_pmsca3 m regs n c) rom) /\
    getr R 11 = wa c /\ getr R 12 = wa n /\ getr R 13 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + n) /\ getr R 14 = wa 7 /\ getr R 15 = wa 9 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n c P Hsc. destruct (mscA_setup regs m n c P) as [HR HK].
  set (E := Ez regs (VALS_mscA n c)) in *. destruct P as [mscA_R11 mscA_R12 mscA_rng_n mscA_rng_c mscA_kr0 mscA_kwr1].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = c) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z10 : bv_unsigned (ev E 10) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10)))) by reflexivity.
  destruct (run_sound SEGS 40 [0xd317c; 0xd30d8] AXF_mscA.scr_pmsca3 0xd3088 AXF_mscA.sr_mscA AXF_mscA.kn_mscA 34 _ _ _ E m rom regs AXF_mscA.RES_pmsca3_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mscA.RES_pmsca3 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mscA_mem_pmsca3 m regs n c) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mscA_mem_pmsca3. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.
    all: try (rewrite wa_u; reflexivity).
  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition mscA_mem_pmsca9 (m : word -> option byte) (regs : bvmap 5 word) (n c : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + 0)) (word_to_le_bytes 1 (wa c))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + n + -1)) (word_to_le_bytes 1 (wa c))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + 1)) (word_to_le_bytes 1 (wa c))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + 2)) (word_to_le_bytes 1 (wa c))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + n + -3)) (word_to_le_bytes 1 (wa c))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + n + -2)) (word_to_le_bytes 1 (wa c))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + 3)) (word_to_le_bytes 1 (wa c))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + n + -4)) (word_to_le_bytes 1 (wa c)).

#[using="Type"] Theorem mscA_pmsca9 : forall regs m rom n c, mscA_pre regs m n c ->
  scs_denot SEGS m (Ez regs (VALS_mscA n c)) (snd (fst AXF_mscA.RES_pmsca9)) ->
  exists R, msteps SEGS (mkst regs (wa 0xd3088) m rom) (mkst R (wa 0xd30d8) (mscA_mem_pmsca9 m regs n c) rom) /\
    getr R 11 = wa 269488128 /\ getr R 12 = wa n /\ getr R 14 = wa 7 /\ getr R 15 = wa 9 /\ getr R 16 = wa (72057594037927936 * c) /\ 0 <= bv_unsigned (getr R 13) <= 3 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n c P Hsc. destruct (mscA_setup regs m n c P) as [HR HK].
  set (E := Ez regs (VALS_mscA n c)) in *. destruct P as [mscA_R11 mscA_R12 mscA_rng_n mscA_rng_c mscA_kr0 mscA_kwr1].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = c) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z10 : bv_unsigned (ev E 10) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10)))) by reflexivity.
  destruct (run_sound SEGS 40 [0xd317c; 0xd30d8] AXF_mscA.scr_pmsca9 0xd3088 AXF_mscA.sr_mscA AXF_mscA.kn_mscA 34 _ _ _ E m rom regs AXF_mscA.RES_pmsca9_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mscA.RES_pmsca9 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mscA_mem_pmsca9 m regs n c) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mscA_mem_pmsca9. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.
    all: try (rewrite wa_u; reflexivity).
  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split.
    { assert (E13 : getr R 13 = edenot E (EAlu ALU_AND (EAluw ALU_SUB (ELit 0) (EVar 10)) (ELit 3))) by (srg HR'; reflexivity).
      rewrite E13, zeval_sound. cbn [zeval]. rewrite u_wa. change (3 mod 2^64) with (Z.ones 2). rewrite Z.land_ones by lia.
      pose proof (Z.mod_pos_bound (zeval E (EAluw ALU_SUB (ELit 0) (EVar 10)) mod 2^64) (2^2) ltac:(lia)) as U.
      rewrite Z.mod_small by lia. lia. }
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MSCA.
End AXF_mscAz.

Module AXF_mscB.
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

Definition e_n := EVar 32.
Definition e_kq := EVar 33.
Definition e_wc := EVar 34.
Definition sr_mscB := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 11 (ELit 269488128)) 12 (e_n)) 13 (e_kq)) 14 (ELit 7)) 15 (ELit 9)) 16 (e_wc)).
Definition kn_mscB : list kentry :=
  [ KRange (EVar 10) 1 (2^47);
    KWr (SA (EVar 10) 0) e_n ].
Definition scr_mscB : scripts := SCR [false; false; false] [] [].
Definition ss_mscB := SS 0xd30d8 sr_mscB [] kn_mscB 35.
Definition RUN_mscB := sym_exec SEGS 60 true [0xd317c; 0xd3160] scr_mscB ss_mscB [].

Definition scr_pmscb1 : scripts := SCR [true] [] [].
Definition RES_pmscb1 := Eval vm_compute in sym_exec SEGS 60 true [0xd317c; 0xd3160] scr_pmscb1 ss_mscB [].
Lemma RES_pmscb1_ok : sym_exec SEGS 60 true [0xd317c; 0xd3160] scr_pmscb1 (SS 0xd30d8 sr_mscB [] kn_mscB 35) [] = RES_pmscb1.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmscb2 : scripts := SCR [false; true] [] [].
Definition RES_pmscb2 := Eval vm_compute in sym_exec SEGS 60 true [0xd317c; 0xd3160] scr_pmscb2 ss_mscB [].
Lemma RES_pmscb2_ok : sym_exec SEGS 60 true [0xd317c; 0xd3160] scr_pmscb2 (SS 0xd30d8 sr_mscB [] kn_mscB 35) [] = RES_pmscb2.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmscb3 : scripts := SCR [false; false; true] [] [].
Definition RES_pmscb3 := Eval vm_compute in sym_exec SEGS 60 true [0xd317c; 0xd3160] scr_pmscb3 ss_mscB [].
Lemma RES_pmscb3_ok : sym_exec SEGS 60 true [0xd317c; 0xd3160] scr_pmscb3 (SS 0xd30d8 sr_mscB [] kn_mscB 35) [] = RES_pmscb3.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmscb4 : scripts := SCR [false; false; false] [] [].
Definition RES_pmscb4 := Eval vm_compute in sym_exec SEGS 60 true [0xd317c; 0xd3160] scr_pmscb4 ss_mscB [].
Lemma RES_pmscb4_ok : sym_exec SEGS 60 true [0xd317c; 0xd3160] scr_pmscb4 (SS 0xd30d8 sr_mscB [] kn_mscB 35) [] = RES_pmscb4.
Proof. vm_compute. reflexivity. Qed.
End AXF_mscB.

Module AXF_mscBz.
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

Section MSCB.
Context {fx : FPState}.

Definition VALS_mscB (n kq wc : Z) : list Z := [n; kq; wc].

Record mscB_pre (regs : bvmap 5 word) (m : word -> option byte) (n kq wc : Z) : Prop := {
  mscB_R11 : getr regs 11 = wa 269488128 ;
  mscB_R12 : getr regs 12 = wa n ;
  mscB_R13 : getr regs 13 = wa kq ;
  mscB_R14 : getr regs 14 = wa 7 ;
  mscB_R15 : getr regs 15 = wa 9 ;
  mscB_R16 : getr regs 16 = wa wc ;
  mscB_rng_n : 9 <= n <= 2^32 ;
  mscB_rng_kq : 0 <= kq <= 3 ;
  mscB_rng_wc : 0 <= wc <= 2^64 - 1 ;
  mscB_kr0 : 1 <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) <= (2^47) ;
  mscB_kwr1 : forall d k, 0 <= d -> d + Z.of_nat k <= n -> store_ok SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + 0 + d)) k = true
}.


#[using="Type"] Lemma mscB_setup : forall regs m n kq wc, mscB_pre regs m n kq wc ->
  regs_ok (Ez regs (VALS_mscB n kq wc)) AXF_mscB.sr_mscB regs /\ know_ok SEGS (Ez regs (VALS_mscB n kq wc)) m AXF_mscB.kn_mscB.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m n kq wc P. destruct P as [mscB_R11 mscB_R12 mscB_R13 mscB_R14 mscB_R15 mscB_R16 mscB_rng_n mscB_rng_kq mscB_rng_wc mscB_kr0 mscB_kwr1].
  set (E := Ez regs (VALS_mscB n kq wc)).
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = kq) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = wc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z10 : bv_unsigned (ev E 10) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10)))) by reflexivity.
  split.
  { unfold AXF_mscB.sr_mscB.
    apply (regs_ok_pin E _ regs 16); [apply (regs_ok_pin E _ regs 15); [apply (regs_ok_pin E _ regs 14); [apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply regs_ok_id|]|]|]|]|]|].
    - rewrite mscB_R11. reflexivity.
    - rewrite mscB_R12. reflexivity.
    - rewrite mscB_R13. reflexivity.
    - rewrite mscB_R14. reflexivity.
    - rewrite mscB_R15. reflexivity.
    - rewrite mscB_R16. reflexivity. }
  unfold know_ok, AXF_mscB.kn_mscB.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_mscB.e_n AXF_mscB.e_kq AXF_mscB.e_wc a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z10.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range n _ _ mscB_rng_n eq_refl eq_refl), ?(mod64_of_range kq _ _ mscB_rng_kq eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply mscB_kwr1]; assumption).
  all: cbn [nth Nat.sub VALS_mscB].
  all: rewrite ?(Z.mod_small (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))))) by (pose proof (bv_unsigned_in_range _ (getr regs (Z_to_bv 5 (Z.of_nat 10)))); unfold bv_modulus in *; change (2 ^ Z.of_N 64) with (2^64) in *; lia).
  all: lia.
Qed.


Definition mscB_mem_pmscb1 (m : word -> option byte) (regs : bvmap 5 word) (n kq wc : Z) : word -> option byte :=
  wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq + 0)) (word_to_le_bytes 4 (wa (bv_unsigned (edenot (Ez regs (VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)) + -4)) (word_to_le_bytes 4 (wa (bv_unsigned (edenot (Ez regs (VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304)))))).

#[using="Type"] Theorem mscB_pmscb1 : forall regs m rom n kq wc, mscB_pre regs m n kq wc ->
  scs_denot SEGS m (Ez regs (VALS_mscB n kq wc)) (snd (fst AXF_mscB.RES_pmscb1)) ->
  exists R, msteps SEGS (mkst regs (wa 0xd30d8) m rom) (mkst R (wa 0xd317c) (mscB_mem_pmscb1 m regs n kq wc) rom) /\
    getr R 11 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq) /\ getr R 13 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2))) /\ getr R 14 = wa (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2) /\ getr R 15 = wa 9 /\ getr R 16 = wa wc /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n kq wc P Hsc. destruct (mscB_setup regs m n kq wc P) as [HR HK].
  set (E := Ez regs (VALS_mscB n kq wc)) in *. destruct P as [mscB_R11 mscB_R12 mscB_R13 mscB_R14 mscB_R15 mscB_R16 mscB_rng_n mscB_rng_kq mscB_rng_wc mscB_kr0 mscB_kwr1].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = kq) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = wc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z10 : bv_unsigned (ev E 10) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10)))) by reflexivity.
  destruct (run_sound SEGS 60 [0xd317c; 0xd3160] AXF_mscB.scr_pmscb1 0xd30d8 AXF_mscB.sr_mscB AXF_mscB.kn_mscB 35 _ _ _ E m rom regs AXF_mscB.RES_pmscb1_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mscB.RES_pmscb1 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mscB_mem_pmscb1 m regs n kq wc) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mscB_mem_pmscb1. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.
    all: try (rewrite wa_u; reflexivity).
  - clear Hms.      (* [comment removed for export] *)
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition mscB_mem_pmscb2 (m : word -> option byte) (regs : bvmap 5 word) (n kq wc : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq + 0)) (word_to_le_bytes 4 (wa (bv_unsigned (edenot (Ez regs (VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)) + -4)) (word_to_le_bytes 4 (wa (bv_unsigned (edenot (Ez regs (VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq + 4)) (word_to_le_bytes 4 (wa (bv_unsigned (edenot (Ez regs (VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq + 8)) (word_to_le_bytes 4 (wa (bv_unsigned (edenot (Ez regs (VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)) + -12)) (word_to_le_bytes 4 (wa (bv_unsigned (edenot (Ez regs (VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)) + -8)) (word_to_le_bytes 4 (wa (bv_unsigned (edenot (Ez regs (VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304)))))).

#[using="Type"] Theorem mscB_pmscb2 : forall regs m rom n kq wc, mscB_pre regs m n kq wc ->
  scs_denot SEGS m (Ez regs (VALS_mscB n kq wc)) (snd (fst AXF_mscB.RES_pmscb2)) ->
  exists R, msteps SEGS (mkst regs (wa 0xd30d8) m rom) (mkst R (wa 0xd317c) (mscB_mem_pmscb2 m regs n kq wc) rom) /\
    getr R 11 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq) /\ getr R 13 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2))) /\ getr R 14 = wa (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2) /\ getr R 15 = wa 25 /\ getr R 16 = wa wc /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n kq wc P Hsc. destruct (mscB_setup regs m n kq wc P) as [HR HK].
  set (E := Ez regs (VALS_mscB n kq wc)) in *. destruct P as [mscB_R11 mscB_R12 mscB_R13 mscB_R14 mscB_R15 mscB_R16 mscB_rng_n mscB_rng_kq mscB_rng_wc mscB_kr0 mscB_kwr1].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = kq) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = wc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z10 : bv_unsigned (ev E 10) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10)))) by reflexivity.
  destruct (run_sound SEGS 60 [0xd317c; 0xd3160] AXF_mscB.scr_pmscb2 0xd30d8 AXF_mscB.sr_mscB AXF_mscB.kn_mscB 35 _ _ _ E m rom regs AXF_mscB.RES_pmscb2_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mscB.RES_pmscb2 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mscB_mem_pmscb2 m regs n kq wc) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mscB_mem_pmscb2. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.
    all: try (rewrite wa_u; reflexivity).
  - clear Hms.      (* [comment removed for export] *)
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition mscB_mem_pmscb3 (m : word -> option byte) (regs : bvmap 5 word) (n kq wc : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq + 0)) (word_to_le_bytes 4 (wa (bv_unsigned (edenot (Ez regs (VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)) + -4)) (word_to_le_bytes 4 (wa (bv_unsigned (edenot (Ez regs (VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq + 4)) (word_to_le_bytes 4 (wa (bv_unsigned (edenot (Ez regs (VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq + 8)) (word_to_le_bytes 4 (wa (bv_unsigned (edenot (Ez regs (VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)) + -12)) (word_to_le_bytes 4 (wa (bv_unsigned (edenot (Ez regs (VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)) + -8)) (word_to_le_bytes 4 (wa (bv_unsigned (edenot (Ez regs (VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq + 12)) (word_to_le_bytes 4 (wa (bv_unsigned (edenot (Ez regs (VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq + 16)) (word_to_le_bytes 4 (wa (bv_unsigned (edenot (Ez regs (VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq + 20)) (word_to_le_bytes 4 (wa (bv_unsigned (edenot (Ez regs (VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq + 24)) (word_to_le_bytes 4 (wa (bv_unsigned (edenot (Ez regs (VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)) + -28)) (word_to_le_bytes 4 (wa (bv_unsigned (edenot (Ez regs (VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)) + -24)) (word_to_le_bytes 4 (wa (bv_unsigned (edenot (Ez regs (VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)) + -20)) (word_to_le_bytes 4 (wa (bv_unsigned (edenot (Ez regs (VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)) + -16)) (word_to_le_bytes 4 (wa (bv_unsigned (edenot (Ez regs (VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304)))))).

#[using="Type"] Theorem mscB_pmscb3 : forall regs m rom n kq wc, mscB_pre regs m n kq wc ->
  scs_denot SEGS m (Ez regs (VALS_mscB n kq wc)) (snd (fst AXF_mscB.RES_pmscb3)) ->
  exists R, msteps SEGS (mkst regs (wa 0xd30d8) m rom) (mkst R (wa 0xd317c) (mscB_mem_pmscb3 m regs n kq wc) rom) /\
    getr R 11 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq) /\ getr R 13 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2))) /\ getr R 14 = wa (((4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2) + (-1 * Z.land (((bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq)) mod 2^64) 4)) + -24) /\ getr R 15 = wa (Z.land (((bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq)) mod 2^64) 4 + 24) /\ getr R 16 = wa 32 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n kq wc P Hsc. destruct (mscB_setup regs m n kq wc P) as [HR HK].
  set (E := Ez regs (VALS_mscB n kq wc)) in *. destruct P as [mscB_R11 mscB_R12 mscB_R13 mscB_R14 mscB_R15 mscB_R16 mscB_rng_n mscB_rng_kq mscB_rng_wc mscB_kr0 mscB_kwr1].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = kq) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = wc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z10 : bv_unsigned (ev E 10) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10)))) by reflexivity.
  destruct (run_sound SEGS 60 [0xd317c; 0xd3160] AXF_mscB.scr_pmscb3 0xd30d8 AXF_mscB.sr_mscB AXF_mscB.kn_mscB 35 _ _ _ E m rom regs AXF_mscB.RES_pmscb3_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mscB.RES_pmscb3 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mscB_mem_pmscb3 m regs n kq wc) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mscB_mem_pmscb3. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.
    all: try (rewrite wa_u; reflexivity).
  - clear Hms.      (* [comment removed for export] *)
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition mscB_mem_pmscb4 (m : word -> option byte) (regs : bvmap 5 word) (n kq wc : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq + 0)) (word_to_le_bytes 4 (wa (bv_unsigned (edenot (Ez regs (VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)) + -4)) (word_to_le_bytes 4 (wa (bv_unsigned (edenot (Ez regs (VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq + 4)) (word_to_le_bytes 4 (wa (bv_unsigned (edenot (Ez regs (VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq + 8)) (word_to_le_bytes 4 (wa (bv_unsigned (edenot (Ez regs (VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)) + -12)) (word_to_le_bytes 4 (wa (bv_unsigned (edenot (Ez regs (VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)) + -8)) (word_to_le_bytes 4 (wa (bv_unsigned (edenot (Ez regs (VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq + 12)) (word_to_le_bytes 4 (wa (bv_unsigned (edenot (Ez regs (VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq + 16)) (word_to_le_bytes 4 (wa (bv_unsigned (edenot (Ez regs (VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq + 20)) (word_to_le_bytes 4 (wa (bv_unsigned (edenot (Ez regs (VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq + 24)) (word_to_le_bytes 4 (wa (bv_unsigned (edenot (Ez regs (VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)) + -28)) (word_to_le_bytes 4 (wa (bv_unsigned (edenot (Ez regs (VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)) + -24)) (word_to_le_bytes 4 (wa (bv_unsigned (edenot (Ez regs (VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)) + -20)) (word_to_le_bytes 4 (wa (bv_unsigned (edenot (Ez regs (VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)) + -16)) (word_to_le_bytes 4 (wa (bv_unsigned (edenot (Ez regs (VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304)))))).

#[using="Type"] Theorem mscB_pmscb4 : forall regs m rom n kq wc, mscB_pre regs m n kq wc ->
  scs_denot SEGS m (Ez regs (VALS_mscB n kq wc)) (snd (fst AXF_mscB.RES_pmscb4)) ->
  exists R, msteps SEGS (mkst regs (wa 0xd30d8) m rom) (mkst R (wa 0xd3160) (mscB_mem_pmscb4 m regs n kq wc) rom) /\
    getr R 11 = wa ((bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (kq + Z.land (((bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq)) mod 2^64) 4)) + 24) /\ getr R 12 = wa (bv_unsigned (edenot (Ez regs (VALS_mscB n kq wc)) (EAlu ALU_OR (EMd M_MUL (ELit 4294967296) (EMd M_MULHU (EVar 34) (ELit 4311810304))) (EAlu ALU_SRL (EMd M_MUL (ELit 4294967296) (EMd M_MULHU (EVar 34) (ELit 4311810304))) (ELit 32))))) /\ getr R 13 = wa 31 /\ getr R 14 = wa (((4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2) + (-1 * Z.land (((bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq)) mod 2^64) 4)) + -24) /\ getr R 15 = wa (Z.land (((bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + kq)) mod 2^64) 4 + 24) /\ getr R 16 = wa 32 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n kq wc P Hsc. destruct (mscB_setup regs m n kq wc P) as [HR HK].
  set (E := Ez regs (VALS_mscB n kq wc)) in *. destruct P as [mscB_R11 mscB_R12 mscB_R13 mscB_R14 mscB_R15 mscB_R16 mscB_rng_n mscB_rng_kq mscB_rng_wc mscB_kr0 mscB_kwr1].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = kq) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = wc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z10 : bv_unsigned (ev E 10) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10)))) by reflexivity.
  destruct (run_sound SEGS 60 [0xd317c; 0xd3160] AXF_mscB.scr_pmscb4 0xd30d8 AXF_mscB.sr_mscB AXF_mscB.kn_mscB 35 _ _ _ E m rom regs AXF_mscB.RES_pmscb4_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mscB.RES_pmscb4 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mscB_mem_pmscb4 m regs n kq wc) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mscB_mem_pmscb4. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.
    all: try (rewrite wa_u; reflexivity).
  - clear Hms.      (* [comment removed for export] *)
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MSCB.
End AXF_mscBz.

Module AXF_mscl.
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

Definition e_blk := EVar 32.
Definition e_rem := EVar 33.
Definition e_vc := EVar 34.
Definition sr_mscl := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 11 (e_blk)) 12 (e_vc)) 13 (ELit 31)) 14 (e_rem)).
Definition kn_mscl : list kentry :=
  [ KRange e_blk 1 (2^47);
    KWr (SA e_blk 0) (ELit 32) ].
Definition scr_mscl : scripts := SCR [true] [] [].
Definition ss_mscl := SS 0xd3160 sr_mscl [] kn_mscl 35.
Definition RUN_mscl := sym_exec SEGS 20 true [0xd317c; 0xd3160] scr_mscl ss_mscl [].

Definition scr_pmsclc : scripts := SCR [true] [] [].
Definition RES_pmsclc := Eval vm_compute in sym_exec SEGS 20 true [0xd317c; 0xd3160] scr_pmsclc ss_mscl [].
Lemma RES_pmsclc_ok : sym_exec SEGS 20 true [0xd317c; 0xd3160] scr_pmsclc (SS 0xd3160 sr_mscl [] kn_mscl 35) [] = RES_pmsclc.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmsclx : scripts := SCR [false] [] [].
Definition RES_pmsclx := Eval vm_compute in sym_exec SEGS 20 true [0xd317c; 0xd3160] scr_pmsclx ss_mscl [].
Lemma RES_pmsclx_ok : sym_exec SEGS 20 true [0xd317c; 0xd3160] scr_pmsclx (SS 0xd3160 sr_mscl [] kn_mscl 35) [] = RES_pmsclx.
Proof. vm_compute. reflexivity. Qed.
End AXF_mscl.

Module AXF_msclz.
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

Section MSCL.
Context {fx : FPState}.

Definition VALS_mscl (blk rem vc : Z) : list Z := [blk; rem; vc].

Record mscl_pre (regs : bvmap 5 word) (m : word -> option byte) (blk rem vc : Z) : Prop := {
  mscl_R11 : getr regs 11 = wa blk ;
  mscl_R12 : getr regs 12 = wa vc ;
  mscl_R13 : getr regs 13 = wa 31 ;
  mscl_R14 : getr regs 14 = wa rem ;
  mscl_rng_blk : 1 <= blk <= 2^47 ;
  mscl_rng_rem : 32 <= rem <= 2^32 ;
  mscl_rng_vc : 0 <= vc <= 2^64 - 1 ;
  mscl_kwr1 : forall d k, 0 <= d -> d + Z.of_nat k <= 32 -> store_ok SEGS m (wa (blk + 0 + d)) k = true
}.


#[using="Type"] Lemma mscl_setup : forall regs m blk rem vc, mscl_pre regs m blk rem vc ->
  regs_ok (Ez regs (VALS_mscl blk rem vc)) AXF_mscl.sr_mscl regs /\ know_ok SEGS (Ez regs (VALS_mscl blk rem vc)) m AXF_mscl.kn_mscl.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m blk rem vc P. destruct P as [mscl_R11 mscl_R12 mscl_R13 mscl_R14 mscl_rng_blk mscl_rng_rem mscl_rng_vc mscl_kwr1].
  set (E := Ez regs (VALS_mscl blk rem vc)).
  assert (Z32 : bv_unsigned (ev E 32) = blk) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = rem) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = vc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mscl.sr_mscl.
    apply (regs_ok_pin E _ regs 14); [apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply regs_ok_id|]|]|]|].
    - rewrite mscl_R11. reflexivity.
    - rewrite mscl_R12. reflexivity.
    - rewrite mscl_R13. reflexivity.
    - rewrite mscl_R14. reflexivity. }
  unfold know_ok, AXF_mscl.kn_mscl.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_mscl.e_blk AXF_mscl.e_rem AXF_mscl.e_vc a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range blk _ _ mscl_rng_blk eq_refl eq_refl), ?(mod64_of_range rem _ _ mscl_rng_rem eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply mscl_kwr1]; assumption).
  all: try (clear - mscl_rng_blk mscl_rng_rem mscl_rng_vc; lia).
  all: first [lia].
Qed.


Definition mscl_mem_pmsclc (m : word -> option byte) (regs : bvmap 5 word) (blk rem vc : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (m) (wa (blk + 0)) (word_to_le_bytes 8 (wa vc))) (wa (blk + 8)) (word_to_le_bytes 8 (wa vc))) (wa (blk + 16)) (word_to_le_bytes 8 (wa vc))) (wa (blk + 24)) (word_to_le_bytes 8 (wa vc)).

#[using="Type"] Theorem mscl_pmsclc : forall regs m rom blk rem vc, mscl_pre regs m blk rem vc ->
  scs_denot SEGS m (Ez regs (VALS_mscl blk rem vc)) (snd (fst AXF_mscl.RES_pmsclc)) ->
  exists R, msteps SEGS (mkst regs (wa 0xd3160) m rom) (mkst R (wa 0xd3160) (mscl_mem_pmsclc m regs blk rem vc) rom) /\
    getr R 11 = wa (blk + 32) /\ getr R 12 = wa vc /\ getr R 13 = wa 31 /\ getr R 14 = wa (rem + -32) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom blk rem vc P Hsc. destruct (mscl_setup regs m blk rem vc P) as [HR HK].
  set (E := Ez regs (VALS_mscl blk rem vc)) in *. destruct P as [mscl_R11 mscl_R12 mscl_R13 mscl_R14 mscl_rng_blk mscl_rng_rem mscl_rng_vc mscl_kwr1].
  assert (Z32 : bv_unsigned (ev E 32) = blk) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = rem) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = vc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 20 [0xd317c; 0xd3160] AXF_mscl.scr_pmsclc 0xd3160 AXF_mscl.sr_mscl AXF_mscl.kn_mscl 35 _ _ _ E m rom regs AXF_mscl.RES_pmsclc_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mscl.RES_pmsclc fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mscl_mem_pmsclc m regs blk rem vc) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mscl_mem_pmsclc. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.
    all: try (rewrite wa_u; reflexivity).
  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition mscl_mem_pmsclx (m : word -> option byte) (regs : bvmap 5 word) (blk rem vc : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (m) (wa (blk + 0)) (word_to_le_bytes 8 (wa vc))) (wa (blk + 8)) (word_to_le_bytes 8 (wa vc))) (wa (blk + 16)) (word_to_le_bytes 8 (wa vc))) (wa (blk + 24)) (word_to_le_bytes 8 (wa vc)).

#[using="Type"] Theorem mscl_pmsclx : forall regs m rom blk rem vc, mscl_pre regs m blk rem vc ->
  scs_denot SEGS m (Ez regs (VALS_mscl blk rem vc)) (snd (fst AXF_mscl.RES_pmsclx)) ->
  exists R, msteps SEGS (mkst regs (wa 0xd3160) m rom) (mkst R (wa 0xd317c) (mscl_mem_pmsclx m regs blk rem vc) rom) /\
    getr R 11 = wa (blk + 32) /\ getr R 12 = wa vc /\ getr R 13 = wa 31 /\ getr R 14 = wa (rem + -32) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom blk rem vc P Hsc. destruct (mscl_setup regs m blk rem vc P) as [HR HK].
  set (E := Ez regs (VALS_mscl blk rem vc)) in *. destruct P as [mscl_R11 mscl_R12 mscl_R13 mscl_R14 mscl_rng_blk mscl_rng_rem mscl_rng_vc mscl_kwr1].
  assert (Z32 : bv_unsigned (ev E 32) = blk) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = rem) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = vc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 20 [0xd317c; 0xd3160] AXF_mscl.scr_pmsclx 0xd3160 AXF_mscl.sr_mscl AXF_mscl.kn_mscl 35 _ _ _ E m rom regs AXF_mscl.RES_pmsclx_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mscl.RES_pmsclx fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mscl_mem_pmsclx m regs blk rem vc) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mscl_mem_pmsclx. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.
    all: try (rewrite wa_u; reflexivity).
  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MSCL.
End AXF_msclz.

Module AXF_msl.
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

Definition e_blk := EVar 32.
Definition e_rem := EVar 33.
Definition sr_msl := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 11 (e_blk)) 12 (ELit 0)) 13 (ELit 31)) 14 (e_rem)).
Definition kn_msl : list kentry :=
  [ KRange e_blk 1 (2^47);
    KWr (SA e_blk 0) (ELit 32) ].
Definition scr_msl : scripts := SCR [true] [] [].
Definition ss_msl := SS 0xd3160 sr_msl [] kn_msl 34.
Definition RUN_msl := sym_exec SEGS 20 true [0xd317c; 0xd3160] scr_msl ss_msl [].

Definition scr_pmslc : scripts := SCR [true] [] [].
Definition RES_pmslc := Eval vm_compute in sym_exec SEGS 20 true [0xd317c; 0xd3160] scr_pmslc ss_msl [].
Lemma RES_pmslc_ok : sym_exec SEGS 20 true [0xd317c; 0xd3160] scr_pmslc (SS 0xd3160 sr_msl [] kn_msl 34) [] = RES_pmslc.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmslx : scripts := SCR [false] [] [].
Definition RES_pmslx := Eval vm_compute in sym_exec SEGS 20 true [0xd317c; 0xd3160] scr_pmslx ss_msl [].
Lemma RES_pmslx_ok : sym_exec SEGS 20 true [0xd317c; 0xd3160] scr_pmslx (SS 0xd3160 sr_msl [] kn_msl 34) [] = RES_pmslx.
Proof. vm_compute. reflexivity. Qed.
End AXF_msl.

Module AXF_mslz.
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

Section MSL.
Context {fx : FPState}.

Definition VALS_msl (blk rem : Z) : list Z := [blk; rem].

Record msl_pre (regs : bvmap 5 word) (m : word -> option byte) (blk rem : Z) : Prop := {
  msl_R11 : getr regs 11 = wa blk ;
  msl_R12 : getr regs 12 = wa 0 ;
  msl_R13 : getr regs 13 = wa 31 ;
  msl_R14 : getr regs 14 = wa rem ;
  msl_rng_blk : 1 <= blk <= 2^47 ;
  msl_rng_rem : 32 <= rem <= 2^32 ;
  msl_kwr1 : forall d k, 0 <= d -> d + Z.of_nat k <= 32 -> store_ok SEGS m (wa (blk + 0 + d)) k = true
}.


#[using="Type"] Lemma msl_setup : forall regs m blk rem, msl_pre regs m blk rem ->
  regs_ok (Ez regs (VALS_msl blk rem)) AXF_msl.sr_msl regs /\ know_ok SEGS (Ez regs (VALS_msl blk rem)) m AXF_msl.kn_msl.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m blk rem P. destruct P as [msl_R11 msl_R12 msl_R13 msl_R14 msl_rng_blk msl_rng_rem msl_kwr1].
  set (E := Ez regs (VALS_msl blk rem)).
  assert (Z32 : bv_unsigned (ev E 32) = blk) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = rem) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_msl.sr_msl.
    apply (regs_ok_pin E _ regs 14); [apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply regs_ok_id|]|]|]|].
    - rewrite msl_R11. reflexivity.
    - rewrite msl_R12. reflexivity.
    - rewrite msl_R13. reflexivity.
    - rewrite msl_R14. reflexivity. }
  unfold know_ok, AXF_msl.kn_msl.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_msl.e_blk AXF_msl.e_rem a_base a_off].
  all: rewrite ?Z32, ?Z33.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range blk _ _ msl_rng_blk eq_refl eq_refl), ?(mod64_of_range rem _ _ msl_rng_rem eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply msl_kwr1]; assumption).
  all: try (clear - msl_rng_blk msl_rng_rem; lia).
  all: first [lia].
Qed.


Definition msl_mem_pmslc (m : word -> option byte) (regs : bvmap 5 word) (blk rem : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (m) (wa (blk + 0)) (word_to_le_bytes 8 (wa 0))) (wa (blk + 8)) (word_to_le_bytes 8 (wa 0))) (wa (blk + 16)) (word_to_le_bytes 8 (wa 0))) (wa (blk + 24)) (word_to_le_bytes 8 (wa 0)).

#[using="Type"] Theorem msl_pmslc : forall regs m rom blk rem, msl_pre regs m blk rem ->
  scs_denot SEGS m (Ez regs (VALS_msl blk rem)) (snd (fst AXF_msl.RES_pmslc)) ->
  exists R, msteps SEGS (mkst regs (wa 0xd3160) m rom) (mkst R (wa 0xd3160) (msl_mem_pmslc m regs blk rem) rom) /\
    getr R 11 = wa (blk + 32) /\ getr R 12 = wa 0 /\ getr R 13 = wa 31 /\ getr R 14 = wa (rem + -32) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom blk rem P Hsc. destruct (msl_setup regs m blk rem P) as [HR HK].
  set (E := Ez regs (VALS_msl blk rem)) in *. destruct P as [msl_R11 msl_R12 msl_R13 msl_R14 msl_rng_blk msl_rng_rem msl_kwr1].
  assert (Z32 : bv_unsigned (ev E 32) = blk) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = rem) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 20 [0xd317c; 0xd3160] AXF_msl.scr_pmslc 0xd3160 AXF_msl.sr_msl AXF_msl.kn_msl 34 _ _ _ E m rom regs AXF_msl.RES_pmslc_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_msl.RES_pmslc fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (msl_mem_pmslc m regs blk rem) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold msl_mem_pmslc. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition msl_mem_pmslx (m : word -> option byte) (regs : bvmap 5 word) (blk rem : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (m) (wa (blk + 0)) (word_to_le_bytes 8 (wa 0))) (wa (blk + 8)) (word_to_le_bytes 8 (wa 0))) (wa (blk + 16)) (word_to_le_bytes 8 (wa 0))) (wa (blk + 24)) (word_to_le_bytes 8 (wa 0)).

#[using="Type"] Theorem msl_pmslx : forall regs m rom blk rem, msl_pre regs m blk rem ->
  scs_denot SEGS m (Ez regs (VALS_msl blk rem)) (snd (fst AXF_msl.RES_pmslx)) ->
  exists R, msteps SEGS (mkst regs (wa 0xd3160) m rom) (mkst R (wa 0xd317c) (msl_mem_pmslx m regs blk rem) rom) /\
    getr R 11 = wa (blk + 32) /\ getr R 12 = wa 0 /\ getr R 13 = wa 31 /\ getr R 14 = wa (rem + -32) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom blk rem P Hsc. destruct (msl_setup regs m blk rem P) as [HR HK].
  set (E := Ez regs (VALS_msl blk rem)) in *. destruct P as [msl_R11 msl_R12 msl_R13 msl_R14 msl_rng_blk msl_rng_rem msl_kwr1].
  assert (Z32 : bv_unsigned (ev E 32) = blk) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = rem) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 20 [0xd317c; 0xd3160] AXF_msl.scr_pmslx 0xd3160 AXF_msl.sr_msl AXF_msl.kn_msl 34 _ _ _ E m rom regs AXF_msl.RES_pmslx_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_msl.RES_pmslx fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (msl_mem_pmslx m regs blk rem) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold msl_mem_pmslx. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MSL.
End AXF_mslz.

Module AXG_ms.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require Import AXG_put AXG_put2.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Ltac scgo := repeat (first [apply Forall_nil | apply Forall_cons]).
Ltac zat := repeat match goal with |- context [bv_unsigned (ev (Ez ?R ?V) ?n)] =>
              let v := eval cbn [nth Nat.sub AXF_ms0z.VALS_ms0 AXF_msAz.VALS_msA AXF_msBz.VALS_msB AXF_mslz.VALS_msl] in (nth (n - 32) V 0) in
              rewrite (zatom R V n v eq_refl eq_refl) by lia end.
Ltac bfin := first [ reflexivity | (apply negb_true_iff; first [apply Z.ltb_ge | apply Z.eqb_neq]; lia)
                   | (apply negb_false_iff; first [apply Z.ltb_lt | apply Z.eqb_eq]; lia)
                   | (apply Z.ltb_lt; lia) | (apply Z.ltb_ge; lia) | (apply Z.eqb_eq; lia) | (apply Z.eqb_neq; lia) ].

(* [comment removed for export] *)
Lemma zero_bytes_nth : forall w j, nth j (Z_to_le_bytes w 0) (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof.
  induction w as [|w IH]; intros j; [destruct j; reflexivity|]. cbn [Z_to_le_bytes]. destruct j as [|j]; [reflexivity|].
  cbn [nth]. rewrite Z.shiftr_0_l. apply IH.
Qed.
Lemma wb0_hit : forall m a w x, 0 <= a -> a + Z.of_nat w <= 2^64 -> a <= x < a + Z.of_nat w ->
  wbytes m (wa a) (word_to_le_bytes w (wa 0)) (wa x) = Some (Z_to_bv 8 0).
Proof.
  intros m a w x Ha Hw Hx.
  assert (Hl : length (word_to_le_bytes w (wa 0)) = w) by (unfold word_to_le_bytes; apply length_Z_to_le_bytes).
  replace (wa x) with (Z_to_bv 64 (bv_unsigned (wa a) + Z.of_nat (Z.to_nat (x - a)))) by (rewrite u_wa_small by lia; f_equal; lia).
  rewrite wbytes_nth; [| rewrite u_wa_small by lia; rewrite Hl; lia | rewrite Hl; lia].
  f_equal. unfold word_to_le_bytes. rewrite u_wa_small by lia.
  apply zero_bytes_nth.
Qed.

(* [comment removed for export] *)
Lemma land4 : forall x, Z.land x 4 = 0 \/ Z.land x 4 = 4.
Proof.
  intros x. replace (Z.land x 4) with (Z.land (Z.land x 7) 4) by (rewrite <- Z.land_assoc; reflexivity).
  replace (Z.land x 7) with (x mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
  assert (Hr : 0 <= x mod 8 < 8) by (apply Z.mod_pos_bound; lia).
  destruct (x mod 8) as [|p|p] eqn:E; [left; reflexivity | | lia].
  assert (Hp : (p < 8)%positive) by lia.
  repeat (destruct p as [p|p|]; try (cbn; tauto); try lia).
Qed.

(* [comment removed for export] *)
Section SCA.
Context {fx : FPState}.
Variables (R : bvmap 5 word) (m : word -> option byte) (s n kq blk rem : Z).
Hypothesis Hs10 : bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10))) = s.
Hypothesis Hsr : 1 <= s <= 2^47.
Hypothesis Hnr : 0 <= n <= 2^32.
Hypothesis Hsn : s + n <= 2^47.
Hypothesis HWR : forall d k, 0 <= d -> d + Z.of_nat k <= n -> store_ok SEGS m (wa (s + d)) k = true.

Ltac reg10 := change (bv_unsigned (ev (Ez R ?V) 10)) with (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10)))); rewrite Hs10.
Ltac scone :=
  first [ (apply sc_br_z; first [rewrite br_geu_z | rewrite br_ltu_z | rewrite br_eq_z | rewrite br_ne_z];
           cbn [zeval edenot]; zat; rewrite ?(Z.mod_small _ (2^64)) by lia; bfin)
        | (cbn [sc_denot]; rewrite adenot_z; cbn [zeval edenot a_base a_off]; zat; try reg10;
           lazymatch goal with |- store_ok _ _ (wa ?a) ?w = true => replace a with (s + (a - s)) by lia; apply HWR; [lia | cbn; lia] end)
        | (cbn [sc_denot]; unfold flat, estart, elenZ; cbn [a_base a_off]; rewrite ?zeval_sound, ?u_wa; cbn [zeval edenot]; zat; try reg10;
           rewrite ?(Z.mod_small _ (2^64)) by lia; lia) ].

#[using="s Hs10 Hsr Hnr Hsn HWR"] Lemma sc_a1 : 1 <= n <= 2 -> scs_denot SEGS m (Ez R (AXF_msAz.VALS_msA n)) (snd (fst AXF_msA.RES_pmsa1)).
Proof. LiaFast.lf_pins (fun (s Hs10 Hsr Hnr Hsn HWR : LiaFast.U) => LiaFast.u0). intros H. cbn [AXF_msA.RES_pmsa1 fst snd]. scgo; scone. Qed.
#[using="s Hs10 Hsr Hnr Hsn HWR"] Lemma sc_a2 : 3 <= n <= 6 -> scs_denot SEGS m (Ez R (AXF_msAz.VALS_msA n)) (snd (fst AXF_msA.RES_pmsa2)).
Proof. LiaFast.lf_pins (fun (s Hs10 Hsr Hnr Hsn HWR : LiaFast.U) => LiaFast.u0). intros H. cbn [AXF_msA.RES_pmsa2 fst snd]. scgo; scone. Qed.
#[using="s Hs10 Hsr Hnr Hsn HWR"] Lemma sc_a3 : 7 <= n <= 8 -> scs_denot SEGS m (Ez R (AXF_msAz.VALS_msA n)) (snd (fst AXF_msA.RES_pmsa3)).
Proof. LiaFast.lf_pins (fun (s Hs10 Hsr Hnr Hsn HWR : LiaFast.U) => LiaFast.u0). intros H. cbn [AXF_msA.RES_pmsa3 fst snd]. scgo; scone. Qed.
#[using="s Hs10 Hsr Hnr Hsn HWR"] Lemma sc_a9 : 9 <= n -> scs_denot SEGS m (Ez R (AXF_msAz.VALS_msA n)) (snd (fst AXF_msA.RES_pmsa9)).
Proof. LiaFast.lf_pins (fun (s Hs10 Hsr Hnr Hsn HWR : LiaFast.U) => LiaFast.u0). intros H. cbn [AXF_msA.RES_pmsa9 fst snd]. scgo; scone. Qed.
End SCA.

Section SCB.
Context {fx : FPState}.
Variables (R : bvmap 5 word) (m : word -> option byte) (s n kq : Z).
Hypothesis Hs10 : bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10))) = s.
Hypothesis Hsr : 1 <= s <= 2^47.
Hypothesis Hnr : 9 <= n <= 2^32.
Hypothesis Hkq : 0 <= kq <= 3.
Hypothesis Hsn : s + n <= 2^47.
Hypothesis HWR : forall d k, 0 <= d -> d + Z.of_nat k <= n -> store_ok SEGS m (wa (s + d)) k = true.

Ltac reg10 := change (bv_unsigned (ev (Ez R ?V) 10)) with (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10)))); rewrite Hs10.
(* [comment removed for export] *)
#[using="Hs10"] Lemma zq_S : zeval (Ez R (AXF_msBz.VALS_msB n kq)) (EVar 10) = s.
Proof. LiaFast.lf_pins (fun (Hs10 : LiaFast.U) => LiaFast.u0). cbn [zeval edenot]. reg10. reflexivity. Qed.
#[using="Hs10 Hkq"] Lemma zq_SK : zeval (Ez R (AXF_msBz.VALS_msB n kq)) (EAlu ALU_ADD (EVar 10) (EVar 33)) = s + kq.
Proof. LiaFast.lf_pins (fun (Hs10 Hkq : LiaFast.U) => LiaFast.u0). cbn [zeval edenot]. zat. reg10. reflexivity. Qed.
#[using="Hnr Hkq"] Lemma zq_N4 : zeval (Ez R (AXF_msBz.VALS_msB n kq)) (EMd M_MUL (ELit 4) (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit (-1)) (EVar 33))) (ELit 2))) =
  4 * ((n - kq) / 4).
Proof. LiaFast.lf_pins (fun (Hnr Hkq : LiaFast.U) => LiaFast.u0).
  cbn [zeval edenot]. zat. change (2 mod 64) with 2. rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^2) with 4.
  replace (n + -1 * kq) with (n - kq) by lia. reflexivity.
Qed.
#[using="Hs10 Hnr Hkq"] Lemma zq_KN : zeval (Ez R (AXF_msBz.VALS_msB n kq))
    (EAlu ALU_ADD (EVar 10) (EAlu ALU_ADD (EVar 33) (EMd M_MUL (ELit 4) (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit (-1)) (EVar 33))) (ELit 2))))) =
  s + (kq + 4 * ((n - kq) / 4)).
Proof. LiaFast.lf_pins (fun (Hs10 Hnr Hkq : LiaFast.U) => LiaFast.u0).
  change (zeval (Ez R (AXF_msBz.VALS_msB n kq))
    (EAlu ALU_ADD (EVar 10) (EAlu ALU_ADD (EVar 33) (EMd M_MUL (ELit 4) (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit (-1)) (EVar 33))) (ELit 2))))))
    with (zeval (Ez R (AXF_msBz.VALS_msB n kq)) (EVar 10) + (zeval (Ez R (AXF_msBz.VALS_msB n kq)) (EVar 33) +
          zeval (Ez R (AXF_msBz.VALS_msB n kq)) (EMd M_MUL (ELit 4) (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit (-1)) (EVar 33))) (ELit 2))))).
  rewrite zq_S, zq_N4. cbn [zeval edenot]. zat. reflexivity.
Qed.
#[using="Hs10 Hsr Hnr Hkq Hsn"] Lemma zq_REM : zeval (Ez R (AXF_msBz.VALS_msB n kq))
    (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 4) (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit (-1)) (EVar 33))) (ELit 2)))
                                (EMd M_MUL (ELit (-1)) (EAlu ALU_AND (EAlu ALU_ADD (EVar 10) (EVar 33)) (ELit 4)))) (ELit (-24))) =
  4 * ((n - kq) / 4) - Z.land (s + kq) 4 - 24.
Proof. LiaFast.lf_pins (fun (Hs10 Hsr Hnr Hkq Hsn : LiaFast.U) => LiaFast.u0).
  change (zeval (Ez R (AXF_msBz.VALS_msB n kq))
    (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 4) (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit (-1)) (EVar 33))) (ELit 2)))
                                (EMd M_MUL (ELit (-1)) (EAlu ALU_AND (EAlu ALU_ADD (EVar 10) (EVar 33)) (ELit 4)))) (ELit (-24))))
    with (zeval (Ez R (AXF_msBz.VALS_msB n kq)) (EMd M_MUL (ELit 4) (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit (-1)) (EVar 33))) (ELit 2)))
          + -1 * Z.land (zeval (Ez R (AXF_msBz.VALS_msB n kq)) (EAlu ALU_ADD (EVar 10) (EVar 33)) mod 2^64) (4 mod 2^64) + -24).
  rewrite zq_N4, zq_SK. change (4 mod 2^64) with 4. rewrite (Z.mod_small (s + kq)) by lia. lia.
Qed.
#[using="HWR"] Lemma HWR' : forall a w, s <= a -> a + Z.of_nat w <= s + n -> store_ok SEGS m (wa a) w = true.
Proof. LiaFast.lf_pins (fun (HWR : LiaFast.U) => LiaFast.u0). intros a w H1 H2. replace a with (s + (a - s)) by lia. apply HWR; lia. Qed.
Ltac zrw := rewrite ?zq_KN, ?zq_REM, ?zq_N4, ?zq_SK.
Ltac scone :=
  first [ (apply sc_br_z; first [rewrite br_geu_z | rewrite br_ltu_z | rewrite br_eq_z | rewrite br_ne_z]; zrw; cbn [zeval];
           rewrite ?(Z.mod_small _ (2^64)) by (pose proof (land4 (s + kq)); pose proof (Z.div_pos (n - kq) 4 ltac:(lia) ltac:(lia)); lia); bfin)
        | (cbn [sc_denot]; rewrite adenot_z; cbn [a_base a_off]; zrw; try (match goal with H : Z.land _ 4 = 0 \/ _ |- _ => clear H end); apply HWR'; cbn; lia)
        | (cbn [sc_denot]; unfold flat, estart, elenZ; cbn [a_base a_off]; rewrite ?zeval_sound, ?u_wa; zrw; cbn [zeval]; try (match goal with H : Z.land _ 4 = 0 \/ _ |- _ => clear H end);
           rewrite ?(Z.mod_small _ (2^64)) by lia; lia) ].

#[using="s Hs10 Hsr Hnr Hkq Hsn HWR"] Lemma sc_b1 : 4 * ((n - kq) / 4) < 9 -> scs_denot SEGS m (Ez R (AXF_msBz.VALS_msB n kq)) (snd (fst AXF_msB.RES_pmsb1)).
Proof. LiaFast.lf_pins (fun (s Hs10 Hsr Hnr Hkq Hsn HWR : LiaFast.U) => LiaFast.u0). intros H. pose proof (Z.div_mod (n - kq) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (n - kq) 4 ltac:(lia)).
  cbn [AXF_msB.RES_pmsb1 fst snd]. scgo; scone. Qed.
#[using="s Hs10 Hsr Hnr Hkq Hsn HWR"] Lemma sc_b2 : 9 <= 4 * ((n - kq) / 4) < 25 -> scs_denot SEGS m (Ez R (AXF_msBz.VALS_msB n kq)) (snd (fst AXF_msB.RES_pmsb2)).
Proof. LiaFast.lf_pins (fun (s Hs10 Hsr Hnr Hkq Hsn HWR : LiaFast.U) => LiaFast.u0). intros H. pose proof (Z.div_mod (n - kq) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (n - kq) 4 ltac:(lia)).
  cbn [AXF_msB.RES_pmsb2 fst snd]. scgo; scone. Qed.
#[using="Hs10 Hsr Hnr Hkq Hsn HWR"] Lemma sc_b3 : 25 <= 4 * ((n - kq) / 4) -> (Z.land (s + kq) 4 = 0 \/ Z.land (s + kq) 4 = 4) ->
  4 * ((n - kq) / 4) - 24 - Z.land (s + kq) 4 < 32 -> scs_denot SEGS m (Ez R (AXF_msBz.VALS_msB n kq)) (snd (fst AXF_msB.RES_pmsb3)).
Proof. LiaFast.lf_pins (fun (Hs10 Hsr Hnr Hkq Hsn HWR : LiaFast.U) => LiaFast.u0). intros H1 H2 H3. pose proof (Z.div_mod (n - kq) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (n - kq) 4 ltac:(lia)).
  cbn [AXF_msB.RES_pmsb3 fst snd]. scgo; scone. Qed.
#[using="Hs10 Hsr Hnr Hkq Hsn HWR"] Lemma sc_b4 : 25 <= 4 * ((n - kq) / 4) -> (Z.land (s + kq) 4 = 0 \/ Z.land (s + kq) 4 = 4) ->
  32 <= 4 * ((n - kq) / 4) - 24 - Z.land (s + kq) 4 -> scs_denot SEGS m (Ez R (AXF_msBz.VALS_msB n kq)) (snd (fst AXF_msB.RES_pmsb4)).
Proof. LiaFast.lf_pins (fun (Hs10 Hsr Hnr Hkq Hsn HWR : LiaFast.U) => LiaFast.u0). intros H1 H2 H3. pose proof (Z.div_mod (n - kq) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (n - kq) 4 ltac:(lia)).
  cbn [AXF_msB.RES_pmsb4 fst snd]. scgo; scone. Qed.
End SCB.

Section SCL.
Context {fx : FPState}.
Variables (R : bvmap 5 word) (m : word -> option byte) (blk rem : Z).
Hypothesis Hbr : 1 <= blk <= 2^47.
Hypothesis Hrr : 32 <= rem <= 2^32.
Hypothesis Hbn : blk + rem <= 2^47.
Ltac scone :=
  first [ (apply sc_br_z; first [rewrite br_geu_z | rewrite br_ltu_z | rewrite br_eq_z | rewrite br_ne_z];
           cbn [zeval edenot]; zat; rewrite ?(Z.mod_small _ (2^64)) by lia; bfin)
        | (cbn [sc_denot]; unfold flat, estart, elenZ; cbn [a_base a_off]; rewrite ?zeval_sound, ?u_wa; cbn [zeval edenot]; zat;
           rewrite ?(Z.mod_small _ (2^64)) by lia; lia) ].
#[using="Hrr"] Lemma sc_lc : 64 <= rem -> scs_denot SEGS m (Ez R (AXF_mslz.VALS_msl blk rem)) (snd (fst AXF_msl.RES_pmslc)).
Proof. LiaFast.lf_pins (fun (Hrr : LiaFast.U) => LiaFast.u0). intros H. cbn [AXF_msl.RES_pmslc fst snd]. scgo; scone. Qed.
#[using="Hrr"] Lemma sc_lx : rem < 64 -> scs_denot SEGS m (Ez R (AXF_mslz.VALS_msl blk rem)) (snd (fst AXF_msl.RES_pmslx)).
Proof. LiaFast.lf_pins (fun (Hrr : LiaFast.U) => LiaFast.u0). intros H. cbn [AXF_msl.RES_pmslx fst snd]. scgo; scone. Qed.
End SCL.

Lemma sc_0 : forall {fx : FPState} R m, scs_denot SEGS m (Ez R (AXF_ms0z.VALS_ms0 0)) (snd (fst AXF_ms0.RES_pms0)).
Proof. intros fx R m. cbn [AXF_ms0.RES_pms0 fst snd]. scgo. Qed.

Lemma grows_wb : forall m m' a bs, mem_grows m m' -> mem_grows m (wbytes m' a bs).
Proof. intros m m' a bs H. eapply mem_grows_trans; [exact H | apply wbytes_grows]. Qed.
Ltac growsc := repeat apply grows_wb; apply mem_grows_refl.

(* [comment removed for export] *)
Lemma blk_zero : forall m blk x, 1 <= blk -> blk + 32 <= 2^47 ->
  wbytes (wbytes (wbytes (wbytes m (wa (blk + 0)) (word_to_le_bytes 8 (wa 0))) (wa (blk + 8)) (word_to_le_bytes 8 (wa 0)))
         (wa (blk + 16)) (word_to_le_bytes 8 (wa 0))) (wa (blk + 24)) (word_to_le_bytes 8 (wa 0)) (wa x) =
  if (Z.leb blk x && Z.ltb x (blk + 32))%bool then Some (Z_to_bv 8 0) else if (Z.leb 0 x && Z.ltb x (2^64))%bool then m (wa x) else
  wbytes (wbytes (wbytes (wbytes m (wa (blk + 0)) (word_to_le_bytes 8 (wa 0))) (wa (blk + 8)) (word_to_le_bytes 8 (wa 0)))
         (wa (blk + 16)) (word_to_le_bytes 8 (wa 0))) (wa (blk + 24)) (word_to_le_bytes 8 (wa 0)) (wa x).
Proof.
  intros m blk x H1 H2.
  destruct (Z.leb blk x && Z.ltb x (blk + 32))%bool eqn:Hin.
  - apply andb_prop in Hin as [Ha Hb]. apply Z.leb_le in Ha. apply Z.ltb_lt in Hb.
    assert (Lw : length (word_to_le_bytes 8 (wa 0)) = 8%nat) by reflexivity.
    destruct (Z_lt_ge_dec x (blk + 24)) as [X1|X1]; [|apply wb0_hit; lia].
    rewrite wb_other by (rewrite ?Lw; cbn; lia).
    destruct (Z_lt_ge_dec x (blk + 16)) as [X2|X2]; [|apply wb0_hit; lia].
    rewrite wb_other by (rewrite ?Lw; cbn; lia).
    destruct (Z_lt_ge_dec x (blk + 8)) as [X3|X3]; [|apply wb0_hit; lia].
    rewrite wb_other by (rewrite ?Lw; cbn; lia). apply wb0_hit; lia.
  - destruct (Z.leb 0 x && Z.ltb x (2^64))%bool eqn:Hx; [|reflexivity].
    apply andb_prop in Hx as [Ha Hb]. apply Z.leb_le in Ha. apply Z.ltb_lt in Hb.
    assert (Hout : x < blk \/ blk + 32 <= x) by (apply andb_false_iff in Hin as [X|X]; [apply Z.leb_gt in X | apply Z.ltb_ge in X]; lia).
    assert (Lw : length (word_to_le_bytes 8 (wa 0)) = 8%nat) by reflexivity.
    rewrite !wb_other by (rewrite ?Lw; cbn; lia). reflexivity.
Qed.

Lemma in_blk_true : forall blk x, blk <= x < blk + 32 -> (Z.leb blk x && Z.ltb x (blk + 32))%bool = true.
Proof. intros blk x H. apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia. Qed.
Lemma in_blk_false : forall blk x, ~ (blk <= x < blk + 32) -> (Z.leb blk x && Z.ltb x (blk + 32))%bool = false.
Proof. intros blk x H. destruct (Z.leb blk x) eqn:E1; [|reflexivity]. apply Z.leb_le in E1. apply Z.ltb_ge. lia. Qed.
Lemma in_rng_true : forall x, 0 <= x < 2^64 -> (Z.leb 0 x && Z.ltb x (2^64))%bool = true.
Proof. intros x H. apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia. Qed.

Definition KLOOP : list nat := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 12; 13; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.

Theorem ms_loop : forall {fx : FPState} rom (t : nat) R mm blk rem, rem / 32 = Z.of_nat t -> 32 <= rem <= 2^32 -> 1 <= blk -> blk + rem <= 2^47 ->
  getr R 11 = wa blk -> getr R 12 = wa 0 -> getr R 13 = wa 31 -> getr R 14 = wa rem ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= rem -> store_ok SEGS mm (wa (blk + d)) k = true) ->
  exists R' mm', msteps SEGS (mkst R (wa 0xd3160) mm rom) (mkst R' (wa 0xd317c) mm' rom) /\
    (forall k, In k KLOOP -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) /\
    (forall x, blk <= x < blk + 32 * (rem / 32) -> mm' (wa x) = Some (Z_to_bv 8 0)) /\
    (forall x, 0 <= x < 2^64 -> ~ (blk <= x < blk + 32 * (rem / 32)) -> mm' (wa x) = mm (wa x)) /\ mem_grows mm mm'.
Proof.
  intros fx rom t. induction t as [|t IH]; intros R mm blk rem Ht Hr Hb Hbr R11 R12 R13 R14 HW.
  { exfalso. pose proof (Z.div_le_lower_bound rem 32 1 ltac:(lia) ltac:(lia)). lia. }
  assert (P : AXF_mslz.msl_pre R mm blk rem).
  { constructor; try assumption; try lia. intros d k Hd Hk. replace (blk + 0 + d) with (blk + d) by lia. apply HW; lia. }
  destruct (Z_lt_ge_dec rem 64) as [Hx|Hc].
  - (* [comment removed for export] *)
    destruct (AXF_mslz.msl_pmslx R mm rom blk rem P (sc_lx R mm blk rem ltac:(lia) Hx)) as (R' & Hms & E11 & E12 & E13 & E14 & KK).
    exists R', (AXF_mslz.msl_mem_pmslx mm R blk rem). split; [exact Hms|].
    assert (Eq1 : rem / 32 = 1) by (symmetry; apply Z.div_unique with (rem - 32); lia).
    rewrite Eq1. split; [|split; [|split]].
    + intros k Hk. cbn [KLOOP In] in Hk.
      repeat (destruct Hk as [<-|Hk]; [first [solve [apply KK; cbn [In]; memb] | (regzH E12; regzH R12; rewrite E12, R12; reflexivity) | (regzH E13; regzH R13; rewrite E13, R13; reflexivity)]|]). destruct Hk.
    + intros x Hx'. unfold AXF_mslz.msl_mem_pmslx. rewrite blk_zero by lia. rewrite (in_blk_true blk x) by lia. reflexivity.
    + intros x Hx' Hn. unfold AXF_mslz.msl_mem_pmslx. rewrite blk_zero by lia.
      rewrite (in_blk_false blk x) by lia. rewrite (in_rng_true x) by lia. reflexivity.
    + unfold AXF_mslz.msl_mem_pmslx. growsc.
  - (* [comment removed for export] *)
    destruct (AXF_mslz.msl_pmslc R mm rom blk rem P (sc_lc R mm blk rem ltac:(lia) ltac:(lia))) as (R1 & Hms1 & E11 & E12 & E13 & E14 & KK1).
    set (mm1 := AXF_mslz.msl_mem_pmslc mm R blk rem) in *.
    assert (Ht' : (rem - 32) / 32 = Z.of_nat t).
    { replace rem with ((rem - 32) + 1 * 32) in Ht by lia. rewrite Z.div_add in Ht by lia. lia. }
    assert (G1 : mem_grows mm mm1) by (unfold mm1, AXF_mslz.msl_mem_pmslc; growsc).
    destruct (IH R1 mm1 (blk + 32) (rem - 32) Ht' ltac:(lia) ltac:(lia) ltac:(lia) E11 E12 E13 ltac:(rewrite E14; f_equal; lia))
      as (R' & mm' & Hms' & KK' & Z' & F' & G').
    { intros d k Hd Hk. replace (blk + 32 + d) with (blk + (32 + d)) by lia. apply (store_ok_mono SEGS k mm mm1 _ G1). apply HW; lia. }
    exists R', mm'. split; [exact (msteps_trans SEGS _ _ _ Hms1 Hms')|].
    assert (Eq : rem / 32 = 1 + (rem - 32) / 32) by (replace rem with ((rem - 32) + 1 * 32) at 1 by lia; rewrite Z.div_add by lia; lia).
    split; [|split; [|split]].
    + intros k Hk. rewrite (KK' k Hk). cbn [KLOOP In] in Hk.
      repeat (destruct Hk as [<-|Hk]; [first [solve [apply KK1; cbn [In]; memb] | (regzH E12; regzH R12; rewrite E12, R12; reflexivity) | (regzH E13; regzH R13; rewrite E13, R13; reflexivity)]|]). destruct Hk.
    + intros x Hx. destruct (Z_lt_ge_dec x (blk + 32)) as [X|X].
      * rewrite F' by lia. unfold mm1, AXF_mslz.msl_mem_pmslc. rewrite blk_zero by lia. rewrite (in_blk_true blk x) by lia. reflexivity.
      * apply Z'. lia.
    + intros x Hx Hn. rewrite F' by lia. unfold mm1, AXF_mslz.msl_mem_pmslc. rewrite blk_zero by lia.
      rewrite (in_blk_false blk x) by lia. rewrite (in_rng_true x) by lia. reflexivity.
    + exact (mem_grows_trans _ _ _ G1 G').
Qed.
End AXG_ms.

Module AXG_ms2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put AXG_put2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np.AXG_ms.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
Fixpoint zw (m : word -> option byte) (L : list (Z * nat)) : word -> option byte :=
  match L with [] => m | (a, w) :: L' => zw (wbytes m (wa a) (word_to_le_bytes w (wa 0))) L' end.
Fixpoint cov (L : list (Z * nat)) (x : Z) : Prop :=
  match L with [] => False | (a, w) :: L' => (a <= x < a + Z.of_nat w) \/ cov L' x end.
Fixpoint wok (L : list (Z * nat)) (lo hi : Z) : Prop :=
  match L with [] => True | (a, w) :: L' => (lo <= a /\ a + Z.of_nat w <= hi /\ (1 <= w)%nat) /\ wok L' lo hi end.

Lemma cov_dec : forall L x, cov L x \/ ~ cov L x.
Proof.
  induction L as [|[a w] L IH]; intros x; cbn [cov]; [right; tauto|].
  destruct (IH x) as [H|H]; [left; right; exact H|].
  destruct (Z_le_gt_dec a x) as [H1|H1]; [destruct (Z_lt_ge_dec x (a + Z.of_nat w)) as [H2|H2]|].
  - left; left; lia.
  - right; intros [X|X]; [lia | exact (H X)].
  - right; intros [X|X]; [lia | exact (H X)].
Qed.
Lemma wok_cov : forall L lo hi x, wok L lo hi -> cov L x -> lo <= x < hi.
Proof. induction L as [|[a w] L IH]; intros lo hi x Hw Hc; cbn [wok cov] in Hw, Hc; [destruct Hc|]. destruct Hc as [Hc|Hc]; [lia | exact (IH lo hi x (proj2 Hw) Hc)]. Qed.
Lemma wok_mono : forall L lo hi lo' hi', wok L lo hi -> lo' <= lo -> hi <= hi' -> wok L lo' hi'.
Proof. induction L as [|[a w] L IH]; intros lo hi lo' hi' Hw H1 H2; cbn [wok] in *; [exact I|]. split; [lia | exact (IH lo hi lo' hi' (proj2 Hw) H1 H2)]. Qed.
Lemma zw_app : forall L1 L2 m, zw m (L1 ++ L2) = zw (zw m L1) L2.
Proof. induction L1 as [|[a w] L1 IH]; intros L2 m; [reflexivity|]. cbn [app zw]. apply IH. Qed.
Lemma cov_app : forall L1 L2 x, cov (L1 ++ L2) x <-> cov L1 x \/ cov L2 x.
Proof. induction L1 as [|[a w] L1 IH]; intros L2 x; cbn [app cov]; [tauto|]. rewrite IH. tauto. Qed.
Lemma wok_app : forall L1 L2 lo hi, wok L1 lo hi -> wok L2 lo hi -> wok (L1 ++ L2) lo hi.
Proof. induction L1 as [|[a w] L1 IH]; intros L2 lo hi H1 H2; cbn [app wok] in *; [exact H2|]. split; [exact (proj1 H1) | exact (IH L2 lo hi (proj2 H1) H2)]. Qed.
Lemma zw_grows : forall L m, mem_grows m (zw m L).
Proof. induction L as [|[a w] L IH]; intros m; cbn [zw]; [apply mem_grows_refl|]. eapply mem_grows_trans; [apply wbytes_grows | apply IH]. Qed.
Lemma cov_in : forall L a w x, In (a, w) L -> a <= x < a + Z.of_nat w -> cov L x.
Proof.
  induction L as [|[b v] L IH]; intros a w x Hi Hx; cbn [In] in Hi; [destruct Hi|]. cbn [cov].
  destruct Hi as [Hi|Hi]; [injection Hi as -> ->; left; exact Hx | right; exact (IH a w x Hi Hx)].
Qed.

Lemma zw_out : forall L m x, 0 <= x < 2^64 -> wok L 0 (2^64) -> ~ cov L x -> zw m L (wa x) = m (wa x).
Proof.
  induction L as [|[a w] L IH]; intros m x Hx Hw Hc; [reflexivity|]. cbn [zw wok cov] in *.
  rewrite IH by tauto. apply wb_other; rewrite ?length_N_to_le_bytes; lia.
Qed.
Lemma zw_hit : forall L m x, 0 <= x < 2^64 -> wok L 0 (2^64) -> cov L x -> zw m L (wa x) = Some (Z_to_bv 8 0).
Proof.
  induction L as [|[a w] L IH]; intros m x Hx Hw Hc; cbn [cov] in Hc; [destruct Hc|]. cbn [zw wok] in *.
  destruct (cov_dec L x) as [HL|HL]; [exact (IH _ x Hx (proj2 Hw) HL)|].
  destruct Hc as [Hc|Hc]; [|contradiction].
  rewrite zw_out by tauto. apply wb0_hit; lia.
Qed.

(* [comment removed for export] *)
Lemma zw_spec : forall L m s n, 0 <= s -> s + n <= 2^64 -> wok L s (s + n) ->
  (forall x, s <= x < s + n -> cov L x) ->
  (forall x, s <= x < s + n -> zw m L (wa x) = Some (Z_to_bv 8 0)) /\
  (forall x, 0 <= x < 2^64 -> ~ (s <= x < s + n) -> zw m L (wa x) = m (wa x)).
Proof.
  intros L m s n H1 H2 Hw Hc. assert (Hw0 : wok L 0 (2^64)) by (apply (wok_mono L s (s + n)); [exact Hw | lia | lia]).
  split.
  - intros x Hx. apply zw_hit; [lia | exact Hw0 | exact (Hc x Hx)].
  - intros x Hx Hn. apply zw_out; [exact Hx | exact Hw0|]. intros Hc'. apply Hn. exact (wok_cov L s (s + n) x Hw Hc').
Qed.



(* [comment removed for export] *)
Definition La1 (S n : Z) : list (Z * nat) := [(S + 0, 1%nat); (S + n + -1, 1%nat)].
Definition La2 (S n : Z) : list (Z * nat) :=
  [(S + 0, 1%nat); (S + n + -1, 1%nat); (S + 1, 1%nat); (S + 2, 1%nat); (S + n + -3, 1%nat); (S + n + -2, 1%nat)].
Definition L9 (S n : Z) : list (Z * nat) :=
  [(S + 0, 1%nat); (S + n + -1, 1%nat); (S + 1, 1%nat); (S + 2, 1%nat); (S + n + -3, 1%nat); (S + n + -2, 1%nat); (S + 3, 1%nat); (S + n + -4, 1%nat)].
Definition LB1 (S kq KN : Z) : list (Z * nat) := [(S + kq + 0, 4%nat); (S + KN + -4, 4%nat)].
Definition LB2 (S kq KN : Z) : list (Z * nat) :=
  [(S + kq + 0, 4%nat); (S + KN + -4, 4%nat); (S + kq + 4, 4%nat); (S + kq + 8, 4%nat); (S + KN + -12, 4%nat); (S + KN + -8, 4%nat)].
Definition LB3 (S kq KN : Z) : list (Z * nat) :=
  [(S + kq + 0, 4%nat); (S + KN + -4, 4%nat); (S + kq + 4, 4%nat); (S + kq + 8, 4%nat); (S + KN + -12, 4%nat); (S + KN + -8, 4%nat);
   (S + kq + 12, 4%nat); (S + kq + 16, 4%nat); (S + kq + 20, 4%nat); (S + kq + 24, 4%nat);
   (S + KN + -28, 4%nat); (S + KN + -24, 4%nat); (S + KN + -20, 4%nat); (S + KN + -16, 4%nat)].

Section EQS.
Context {fx : FPState}.
Abbreviation S10 R := (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10)))).
Abbreviation KNf n kq := (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)).
#[using="Type"] Lemma eq_a1 : forall m R n, AXF_msAz.msA_mem_pmsa1 m R n = zw m (La1 (S10 R) n).
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma eq_a2 : forall m R n, AXF_msAz.msA_mem_pmsa2 m R n = zw m (La2 (S10 R) n).
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma eq_a3 : forall m R n, AXF_msAz.msA_mem_pmsa3 m R n = zw m (L9 (S10 R) n).
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma eq_a9 : forall m R n, AXF_msAz.msA_mem_pmsa9 m R n = zw m (L9 (S10 R) n).
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma eq_b1 : forall m R n kq, AXF_msBz.msB_mem_pmsb1 m R n kq = zw m (LB1 (S10 R) kq (KNf n kq)).
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma eq_b2 : forall m R n kq, AXF_msBz.msB_mem_pmsb2 m R n kq = zw m (LB2 (S10 R) kq (KNf n kq)).
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma eq_b3 : forall m R n kq, AXF_msBz.msB_mem_pmsb3 m R n kq = zw m (LB3 (S10 R) kq (KNf n kq)).
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma eq_b4 : forall m R n kq, AXF_msBz.msB_mem_pmsb4 m R n kq = zw m (LB3 (S10 R) kq (KNf n kq)).
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
End EQS.

(* [comment removed for export] *)
Ltac pick k := lazymatch k with O => left; reflexivity | Datatypes.S ?k' => right; pick k' end.
Ltac pk k := eapply cov_in; [pick k | lia].
Ltac ltc x c := destruct (Z_lt_ge_dec x c).

Lemma cov_a1 : forall S n x, 1 <= n <= 2 -> S <= x < S + n -> cov (La1 S n) x.
Proof. intros S n x Hn Hx. unfold La1. destruct (Z.eq_dec x S); [pk 0%nat | pk 1%nat]. Qed.
Lemma cov_a2 : forall S n x, 3 <= n <= 6 -> S <= x < S + n -> cov (La2 S n) x.
Proof.
  intros S n x Hn Hx. unfold La2. ltc x (S + 3).
  - ltc x (S + 1); [pk 0%nat|]. ltc x (S + 2); [pk 2%nat | pk 3%nat].
  - ltc x (S + n + -2); [pk 4%nat|]. ltc x (S + n + -1); [pk 5%nat | pk 1%nat].
Qed.
(* [comment removed for export] *)
Lemma cov_hd : forall S n x L', 7 <= n -> (S <= x < S + 4 \/ S + n - 4 <= x < S + n) -> cov (L9 S n ++ L') x.
Proof.
  intros S n x L' Hn Hx. unfold L9. cbn [app]. destruct Hx as [Hx|Hx].
  - ltc x (S + 1); [pk 0%nat|]. ltc x (S + 2); [pk 2%nat|]. ltc x (S + 3); [pk 3%nat | pk 6%nat].
  - ltc x (S + n + -3); [pk 7%nat|]. ltc x (S + n + -2); [pk 4%nat|]. ltc x (S + n + -1); [pk 5%nat | pk 1%nat].
Qed.
Lemma cov_a3 : forall S n x, 7 <= n <= 8 -> S <= x < S + n -> cov (L9 S n) x.
Proof. intros S n x Hn Hx. rewrite <- (app_nil_r (L9 S n)). apply cov_hd; lia. Qed.

Section CovB.
Variables (S n kq q x : Z).
Hypothesis Hn : 9 <= n.
Hypothesis Hkq : 0 <= kq <= 3.
Hypothesis Hq : n - kq - 3 <= 4 * q <= n - kq.
Hypothesis Hx : S <= x < S + n.

#[using="Hn Hkq Hq Hx"] Lemma cov_b1 : 4 * q < 9 -> cov (L9 S n ++ LB1 S kq (kq + 4 * q)) x.
Proof. LiaFast.lf_pins (fun (Hn Hkq Hq Hx : LiaFast.U) => LiaFast.u0).
  intros H. ltc x (S + 4); [apply cov_hd; lia|]. ltc x (S + n - 4); [|apply cov_hd; lia].
  unfold L9, LB1. cbn [app]. ltc x (S + kq + 4); [pk 8%nat | pk 9%nat].
Qed.
#[using="Hn Hkq Hq Hx"] Lemma cov_b2 : 9 <= 4 * q < 25 -> cov (L9 S n ++ LB2 S kq (kq + 4 * q)) x.
Proof. LiaFast.lf_pins (fun (Hn Hkq Hq Hx : LiaFast.U) => LiaFast.u0).
  intros H. ltc x (S + 4); [apply cov_hd; lia|]. ltc x (S + n - 4); [|apply cov_hd; lia].
  unfold L9, LB2. cbn [app].
  ltc x (S + kq + 4); [pk 8%nat|]. ltc x (S + kq + 8); [pk 10%nat|]. ltc x (S + kq + 12); [pk 11%nat|].
  ltc x (S + (kq + 4 * q) + -8); [pk 12%nat|]. ltc x (S + (kq + 4 * q) + -4); [pk 13%nat | pk 9%nat].
Qed.
(* [comment removed for export] *)
#[using="Hkq Hq"] Lemma cov_w14 : 25 <= 4 * q -> S + 4 <= x < S + n - 4 -> (x < S + kq + 28 \/ S + (kq + 4 * q) - 28 <= x) -> cov (L9 S n ++ LB3 S kq (kq + 4 * q)) x.
Proof. LiaFast.lf_pins (fun (Hkq Hq : LiaFast.U) => LiaFast.u0).
  intros H Hm Hw. unfold L9, LB3. cbn [app]. destruct Hw as [Hw|Hw].
  - ltc x (S + kq + 4); [pk 8%nat|]. ltc x (S + kq + 8); [pk 10%nat|]. ltc x (S + kq + 12); [pk 11%nat|].
    ltc x (S + kq + 16); [pk 14%nat|]. ltc x (S + kq + 20); [pk 15%nat|]. ltc x (S + kq + 24); [pk 16%nat | pk 17%nat].
  - ltc x (S + (kq + 4 * q) + -24); [pk 18%nat|]. ltc x (S + (kq + 4 * q) + -20); [pk 19%nat|]. ltc x (S + (kq + 4 * q) + -16); [pk 20%nat|].
    ltc x (S + (kq + 4 * q) + -12); [pk 21%nat|]. ltc x (S + (kq + 4 * q) + -8); [pk 12%nat|]. ltc x (S + (kq + 4 * q) + -4); [pk 13%nat | pk 9%nat].
Qed.
#[using="Hn Hkq Hq Hx"] Lemma cov_b3 : 25 <= 4 * q <= 56 -> cov (L9 S n ++ LB3 S kq (kq + 4 * q)) x.
Proof. LiaFast.lf_pins (fun (Hn Hkq Hq Hx : LiaFast.U) => LiaFast.u0).
  intros H. ltc x (S + 4); [apply cov_hd; lia|]. ltc x (S + n - 4); [|apply cov_hd; lia].
  apply cov_w14; lia.
Qed.
#[using="Hn Hkq Hq Hx"] Lemma cov_b4 : forall k4, (k4 = 0 \/ k4 = 4) -> 32 <= 4 * q - 24 - k4 ->
  cov (L9 S n ++ LB3 S kq (kq + 4 * q)) x \/ (S + kq + k4 + 24 <= x < S + kq + k4 + 24 + 32 * ((4 * q - 24 - k4) / 32)).
Proof. LiaFast.lf_pins (fun (Hn Hkq Hq Hx : LiaFast.U) => LiaFast.u0).
  intros k4 Hk4 Hr. ltc x (S + 4); [left; apply cov_hd; lia|]. ltc x (S + n - 4); [|left; apply cov_hd; lia].
  ltc x (S + kq + 28); [left; apply cov_w14; lia|]. destruct (Z_lt_ge_dec x (S + (kq + 4 * q) - 28)); [|left; apply cov_w14; lia].
  right. Z.div_mod_to_equations. lia.
Qed.
End CovB.

(* [comment removed for export] *)
Lemma wok_a1 : forall s n, 1 <= n <= 2 -> wok (La1 s n) s (s + n).
Proof. intros s n H. unfold La1; cbn [wok]; repeat split; lia. Qed.
Lemma wok_a2 : forall s n, 3 <= n <= 6 -> wok (La2 s n) s (s + n).
Proof. intros s n H. unfold La2; cbn [wok]; repeat split; lia. Qed.
Lemma wok_9 : forall s n, 7 <= n -> wok (L9 s n) s (s + n).
Proof. intros s n H. unfold L9; cbn [wok]; repeat split; lia. Qed.
Section WokB.
Variables (s n kq q : Z).
Hypothesis Hn : 9 <= n.
Hypothesis Hkq : 0 <= kq <= 3.
Hypothesis Hq : n - kq - 3 <= 4 * q <= n - kq.
#[using="Hn Hkq Hq"] Lemma wok_b1 : wok (L9 s n ++ LB1 s kq (kq + 4 * q)) s (s + n).
Proof. LiaFast.lf_pins (fun (Hn Hkq Hq : LiaFast.U) => LiaFast.u0). apply wok_app; [apply wok_9; lia|]. unfold LB1; cbn [wok]; repeat split; lia. Qed.
#[using="Hn Hkq Hq"] Lemma wok_b2 : 9 <= 4 * q -> wok (L9 s n ++ LB2 s kq (kq + 4 * q)) s (s + n).
Proof. LiaFast.lf_pins (fun (Hn Hkq Hq : LiaFast.U) => LiaFast.u0). intros H. apply wok_app; [apply wok_9; lia|]. unfold LB2; cbn [wok]; repeat split; lia. Qed.
#[using="Hn Hkq Hq"] Lemma wok_b3 : 25 <= 4 * q -> wok (L9 s n ++ LB3 s kq (kq + 4 * q)) s (s + n).
Proof. LiaFast.lf_pins (fun (Hn Hkq Hq : LiaFast.U) => LiaFast.u0). intros H. apply wok_app; [apply wok_9; lia|]. unfold LB3; cbn [wok]; repeat split; lia. Qed.
End WokB.

(* [comment removed for export] *)
Lemma fin_path : forall m L s n, 1 <= s -> s + n <= 2^47 -> wok L s (s + n) -> (forall x, s <= x < s + n -> cov L x) ->
  (forall x, s <= x < s + n -> zw m L (wa x) = Some (Z_to_bv 8 0)) /\
  (forall x, 0 <= x < 2^64 -> ~ (s <= x < s + n) -> zw m L (wa x) = m (wa x)) /\ mem_grows m (zw m L).
Proof.
  intros m L s n H1 H2 Hw Hc. destruct (zw_spec L m s n ltac:(lia) ltac:(lia) Hw Hc) as [Z1 F1].
  split; [exact Z1 | split; [exact F1 | apply zw_grows]].
Qed.
(* [comment removed for export] *)
Lemma fin_loop : forall m m' L s n blk lb, 1 <= s -> s + n <= 2^47 -> wok L s (s + n) -> s <= blk -> blk + lb <= s + n ->
  (forall x, s <= x < s + n -> cov L x \/ blk <= x < blk + lb) ->
  (forall x, blk <= x < blk + lb -> m' (wa x) = Some (Z_to_bv 8 0)) ->
  (forall x, 0 <= x < 2^64 -> ~ (blk <= x < blk + lb) -> m' (wa x) = zw m L (wa x)) ->
  (forall x, s <= x < s + n -> m' (wa x) = Some (Z_to_bv 8 0)) /\ (forall x, 0 <= x < 2^64 -> ~ (s <= x < s + n) -> m' (wa x) = m (wa x)).
Proof.
  intros m m' L s n blk lb H1 H2 Hw Hb1 Hb2 Hc ZL FL.
  assert (Hw0 : wok L 0 (2^64)) by (apply (wok_mono L s (s + n)); [exact Hw | lia | lia]).
  split.
  - intros x Hx. destruct (Hc x Hx) as [Hcv|Hl]; [|exact (ZL x Hl)].
    destruct (Z_le_gt_dec blk x) as [X1|X1]; [destruct (Z_lt_ge_dec x (blk + lb)) as [X2|X2]|].
    + exact (ZL x ltac:(lia)).
    + rewrite (FL x ltac:(lia) ltac:(lia)). apply zw_hit; [lia | exact Hw0 | exact Hcv].
    + rewrite (FL x ltac:(lia) ltac:(lia)). apply zw_hit; [lia | exact Hw0 | exact Hcv].
  - intros x Hx Hn'. rewrite (FL x Hx ltac:(lia)). apply zw_out; [exact Hx | exact Hw0 |].
    intros Hcv. apply Hn'. exact (wok_cov L s (s + n) x Hw Hcv).
Qed.
(* [comment removed for export] *)
Lemma cov_b4' : forall S n kq q x k4 blk rem, 9 <= n -> 0 <= kq <= 3 -> n - kq - 3 <= 4 * q <= n - kq -> S <= x < S + n ->
  (k4 = 0 \/ k4 = 4) -> blk = S + (kq + k4) + 24 -> rem = 4 * q + -1 * k4 + -24 -> 32 <= rem ->
  cov (L9 S n ++ LB3 S kq (kq + 4 * q)) x \/ (blk <= x < blk + 32 * (rem / 32)).
Proof.
  intros S n kq q x k4 blk rem Hn Hkq Hq Hx Hk4 -> -> Hr.
  replace (4 * q + -1 * k4 + -24) with (4 * q - 24 - k4) by lia. replace (S + (kq + k4) + 24) with (S + kq + k4 + 24) by lia.
  apply cov_b4; lia.
Qed.
Lemma loop_bounds : forall s n kq q k4 blk rem, 9 <= n -> 0 <= kq <= 3 -> n - kq - 3 <= 4 * q <= n - kq -> (k4 = 0 \/ k4 = 4) ->
  blk = s + (kq + k4) + 24 -> rem = 4 * q + -1 * k4 + -24 -> 32 <= rem ->
  s <= blk /\ blk + 32 * (rem / 32) <= s + n /\ rem / 32 = Z.of_nat (Z.to_nat (rem / 32)) /\ 32 <= rem <= n /\ blk + rem <= s + n.
Proof.
  intros s n kq q k4 blk rem Hn Hkq Hq Hk4 -> -> Hr.
  split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [rewrite Z2Nat.id by (Z.div_mod_to_equations; lia); reflexivity|]. lia.
Qed.

Ltac is_arith T := lazymatch T with
  | @eq Z _ _ => idtac | Z.le _ _ => idtac | Z.lt _ _ => idtac | Z.ge _ _ => idtac | Z.gt _ _ => idtac
  | @eq nat _ _ => idtac | Nat.le _ _ => idtac | Nat.lt _ _ => idtac | le _ _ => idtac | lt _ _ => idtac
  | ?A /\ ?B => is_arith A; is_arith B
  | ?A \/ ?B => is_arith A; is_arith B
  | ~ ?A => is_arith A
  | True => idtac | False => idtac
  end.
Ltac prune_ctx := repeat match goal with
  | H : ?T |- _ => lazymatch type of T with
                   | Prop => tryif is_arith T then fail else clear H
                   | _ => fail
                   end
  end.
Ltac slia := first [ LiaFast.lia_fast_tiers | (prune_ctx; lia) ].

(* [comment removed for export] *)
Definition KMS : list nat := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.
Lemma In_sub : forall (k : nat) L1 L2, forallb (fun j => existsb (Nat.eqb j) L2) L1 = true -> In k L1 -> In k L2.
Proof.
  intros k L1 L2 H Hk. rewrite forallb_forall in H. specialize (H k Hk). apply existsb_exists in H as (j & Hj & E).
  apply Nat.eqb_eq in E. subst. exact Hj.
Qed.
Ltac insub Hk := apply (In_sub _ KMS); [vm_compute; reflexivity | exact Hk].
Ltac kms KK := intros k Hk; apply KK; insub Hk.

Section Contract.
Context {fx : FPState}.

#[using="Type"] Theorem memset0_contract : forall rom R m s n,
  getr R 10 = wa s -> getr R 11 = wa 0 -> getr R 12 = wa n ->
  1 <= s -> 0 <= n <= 2^32 -> s + n <= 2^47 ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= n -> store_ok SEGS m (wa (s + d)) k = true) ->
  exists R' m', msteps SEGS (mkst R (wa 0xd3088) m rom) (mkst R' (wa 0xd317c) m' rom) /\
    (forall k, In k KMS -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) /\
    (forall x, s <= x < s + n -> m' (wa x) = Some (Z_to_bv 8 0)) /\
    (forall x, 0 <= x < 2^64 -> ~ (s <= x < s + n) -> m' (wa x) = m (wa x)) /\ mem_grows m m'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros rom R m s n R10 R11 R12 Hs Hn Hsn HW.
  assert (Hs10 : bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10))) = s) by (regzH R10; rewrite R10; apply u_wa_small; lia).
  destruct (Z.eq_dec n 0) as [Hn0|Hn0].
  { subst n.
    assert (P : AXF_ms0z.ms0_pre R m 0) by (constructor; [exact R11 | exact R12 | lia | rewrite Hs10; lia]).
    destruct (AXF_ms0z.ms0_pms0 R m rom 0 P (sc_0 R m)) as (R' & Hms & _ & _ & KK).
    exists R', m. split; [exact Hms|]. split; [kms KK|]. split; [intros x Hx; lia|]. split; [intros x _ _; reflexivity | apply mem_grows_refl]. }
  assert (Hn1 : 1 <= n) by lia. clear Hn0.
  assert (HWA : forall d k, 0 <= d -> d + Z.of_nat k <= n -> store_ok SEGS m (wa (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10))) + 0 + d)) k = true).
  { intros d k Hd Hk. rewrite Hs10. replace (s + 0 + d) with (s + d) by lia. apply HW; lia. }
  assert (PA : AXF_msAz.msA_pre R m n) by (constructor; [exact R11 | exact R12 | lia | rewrite Hs10; lia | exact HWA]).
  destruct (Z_lt_ge_dec n 9) as [Hn9|Hn9].
  { destruct (Z_lt_ge_dec n 3) as [H3|H3]; [|destruct (Z_lt_ge_dec n 7) as [H7|H7]].
    - destruct (AXF_msAz.msA_pmsa1 R m rom n PA (sc_a1 R m s n Hs10 ltac:(lia) ltac:(lia) ltac:(lia) HW ltac:(lia))) as (R' & Hms & _ & _ & _ & _ & KK).
      exists R', (AXF_msAz.msA_mem_pmsa1 m R n). split; [exact Hms|]. split; [kms KK|].
      rewrite eq_a1, Hs10. exact (fin_path m _ s n Hs Hsn (wok_a1 s n ltac:(lia)) (fun x Hx => cov_a1 s n x ltac:(lia) Hx)).
    - destruct (AXF_msAz.msA_pmsa2 R m rom n PA (sc_a2 R m s n Hs10 ltac:(lia) ltac:(lia) ltac:(lia) HW ltac:(lia))) as (R' & Hms & _ & _ & _ & _ & KK).
      exists R', (AXF_msAz.msA_mem_pmsa2 m R n). split; [exact Hms|]. split; [kms KK|].
      rewrite eq_a2, Hs10. exact (fin_path m _ s n Hs Hsn (wok_a2 s n ltac:(lia)) (fun x Hx => cov_a2 s n x ltac:(lia) Hx)).
    - destruct (AXF_msAz.msA_pmsa3 R m rom n PA (sc_a3 R m s n Hs10 ltac:(lia) ltac:(lia) ltac:(lia) HW ltac:(lia))) as (R' & Hms & _ & _ & _ & _ & _ & KK).
      exists R', (AXF_msAz.msA_mem_pmsa3 m R n). split; [exact Hms|]. split; [kms KK|].
      rewrite eq_a3, Hs10. exact (fin_path m _ s n Hs Hsn (wok_9 s n ltac:(lia)) (fun x Hx => cov_a3 s n x ltac:(lia) Hx)). }
  (* [comment removed for export] *)
  assert (Hn9' : 9 <= n) by lia. clear Hn9. rename Hn9' into Hn9.
  destruct (AXF_msAz.msA_pmsa9 R m rom n PA (sc_a9 R m s n Hs10 ltac:(lia) ltac:(lia) ltac:(lia) HW ltac:(lia))) as (R9 & Hms9 & A11 & A12 & A14 & A15 & A16 & A13 & KK9).
  set (m9 := AXF_msAz.msA_mem_pmsa9 m R n) in *.
  assert (G9 : mem_grows m m9) by (unfold m9; rewrite eq_a9; apply zw_grows).
  set (kq := bv_unsigned (getr R9 13)) in *.
  assert (B13 : getr R9 13 = wa kq) by (unfold kq; rewrite wa_u; reflexivity).
  assert (S9 : bv_unsigned (getr R9 (Z_to_bv 5 (Z.of_nat 10))) = s) by (rewrite (KK9 10%nat ltac:(cbn; tauto)); exact Hs10).
  assert (HW9 : forall d k, 0 <= d -> d + Z.of_nat k <= n -> store_ok SEGS m9 (wa (s + d)) k = true).
  { intros d k Hd Hk. apply (store_ok_mono SEGS k m m9 _ G9). apply HW; lia. }
  assert (PB : AXF_msBz.msB_pre R9 m9 n kq).
  { constructor; [exact A11 | exact A12 | exact B13 | exact A14 | exact A15 | exact A16 | lia | lia | rewrite S9; lia |].
    intros d k Hd Hk. rewrite S9. replace (s + 0 + d) with (s + d) by lia. apply HW9; lia. }
  set (q := (n - kq) / 4).
  assert (Hq : n - kq - 3 <= 4 * q <= n - kq) by (unfold q; clear - Hn9 A13; Z.div_mod_to_equations; lia).
  assert (EN4 : 4 * Z.shiftr ((n + -1 * kq) mod 2^64) 2 = 4 * q).
  { rewrite Z.mod_small by slia. rewrite Z.shiftr_div_pow2 by lia. change (2^2) with 4. replace (n + -1 * kq) with (n - kq) by lia. reflexivity. }
  assert (EKN : kq + 4 * Z.shiftr ((n + -1 * kq) mod 2^64) 2 = kq + 4 * q) by (rewrite EN4; reflexivity).
  assert (M9 : m9 = zw m (L9 s n)) by (unfold m9; rewrite eq_a9, Hs10; reflexivity).
  assert (KK2 : forall RB, (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat ->
                 getr RB (Z_to_bv 5 (Z.of_nat k)) = getr R9 (Z_to_bv 5 (Z.of_nat k))) ->
                forall k, In k KMS -> getr RB (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
  { intros RB KKB k Hk. rewrite (KKB k Hk). exact (KK9 k Hk). }
  clear HWA PA.
  destruct (Z_lt_ge_dec (4 * q) 9) as [Hb1|Hb1].
  { destruct (AXF_msBz.msB_pmsb1 R9 m9 rom n kq PB (sc_b1 R9 m9 s n kq S9 ltac:(slia) ltac:(slia) ltac:(slia) ltac:(slia) HW9 ltac:(change ((n - kq) / 4) with q; slia)))
      as (RB & HmsB & _ & _ & _ & _ & _ & _ & KKB).
    exists RB, (AXF_msBz.msB_mem_pmsb1 m9 R9 n kq). split; [exact (msteps_trans SEGS _ _ _ Hms9 HmsB)|]. split; [exact (KK2 RB KKB)|].
    rewrite eq_b1, S9, EKN, M9, <- zw_app.
    exact (fin_path m _ s n Hs Hsn (wok_b1 s n kq q Hn9 A13 Hq) (fun x Hx => cov_b1 s n kq q x Hn9 A13 Hq Hx Hb1)). }
  destruct (Z_lt_ge_dec (4 * q) 25) as [Hb2|Hb2].
  { destruct (AXF_msBz.msB_pmsb2 R9 m9 rom n kq PB (sc_b2 R9 m9 s n kq S9 ltac:(slia) ltac:(slia) ltac:(slia) ltac:(slia) HW9 ltac:(change ((n - kq) / 4) with q; slia)))
      as (RB & HmsB & _ & _ & _ & _ & _ & _ & KKB).
    exists RB, (AXF_msBz.msB_mem_pmsb2 m9 R9 n kq). split; [exact (msteps_trans SEGS _ _ _ Hms9 HmsB)|]. split; [exact (KK2 RB KKB)|].
    rewrite eq_b2, S9, EKN, M9, <- zw_app.
    exact (fin_path m _ s n Hs Hsn (wok_b2 s n kq q Hn9 A13 Hq ltac:(lia)) (fun x Hx => cov_b2 s n kq q x Hn9 A13 Hq Hx ltac:(lia))). }
  set (k4 := Z.land (s + kq) 4).
  assert (Hk4 : k4 = 0 \/ k4 = 4) by apply land4.
  assert (EK4 : Z.land ((s + kq) mod 2^64) 4 = k4) by (rewrite Z.mod_small by slia; reflexivity).
  destruct (Z_lt_ge_dec (4 * q - 24 - k4) 32) as [Hb3|Hb3].
  { destruct (AXF_msBz.msB_pmsb3 R9 m9 rom n kq PB (sc_b3 R9 m9 s n kq S9 ltac:(slia) ltac:(slia) ltac:(slia) ltac:(slia) HW9 ltac:(change ((n - kq) / 4) with q; slia)
                 Hk4 ltac:(change ((n - kq) / 4) with q; fold k4; slia)))
      as (RB & HmsB & _ & _ & _ & _ & _ & _ & KKB).
    exists RB, (AXF_msBz.msB_mem_pmsb3 m9 R9 n kq). split; [exact (msteps_trans SEGS _ _ _ Hms9 HmsB)|]. split; [exact (KK2 RB KKB)|].
    rewrite eq_b3, S9, EKN, M9, <- zw_app.
    exact (fin_path m _ s n Hs Hsn (wok_b3 s n kq q Hn9 A13 Hq ltac:(lia)) (fun x Hx => cov_b3 s n kq q x Hn9 A13 Hq Hx ltac:(slia))). }
  (* [comment removed for export] *)
  destruct (AXF_msBz.msB_pmsb4 R9 m9 rom n kq PB (sc_b4 R9 m9 s n kq S9 ltac:(slia) ltac:(slia) ltac:(slia) ltac:(slia) HW9 ltac:(change ((n - kq) / 4) with q; slia)
               Hk4 ltac:(change ((n - kq) / 4) with q; fold k4; slia)))
    as (RB & HmsB & B11 & B12 & B13' & B14 & _ & _ & KKB).
  set (mB := AXF_msBz.msB_mem_pmsb4 m9 R9 n kq) in *.
  assert (MB : mB = zw m (L9 s n ++ LB3 s kq (kq + 4 * q))) by (unfold mB; rewrite eq_b4, S9, EKN, M9, <- zw_app; reflexivity).
  assert (GB : mem_grows m mB) by (rewrite MB; apply zw_grows).
  set (blk := s + (kq + k4) + 24) in *. set (rem := 4 * q + -1 * k4 + -24) in *.
  assert (B11' : getr RB 11 = wa blk) by (rewrite B11, S9, EK4; reflexivity).
  assert (B14' : getr RB 14 = wa rem) by (rewrite B14, S9, EK4, EN4; reflexivity).
  destruct (loop_bounds s n kq q k4 blk rem Hn9 A13 Hq Hk4 eq_refl eq_refl ltac:(unfold rem; slia)) as (Lb1 & Lb2 & Hrem & Lr & Lbr).
  assert (HWL : forall d k, 0 <= d -> d + Z.of_nat k <= rem -> store_ok SEGS mB (wa (blk + d)) k = true).
  { intros d k Hd Hk. apply (store_ok_mono SEGS k m mB _ GB). replace (blk + d) with (s + (blk - s + d)) by lia. apply HW; slia. }
  destruct (ms_loop rom (Z.to_nat (rem / 32)) RB mB blk rem Hrem ltac:(slia) ltac:(slia) ltac:(slia) B11' B12 B13' B14' HWL)
    as (R' & m' & HmsL & KKL & ZL & FL & GL).
  exists R', m'. split; [exact (msteps_trans SEGS _ _ _ (msteps_trans SEGS _ _ _ Hms9 HmsB) HmsL)|].
  split; [intros k Hk; rewrite (KKL k ltac:(insub Hk)); exact (KK2 RB KKB k Hk)|].
  rewrite MB in FL.
  destruct (fin_loop m m' _ s n blk (32 * (rem / 32)) Hs Hsn (wok_b3 s n kq q Hn9 A13 Hq ltac:(lia)) Lb1 Lb2
              (fun x Hx => cov_b4' s n kq q x k4 blk rem Hn9 A13 Hq Hx Hk4 eq_refl eq_refl ltac:(slia)) ZL FL) as [Z1 F1].
  split; [exact Z1 | split; [exact F1 | exact (mem_grows_trans _ _ _ GB GL)]].
Qed.
End Contract.
End AXG_ms2.

Module AXG_msc.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put AXG_put2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np.AXG_ms OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np.AXG_ms2.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Ltac zatc := repeat match goal with |- context [bv_unsigned (ev (Ez ?R ?V) ?n)] =>
              let v := eval cbn [nth Nat.sub AXF_msc0z.VALS_msc0 AXF_mscAz.VALS_mscA AXF_mscBz.VALS_mscB AXF_msclz.VALS_mscl] in (nth (n - 32) V 0) in
              rewrite (zatom R V n v eq_refl eq_refl) by lia end.

(* [comment removed for export] *)
Section SCA.
Context {fx : FPState}.
Variables (R : bvmap 5 word) (m : word -> option byte) (s n c : Z).
Hypothesis Hs10 : bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10))) = s.
Hypothesis Hsr : 1 <= s <= 2^47.
Hypothesis Hnr : 0 <= n <= 2^32.
Hypothesis Hcr : 0 <= c <= 2^64 - 1.
Hypothesis Hsn : s + n <= 2^47.
Hypothesis HWR : forall d k, 0 <= d -> d + Z.of_nat k <= n -> store_ok SEGS m (wa (s + d)) k = true.

Ltac reg10 := change (bv_unsigned (ev (Ez R ?V) 10)) with (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10)))); rewrite Hs10.
Ltac scone :=
  first [ (apply sc_br_z; first [rewrite br_geu_z | rewrite br_ltu_z | rewrite br_eq_z | rewrite br_ne_z];
           cbn [zeval edenot]; zatc; rewrite ?(Z.mod_small _ (2^64)) by lia; bfin)
        | (cbn [sc_denot]; rewrite adenot_z; cbn [zeval edenot a_base a_off]; zatc; try reg10;
           lazymatch goal with |- store_ok _ _ (wa ?a) ?w = true => replace a with (s + (a - s)) by lia; apply HWR; [lia | cbn; lia] end)
        | (cbn [sc_denot]; unfold flat, estart, elenZ; cbn [a_base a_off]; rewrite ?zeval_sound, ?u_wa; cbn [zeval edenot]; zatc; try reg10;
           rewrite ?(Z.mod_small _ (2^64)) by lia; lia) ].

#[using="s Hs10 Hsr Hnr Hsn HWR"] Lemma scc_a1 : 1 <= n <= 2 -> scs_denot SEGS m (Ez R (AXF_mscAz.VALS_mscA n c)) (snd (fst AXF_mscA.RES_pmsca1)).
Proof. LiaFast.lf_pins (fun (s Hs10 Hsr Hnr Hsn HWR : LiaFast.U) => LiaFast.u0). intros H. cbn [AXF_mscA.RES_pmsca1 fst snd]. scgo; scone. Qed.
#[using="s Hs10 Hsr Hnr Hsn HWR"] Lemma scc_a2 : 3 <= n <= 6 -> scs_denot SEGS m (Ez R (AXF_mscAz.VALS_mscA n c)) (snd (fst AXF_mscA.RES_pmsca2)).
Proof. LiaFast.lf_pins (fun (s Hs10 Hsr Hnr Hsn HWR : LiaFast.U) => LiaFast.u0). intros H. cbn [AXF_mscA.RES_pmsca2 fst snd]. scgo; scone. Qed.
#[using="s Hs10 Hsr Hnr Hsn HWR"] Lemma scc_a3 : 7 <= n <= 8 -> scs_denot SEGS m (Ez R (AXF_mscAz.VALS_mscA n c)) (snd (fst AXF_mscA.RES_pmsca3)).
Proof. LiaFast.lf_pins (fun (s Hs10 Hsr Hnr Hsn HWR : LiaFast.U) => LiaFast.u0). intros H. cbn [AXF_mscA.RES_pmsca3 fst snd]. scgo; scone. Qed.
#[using="s Hs10 Hsr Hnr Hsn HWR"] Lemma scc_a9 : 9 <= n -> scs_denot SEGS m (Ez R (AXF_mscAz.VALS_mscA n c)) (snd (fst AXF_mscA.RES_pmsca9)).
Proof. LiaFast.lf_pins (fun (s Hs10 Hsr Hnr Hsn HWR : LiaFast.U) => LiaFast.u0). intros H. cbn [AXF_mscA.RES_pmsca9 fst snd]. scgo; scone. Qed.
End SCA.

Section SCB.
Context {fx : FPState}.
Variables (R : bvmap 5 word) (m : word -> option byte) (s n kq wc : Z).
Hypothesis Hs10 : bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10))) = s.
Hypothesis Hsr : 1 <= s <= 2^47.
Hypothesis Hnr : 9 <= n <= 2^32.
Hypothesis Hkq : 0 <= kq <= 3.
Hypothesis Hwc : 0 <= wc <= 2^64 - 1.
Hypothesis Hsn : s + n <= 2^47.
Hypothesis HWR : forall d k, 0 <= d -> d + Z.of_nat k <= n -> store_ok SEGS m (wa (s + d)) k = true.

Ltac reg10 := change (bv_unsigned (ev (Ez R ?V) 10)) with (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10)))); rewrite Hs10.
(* [comment removed for export] *)
#[using="Hs10"] Lemma zq_S : zeval (Ez R (AXF_mscBz.VALS_mscB n kq wc)) (EVar 10) = s.
Proof. LiaFast.lf_pins (fun (Hs10 : LiaFast.U) => LiaFast.u0). cbn [zeval edenot]. reg10. reflexivity. Qed.
#[using="Hs10 Hkq"] Lemma zq_SK : zeval (Ez R (AXF_mscBz.VALS_mscB n kq wc)) (EAlu ALU_ADD (EVar 10) (EVar 33)) = s + kq.
Proof. LiaFast.lf_pins (fun (Hs10 Hkq : LiaFast.U) => LiaFast.u0). cbn [zeval edenot]. zatc. reg10. reflexivity. Qed.
#[using="Hnr Hkq"] Lemma zq_N4 : zeval (Ez R (AXF_mscBz.VALS_mscB n kq wc)) (EMd M_MUL (ELit 4) (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit (-1)) (EVar 33))) (ELit 2))) =
  4 * ((n - kq) / 4).
Proof. LiaFast.lf_pins (fun (Hnr Hkq : LiaFast.U) => LiaFast.u0).
  cbn [zeval edenot]. zatc. change (2 mod 64) with 2. rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^2) with 4.
  replace (n + -1 * kq) with (n - kq) by lia. reflexivity.
Qed.
#[using="Hs10 Hnr Hkq"] Lemma zq_KN : zeval (Ez R (AXF_mscBz.VALS_mscB n kq wc))
    (EAlu ALU_ADD (EVar 10) (EAlu ALU_ADD (EVar 33) (EMd M_MUL (ELit 4) (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit (-1)) (EVar 33))) (ELit 2))))) =
  s + (kq + 4 * ((n - kq) / 4)).
Proof. LiaFast.lf_pins (fun (Hs10 Hnr Hkq : LiaFast.U) => LiaFast.u0).
  change (zeval (Ez R (AXF_mscBz.VALS_mscB n kq wc))
    (EAlu ALU_ADD (EVar 10) (EAlu ALU_ADD (EVar 33) (EMd M_MUL (ELit 4) (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit (-1)) (EVar 33))) (ELit 2))))))
    with (zeval (Ez R (AXF_mscBz.VALS_mscB n kq wc)) (EVar 10) + (zeval (Ez R (AXF_mscBz.VALS_mscB n kq wc)) (EVar 33) +
          zeval (Ez R (AXF_mscBz.VALS_mscB n kq wc)) (EMd M_MUL (ELit 4) (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit (-1)) (EVar 33))) (ELit 2))))).
  rewrite zq_S, zq_N4. cbn [zeval edenot]. zatc. reflexivity.
Qed.
#[using="Hs10 Hsr Hnr Hkq Hsn"] Lemma zq_REM : zeval (Ez R (AXF_mscBz.VALS_mscB n kq wc))
    (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 4) (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit (-1)) (EVar 33))) (ELit 2)))
                                (EMd M_MUL (ELit (-1)) (EAlu ALU_AND (EAlu ALU_ADD (EVar 10) (EVar 33)) (ELit 4)))) (ELit (-24))) =
  4 * ((n - kq) / 4) - Z.land (s + kq) 4 - 24.
Proof. LiaFast.lf_pins (fun (Hs10 Hsr Hnr Hkq Hsn : LiaFast.U) => LiaFast.u0).
  change (zeval (Ez R (AXF_mscBz.VALS_mscB n kq wc))
    (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 4) (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit (-1)) (EVar 33))) (ELit 2)))
                                (EMd M_MUL (ELit (-1)) (EAlu ALU_AND (EAlu ALU_ADD (EVar 10) (EVar 33)) (ELit 4)))) (ELit (-24))))
    with (zeval (Ez R (AXF_mscBz.VALS_mscB n kq wc)) (EMd M_MUL (ELit 4) (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit (-1)) (EVar 33))) (ELit 2)))
          + -1 * Z.land (zeval (Ez R (AXF_mscBz.VALS_mscB n kq wc)) (EAlu ALU_ADD (EVar 10) (EVar 33)) mod 2^64) (4 mod 2^64) + -24).
  rewrite zq_N4, zq_SK. change (4 mod 2^64) with 4. rewrite (Z.mod_small (s + kq)) by lia. lia.
Qed.
#[using="HWR"] Lemma HWR' : forall a w, s <= a -> a + Z.of_nat w <= s + n -> store_ok SEGS m (wa a) w = true.
Proof. LiaFast.lf_pins (fun (HWR : LiaFast.U) => LiaFast.u0). intros a w H1 H2. replace a with (s + (a - s)) by lia. apply HWR; lia. Qed.
Ltac zrw := rewrite ?zq_KN, ?zq_REM, ?zq_N4, ?zq_SK.
Ltac scone :=
  first [ (apply sc_br_z; first [rewrite br_geu_z | rewrite br_ltu_z | rewrite br_eq_z | rewrite br_ne_z]; zrw; cbn [zeval];
           rewrite ?(Z.mod_small _ (2^64)) by (pose proof (land4 (s + kq)); pose proof (Z.div_pos (n - kq) 4 ltac:(lia) ltac:(lia)); lia); bfin)
        | (cbn [sc_denot]; rewrite adenot_z; cbn [a_base a_off]; zrw; try (match goal with H : Z.land _ 4 = 0 \/ _ |- _ => clear H end); apply HWR'; cbn; lia)
        | (cbn [sc_denot]; unfold flat, estart, elenZ; cbn [a_base a_off]; rewrite ?zeval_sound, ?u_wa; zrw; cbn [zeval]; try (match goal with H : Z.land _ 4 = 0 \/ _ |- _ => clear H end);
           rewrite ?(Z.mod_small _ (2^64)) by lia; lia) ].

#[using="s Hs10 Hsr Hnr Hkq Hsn HWR"] Lemma scc_b1 : 4 * ((n - kq) / 4) < 9 -> scs_denot SEGS m (Ez R (AXF_mscBz.VALS_mscB n kq wc)) (snd (fst AXF_mscB.RES_pmscb1)).
Proof. LiaFast.lf_pins (fun (s Hs10 Hsr Hnr Hkq Hsn HWR : LiaFast.U) => LiaFast.u0). intros H. pose proof (Z.div_mod (n - kq) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (n - kq) 4 ltac:(lia)).
  cbn [AXF_mscB.RES_pmscb1 fst snd]. scgo; scone. Qed.
#[using="s Hs10 Hsr Hnr Hkq Hsn HWR"] Lemma scc_b2 : 9 <= 4 * ((n - kq) / 4) < 25 -> scs_denot SEGS m (Ez R (AXF_mscBz.VALS_mscB n kq wc)) (snd (fst AXF_mscB.RES_pmscb2)).
Proof. LiaFast.lf_pins (fun (s Hs10 Hsr Hnr Hkq Hsn HWR : LiaFast.U) => LiaFast.u0). intros H. pose proof (Z.div_mod (n - kq) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (n - kq) 4 ltac:(lia)).
  cbn [AXF_mscB.RES_pmscb2 fst snd]. scgo; scone. Qed.
#[using="Hs10 Hsr Hnr Hkq Hsn HWR"] Lemma scc_b3 : 25 <= 4 * ((n - kq) / 4) -> (Z.land (s + kq) 4 = 0 \/ Z.land (s + kq) 4 = 4) ->
  4 * ((n - kq) / 4) - 24 - Z.land (s + kq) 4 < 32 -> scs_denot SEGS m (Ez R (AXF_mscBz.VALS_mscB n kq wc)) (snd (fst AXF_mscB.RES_pmscb3)).
Proof. LiaFast.lf_pins (fun (Hs10 Hsr Hnr Hkq Hsn HWR : LiaFast.U) => LiaFast.u0). intros H1 H2 H3. pose proof (Z.div_mod (n - kq) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (n - kq) 4 ltac:(lia)).
  cbn [AXF_mscB.RES_pmscb3 fst snd]. scgo; scone. Qed.
#[using="Hs10 Hsr Hnr Hkq Hsn HWR"] Lemma scc_b4 : 25 <= 4 * ((n - kq) / 4) -> (Z.land (s + kq) 4 = 0 \/ Z.land (s + kq) 4 = 4) ->
  32 <= 4 * ((n - kq) / 4) - 24 - Z.land (s + kq) 4 -> scs_denot SEGS m (Ez R (AXF_mscBz.VALS_mscB n kq wc)) (snd (fst AXF_mscB.RES_pmscb4)).
Proof. LiaFast.lf_pins (fun (Hs10 Hsr Hnr Hkq Hsn HWR : LiaFast.U) => LiaFast.u0). intros H1 H2 H3. pose proof (Z.div_mod (n - kq) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (n - kq) 4 ltac:(lia)).
  cbn [AXF_mscB.RES_pmscb4 fst snd]. scgo; scone. Qed.
End SCB.

Section SCL.
Context {fx : FPState}.
Variables (R : bvmap 5 word) (m : word -> option byte) (blk rem vc : Z).
Hypothesis Hbr : 1 <= blk <= 2^47.
Hypothesis Hrr : 32 <= rem <= 2^32.
Hypothesis Hvc : 0 <= vc <= 2^64 - 1.
Hypothesis Hbn : blk + rem <= 2^47.
Ltac scone :=
  first [ (apply sc_br_z; first [rewrite br_geu_z | rewrite br_ltu_z | rewrite br_eq_z | rewrite br_ne_z];
           cbn [zeval edenot]; zatc; rewrite ?(Z.mod_small _ (2^64)) by lia; bfin)
        | (cbn [sc_denot]; unfold flat, estart, elenZ; cbn [a_base a_off]; rewrite ?zeval_sound, ?u_wa; cbn [zeval edenot]; zatc;
           rewrite ?(Z.mod_small _ (2^64)) by lia; lia) ].
#[using="Hrr"] Lemma scc_lc : 64 <= rem -> scs_denot SEGS m (Ez R (AXF_msclz.VALS_mscl blk rem vc)) (snd (fst AXF_mscl.RES_pmsclc)).
Proof. LiaFast.lf_pins (fun (Hrr : LiaFast.U) => LiaFast.u0). intros H. cbn [AXF_mscl.RES_pmsclc fst snd]. scgo; scone. Qed.
#[using="Hrr"] Lemma scc_lx : rem < 64 -> scs_denot SEGS m (Ez R (AXF_msclz.VALS_mscl blk rem vc)) (snd (fst AXF_mscl.RES_pmsclx)).
Proof. LiaFast.lf_pins (fun (Hrr : LiaFast.U) => LiaFast.u0). intros H. cbn [AXF_mscl.RES_pmsclx fst snd]. scgo; scone. Qed.
End SCL.

Lemma scc_0 : forall {fx : FPState} R m c, scs_denot SEGS m (Ez R (AXF_msc0z.VALS_msc0 c)) (snd (fst AXF_msc0.RES_pmsc0)).
Proof. intros fx R m c. cbn [AXF_msc0.RES_pmsc0 fst snd]. scgo. Qed.

(* [comment removed for export] *)
Definition fr_in (m m' : word -> option byte) (lo hi : Z) : Prop :=
  forall x, 0 <= x < 2^64 -> ~ (lo <= x < hi) -> m' (wa x) = m (wa x).
Lemma fr_refl : forall m lo hi, fr_in m m lo hi.
Proof. intros m lo hi x _ _. reflexivity. Qed.
Lemma fr_wb : forall m m1 a bs lo hi, fr_in m m1 lo hi -> 0 <= lo -> hi <= 2^64 -> lo <= a -> a + Z.of_nat (length bs) <= hi -> (1 <= length bs)%nat ->
  fr_in m (wbytes m1 (wa a) bs) lo hi.
Proof. intros m m1 a bs lo hi H H1 H2 H3 H4 H5 x Hx Hn. rewrite wb_other by lia. exact (H x Hx Hn). Qed.
Lemma fr_trans : forall m1 m2 m3 lo hi, fr_in m1 m2 lo hi -> fr_in m2 m3 lo hi -> fr_in m1 m3 lo hi.
Proof. intros m1 m2 m3 lo hi H1 H2 x Hx Hn. rewrite (H2 x Hx Hn). exact (H1 x Hx Hn). Qed.
Lemma fr_mono : forall m m' lo hi lo' hi', fr_in m m' lo hi -> lo' <= lo -> hi <= hi' -> fr_in m m' lo' hi'.
Proof. intros m m' lo hi lo' hi' H H1 H2 x Hx Hn. apply H; [exact Hx | lia]. Qed.
Ltac frgo := repeat (apply fr_wb; [| lia | lia | lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia]); apply fr_refl.

(* [comment removed for export] *)
Lemma fr_blk : forall m blk v, 1 <= blk -> blk + 32 <= 2^47 ->
  fr_in m (wbytes (wbytes (wbytes (wbytes m (wa (blk + 0)) (word_to_le_bytes 8 v)) (wa (blk + 8)) (word_to_le_bytes 8 v))
         (wa (blk + 16)) (word_to_le_bytes 8 v)) (wa (blk + 24)) (word_to_le_bytes 8 v)) blk (blk + 32).
Proof. intros m blk v H1 H2. frgo. Qed.

Theorem msc_loop : forall {fx : FPState} rom (t : nat) R mm blk rem, rem / 32 = Z.of_nat t -> 32 <= rem <= 2^32 -> 1 <= blk -> blk + rem <= 2^47 ->
  getr R 11 = wa blk -> getr R 13 = wa 31 -> getr R 14 = wa rem ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= rem -> store_ok SEGS mm (wa (blk + d)) k = true) ->
  exists R' mm', msteps SEGS (mkst R (wa 0xd3160) mm rom) (mkst R' (wa 0xd317c) mm' rom) /\
    (forall k, In k KLOOP -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) /\
    fr_in mm mm' blk (blk + rem) /\ mem_grows mm mm'.
Proof.
  intros fx rom t. induction t as [|t IH]; intros R mm blk rem Ht Hr Hb Hbr R11 R13 R14 HW.
  { exfalso. pose proof (Z.div_le_lower_bound rem 32 1 ltac:(lia) ltac:(lia)). lia. }
  set (vc := bv_unsigned (getr R 12)).
  assert (R12 : getr R 12 = wa vc) by (unfold vc; rewrite wa_u; reflexivity).
  assert (Hvc : 0 <= vc <= 2^64 - 1) by (pose proof (bv_unsigned_in_range _ (getr R 12)) as X; unfold bv_modulus in X; change (2 ^ Z.of_N 64) with (2^64) in X; unfold vc; lia).
  assert (P : AXF_msclz.mscl_pre R mm blk rem vc).
  { constructor; try assumption; try lia. intros d k Hd Hk. replace (blk + 0 + d) with (blk + d) by lia. apply HW; lia. }
  destruct (Z_lt_ge_dec rem 64) as [Hx|Hc].
  - (* [comment removed for export] *)
    destruct (AXF_msclz.mscl_pmsclx R mm rom blk rem vc P (scc_lx R mm blk rem vc ltac:(lia) ltac:(lia))) as (R' & Hms & E11 & E12 & E13 & E14 & KK).
    exists R', (AXF_msclz.mscl_mem_pmsclx mm R blk rem vc). split; [exact Hms|]. split; [|split].
    + intros k Hk. cbn [KLOOP In] in Hk.
      repeat (destruct Hk as [<-|Hk]; [first [solve [apply KK; cbn [In]; memb] | (regzH E12; regzH R12; rewrite E12, R12; reflexivity) | (regzH E13; regzH R13; rewrite E13, R13; reflexivity)]|]). destruct Hk.
    + unfold AXF_msclz.mscl_mem_pmsclx. apply (fr_mono _ _ blk (blk + 32)); [apply fr_blk; lia | lia | lia].
    + unfold AXF_msclz.mscl_mem_pmsclx. growsc.
  - (* [comment removed for export] *)
    destruct (AXF_msclz.mscl_pmsclc R mm rom blk rem vc P (scc_lc R mm blk rem vc ltac:(lia) ltac:(lia))) as (R1 & Hms1 & E11 & E12 & E13 & E14 & KK1).
    set (mm1 := AXF_msclz.mscl_mem_pmsclc mm R blk rem vc) in *.
    assert (Ht' : (rem - 32) / 32 = Z.of_nat t).
    { replace rem with ((rem - 32) + 1 * 32) in Ht by lia. rewrite Z.div_add in Ht by lia. lia. }
    assert (G1 : mem_grows mm mm1) by (unfold mm1, AXF_mslz.msl_mem_pmslc; growsc).
    destruct (IH R1 mm1 (blk + 32) (rem - 32) Ht' ltac:(lia) ltac:(lia) ltac:(lia) E11 E13 ltac:(rewrite E14; f_equal; lia))
      as (R' & mm' & Hms' & KK' & F' & G').
    { intros d k Hd Hk. replace (blk + 32 + d) with (blk + (32 + d)) by lia. apply (store_ok_mono SEGS k mm mm1 _ G1). apply HW; lia. }
    exists R', mm'. split; [exact (msteps_trans SEGS _ _ _ Hms1 Hms')|]. split; [|split].
    + intros k Hk. rewrite (KK' k Hk). cbn [KLOOP In] in Hk.
      repeat (destruct Hk as [<-|Hk]; [first [solve [apply KK1; cbn [In]; memb] | (regzH E12; regzH R12; rewrite E12, R12; reflexivity) | (regzH E13; regzH R13; rewrite E13, R13; reflexivity)]|]). destruct Hk.
    + apply (fr_trans _ mm1).
      * unfold mm1, AXF_msclz.mscl_mem_pmsclc. apply (fr_mono _ _ blk (blk + 32)); [apply fr_blk; lia | lia | lia].
      * apply (fr_mono _ _ (blk + 32) (blk + 32 + (rem - 32))); [exact F' | lia | lia].
    + exact (mem_grows_trans _ _ _ G1 G').
Qed.
End AXG_msc.

Module AXG_msc2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put AXG_put2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np.AXG_ms OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np.AXG_ms2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np.AXG_msc.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.
Abbreviation S10 R := (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10)))).

(* [comment removed for export] *)
Section FrA.
Context {fx : FPState}.
Variables (m : word -> option byte) (R : bvmap 5 word) (s n c : Z).
Hypothesis Hs : S10 R = s.
Hypothesis H1 : 1 <= s.
Hypothesis H2 : s + n <= 2^47.
#[using="Hs H1 H2"] Lemma fr_a1 : 1 <= n <= 2 -> fr_in m (AXF_mscAz.mscA_mem_pmsca1 m R n c) s (s + n).
Proof. LiaFast.lf_pins (fun (Hs H1 H2 : LiaFast.U) => LiaFast.u0). intros H. unfold AXF_mscAz.mscA_mem_pmsca1. rewrite Hs. frgo. Qed.
#[using="Hs H1 H2"] Lemma fr_a2 : 3 <= n <= 6 -> fr_in m (AXF_mscAz.mscA_mem_pmsca2 m R n c) s (s + n).
Proof. LiaFast.lf_pins (fun (Hs H1 H2 : LiaFast.U) => LiaFast.u0). intros H. unfold AXF_mscAz.mscA_mem_pmsca2. rewrite Hs. frgo. Qed.
#[using="Hs H1 H2"] Lemma fr_a3 : 7 <= n <= 8 -> fr_in m (AXF_mscAz.mscA_mem_pmsca3 m R n c) s (s + n).
Proof. LiaFast.lf_pins (fun (Hs H1 H2 : LiaFast.U) => LiaFast.u0). intros H. unfold AXF_mscAz.mscA_mem_pmsca3. rewrite Hs. frgo. Qed.
#[using="Hs H1 H2"] Lemma fr_a9 : 9 <= n -> fr_in m (AXF_mscAz.mscA_mem_pmsca9 m R n c) s (s + n).
Proof. LiaFast.lf_pins (fun (Hs H1 H2 : LiaFast.U) => LiaFast.u0). intros H. unfold AXF_mscAz.mscA_mem_pmsca9. rewrite Hs. frgo. Qed.
End FrA.

Section FrB.
Context {fx : FPState}.
Variables (m : word -> option byte) (R : bvmap 5 word) (s n kq q wc : Z).
Hypothesis Hs : S10 R = s.
Hypothesis H1 : 1 <= s.
Hypothesis H2 : s + n <= 2^47.
Hypothesis Hn : 9 <= n.
Hypothesis Hkq : 0 <= kq <= 3.
Hypothesis Hq : n - kq - 3 <= 4 * q <= n - kq.
Hypothesis EN : 4 * Z.shiftr ((n + -1 * kq) mod 2^64) 2 = 4 * q.
#[using="q Hs H1 H2 Hn Hkq Hq EN"] Lemma fr_b1 : fr_in m (AXF_mscBz.mscB_mem_pmscb1 m R n kq wc) s (s + n).
Proof. LiaFast.lf_pins (fun (q Hs H1 H2 Hn Hkq Hq EN : LiaFast.U) => LiaFast.u0). unfold AXF_mscBz.mscB_mem_pmscb1. rewrite Hs, EN. frgo. Qed.
#[using="Hs H1 H2 Hkq Hq EN"] Lemma fr_b2 : 9 <= 4 * q -> fr_in m (AXF_mscBz.mscB_mem_pmscb2 m R n kq wc) s (s + n).
Proof. LiaFast.lf_pins (fun (Hs H1 H2 Hkq Hq EN : LiaFast.U) => LiaFast.u0). intros H. unfold AXF_mscBz.mscB_mem_pmscb2. rewrite Hs, EN. frgo. Qed.
#[using="Hs H1 H2 Hkq Hq EN"] Lemma fr_b3 : 25 <= 4 * q -> fr_in m (AXF_mscBz.mscB_mem_pmscb3 m R n kq wc) s (s + n).
Proof. LiaFast.lf_pins (fun (Hs H1 H2 Hkq Hq EN : LiaFast.U) => LiaFast.u0). intros H. unfold AXF_mscBz.mscB_mem_pmscb3. rewrite Hs, EN. frgo. Qed.
#[using="Hs H1 H2 Hkq Hq EN"] Lemma fr_b4 : 25 <= 4 * q -> fr_in m (AXF_mscBz.mscB_mem_pmscb4 m R n kq wc) s (s + n).
Proof. LiaFast.lf_pins (fun (Hs H1 H2 Hkq Hq EN : LiaFast.U) => LiaFast.u0). intros H. unfold AXF_mscBz.mscB_mem_pmscb4. rewrite Hs, EN. frgo. Qed.
End FrB.

Ltac insub Hk := apply (In_sub _ KMS); [vm_compute; reflexivity | exact Hk].
Ltac kms KK := intros k Hk; apply KK; insub Hk.
Lemma rng64 : forall w : word, 0 <= bv_unsigned w <= 2^64 - 1.
Proof. intros w. pose proof (bv_unsigned_in_range _ w) as X. unfold bv_modulus in X. change (2 ^ Z.of_N 64) with (2^64) in X. lia. Qed.

(* [comment removed for export] *)
End AXG_msc2.

Module AXG_msc3.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put AXG_put2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np.AXG_ms OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np.AXG_ms2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np.AXG_msc OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np.AXG_msc2.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.
Abbreviation S10 R := (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10)))).

(* [comment removed for export] *)
Definition uni (b : Z) (w : nat) (v : Z) : Prop := forall j, (j < w)%nat -> nth j (word_to_le_bytes w (wa v)) (Z_to_bv 8 0) = Z_to_bv 8 b.
Fixpoint zwv (m : word -> option byte) (L : list (Z * nat * Z)) : word -> option byte :=
  match L with [] => m | (a, w, v) :: L' => zwv (wbytes m (wa a) (word_to_le_bytes w (wa v))) L' end.
Definition pj (L : list (Z * nat * Z)) : list (Z * nat) := List.map (fun t => (fst (fst t), snd (fst t))) L.
Fixpoint univ (b : Z) (L : list (Z * nat * Z)) : Prop :=
  match L with [] => True | (a, w, v) :: L' => uni b w v /\ univ b L' end.

Lemma zwv_out : forall L m x, 0 <= x < 2^64 -> wok (pj L) 0 (2^64) -> ~ cov (pj L) x -> zwv m L (wa x) = m (wa x).
Proof.
  induction L as [|[[a w] v] L IH]; intros m x Hx Hw Hc; [reflexivity|]. cbn [zwv pj List.map fst snd wok cov] in *.
  rewrite IH by tauto. apply wb_other; rewrite ?length_N_to_le_bytes; lia.
Qed.
Lemma wbv_hit : forall m a w v b x, uni b w v -> 0 <= a -> a + Z.of_nat w <= 2^64 -> a <= x < a + Z.of_nat w ->
  wbytes m (wa a) (word_to_le_bytes w (wa v)) (wa x) = Some (Z_to_bv 8 b).
Proof.
  intros m a w v b x Hu Ha Hw Hx.
  assert (Hl : length (word_to_le_bytes w (wa v)) = w) by apply length_N_to_le_bytes.
  replace (wa x) with (Z_to_bv 64 (bv_unsigned (wa a) + Z.of_nat (Z.to_nat (x - a)))) by (rewrite u_wa_small by lia; unfold wa; f_equal; lia).
  rewrite wbytes_nth; [| rewrite u_wa_small by lia; rewrite Hl; lia | rewrite Hl; lia].
  f_equal. apply Hu. lia.
Qed.
Lemma zwv_hit : forall L m b x, 0 <= x < 2^64 -> univ b L -> wok (pj L) 0 (2^64) -> cov (pj L) x -> zwv m L (wa x) = Some (Z_to_bv 8 b).
Proof.
  induction L as [|[[a w] v] L IH]; intros m b x Hx Hu Hw Hc; cbn [pj List.map cov] in Hc; [destruct Hc|]. cbn [zwv pj List.map fst snd wok univ] in *.
  destruct (cov_dec (pj L) x) as [HL|HL]; [exact (IH _ b x Hx (proj2 Hu) (proj2 Hw) HL)|].
  destruct Hc as [Hc|Hc]; [|contradiction].
  rewrite zwv_out by tauto. apply (wbv_hit m a w v b x (proj1 Hu)); lia.
Qed.
Lemma zwv_app : forall L1 L2 m, zwv m (L1 ++ L2) = zwv (zwv m L1) L2.
Proof. induction L1 as [|[[a w] v] L1 IH]; intros L2 m; [reflexivity|]. cbn [app zwv]. apply IH. Qed.
Lemma pj_app : forall L1 L2, pj (L1 ++ L2) = pj L1 ++ pj L2.
Proof. intros. unfold pj. apply map_app. Qed.
Lemma univ_app : forall b L1 L2, univ b L1 -> univ b L2 -> univ b (L1 ++ L2).
Proof. induction L1 as [|[[a w] v] L1 IH]; intros L2 H1 H2; cbn [app univ] in *; [exact H2|]. split; [exact (proj1 H1) | exact (IH L2 (proj2 H1) H2)]. Qed.

(* [comment removed for export] *)
Lemma fin_v : forall m L s n b, 1 <= s -> s + n <= 2^47 -> univ b L -> wok (pj L) s (s + n) -> (forall x, s <= x < s + n -> cov (pj L) x) ->
  forall x, s <= x < s + n -> zwv m L (wa x) = Some (Z_to_bv 8 b).
Proof.
  intros m L s n b H1 H2 Hu Hw Hc x Hx. apply zwv_hit; [lia | exact Hu | apply (wok_mono _ s (s + n)); [exact Hw | lia | lia] | exact (Hc x Hx)].
Qed.

(* [comment removed for export] *)
Lemma bv8_mod : forall z, Z_to_bv 8 z = Z_to_bv 8 (z mod 256).
Proof. intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_mod by lia. reflexivity. Qed.
Lemma nth_le : forall w z j, (j < w)%nat -> nth j (Z_to_le_bytes w z) (Z_to_bv 8 0) = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat j)).
Proof.
  induction w as [|w IH]; intros z j Hj; [lia|]. cbn [Z_to_le_bytes]. destruct j as [|j]; [cbn [nth]; rewrite Z.shiftr_0_r; reflexivity|].
  cbn [nth]. rewrite IH by lia. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.
Lemma uni1 : forall c, 0 <= c < 2^64 -> uni (c mod 256) 1 c.
Proof.
  intros c Hc j Hj. assert (j = O) by lia. subst j. unfold word_to_le_bytes. rewrite u_wa_small by lia.
  rewrite nth_le by lia. rewrite Z.shiftr_0_r. apply bv8_mod.
Qed.
Lemma uni4 : forall b, 0 <= b < 256 -> uni b 4 (b * 16843009).
Proof.
  intros b Hb j Hj. unfold word_to_le_bytes. rewrite u_wa_small by lia. rewrite nth_le by lia. rewrite bv8_mod. f_equal.
  rewrite Z.shiftr_div_pow2 by lia.
  assert (Hj4 : (j = 0 \/ j = 1 \/ j = 2 \/ j = 3)%nat) by lia.
  destruct Hj4 as [E|[E|[E|E]]]; subst j; cbn [Z.of_nat Pos.of_succ_nat]; Z.div_mod_to_equations; lia.
Qed.
Lemma uni8 : forall b, 0 <= b < 256 -> uni b 8 (b * 72340172838076673).
Proof.
  intros b Hb j Hj. unfold word_to_le_bytes. rewrite u_wa_small by lia. rewrite nth_le by lia. rewrite bv8_mod. f_equal.
  rewrite Z.shiftr_div_pow2 by lia.
  assert (Hj8 : (j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7)%nat) by lia.
  destruct Hj8 as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; subst j; cbn [Z.of_nat Pos.of_succ_nat]; Z.div_mod_to_equations; lia.
Qed.

Section Vals.
Context {fx : FPState}.
Variables (R : bvmap 5 word) (n kq wc b : Z).
Hypothesis Hb : 0 <= b < 256.
Hypothesis Hwc : wc = 72057594037927936 * b.
Hypothesis Hn : 0 <= n <= 2^32.
Hypothesis Hkq : 0 <= kq <= 3.
#[using="b Hb Hwc"] Lemma z34 : bv_unsigned (ev (Ez R (AXF_mscBz.VALS_mscB n kq wc)) 34) = wc.
Proof. LiaFast.lf_pins (fun (b Hb Hwc : LiaFast.U) => LiaFast.u0). rewrite (zatom R (AXF_mscBz.VALS_mscB n kq wc) 34 wc eq_refl eq_refl) by lia. reflexivity. Qed.
#[using="Hb Hwc"] Lemma val4 : bv_unsigned (edenot (Ez R (AXF_mscBz.VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304))) = b * 16843009.
Proof. LiaFast.lf_pins (fun (Hb Hwc : LiaFast.U) => LiaFast.u0).
  cbn [edenot]. unfold mul_div. unfold bv_mulhuu. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  rewrite z34. change (bv_unsigned (Z_to_bv 64 4311810304)) with 4311810304. change (Z.of_N 64) with 64.
  rewrite Z.shiftr_div_pow2 by lia. subst wc. Z.div_mod_to_equations. lia.
Qed.
Definition pat8 (u : Z) : Z := Z.lor ((4294967296 * u) mod 2^64) (Z.shiftr ((4294967296 * u) mod 2^64) (32 mod 64) mod 2^64) mod 2^64.
#[using="Type"] Lemma pat8_check : forallb (fun k => Z.eqb (pat8 (Z.of_nat k * 16843009)) (Z.of_nat k * 72340172838076673)) (List.seq 0 256) = true.
Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Hb"] Lemma pat8_val : pat8 (b * 16843009) = b * 72340172838076673.
Proof. LiaFast.lf_pins (fun (Hb : LiaFast.U) => LiaFast.u0).
  pose proof pat8_check as H. rewrite forallb_forall in H.
  specialize (H (Z.to_nat b) ltac:(apply in_seq; lia)). apply Z.eqb_eq in H. rewrite Z2Nat.id in H by lia. exact H.
Qed.
#[using="Hb Hwc"] Lemma val8 : bv_unsigned (edenot (Ez R (AXF_mscBz.VALS_mscB n kq wc))
    (EAlu ALU_OR (EMd M_MUL (ELit 4294967296) (EMd M_MULHU (EVar 34) (ELit 4311810304)))
                 (EAlu ALU_SRL (EMd M_MUL (ELit 4294967296) (EMd M_MULHU (EVar 34) (ELit 4311810304))) (ELit 32)))) = b * 72340172838076673.
Proof. LiaFast.lf_pins (fun (Hb Hwc : LiaFast.U) => LiaFast.u0).
  rewrite zeval_sound, u_wa. cbn [zeval]. rewrite val4. exact pat8_val.
Qed.
End Vals.

(* [comment removed for export] *)
Definition La1v (S n c : Z) : list (Z * nat * Z) := [(S + 0, 1%nat, c); (S + n + -1, 1%nat, c)].
Definition La2v (S n c : Z) : list (Z * nat * Z) :=
  [(S + 0, 1%nat, c); (S + n + -1, 1%nat, c); (S + 1, 1%nat, c); (S + 2, 1%nat, c); (S + n + -3, 1%nat, c); (S + n + -2, 1%nat, c)].
Definition L9v (S n c : Z) : list (Z * nat * Z) :=
  [(S + 0, 1%nat, c); (S + n + -1, 1%nat, c); (S + 1, 1%nat, c); (S + 2, 1%nat, c); (S + n + -3, 1%nat, c); (S + n + -2, 1%nat, c);
   (S + 3, 1%nat, c); (S + n + -4, 1%nat, c)].
Definition LB1v (S kq KN V : Z) : list (Z * nat * Z) := [(S + kq + 0, 4%nat, V); (S + KN + -4, 4%nat, V)].
Definition LB2v (S kq KN V : Z) : list (Z * nat * Z) :=
  [(S + kq + 0, 4%nat, V); (S + KN + -4, 4%nat, V); (S + kq + 4, 4%nat, V); (S + kq + 8, 4%nat, V); (S + KN + -12, 4%nat, V); (S + KN + -8, 4%nat, V)].
Definition LB3v (S kq KN V : Z) : list (Z * nat * Z) :=
  [(S + kq + 0, 4%nat, V); (S + KN + -4, 4%nat, V); (S + kq + 4, 4%nat, V); (S + kq + 8, 4%nat, V); (S + KN + -12, 4%nat, V); (S + KN + -8, 4%nat, V);
   (S + kq + 12, 4%nat, V); (S + kq + 16, 4%nat, V); (S + kq + 20, 4%nat, V); (S + kq + 24, 4%nat, V);
   (S + KN + -28, 4%nat, V); (S + KN + -24, 4%nat, V); (S + KN + -20, 4%nat, V); (S + KN + -16, 4%nat, V)].

Lemma pj_La1v : forall S n c, pj (La1v S n c) = La1 S n. Proof. reflexivity. Qed.
Lemma pj_La2v : forall S n c, pj (La2v S n c) = La2 S n. Proof. reflexivity. Qed.
Lemma pj_L9v : forall S n c, pj (L9v S n c) = L9 S n. Proof. reflexivity. Qed.
Lemma pj_LB1v : forall S kq KN V, pj (LB1v S kq KN V) = LB1 S kq KN. Proof. reflexivity. Qed.
Lemma pj_LB2v : forall S kq KN V, pj (LB2v S kq KN V) = LB2 S kq KN. Proof. reflexivity. Qed.
Lemma pj_LB3v : forall S kq KN V, pj (LB3v S kq KN V) = LB3 S kq KN. Proof. reflexivity. Qed.
Lemma univ_a : forall b c S n, uni b 1 c -> univ b (L9v S n c) /\ univ b (La2v S n c) /\ univ b (La1v S n c).
Proof. intros b c S n H. cbn [L9v La2v La1v univ]. tauto. Qed.
Lemma univ_b : forall b V S kq KN, uni b 4 V -> univ b (LB1v S kq KN V) /\ univ b (LB2v S kq KN V) /\ univ b (LB3v S kq KN V).
Proof. intros b V S kq KN H. cbn [LB1v LB2v LB3v univ]. tauto. Qed.

Section EQV.
Context {fx : FPState}.
Abbreviation KNf n kq := (kq + (4 * Z.shiftr (((n + (-1 * kq))) mod 2^64) 2)).
Abbreviation V4f R n kq wc := (bv_unsigned (edenot (Ez R (AXF_mscBz.VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304)))).
#[using="Type"] Lemma eqv_a1 : forall m R n c, AXF_mscAz.mscA_mem_pmsca1 m R n c = zwv m (La1v (S10 R) n c). Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma eqv_a2 : forall m R n c, AXF_mscAz.mscA_mem_pmsca2 m R n c = zwv m (La2v (S10 R) n c). Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma eqv_a3 : forall m R n c, AXF_mscAz.mscA_mem_pmsca3 m R n c = zwv m (L9v (S10 R) n c). Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma eqv_a9 : forall m R n c, AXF_mscAz.mscA_mem_pmsca9 m R n c = zwv m (L9v (S10 R) n c). Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma eqv_b1 : forall m R n kq wc, AXF_mscBz.mscB_mem_pmscb1 m R n kq wc = zwv m (LB1v (S10 R) kq (KNf n kq) (V4f R n kq wc)). Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma eqv_b2 : forall m R n kq wc, AXF_mscBz.mscB_mem_pmscb2 m R n kq wc = zwv m (LB2v (S10 R) kq (KNf n kq) (V4f R n kq wc)). Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma eqv_b3 : forall m R n kq wc, AXF_mscBz.mscB_mem_pmscb3 m R n kq wc = zwv m (LB3v (S10 R) kq (KNf n kq) (V4f R n kq wc)). Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma eqv_b4 : forall m R n kq wc, AXF_mscBz.mscB_mem_pmscb4 m R n kq wc = zwv m (LB3v (S10 R) kq (KNf n kq) (V4f R n kq wc)). Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
End EQV.

(* [comment removed for export] *)
Lemma blk_v : forall m blk v b x, uni b 8 v -> 1 <= blk -> blk + 32 <= 2^47 -> blk <= x < blk + 32 ->
  wbytes (wbytes (wbytes (wbytes m (wa (blk + 0)) (word_to_le_bytes 8 (wa v))) (wa (blk + 8)) (word_to_le_bytes 8 (wa v)))
         (wa (blk + 16)) (word_to_le_bytes 8 (wa v))) (wa (blk + 24)) (word_to_le_bytes 8 (wa v)) (wa x) = Some (Z_to_bv 8 b).
Proof.
  intros m blk v b x Hu H1 H2 Hx.
  assert (Lw : length (word_to_le_bytes 8 (wa v)) = 8%nat) by apply length_N_to_le_bytes.
  destruct (Z_lt_ge_dec x (blk + 24)) as [X1|X1]; [|apply (wbv_hit _ _ 8 v b x Hu); lia].
  rewrite wb_other by (rewrite ?Lw; cbn; lia).
  destruct (Z_lt_ge_dec x (blk + 16)) as [X2|X2]; [|apply (wbv_hit _ _ 8 v b x Hu); lia].
  rewrite wb_other by (rewrite ?Lw; cbn; lia).
  destruct (Z_lt_ge_dec x (blk + 8)) as [X3|X3]; [|apply (wbv_hit _ _ 8 v b x Hu); lia].
  rewrite wb_other by (rewrite ?Lw; cbn; lia). apply (wbv_hit _ _ 8 v b x Hu); lia.
Qed.

Theorem msc_loop_v : forall {fx : FPState} rom (t : nat) R mm blk rem b, rem / 32 = Z.of_nat t -> 32 <= rem <= 2^32 -> 1 <= blk -> blk + rem <= 2^47 ->
  getr R 11 = wa blk -> getr R 13 = wa 31 -> getr R 14 = wa rem -> uni b 8 (bv_unsigned (getr R 12)) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= rem -> store_ok SEGS mm (wa (blk + d)) k = true) ->
  exists R' mm', msteps SEGS (mkst R (wa 0xd3160) mm rom) (mkst R' (wa 0xd317c) mm' rom) /\
    (forall k, In k KLOOP -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) /\
    (forall x, blk <= x < blk + 32 * (rem / 32) -> mm' (wa x) = Some (Z_to_bv 8 b)) /\
    (forall x, 0 <= x < 2^64 -> ~ (blk <= x < blk + 32 * (rem / 32)) -> mm' (wa x) = mm (wa x)) /\ mem_grows mm mm'.
Proof.
  intros fx rom t. induction t as [|t IH]; intros R mm blk rem b Ht Hr Hb Hbr R11 R13 R14 Hu HW.
  { exfalso. pose proof (Z.div_le_lower_bound rem 32 1 ltac:(lia) ltac:(lia)). lia. }
  set (vc := bv_unsigned (getr R 12)) in *.
  assert (R12 : getr R 12 = wa vc) by (unfold vc; rewrite wa_u; reflexivity).
  assert (Hvc : 0 <= vc <= 2^64 - 1) by apply rng64.
  assert (P : AXF_msclz.mscl_pre R mm blk rem vc).
  { constructor; try assumption; try lia. intros d k Hd Hk. replace (blk + 0 + d) with (blk + d) by lia. apply HW; lia. }
  destruct (Z_lt_ge_dec rem 64) as [Hx|Hc].
  - destruct (AXF_msclz.mscl_pmsclx R mm rom blk rem vc P (scc_lx R mm blk rem vc ltac:(lia) ltac:(lia))) as (R' & Hms & E11 & E12 & E13 & E14 & KK).
    exists R', (AXF_msclz.mscl_mem_pmsclx mm R blk rem vc). split; [exact Hms|].
    assert (Eq1 : rem / 32 = 1) by (symmetry; apply Z.div_unique with (rem - 32); lia).
    rewrite Eq1. split; [|split; [|split]].
    + intros k Hk. cbn [KLOOP In] in Hk.
      repeat (destruct Hk as [<-|Hk]; [first [solve [apply KK; cbn [In]; memb] | (regzH E12; regzH R12; rewrite E12, R12; reflexivity) | (regzH E13; regzH R13; rewrite E13, R13; reflexivity)]|]). destruct Hk.
    + intros x Hx'. unfold AXF_msclz.mscl_mem_pmsclx. apply blk_v; [exact Hu | lia | lia | lia].
    + intros x Hx' Hn. unfold AXF_msclz.mscl_mem_pmsclx. rewrite !wb_other by (rewrite ?length_N_to_le_bytes; lia). reflexivity.
    + unfold AXF_msclz.mscl_mem_pmsclx. growsc.
  - destruct (AXF_msclz.mscl_pmsclc R mm rom blk rem vc P (scc_lc R mm blk rem vc ltac:(lia) ltac:(lia))) as (R1 & Hms1 & E11 & E12 & E13 & E14 & KK1).
    set (mm1 := AXF_msclz.mscl_mem_pmsclc mm R blk rem vc) in *.
    assert (Ht' : (rem - 32) / 32 = Z.of_nat t).
    { replace rem with ((rem - 32) + 1 * 32) in Ht by lia. rewrite Z.div_add in Ht by lia. lia. }
    assert (G1 : mem_grows mm mm1) by (unfold mm1, AXF_msclz.mscl_mem_pmsclc; growsc).
    assert (Z1 : forall x, blk <= x < blk + 32 -> mm1 (wa x) = Some (Z_to_bv 8 b)) by (intros x Hx; unfold mm1, AXF_msclz.mscl_mem_pmsclc; apply blk_v; [exact Hu | lia | lia | lia]).
    assert (F1 : forall x, 0 <= x < 2^64 -> ~ (blk <= x < blk + 32) -> mm1 (wa x) = mm (wa x)).
    { intros x Hx Hn. unfold mm1, AXF_msclz.mscl_mem_pmsclc. rewrite !wb_other by (rewrite ?length_N_to_le_bytes; lia). reflexivity. }
    clearbody mm1.
    assert (Hu1 : uni b 8 (bv_unsigned (getr R1 12))) by (rewrite E12, u_wa_small by lia; exact Hu).
    destruct (IH R1 mm1 (blk + 32) (rem - 32) b Ht' ltac:(lia) ltac:(lia) ltac:(lia) E11 E13 ltac:(rewrite E14; f_equal; lia) Hu1)
      as (R' & mm' & Hms' & KK' & Z' & F' & G').
    { intros d k Hd Hk. replace (blk + 32 + d) with (blk + (32 + d)) by lia. apply (store_ok_mono SEGS k mm mm1 _ G1). apply HW; lia. }
    exists R', mm'. split; [exact (msteps_trans SEGS _ _ _ Hms1 Hms')|].
    assert (Eq : rem / 32 = 1 + (rem - 32) / 32) by (replace rem with ((rem - 32) + 1 * 32) at 1 by lia; rewrite Z.div_add by lia; lia).
    split; [|split; [|split]].
    + intros k Hk. rewrite (KK' k Hk). cbn [KLOOP In] in Hk.
      repeat (destruct Hk as [<-|Hk]; [first [solve [apply KK1; cbn [In]; memb] | (regzH E12; regzH R12; rewrite E12, R12; reflexivity) | (regzH E13; regzH R13; rewrite E13, R13; reflexivity)]|]). destruct Hk.
    + intros x Hx. destruct (Z_lt_ge_dec x (blk + 32)) as [X|X].
      * rewrite F' by lia. apply Z1; lia.
      * apply Z'. lia.
    + intros x Hx Hn. rewrite F' by lia. apply F1; lia.
    + exact (mem_grows_trans _ _ _ G1 G').
Qed.

(* [comment removed for export] *)
Lemma wc_of_c : forall c, 0 <= c -> (72057594037927936 * c) mod 2^64 = 72057594037927936 * (c mod 256).
Proof. intros c Hc. change (2^64) with (72057594037927936 * 256). apply Z.mul_mod_distr_l; lia. Qed.

Section Contract.
Context {fx : FPState}.

#[using="Type"] Theorem memsetck_contract : forall rom R m s n,
  getr R 10 = wa s -> getr R 12 = wa n ->
  1 <= s -> 0 <= n <= 2^32 -> s + n <= 2^47 ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= n -> store_ok SEGS m (wa (s + d)) k = true) ->
  exists R' m', msteps SEGS (mkst R (wa 0xd3088) m rom) (mkst R' (wa 0xd317c) m' rom) /\
    (forall k, In k KMS -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) /\
    (forall x, s <= x < s + n -> m' (wa x) = Some (Z_to_bv 8 (bv_unsigned (getr R 11) mod 256))) /\
    (forall x, 0 <= x < 2^64 -> ~ (s <= x < s + n) -> m' (wa x) = m (wa x)) /\ mem_grows m m'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros rom R m s n R10 R12 Hs Hn Hsn HW.
  assert (Hs10 : bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10))) = s) by (regzH R10; rewrite R10; apply u_wa_small; lia).
  set (c := bv_unsigned (getr R 11)).
  assert (R11 : getr R 11 = wa c) by (unfold c; rewrite wa_u; reflexivity).
  assert (Hc : 0 <= c <= 2^64 - 1) by apply rng64.
  set (b := c mod 256).
  assert (Hb : 0 <= b < 256) by (unfold b; apply Z.mod_pos_bound; lia).
  assert (U1 : uni b 1 c) by (apply uni1; lia).
  destruct (univ_a b c s n U1) as (UA9 & UA2 & UA1).
  destruct (Z.eq_dec n 0) as [Hn0|Hn0].
  { subst n.
    assert (P : AXF_msc0z.msc0_pre R m c) by (constructor; [exact R11 | exact R12 | exact Hc | rewrite Hs10; lia]).
    destruct (AXF_msc0z.msc0_pmsc0 R m rom c P (scc_0 R m c)) as (R' & Hms & _ & _ & KK).
    exists R', m. split; [exact Hms|]. split; [kms KK|]. split; [intros x Hx; lia|]. split; [intros x _ _; reflexivity | apply mem_grows_refl]. }
  assert (Hn1 : 1 <= n) by lia. clear Hn0.
  assert (HWA : forall d k, 0 <= d -> d + Z.of_nat k <= n -> store_ok SEGS m (wa (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10))) + 0 + d)) k = true).
  { intros d k Hd Hk. rewrite Hs10. replace (s + 0 + d) with (s + d) by lia. apply HW; lia. }
  assert (PA : AXF_mscAz.mscA_pre R m n c) by (constructor; [exact R11 | exact R12 | lia | exact Hc | rewrite Hs10; lia | exact HWA]).
  destruct (Z_lt_ge_dec n 9) as [Hn9|Hn9].
  { destruct (Z_lt_ge_dec n 3) as [H3|H3]; [|destruct (Z_lt_ge_dec n 7) as [H7|H7]].
    - destruct (AXF_mscAz.mscA_pmsca1 R m rom n c PA (scc_a1 R m s n c Hs10 ltac:(lia) ltac:(lia) ltac:(lia) HW ltac:(lia))) as (R' & Hms & _ & _ & _ & _ & KK).
      exists R', (AXF_mscAz.mscA_mem_pmsca1 m R n c). split; [exact Hms|]. split; [kms KK|].
      split; [|split; [exact (fr_a1 m R s n c Hs10 Hs Hsn ltac:(lia)) | unfold AXF_mscAz.mscA_mem_pmsca1; growsc]].
      intros x Hx. rewrite eqv_a1, Hs10. apply (fin_v m _ s n b Hs Hsn UA1); rewrite ?pj_La1v; [apply wok_a1; lia | intros y Hy; apply cov_a1; lia | exact Hx].
    - destruct (AXF_mscAz.mscA_pmsca2 R m rom n c PA (scc_a2 R m s n c Hs10 ltac:(lia) ltac:(lia) ltac:(lia) HW ltac:(lia))) as (R' & Hms & _ & _ & _ & _ & KK).
      exists R', (AXF_mscAz.mscA_mem_pmsca2 m R n c). split; [exact Hms|]. split; [kms KK|].
      split; [|split; [exact (fr_a2 m R s n c Hs10 Hs Hsn ltac:(lia)) | unfold AXF_mscAz.mscA_mem_pmsca2; growsc]].
      intros x Hx. rewrite eqv_a2, Hs10. apply (fin_v m _ s n b Hs Hsn UA2); rewrite ?pj_La2v; [apply wok_a2; lia | intros y Hy; apply cov_a2; lia | exact Hx].
    - destruct (AXF_mscAz.mscA_pmsca3 R m rom n c PA (scc_a3 R m s n c Hs10 ltac:(lia) ltac:(lia) ltac:(lia) HW ltac:(lia))) as (R' & Hms & _ & _ & _ & _ & _ & KK).
      exists R', (AXF_mscAz.mscA_mem_pmsca3 m R n c). split; [exact Hms|]. split; [kms KK|].
      split; [|split; [exact (fr_a3 m R s n c Hs10 Hs Hsn ltac:(lia)) | unfold AXF_mscAz.mscA_mem_pmsca3; growsc]].
      intros x Hx. rewrite eqv_a3, Hs10. apply (fin_v m _ s n b Hs Hsn UA9); rewrite ?pj_L9v; [apply wok_9; lia | intros y Hy; apply cov_a3; lia | exact Hx]. }
  (* [comment removed for export] *)
  assert (Hn9' : 9 <= n) by lia. clear Hn9. rename Hn9' into Hn9.
  destruct (AXF_mscAz.mscA_pmsca9 R m rom n c PA (scc_a9 R m s n c Hs10 ltac:(lia) ltac:(lia) ltac:(lia) HW ltac:(lia))) as (R9 & Hms9 & A11 & A12 & A14 & A15 & A16 & A13 & KK9).
  set (m9 := AXF_mscAz.mscA_mem_pmsca9 m R n c) in *.
  assert (G9 : mem_grows m m9) by (unfold m9, AXF_mscAz.mscA_mem_pmsca9; growsc).
  assert (F9 : fr_in m m9 s (s + n)) by exact (fr_a9 m R s n c Hs10 Hs Hsn Hn9).
  assert (M9 : m9 = zwv m (L9v s n c)) by (unfold m9; rewrite eqv_a9, Hs10; reflexivity).
  clearbody m9.
  set (kq := bv_unsigned (getr R9 13)) in *.
  assert (B13 : getr R9 13 = wa kq) by (unfold kq; rewrite wa_u; reflexivity).
  set (wc := bv_unsigned (getr R9 16)).
  assert (B16 : getr R9 16 = wa wc) by (unfold wc; rewrite wa_u; reflexivity).
  assert (Hwc : 0 <= wc <= 2^64 - 1) by apply rng64.
  assert (Ewc : wc = 72057594037927936 * b) by (unfold wc; rewrite A16, u_wa; unfold b; apply wc_of_c; lia).
  assert (S9 : bv_unsigned (getr R9 (Z_to_bv 5 (Z.of_nat 10))) = s) by (rewrite (KK9 10%nat ltac:(cbn; tauto)); exact Hs10).
  assert (HW9 : forall d k, 0 <= d -> d + Z.of_nat k <= n -> store_ok SEGS m9 (wa (s + d)) k = true).
  { intros d k Hd Hk. apply (store_ok_mono SEGS k m m9 _ G9). apply HW; lia. }
  assert (PB : AXF_mscBz.mscB_pre R9 m9 n kq wc).
  { constructor; [exact A11 | exact A12 | exact B13 | exact A14 | exact A15 | exact B16 | lia | lia | exact Hwc | rewrite S9; lia |].
    intros d k Hd Hk. rewrite S9. replace (s + 0 + d) with (s + d) by lia. apply HW9; lia. }
  set (q := (n - kq) / 4).
  assert (Hq : n - kq - 3 <= 4 * q <= n - kq) by (unfold q; clear - Hn9 A13; Z.div_mod_to_equations; lia).
  assert (EN4 : 4 * Z.shiftr ((n + -1 * kq) mod 2^64) 2 = 4 * q).
  { rewrite Z.mod_small by (clear - Hn Hn9 A13; lia). rewrite Z.shiftr_div_pow2 by lia. change (2^2) with 4. replace (n + -1 * kq) with (n - kq) by lia. reflexivity. }
  assert (EKN : kq + 4 * Z.shiftr ((n + -1 * kq) mod 2^64) 2 = kq + 4 * q) by (rewrite EN4; reflexivity).
  assert (EV4 : bv_unsigned (edenot (Ez R9 (AXF_mscBz.VALS_mscB n kq wc)) (EMd M_MULHU (EVar 34) (ELit 4311810304))) = b * 16843009)
    by exact (val4 R9 n kq wc b Hb Ewc).
  destruct (univ_b b (b * 16843009) s kq (kq + 4 * q) (uni4 b Hb)) as (UB1 & UB2 & UB3).
  assert (KK2 : forall RB, (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat ->
                 getr RB (Z_to_bv 5 (Z.of_nat k)) = getr R9 (Z_to_bv 5 (Z.of_nat k))) ->
                forall k, In k KMS -> getr RB (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
  { intros RB KKB k Hk. rewrite (KKB k Hk). exact (KK9 k Hk). }
  clear HWA PA.
  destruct (Z_lt_ge_dec (4 * q) 9) as [Hb1|Hb1].
  { destruct (AXF_mscBz.mscB_pmscb1 R9 m9 rom n kq wc PB (scc_b1 R9 m9 s n kq wc S9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HW9 ltac:(change ((n - kq) / 4) with q; lia)))
      as (RB & HmsB & _ & _ & _ & _ & _ & KKB).
    exists RB, (AXF_mscBz.mscB_mem_pmscb1 m9 R9 n kq wc). split; [exact (msteps_trans SEGS _ _ _ Hms9 HmsB)|]. split; [exact (KK2 RB KKB)|].
    split; [|split; [exact (fr_trans _ _ _ _ _ F9 (fr_b1 m9 R9 s n kq q wc S9 Hs Hsn Hn9 A13 Hq EN4)) | exact (mem_grows_trans _ _ _ G9 (ltac:(unfold AXF_mscBz.mscB_mem_pmscb1; growsc) : mem_grows m9 (AXF_mscBz.mscB_mem_pmscb1 m9 R9 n kq wc)))]].
    intros x Hx. rewrite eqv_b1, S9, EKN, EV4, M9, <- zwv_app.
    apply (fin_v m _ s n b Hs Hsn (univ_app b _ _ UA9 UB1)); rewrite ?pj_app, ?pj_L9v, ?pj_LB1v; [exact (wok_b1 s n kq q Hn9 A13 Hq) | intros y Hy; exact (cov_b1 s n kq q y Hn9 A13 Hq Hy Hb1) | exact Hx]. }
  destruct (Z_lt_ge_dec (4 * q) 25) as [Hb2|Hb2].
  { destruct (AXF_mscBz.mscB_pmscb2 R9 m9 rom n kq wc PB (scc_b2 R9 m9 s n kq wc S9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HW9 ltac:(change ((n - kq) / 4) with q; lia)))
      as (RB & HmsB & _ & _ & _ & _ & _ & KKB).
    exists RB, (AXF_mscBz.mscB_mem_pmscb2 m9 R9 n kq wc). split; [exact (msteps_trans SEGS _ _ _ Hms9 HmsB)|]. split; [exact (KK2 RB KKB)|].
    split; [|split; [exact (fr_trans _ _ _ _ _ F9 (fr_b2 m9 R9 s n kq q wc S9 Hs Hsn A13 Hq EN4 (Z.ge_le _ _ Hb1))) | exact (mem_grows_trans _ _ _ G9 (ltac:(unfold AXF_mscBz.mscB_mem_pmscb2; growsc) : mem_grows m9 (AXF_mscBz.mscB_mem_pmscb2 m9 R9 n kq wc)))]].
    intros x Hx. rewrite eqv_b2, S9, EKN, EV4, M9, <- zwv_app.
    apply (fin_v m _ s n b Hs Hsn (univ_app b _ _ UA9 UB2)); rewrite ?pj_app, ?pj_L9v, ?pj_LB2v; [exact (wok_b2 s n kq q Hn9 A13 Hq (Z.ge_le _ _ Hb1)) | intros y Hy; exact (cov_b2 s n kq q y Hn9 A13 Hq Hy ltac:(lia)) | exact Hx]. }
  set (k4 := Z.land (s + kq) 4).
  assert (Hk4 : k4 = 0 \/ k4 = 4) by apply land4.
  assert (EK4 : Z.land ((s + kq) mod 2^64) 4 = k4) by (rewrite Z.mod_small by (clear - Hs Hsn Hn A13; lia); reflexivity).
  destruct (Z_lt_ge_dec (4 * q - 24 - k4) 32) as [Hb3|Hb3].
  { destruct (AXF_mscBz.mscB_pmscb3 R9 m9 rom n kq wc PB (scc_b3 R9 m9 s n kq wc S9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HW9 ltac:(change ((n - kq) / 4) with q; lia) Hk4 ltac:(change ((n - kq) / 4) with q; fold k4; lia)))
      as (RB & HmsB & _ & _ & _ & _ & _ & KKB).
    exists RB, (AXF_mscBz.mscB_mem_pmscb3 m9 R9 n kq wc). split; [exact (msteps_trans SEGS _ _ _ Hms9 HmsB)|]. split; [exact (KK2 RB KKB)|].
    split; [|split; [exact (fr_trans _ _ _ _ _ F9 (fr_b3 m9 R9 s n kq q wc S9 Hs Hsn A13 Hq EN4 (Z.ge_le _ _ Hb2))) | exact (mem_grows_trans _ _ _ G9 (ltac:(unfold AXF_mscBz.mscB_mem_pmscb3; growsc) : mem_grows m9 (AXF_mscBz.mscB_mem_pmscb3 m9 R9 n kq wc)))]].
    intros x Hx. rewrite eqv_b3, S9, EKN, EV4, M9, <- zwv_app.
    apply (fin_v m _ s n b Hs Hsn (univ_app b _ _ UA9 UB3)); rewrite ?pj_app, ?pj_L9v, ?pj_LB3v; [exact (wok_b3 s n kq q Hn9 A13 Hq (Z.ge_le _ _ Hb2)) | intros y Hy; exact (cov_b3 s n kq q y Hn9 A13 Hq Hy ltac:(slia)) | exact Hx]. }
  (* [comment removed for export] *)
  destruct (AXF_mscBz.mscB_pmscb4 R9 m9 rom n kq wc PB (scc_b4 R9 m9 s n kq wc S9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HW9 ltac:(change ((n - kq) / 4) with q; lia) Hk4 ltac:(change ((n - kq) / 4) with q; fold k4; lia)))
    as (RB & HmsB & B11 & B12' & B13' & B14 & _ & _ & KKB).
  set (mB := AXF_mscBz.mscB_mem_pmscb4 m9 R9 n kq wc) in *.
  assert (GB : mem_grows m mB) by exact (mem_grows_trans _ _ _ G9 (ltac:(unfold mB, AXF_mscBz.mscB_mem_pmscb4; growsc) : mem_grows m9 mB)).
  assert (FB : fr_in m mB s (s + n)) by exact (fr_trans _ _ _ _ _ F9 (fr_b4 m9 R9 s n kq q wc S9 Hs Hsn A13 Hq EN4 (Z.ge_le _ _ Hb2))).
  assert (MB : mB = zwv m (L9v s n c ++ LB3v s kq (kq + 4 * q) (b * 16843009))) by (unfold mB; rewrite eqv_b4, S9, EKN, EV4, M9, <- zwv_app; reflexivity).
  clearbody mB.
  set (blk := s + (kq + k4) + 24) in *. set (rem := 4 * q + -1 * k4 + -24) in *.
  assert (B11' : getr RB 11 = wa blk) by (rewrite B11, S9, EK4; reflexivity).
  assert (B14' : getr RB 14 = wa rem) by (rewrite B14, S9, EK4, EN4; reflexivity).
  assert (U8 : uni b 8 (bv_unsigned (getr RB 12))) by (rewrite B12', u_wa_small by (pose proof (rng64 (edenot (Ez R9 (AXF_mscBz.VALS_mscB n kq wc)) (EAlu ALU_OR (EMd M_MUL (ELit 4294967296) (EMd M_MULHU (EVar 34) (ELit 4311810304))) (EAlu ALU_SRL (EMd M_MUL (ELit 4294967296) (EMd M_MULHU (EVar 34) (ELit 4311810304))) (ELit 32))))); lia);
                                                       rewrite (val8 R9 n kq wc b Hb Ewc); apply uni8; exact Hb).
  destruct (loop_bounds s n kq q k4 blk rem Hn9 A13 Hq Hk4 eq_refl eq_refl ltac:(unfold rem; lia)) as (Lb1 & Lb2 & Hrem & Lr & Lbr).
  assert (HWL : forall d k, 0 <= d -> d + Z.of_nat k <= rem -> store_ok SEGS mB (wa (blk + d)) k = true).
  { intros d k Hd Hk. apply (store_ok_mono SEGS k m mB _ GB). replace (blk + d) with (s + (blk - s + d)) by slia. apply HW; slia. }
  destruct (msc_loop_v rom (Z.to_nat (rem / 32)) RB mB blk rem b Hrem ltac:(slia) ltac:(slia) ltac:(slia) B11' B13' B14' U8 HWL)
    as (R' & m' & HmsL & KKL & ZL & FL & GL).
  exists R', m'. split; [exact (msteps_trans SEGS _ _ _ (msteps_trans SEGS _ _ _ Hms9 HmsB) HmsL)|].
  split; [intros k Hk; rewrite (KKL k ltac:(insub Hk)); exact (KK2 RB KKB k Hk)|].
  split; [|split; [intros x Hx Hn'; rewrite (FL x Hx ltac:(slia)); exact (FB x Hx Hn') | exact (mem_grows_trans _ _ _ GB GL)]].
  assert (W3 : wok (pj (L9v s n c ++ LB3v s kq (kq + 4 * q) (b * 16843009))) 0 (2^64))
    by (rewrite pj_app, pj_L9v, pj_LB3v; apply (wok_mono _ s (s + n)); [exact (wok_b3 s n kq q Hn9 A13 Hq (Z.ge_le _ _ Hb2)) | lia | lia]).
  intros x Hx. destruct (cov_b4' s n kq q x k4 blk rem Hn9 A13 Hq Hx Hk4 eq_refl eq_refl ltac:(slia)) as [Hcv|Hl]; [|exact (ZL x Hl)].
  rewrite <- (pj_L9v s n c), <- (pj_LB3v s kq (kq + 4 * q) (b * 16843009)), <- pj_app in Hcv.
  destruct (Z_le_gt_dec blk x) as [X1|X1]; [destruct (Z_lt_ge_dec x (blk + 32 * (rem / 32))) as [X2|X2]|].
  - exact (ZL x ltac:(slia)).
  - rewrite (FL x ltac:(slia) ltac:(slia)), MB. exact (zwv_hit _ m b x ltac:(slia) (univ_app b _ _ UA9 UB3) W3 Hcv).
  - rewrite (FL x ltac:(slia) ltac:(slia)), MB. exact (zwv_hit _ m b x ltac:(slia) (univ_app b _ _ UA9 UB3) W3 Hcv).
Qed.
End Contract.
End AXG_msc3.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac is_arith T := lazymatch T with
  | @eq Z _ _ => idtac | Z.le _ _ => idtac | Z.lt _ _ => idtac | Z.ge _ _ => idtac | Z.gt _ _ => idtac
  | @eq nat _ _ => idtac | Nat.le _ _ => idtac | Nat.lt _ _ => idtac | le _ _ => idtac | lt _ _ => idtac
  | ?A /\ ?B => is_arith A; is_arith B
  | ?A \/ ?B => is_arith A; is_arith B
  | ~ ?A => is_arith A
  | True => idtac | False => idtac
  end.
Ltac prune_ctx := repeat match goal with
  | H : ?T |- _ => lazymatch type of T with
                   | Prop => tryif is_arith T then fail else clear H
                   | _ => fail
                   end
  end.
Ltac prune_mod := lazymatch goal with
  | |- context [Z.modulo _ _] => idtac
  | |- context [Z.div _ _] => idtac
  | _ => repeat match goal with
              | H : Z.modulo _ _ = _ |- _ => clear H
              | H : context [Z.modulo _ _] |- _ => lazymatch type of H with _ /\ _ => let H1 := fresh "C" in let H2 := fresh "C" in pose proof H as [H1 H2]; clear H end
              end
  end.
Ltac slia := first [ LiaFast.lia_fast_tiers | (prune_ctx; prune_mod; lia) ].
Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
Definition b_of (nc j : Z) : Z := (j + nc - 1) / nc.      (* [comment removed for export] *)
Definition cnt_of (nc j : Z) : Z := nc * b_of nc j - j.   (* [comment removed for export] *)

Lemma b_of_bounds : forall nc j, 1 <= nc -> 1 <= j -> nc * (b_of nc j - 1) < j <= nc * b_of nc j.
Proof.
  intros nc j Hn Hj. unfold b_of.
  pose proof (Z.div_mod (j + nc - 1) nc ltac:(lia)) as E. pose proof (Z.mod_pos_bound (j + nc - 1) nc ltac:(lia)) as R. nia.
Qed.
Lemma cnt_of_range : forall nc j, 1 <= nc -> 1 <= j -> 0 <= cnt_of nc j < nc.
Proof. intros nc j Hn Hj. pose proof (b_of_bounds nc j Hn Hj). unfold cnt_of. lia. Qed.
Lemma b_of_unique : forall nc j b, 1 <= nc -> nc * (b - 1) < j <= nc * b -> b_of nc j = b.
Proof.
  intros nc j b Hn H. unfold b_of. symmetry. apply (Z.div_unique _ _ _ (j + nc - 1 - nc * b)); [left; lia | ring].
Qed.
Lemma b_of_pos : forall nc j, 1 <= nc -> 1 <= j -> 1 <= b_of nc j.
Proof. intros nc j Hn Hj. pose proof (b_of_bounds nc j Hn Hj). nia. Qed.
Lemma pop_step : forall nc j, 1 <= nc -> 1 <= j -> 1 <= cnt_of nc j -> b_of nc (j + 1) = b_of nc j /\ cnt_of nc (j + 1) = cnt_of nc j - 1.
Proof.
  intros nc j Hn Hj Hc. pose proof (b_of_bounds nc j Hn Hj) as B. unfold cnt_of in *.
  assert (E : b_of nc (j + 1) = b_of nc j) by (apply b_of_unique; lia). rewrite E. split; [reflexivity | ring].
Qed.
Lemma refill_step : forall nc j, 1 <= nc -> 1 <= j -> cnt_of nc j = 0 -> j = nc * b_of nc j /\ b_of nc (j + 1) = b_of nc j + 1 /\ cnt_of nc (j + 1) = nc - 1.
Proof.
  intros nc j Hn Hj Hc. pose proof (b_of_bounds nc j Hn Hj) as B. unfold cnt_of in *.
  assert (E : b_of nc (j + 1) = b_of nc j + 1) by (apply b_of_unique; lia). rewrite E. split; [lia | split; [reflexivity | lia]].
Qed.
Lemma c_of_nd : forall ND, 33 <= ND <= 512 -> Z.shiftr ((ND + 31) mod 2^64) 5 = (ND + 31) / 32.
Proof. intros ND H. rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma c_of_nd_range : forall ND, 33 <= ND <= 512 -> 2 <= (ND + 31) / 32 <= 16.
Proof. intros ND H. split; [apply Z.div_le_lower_bound; lia | apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia]. Qed.
Lemma chp_off : forall cnt, 1 <= cnt < 2^31 -> Z.shiftr ((4294967296 * ext_Z true 0 4 cnt + -4294967296) mod 2^64) 30 = 4 * (cnt - 1).
Proof.
  intros cnt H. rewrite ext_Z_lo32_small by lia.
  rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^30) with 1073741824.
  replace (4294967296 * cnt + -4294967296) with ((4 * (cnt - 1)) * 1073741824) by ring. apply Z.div_mul. lia.
Qed.
Lemma ext_Z_u32 : forall z, 0 <= z < 2^32 -> ext_Z false 0 4 z = z.
Proof. intros z H. unfold ext_Z. change (2 ^ (8 * Z.of_nat 0)) with 1. change (2 ^ (8 * Z.of_nat 4)) with (2^32). rewrite Z.div_1_r. apply Z.mod_small. lia. Qed.

(* [comment removed for export] *)
Definition wr (m : word -> option byte) (a n : Z) : Prop :=
  forall d k, 0 <= d -> d + Z.of_nat k <= n -> store_ok SEGS m (wa (a + d)) k = true.

Abbreviation REC CA c := (CA + 80 * c).
Abbreviation RIX SB c := (SB + 137438953472 + 128 * c).       (* [comment removed for export] *)
Abbreviation FAX SB c := (SB + c * 4294967296 + 3758096384).  (* [comment removed for export] *)

Record INV_C (m : word -> option byte) (CA SB c sz nc newc j : Z) : Prop := {
  ic_geo : 2 <= c <= 16 /\ 16 <= sz /\ sz mod 16 = 0 /\ 1 <= nc <= 8 /\ 1 <= j /\ j + nc <= newc /\ newc * sz <= 262144 /\ newc <= 16384 ;
  ic_SB : rd m 923512 8 SB ;
  ic_RIB : rd m 923528 8 (SB + 137438953472) ;
  ic_cnt : rd m (REC CA c) 4 (cnt_of nc j) ;
  ic_mc : rd m (REC CA c + 4) 4 (2 * nc) ;
  ic_sz : rd m (REC CA c + 8) 8 sz ;
  ic_chunks : forall i, 0 <= i < cnt_of nc j -> rd m (REC CA c + 16 + 4 * i) 4 ((j + cnt_of nc j - 1 - i) * (sz / 16)) ;
  ic_mutex : rd m (RIX SB c) 8 0 ;
  ic_nf : rd m (RIX SB c + 16) 8 (newc - nc * b_of nc j) ;
  ic_na : exists na, 0 <= na < 2^64 /\ rd m (RIX SB c + 72) 8 na ;
  ic_fa : forall k, 0 <= k < newc - nc * b_of nc j -> rd m (FAX SB c + 4 * k) 4 ((newc - 1 - k) * (sz / 16)) ;
  ic_st : exists st, 0 <= st < 2^64 /\ rd m (CA + 2576) 8 st ;
  ic_wrec : wr m (REC CA c) 80 ;
  ic_wri : wr m (RIX SB c) 128 ;
  ic_wst : wr m (CA + 2560) 32
}.

(* [comment removed for export] *)
Definition owned_C (CA SB c x : Z) : Prop :=
  REC CA c <= x < REC CA c + 80 \/ RIX SB c <= x < RIX SB c + 128 \/ CA + 2560 <= x < CA + 2592.

(* [comment removed for export] *)
Definition e_C : expr := EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit 31)) (ELit 5).
Definition e_REC : expr := EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit 80) e_C).
Definition e_RI : expr := EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 128) e_C).
Definition e_CHP : expr := EAlu ALU_ADD (EVar 32) (EAlu ALU_ADD (EMd M_MUL (ELit 80) e_C)
                             (EAlu ALU_SRL (EAlu ALU_ADD (EMd M_MUL (ELit 4294967296) (EExt true 0 4 (EVar 34))) (ELit (-4294967296))) (ELit 30))).

Section ZQ.
Variable E : env.
Variables (CA ND RIB cnt : Z).
Hypothesis H32 : bv_unsigned (ev E 32) = CA.
Hypothesis H33 : bv_unsigned (ev E 33) = ND.
Hypothesis HND : 33 <= ND <= 512.
#[using="H33 HND"] Lemma zq_C : zeval E e_C = (ND + 31) / 32.
Proof. LiaFast.lf_pins (fun (H33 HND : LiaFast.U) => LiaFast.u0). unfold e_C. cbn [zeval edenot]. rewrite H33. change (5 mod 64) with 5. apply c_of_nd. exact HND. Qed.
#[using="H32 H33 HND"] Lemma zq_REC : zeval E e_REC = CA + 80 * ((ND + 31) / 32).
Proof. LiaFast.lf_pins (fun (H32 H33 HND : LiaFast.U) => LiaFast.u0). unfold e_REC. cbn [zeval]. rewrite zq_C. cbn [edenot]. rewrite H32. reflexivity. Qed.
Hypothesis H36 : bv_unsigned (ev E 36) = RIB.
#[using="H33 HND H36"] Lemma zq_RI : zeval E e_RI = RIB + 128 * ((ND + 31) / 32).
Proof. LiaFast.lf_pins (fun (H33 HND H36 : LiaFast.U) => LiaFast.u0). unfold e_RI. cbn [zeval]. rewrite zq_C. cbn [edenot]. rewrite H36. reflexivity. Qed.
Hypothesis H34 : bv_unsigned (ev E 34) = cnt.
Hypothesis Hcnt : 1 <= cnt <= 16.
#[using="H32 H33 HND H34 Hcnt"] Lemma zq_CHP : zeval E e_CHP = CA + (80 * ((ND + 31) / 32) + 4 * (cnt - 1)).
Proof. LiaFast.lf_pins (fun (H32 H33 HND H34 Hcnt : LiaFast.U) => LiaFast.u0).
  unfold e_CHP. cbn [zeval]. rewrite zq_C. cbn [edenot]. rewrite H32, H34. rewrite (Z.mod_small cnt) by lia.
  change (30 mod 64) with 30. rewrite chp_off by lia. reflexivity.
Qed.
End ZQ.

(* [comment removed for export] *)
Ltac bfin := first [ reflexivity | (apply negb_true_iff; first [apply Z.ltb_ge | apply Z.eqb_neq]; slia)
                   | (apply negb_false_iff; first [apply Z.ltb_lt | apply Z.eqb_eq]; slia)
                   | (apply Z.ltb_lt; slia) | (apply Z.ltb_ge; slia) | (apply Z.eqb_eq; slia) | (apply Z.eqb_neq; slia) ].
Ltac scgo := repeat (first [apply Forall_nil | apply Forall_cons]).

Section SCS.
Context {fx : FPState}.
Variables (R : bvmap 5 word) (m : word -> option byte).
Variables (SPa CA ND SB RIB : Z).
Hypothesis HSPa : bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 2))) = SPa.
Hypothesis HND : 33 <= ND <= 512.
Hypothesis HCA : 4194304 <= CA /\ CA + 2592 + 256 <= SPa /\ SPa <= 2^47.
Hypothesis HRI : 4194304 <= RIB /\ RIB + 4096 + 256 <= SPa.
Hypothesis HSEP : CA + 2592 <= RIB \/ RIB + 4096 <= CA.

Ltac zat := repeat match goal with |- context [bv_unsigned (ev (Ez ?R ?V) ?n)] =>
              lazymatch eval cbn in (Nat.ltb n 32) with
              | true => change (bv_unsigned (ev (Ez R V) n)) with (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat n))))
              | false => let v := eval cbn [nth Nat.sub] in (nth (n - 32) V 0) in rewrite (zatom R V n v eq_refl eq_refl) by slia
              end end.
Ltac zq1 V C := first [ rewrite (zq_CHP (Ez R V) CA ND C) by (first [zat; reflexivity | slia])
                      | rewrite (zq_REC (Ez R V) CA ND) by (first [zat; reflexivity | slia])
                      | rewrite (zq_RI (Ez R V) ND RIB) by (first [zat; reflexivity | slia]) ].
Ltac scd V C :=
  first [ (apply sc_br_z; first [rewrite br_geu_z | rewrite br_ltu_z | rewrite br_eq_z | rewrite br_ne_z];
           cbn [zeval edenot]; zat; rewrite ?HSPa; rewrite ?ext_Z_lo32_small by slia; rewrite ?(Z.mod_small _ (2^64)) by slia; bfin)
        | (cbn [sc_denot]; unfold flat, estart, elenZ; cbn [a_base a_off]; rewrite ?zeval_sound, ?u_wa;
           fold e_C e_REC e_RI e_CHP; repeat zq1 V C; cbn [zeval edenot]; zat; rewrite ?HSPa;
           pose proof (c_of_nd_range ND HND); rewrite ?(Z.mod_small _ (2^64)) by slia; repeat split; slia) ].

(* [comment removed for export] *)
#[using="SPa RIB HSPa HND HCA HRI"] Lemma sc_np0p : forall cnt sz cp st, 1 <= cnt <= 16 ->
  scs_denot SEGS m (Ez R (AXF_np0z.VALS_np0 CA ND cnt sz cp SB st)) (snd (fst OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXF_np0z.AXF_np0.RES_pnp0p)).
Proof. LiaFast.lf_pins (fun (SPa RIB HSPa HND HCA HRI : LiaFast.U) => LiaFast.u0). intros cnt sz cp st Hc. cbn [OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXF_np0z.AXF_np0.RES_pnp0p fst snd]. unfold AXF_np0z.VALS_np0. scgo; scd [CA; ND; cnt; sz; cp; SB; st] cnt. Qed.
(* [comment removed for export] *)
#[using="SPa RIB HSPa HND HCA HRI"] Lemma sc_np0r : forall sz st,
  scs_denot SEGS m (Ez R (AXF_np0rz.VALS_np0r CA ND 0 sz SB st)) (snd (fst OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXF_np0rz.AXF_np0r.RES_pnp0r)).
Proof. LiaFast.lf_pins (fun (SPa RIB HSPa HND HCA HRI : LiaFast.U) => LiaFast.u0). intros sz st. cbn [OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXF_np0rz.AXF_np0r.RES_pnp0r fst snd]. unfold AXF_np0rz.VALS_np0r. scgo; scd [CA; ND; 0; sz; SB; st] 1. Qed.
(* [comment removed for export] *)
#[using="SPa RIB HSPa HND HCA HRI"] Lemma sc_npr : forall mc, 2 <= mc <= 16 ->
  scs_denot SEGS m (Ez R (AXF_nprz.VALS_npr CA ND mc)) (snd (fst OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXF_nprz.AXF_npr.RES_pnpr)).
Proof. LiaFast.lf_pins (fun (SPa RIB HSPa HND HCA HRI : LiaFast.U) => LiaFast.u0). intros mc Hmc. cbn [OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXF_nprz.AXF_npr.RES_pnpr fst snd]. unfold AXF_nprz.VALS_npr. scgo; scd [CA; ND; mc] 1. Qed.
(* [comment removed for export] *)
#[using="SPa HSPa HND HCA HRI"] Lemma sc_ng0 : forall n nf, 1 <= n <= 8 -> n <= nf < 2^64 ->
  scs_denot SEGS m (Ez R (AXF_ng0z.VALS_ng0 CA ND n SB RIB nf)) (snd (fst OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXF_ng0z.AXF_ng0.RES_png0)).
Proof. LiaFast.lf_pins (fun (SPa HSPa HND HCA HRI : LiaFast.U) => LiaFast.u0). intros n nf Hn Hnf. cbn [OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXF_ng0z.AXF_ng0.RES_png0 fst snd]. unfold AXF_ng0z.VALS_ng0. scgo; scd [CA; ND; n; SB; RIB; nf] n. Qed.
(* [comment removed for export] *)
#[using="SPa HSPa HND HCA HRI HSEP"] Lemma sc_ngt : forall n na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra, 1 <= n <= 8 ->
  scs_denot SEGS m (Ez R (AXF_ngtz.VALS_ngt CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra)) (snd (fst OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXF_ngtz.AXF_ngt.RES_pngt)).
Proof. LiaFast.lf_pins (fun (SPa HSPa HND HCA HRI HSEP : LiaFast.U) => LiaFast.u0).
  intros n na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra Hn. cbn [OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXF_ngtz.AXF_ngt.RES_pngt fst snd]. unfold AXF_ngtz.VALS_ngt.
  scgo; scd [CA; ND; n; SB; RIB; na; cp; sz; st; g1; g2; g3; g4; g5; g6; g7; g8; g9; g10; g11; c1; c2; c3; c4; c5; cra] n.
Qed.
End SCS.

(* [comment removed for export] *)
Section SCL.
Context {fx : FPState}.
Variables (R : bvmap 5 word) (m : word -> option byte) (FP CP EN w : Z).
Hypothesis HR : 1 <= FP <= 2^47 /\ 1 <= CP <= 2^47 /\ 1 <= EN <= 2^47 /\ 0 <= w <= 2^32 - 1.
Ltac zat := repeat match goal with |- context [bv_unsigned (ev (Ez ?R ?V) ?n)] =>
              let v := eval cbn [nth Nat.sub] in (nth (n - 32) V 0) in rewrite (zatom R V n v eq_refl eq_refl) by slia end.
Ltac scb := apply sc_br_z; first [rewrite br_geu_z | rewrite br_ltu_z | rewrite br_eq_z | rewrite br_ne_z];
            cbn [zeval edenot]; zat; rewrite ?(Z.mod_small _ (2^64)) by slia; bfin.
#[using="HR"] Lemma sc_nglc : CP + 4 <> EN -> scs_denot SEGS m (Ez R (AXF_nglz.VALS_ngl FP CP EN w)) (snd (fst AXF_ngl.RES_pnglc)).
Proof. LiaFast.lf_pins (fun (HR : LiaFast.U) => LiaFast.u0). intros H. cbn [AXF_ngl.RES_pnglc fst snd]. unfold AXF_nglz.VALS_ngl. scgo; scb. Qed.
#[using="HR"] Lemma sc_nglx : CP + 4 = EN -> scs_denot SEGS m (Ez R (AXF_nglz.VALS_ngl FP CP EN w)) (snd (fst AXF_ngl.RES_pnglx)).
Proof. LiaFast.lf_pins (fun (HR : LiaFast.U) => LiaFast.u0). intros H. cbn [AXF_ngl.RES_pnglx fst snd]. unfold AXF_nglz.VALS_ngl. scgo; scb. Qed.
End SCL.
