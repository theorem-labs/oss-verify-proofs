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

Module AXF_mt1.
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

Definition e_d := EVar 32.
Definition sr_mt1 := (sr_upd sr_id 19 (ELit 621712)).
Definition kn_mt1 : list kentry :=
  [ KWord (SA (ELit 0) 621728) 4 (ELit 1);
    KWord (SA (ELit 0) 621648) 8 (ELit 4096);
    KWord (SA (ELit 0) 621736) 8 (ELit 0) ].
Definition scr_mt1 : scripts := SCR [] [] [].
Definition ss_mt1 := SS 0x53a94 sr_mt1 [] kn_mt1 33.
Definition RUN_mt1 := sym_exec SEGS 100 true [0x53b4c; 0x53cd4] scr_mt1 ss_mt1 [].

Definition scr_pmt1 : scripts := SCR [] [] [].
Definition RES_pmt1 := Eval vm_compute in sym_exec SEGS 100 true [0x53b4c; 0x53cd4] scr_pmt1 ss_mt1 [].
Lemma RES_pmt1_ok : sym_exec SEGS 100 true [0x53b4c; 0x53cd4] scr_pmt1 (SS 0x53a94 sr_mt1 [] kn_mt1 33) [] = RES_pmt1.
Proof. vm_compute. reflexivity. Qed.
End AXF_mt1.

Import ListNotations AX2 AX2S.

Module AXF_mt1f.
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

Definition e_fm := EVar 32.
Definition e_nx := EVar 33.
Definition e_pv := EVar 34.
Definition sr_mt1f := (sr_upd sr_id 19 (ELit 621712)).
Definition kn_mt1f : list kentry :=
  [ KRange e_fm 1 (2^63-1);
    KAlign e_fm 8;
    KRange e_nx 1 (2^63-1);
    KRange e_pv 1 (2^63-1);
    KWord (SA (ELit 0) 621728) 4 (ELit 1);
    KWord (SA (ELit 0) 621648) 8 (ELit 4096);
    KWord (SA (ELit 0) 621736) 8 e_fm;
    KWord (SA e_fm 8) 8 e_nx;
    KWord (SA e_fm 0) 8 e_pv;
    KWr (SA (ELit 0) 621736) (ELit 8);
    KWr (SA e_pv 8) (ELit 8);
    KWr (SA e_nx 0) (ELit 8);
    KDisj (SA (ELit 0) 621736) (ELit 8) (SA e_pv 8) (ELit 8);
    KDisj (SA (ELit 0) 621736) (ELit 8) (SA e_nx 0) (ELit 8);
    KDisj (SA e_pv 8) (ELit 8) (SA e_fm 0) (ELit 16);
    KDisj (SA e_nx 0) (ELit 8) (SA e_fm 0) (ELit 16) ].
Definition scr_mt1f : scripts := SCR [true] [] [].
Definition ss_mt1f := SS 0x53a94 sr_mt1f [] kn_mt1f 35.
Definition RUN_mt1f := sym_exec SEGS 100 true [0x53b4c; 0x53cd4] scr_mt1f ss_mt1f [].

Definition scr_pmf1 : scripts := SCR [true] [] [].
Definition RES_pmf1 := Eval vm_compute in sym_exec SEGS 100 true [0x53b4c; 0x53cd4] scr_pmf1 ss_mt1f [].
Lemma RES_pmf1_ok : sym_exec SEGS 100 true [0x53b4c; 0x53cd4] scr_pmf1 (SS 0x53a94 sr_mt1f [] kn_mt1f 35) [] = RES_pmf1.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmfn : scripts := SCR [false] [] [].
Definition RES_pmfn := Eval vm_compute in sym_exec SEGS 100 true [0x53b4c; 0x53cd4] scr_pmfn ss_mt1f [].
Lemma RES_pmfn_ok : sym_exec SEGS 100 true [0x53b4c; 0x53cd4] scr_pmfn (SS 0x53a94 sr_mt1f [] kn_mt1f 35) [] = RES_pmfn.
Proof. vm_compute. reflexivity. Qed.
End AXF_mt1f.

Module AXF_mt1fz.
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

Section MT1F.
Context {fx : FPState}.

Definition VALS_mt1f (fm nx pv : Z) : list Z := [fm; nx; pv].

Record mt1f_pre (regs : bvmap 5 word) (m : word -> option byte) (fm nx pv : Z) : Prop := {
  mt1f_R19 : getr regs 19 = wa 621712 ;
  mt1f_rng_fm : 1 <= fm <= 2^63-1 ;
  mt1f_rng_nx : 1 <= nx <= 2^63-1 ;
  mt1f_rng_pv : 1 <= pv <= 2^63-1 ;
  mt1f_ka1 : fm mod 8 = 0 ;
  mt1f_kw4 : rdn SEGS m (wa (0 + 621728)) 4 = Some (word_to_le_bytes 4 (wa 1)) ;
  mt1f_kw5 : rdn SEGS m (wa (0 + 621648)) 8 = Some (word_to_le_bytes 8 (wa 4096)) ;
  mt1f_kw6 : rdn SEGS m (wa (0 + 621736)) 8 = Some (word_to_le_bytes 8 (wa fm)) ;
  mt1f_kw7 : rdn SEGS m (wa (fm + 8)) 8 = Some (word_to_le_bytes 8 (wa nx)) ;
  mt1f_kw8 : rdn SEGS m (wa (fm + 0)) 8 = Some (word_to_le_bytes 8 (wa pv)) ;
  mt1f_kwr9 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (0 + 621736 + d)) k = true ;
  mt1f_kwr10 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (pv + 8 + d)) k = true ;
  mt1f_kwr11 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (nx + 0 + d)) k = true ;
  mt1f_kd12 : 0 + 621736 + 8 <= pv + 8 \/ pv + 8 + 8 <= 0 + 621736 ;
  mt1f_kd13 : 0 + 621736 + 8 <= nx + 0 \/ nx + 0 + 8 <= 0 + 621736 ;
  mt1f_kd14 : pv + 8 + 8 <= fm + 0 \/ fm + 0 + 16 <= pv + 8 ;
  mt1f_kd15 : nx + 0 + 8 <= fm + 0 \/ fm + 0 + 16 <= nx + 0
}.


#[using="Type"] Lemma mt1f_setup : forall regs m fm nx pv, mt1f_pre regs m fm nx pv ->
  regs_ok (Ez regs (VALS_mt1f fm nx pv)) AXF_mt1f.sr_mt1f regs /\ know_ok SEGS (Ez regs (VALS_mt1f fm nx pv)) m AXF_mt1f.kn_mt1f.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m fm nx pv P. destruct P as [mt1f_R19 mt1f_rng_fm mt1f_rng_nx mt1f_rng_pv mt1f_ka1 mt1f_kw4 mt1f_kw5 mt1f_kw6 mt1f_kw7 mt1f_kw8 mt1f_kwr9 mt1f_kwr10 mt1f_kwr11 mt1f_kd12 mt1f_kd13 mt1f_kd14 mt1f_kd15].
  set (E := Ez regs (VALS_mt1f fm nx pv)).
  assert (Z32 : bv_unsigned (ev E 32) = fm) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = nx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = pv) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mt1f.sr_mt1f.
    apply (regs_ok_pin E _ regs 19); [apply regs_ok_id|].
    - rewrite mt1f_R19. reflexivity. }
  unfold know_ok, AXF_mt1f.kn_mt1f.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mt1f.e_fm AXF_mt1f.e_nx AXF_mt1f.e_pv a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range fm _ _ mt1f_rng_fm eq_refl eq_refl), ?(mod64_of_range nx _ _ mt1f_rng_nx eq_refl eq_refl), ?(mod64_of_range pv _ _ mt1f_rng_pv eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply mt1f_kwr9 | apply mt1f_kwr10 | apply mt1f_kwr11]; assumption).
  all: try (clear - mt1f_rng_fm mt1f_rng_nx mt1f_rng_pv mt1f_ka1; lia).
  all: first [(clear - mt1f_rng_fm mt1f_rng_nx mt1f_rng_pv mt1f_ka1 mt1f_kd12; lia) | (clear - mt1f_rng_fm mt1f_rng_nx mt1f_rng_pv mt1f_ka1 mt1f_kd13; lia) | (clear - mt1f_rng_fm mt1f_rng_nx mt1f_rng_pv mt1f_ka1 mt1f_kd14; lia) | (clear - mt1f_rng_fm mt1f_rng_nx mt1f_rng_pv mt1f_ka1 mt1f_kd15; lia) | lia].
Qed.


Definition mt1f_mem_pmf1 (m : word -> option byte) (regs : bvmap 5 word) (fm nx pv : Z) : word -> option byte :=
  wbytes (m) (wa (0 + 621736)) (word_to_le_bytes 8 (wa 0)).

#[using="Type"] Theorem mt1f_pmf1 : forall regs m rom fm nx pv, mt1f_pre regs m fm nx pv ->
  scs_denot SEGS m (Ez regs (VALS_mt1f fm nx pv)) (snd (fst AXF_mt1f.RES_pmf1)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53a94) m rom) (mkst R (wa 0x53cd4) (mt1f_mem_pmf1 m regs fm nx pv) rom) /\
    getr R 8 = wa 4096 /\ getr R 10 = wa fm /\ getr R 11 = wa nx /\ getr R 19 = wa 621712 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 9; 12; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom fm nx pv P Hsc. destruct (mt1f_setup regs m fm nx pv P) as [HR HK].
  set (E := Ez regs (VALS_mt1f fm nx pv)) in *. destruct P as [mt1f_R19 mt1f_rng_fm mt1f_rng_nx mt1f_rng_pv mt1f_ka1 mt1f_kw4 mt1f_kw5 mt1f_kw6 mt1f_kw7 mt1f_kw8 mt1f_kwr9 mt1f_kwr10 mt1f_kwr11 mt1f_kd12 mt1f_kd13 mt1f_kd14 mt1f_kd15].
  assert (Z32 : bv_unsigned (ev E 32) = fm) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = nx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = pv) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53b4c; 0x53cd4] AXF_mt1f.scr_pmf1 0x53a94 AXF_mt1f.sr_mt1f AXF_mt1f.kn_mt1f 35 _ _ _ E m rom regs AXF_mt1f.RES_pmf1_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mt1f.RES_pmf1 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mt1f_mem_pmf1 m regs fm nx pv) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mt1f_mem_pmf1. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition mt1f_mem_pmfn (m : word -> option byte) (regs : bvmap 5 word) (fm nx pv : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (m) (wa (pv + 8)) (word_to_le_bytes 8 (wa nx))) (wa (nx + 0)) (word_to_le_bytes 8 (wa pv))) (wa (0 + 621736)) (word_to_le_bytes 8 (wa nx)).

#[using="Type"] Theorem mt1f_pmfn : forall regs m rom fm nx pv, mt1f_pre regs m fm nx pv ->
  scs_denot SEGS m (Ez regs (VALS_mt1f fm nx pv)) (snd (fst AXF_mt1f.RES_pmfn)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53a94) m rom) (mkst R (wa 0x53cd4) (mt1f_mem_pmfn m regs fm nx pv) rom) /\
    getr R 8 = wa 4096 /\ getr R 10 = wa fm /\ getr R 11 = wa nx /\ getr R 12 = wa nx /\ getr R 19 = wa 621712 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 9; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom fm nx pv P Hsc. destruct (mt1f_setup regs m fm nx pv P) as [HR HK].
  set (E := Ez regs (VALS_mt1f fm nx pv)) in *. destruct P as [mt1f_R19 mt1f_rng_fm mt1f_rng_nx mt1f_rng_pv mt1f_ka1 mt1f_kw4 mt1f_kw5 mt1f_kw6 mt1f_kw7 mt1f_kw8 mt1f_kwr9 mt1f_kwr10 mt1f_kwr11 mt1f_kd12 mt1f_kd13 mt1f_kd14 mt1f_kd15].
  assert (Z32 : bv_unsigned (ev E 32) = fm) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = nx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = pv) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53b4c; 0x53cd4] AXF_mt1f.scr_pmfn 0x53a94 AXF_mt1f.sr_mt1f AXF_mt1f.kn_mt1f 35 _ _ _ E m rom regs AXF_mt1f.RES_pmfn_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mt1f.RES_pmfn fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mt1f_mem_pmfn m regs fm nx pv) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mt1f_mem_pmfn. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MT1F.
End AXF_mt1fz.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section MT1.
Context {fx : FPState}.

Definition VALS_mt1 (d : Z) : list Z := [d].

Record mt1_pre (regs : bvmap 5 word) (m : word -> option byte) (d : Z) : Prop := {
  mt1_R19 : getr regs 19 = wa 621712 ;
  mt1_rng_d : 0 <= d <= 1 ;
  mt1_kw0 : rdn SEGS m (wa (0 + 621728)) 4 = Some (word_to_le_bytes 4 (wa 1)) ;
  mt1_kw1 : rdn SEGS m (wa (0 + 621648)) 8 = Some (word_to_le_bytes 8 (wa 4096)) ;
  mt1_kw2 : rdn SEGS m (wa (0 + 621736)) 8 = Some (word_to_le_bytes 8 (wa 0))
}.


#[using="Type"] Lemma mt1_setup : forall regs m d, mt1_pre regs m d ->
  regs_ok (Ez regs (VALS_mt1 d)) AXF_mt1.sr_mt1 regs /\ know_ok SEGS (Ez regs (VALS_mt1 d)) m AXF_mt1.kn_mt1.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m d P. destruct P as [mt1_R19 mt1_rng_d mt1_kw0 mt1_kw1 mt1_kw2].
  set (E := Ez regs (VALS_mt1 d)).
  assert (Z32 : bv_unsigned (ev E 32) = d) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mt1.sr_mt1.
    apply (regs_ok_pin E _ regs 19); [apply regs_ok_id|].
    - rewrite mt1_R19. reflexivity. }
  unfold know_ok, AXF_mt1.kn_mt1.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mt1.e_d a_base a_off].
  all: rewrite ?Z32.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range d _ _ mt1_rng_d eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - mt1_rng_d; lia).
  all: first [lia].
Qed.


Definition mt1_mem_pmt1 (m : word -> option byte) (regs : bvmap 5 word) (d : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mt1_pmt1 : forall regs m rom d, mt1_pre regs m d ->
  scs_denot SEGS m (Ez regs (VALS_mt1 d)) (snd (fst AXF_mt1.RES_pmt1)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53a94) m rom) (mkst R (wa 0x53b4c) (mt1_mem_pmt1 m regs d) rom) /\
    getr R 8 = wa 4096 /\ getr R 10 = wa 0 /\ getr R 11 = wa 621208 /\ getr R 19 = wa 621712 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 9; 12; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom d P Hsc. destruct (mt1_setup regs m d P) as [HR HK].
  set (E := Ez regs (VALS_mt1 d)) in *. destruct P as [mt1_R19 mt1_rng_d mt1_kw0 mt1_kw1 mt1_kw2].
  assert (Z32 : bv_unsigned (ev E 32) = d) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53b4c; 0x53cd4] AXF_mt1.scr_pmt1 0x53a94 AXF_mt1.sr_mt1 AXF_mt1.kn_mt1 33 _ _ _ E m rom regs AXF_mt1.RES_pmt1_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mt1.RES_pmt1 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mt1_mem_pmt1 m regs d) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mt1_mem_pmt1. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MT1.
