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
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ MngWb.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AxAsan AXG_put AXG_put2 AXG_np.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngZ.

Module AXF_immh.
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

Definition e_D := EVar 32.
Definition e_S := EVar 33.
Definition e_N := EVar 34.
Definition sr_immh := (sr_upd (sr_upd (sr_upd sr_id 10 (e_D)) 11 (e_S)) 12 (e_N)).
Definition kn_immh : list kentry :=
  [ KRange e_D 0 (2^62);
    KRange e_S 0 (2^62);
    KRange e_N 1 (2^40) ].
Definition scr_immh : scripts := SCR [false] [] [].
Definition ss_immh := SS 0x733e8 sr_immh [] kn_immh 35.
Definition RUN_immh := sym_exec SEGS 12 true [0x733f8; 0x73420] scr_immh ss_immh [].

Definition scr_pfw : scripts := SCR [false] [] [].
Definition RES_pfw := Eval vm_compute in sym_exec SEGS 12 true [0x733f8; 0x73420] scr_pfw ss_immh [].
Lemma RES_pfw_ok : sym_exec SEGS 12 true [0x733f8; 0x73420] scr_pfw (SS 0x733e8 sr_immh [] kn_immh 35) [] = RES_pfw.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pbw : scripts := SCR [true; false] [] [].
Definition RES_pbw := Eval vm_compute in sym_exec SEGS 12 true [0x733f8; 0x73420] scr_pbw ss_immh [].
Lemma RES_pbw_ok : sym_exec SEGS 12 true [0x733f8; 0x73420] scr_pbw (SS 0x733e8 sr_immh [] kn_immh 35) [] = RES_pbw.
Proof. vm_compute. reflexivity. Qed.
End AXF_immh.

Module AXF_immhz.
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

Section IMMH.
Context {fx : FPState}.

Definition VALS_immh (D S N : Z) : list Z := [D; S; N].

Record immh_pre (regs : bvmap 5 word) (m : word -> option byte) (D S N : Z) : Prop := {
  immh_R10 : getr regs 10 = wa D ;
  immh_R11 : getr regs 11 = wa S ;
  immh_R12 : getr regs 12 = wa N ;
  immh_rng_D : 0 <= D <= 2^62 ;
  immh_rng_S : 0 <= S <= 2^62 ;
  immh_rng_N : 1 <= N <= 2^40
}.


#[using="Type"] Lemma immh_setup : forall regs m D S N, immh_pre regs m D S N ->
  regs_ok (Ez regs (VALS_immh D S N)) AXF_immh.sr_immh regs /\ know_ok SEGS (Ez regs (VALS_immh D S N)) m AXF_immh.kn_immh.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m D S N P. destruct P as [immh_R10 immh_R11 immh_R12 immh_rng_D immh_rng_S immh_rng_N].
  set (E := Ez regs (VALS_immh D S N)).
  assert (Z32 : bv_unsigned (ev E 32) = D) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = S) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = N) by (apply zatom; [reflexivity | reflexivity | zrange]).

  split.
  { unfold AXF_immh.sr_immh.
    apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|]|].
    - rewrite immh_R10. reflexivity.
    - rewrite immh_R11. reflexivity.
    - rewrite immh_R12. reflexivity. }
  unfold know_ok, AXF_immh.kn_immh.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_immh.e_D AXF_immh.e_S AXF_immh.e_N a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range D _ _ immh_rng_D eq_refl eq_refl), ?(mod64_of_range S _ _ immh_rng_S eq_refl eq_refl), ?(mod64_of_range N _ _ immh_rng_N eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - immh_rng_D immh_rng_S immh_rng_N; lia).
  all: first [lia].
Qed.


Definition immh_mem_pfw (m : word -> option byte) (regs : bvmap 5 word) (D S N : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem immh_pfw : forall regs m rom D S N, immh_pre regs m D S N ->
  scs_denot SEGS m (Ez regs (VALS_immh D S N)) (snd (fst AXF_immh.RES_pfw)) ->
  exists R, msteps SEGS (mkst regs (wa 0x733e8) m rom) (mkst R (wa 0x733f8) (immh_mem_pfw m regs D S N) rom) /\
    getr R 10 = wa D /\ getr R 11 = wa S /\ getr R 12 = wa (D + N) /\ getr R 13 = wa D /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom D S N P Hsc. destruct (immh_setup regs m D S N P) as [HR HK].
  set (E := Ez regs (VALS_immh D S N)) in *. destruct P as [immh_R10 immh_R11 immh_R12 immh_rng_D immh_rng_S immh_rng_N].
  assert (Z32 : bv_unsigned (ev E 32) = D) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = S) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = N) by (apply zatom; [reflexivity | reflexivity | zrange]).

  destruct (run_sound SEGS 12 [0x733f8; 0x73420] AXF_immh.scr_pfw 0x733e8 AXF_immh.sr_immh AXF_immh.kn_immh 35 _ _ _ E m rom regs AXF_immh.RES_pfw_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_immh.RES_pfw fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (immh_mem_pfw m regs D S N) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold immh_mem_pfw. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition immh_mem_pbw (m : word -> option byte) (regs : bvmap 5 word) (D S N : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem immh_pbw : forall regs m rom D S N, immh_pre regs m D S N ->
  scs_denot SEGS m (Ez regs (VALS_immh D S N)) (snd (fst AXF_immh.RES_pbw)) ->
  exists R, msteps SEGS (mkst regs (wa 0x733e8) m rom) (mkst R (wa 0x73420) (immh_mem_pbw m regs D S N) rom) /\
    getr R 10 = wa D /\ getr R 11 = wa S /\ getr R 12 = wa 1 /\ getr R 13 = wa (N + -1) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom D S N P Hsc. destruct (immh_setup regs m D S N P) as [HR HK].
  set (E := Ez regs (VALS_immh D S N)) in *. destruct P as [immh_R10 immh_R11 immh_R12 immh_rng_D immh_rng_S immh_rng_N].
  assert (Z32 : bv_unsigned (ev E 32) = D) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = S) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = N) by (apply zatom; [reflexivity | reflexivity | zrange]).

  destruct (run_sound SEGS 12 [0x733f8; 0x73420] AXF_immh.scr_pbw 0x733e8 AXF_immh.sr_immh AXF_immh.kn_immh 35 _ _ _ E m rom regs AXF_immh.RES_pbw_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_immh.RES_pbw fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (immh_mem_pbw m regs D S N) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold immh_mem_pbw. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End IMMH.
End AXF_immhz.

Module AXF_immf.
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

Definition e_DP := EVar 32.
Definition e_SQ := EVar 33.
Definition e_EN := EVar 34.
Definition e_bv := EVar 35.
Definition sr_immf := (sr_upd (sr_upd (sr_upd sr_id 11 (e_SQ)) 12 (e_EN)) 13 (e_DP)).
Definition kn_immf : list kentry :=
  [ KRange e_DP 0 (2^62);
    KRange e_SQ 0 (2^62);
    KRange e_EN 1 (2^62);
    KWord (SA e_SQ 0) 1 e_bv;
    KWr (SA e_DP 0) (ELit 1) ].
Definition scr_immf : scripts := SCR [true] [] [].
Definition ss_immf := SS 0x733f8 sr_immf [] kn_immf 36.
Definition RUN_immf := sym_exec SEGS 10 true [0x733f8; 0x7343c] scr_immf ss_immf [].

Definition scr_pfc : scripts := SCR [true] [] [].
Definition RES_pfc := Eval vm_compute in sym_exec SEGS 10 true [0x733f8; 0x7343c] scr_pfc ss_immf [].
Lemma RES_pfc_ok : sym_exec SEGS 10 true [0x733f8; 0x7343c] scr_pfc (SS 0x733f8 sr_immf [] kn_immf 36) [] = RES_pfc.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pfx : scripts := SCR [false] [] [].
Definition RES_pfx := Eval vm_compute in sym_exec SEGS 10 true [0x733f8; 0x7343c] scr_pfx ss_immf [].
Lemma RES_pfx_ok : sym_exec SEGS 10 true [0x733f8; 0x7343c] scr_pfx (SS 0x733f8 sr_immf [] kn_immf 36) [] = RES_pfx.
Proof. vm_compute. reflexivity. Qed.
End AXF_immf.

Module AXF_immfz.
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

Section IMMF.
Context {fx : FPState}.

Definition VALS_immf (DP SQ EN bv : Z) : list Z := [DP; SQ; EN; bv].

Record immf_pre (regs : bvmap 5 word) (m : word -> option byte) (DP SQ EN bv : Z) : Prop := {
  immf_R11 : getr regs 11 = wa SQ ;
  immf_R12 : getr regs 12 = wa EN ;
  immf_R13 : getr regs 13 = wa DP ;
  immf_rng_DP : 0 <= DP <= 2^62 ;
  immf_rng_SQ : 0 <= SQ <= 2^62 ;
  immf_rng_EN : 1 <= EN <= 2^62 ;
  immf_rng_bv : 0 <= bv <= 255 ;
  immf_kw3 : rdn SEGS m (wa (SQ + 0)) 1 = Some (word_to_le_bytes 1 (wa bv)) ;
  immf_kwr4 : forall d k, 0 <= d -> d + Z.of_nat k <= 1 -> store_ok SEGS m (wa (DP + 0 + d)) k = true
}.


#[using="Type"] Lemma immf_setup : forall regs m DP SQ EN bv, immf_pre regs m DP SQ EN bv ->
  regs_ok (Ez regs (VALS_immf DP SQ EN bv)) AXF_immf.sr_immf regs /\ know_ok SEGS (Ez regs (VALS_immf DP SQ EN bv)) m AXF_immf.kn_immf.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m DP SQ EN bv P. destruct P as [immf_R11 immf_R12 immf_R13 immf_rng_DP immf_rng_SQ immf_rng_EN immf_rng_bv immf_kw3 immf_kwr4].
  set (E := Ez regs (VALS_immf DP SQ EN bv)).
  assert (Z32 : bv_unsigned (ev E 32) = DP) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = SQ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = EN) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = bv) by (apply zatom; [reflexivity | reflexivity | zrange]).

  split.
  { unfold AXF_immf.sr_immf.
    apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply regs_ok_id|]|]|].
    - rewrite immf_R11. reflexivity.
    - rewrite immf_R12. reflexivity.
    - rewrite immf_R13. reflexivity. }
  unfold know_ok, AXF_immf.kn_immf.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_immf.e_DP AXF_immf.e_SQ AXF_immf.e_EN AXF_immf.e_bv a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range DP _ _ immf_rng_DP eq_refl eq_refl), ?(mod64_of_range SQ _ _ immf_rng_SQ eq_refl eq_refl), ?(mod64_of_range EN _ _ immf_rng_EN eq_refl eq_refl), ?(mod64_of_range bv _ _ immf_rng_bv eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply immf_kwr4]; assumption).
  all: try (clear - immf_rng_DP immf_rng_SQ immf_rng_EN immf_rng_bv; lia).
  all: first [lia].
Qed.


Definition immf_mem_pfc (m : word -> option byte) (regs : bvmap 5 word) (DP SQ EN bv : Z) : word -> option byte :=
  wbytes (m) (wa (DP + 0)) (word_to_le_bytes 1 (wa (ext_Z false 0 1 bv))).

#[using="Type"] Theorem immf_pfc : forall regs m rom DP SQ EN bv, immf_pre regs m DP SQ EN bv ->
  scs_denot SEGS m (Ez regs (VALS_immf DP SQ EN bv)) (snd (fst AXF_immf.RES_pfc)) ->
  exists R, msteps SEGS (mkst regs (wa 0x733f8) m rom) (mkst R (wa 0x733f8) (immf_mem_pfc m regs DP SQ EN bv) rom) /\
    getr R 11 = wa (SQ + 1) /\ getr R 12 = wa EN /\ getr R 13 = wa (DP + 1) /\ getr R 14 = wa (ext_Z false 0 1 bv) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom DP SQ EN bv P Hsc. destruct (immf_setup regs m DP SQ EN bv P) as [HR HK].
  set (E := Ez regs (VALS_immf DP SQ EN bv)) in *. destruct P as [immf_R11 immf_R12 immf_R13 immf_rng_DP immf_rng_SQ immf_rng_EN immf_rng_bv immf_kw3 immf_kwr4].
  assert (Z32 : bv_unsigned (ev E 32) = DP) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = SQ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = EN) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = bv) by (apply zatom; [reflexivity | reflexivity | zrange]).

  destruct (run_sound SEGS 10 [0x733f8; 0x7343c] AXF_immf.scr_pfc 0x733f8 AXF_immf.sr_immf AXF_immf.kn_immf 36 _ _ _ E m rom regs AXF_immf.RES_pfc_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_immf.RES_pfc fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (immf_mem_pfc m regs DP SQ EN bv) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold immf_mem_pfc. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition immf_mem_pfx (m : word -> option byte) (regs : bvmap 5 word) (DP SQ EN bv : Z) : word -> option byte :=
  wbytes (m) (wa (DP + 0)) (word_to_le_bytes 1 (wa (ext_Z false 0 1 bv))).

#[using="Type"] Theorem immf_pfx : forall regs m rom DP SQ EN bv, immf_pre regs m DP SQ EN bv ->
  scs_denot SEGS m (Ez regs (VALS_immf DP SQ EN bv)) (snd (fst AXF_immf.RES_pfx)) ->
  exists R, msteps SEGS (mkst regs (wa 0x733f8) m rom) (mkst R (wa 0x7343c) (immf_mem_pfx m regs DP SQ EN bv) rom) /\
    getr R 11 = wa (SQ + 1) /\ getr R 12 = wa EN /\ getr R 13 = wa (DP + 1) /\ getr R 14 = wa (ext_Z false 0 1 bv) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom DP SQ EN bv P Hsc. destruct (immf_setup regs m DP SQ EN bv P) as [HR HK].
  set (E := Ez regs (VALS_immf DP SQ EN bv)) in *. destruct P as [immf_R11 immf_R12 immf_R13 immf_rng_DP immf_rng_SQ immf_rng_EN immf_rng_bv immf_kw3 immf_kwr4].
  assert (Z32 : bv_unsigned (ev E 32) = DP) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = SQ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = EN) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = bv) by (apply zatom; [reflexivity | reflexivity | zrange]).

  destruct (run_sound SEGS 10 [0x733f8; 0x7343c] AXF_immf.scr_pfx 0x733f8 AXF_immf.sr_immf AXF_immf.kn_immf 36 _ _ _ E m rom regs AXF_immf.RES_pfx_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_immf.RES_pfx fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (immf_mem_pfx m regs DP SQ EN bv) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold immf_mem_pfx. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End IMMF.
End AXF_immfz.

Module AXF_immb.
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

Definition e_D := EVar 32.
Definition e_S := EVar 33.
Definition e_I := EVar 34.
Definition e_bv := EVar 35.
Definition SI := EAlu ALU_ADD e_S e_I.
Definition DI := EAlu ALU_ADD e_D e_I.
Definition sr_immb := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (e_D)) 11 (e_S)) 12 (ELit 1)) 13 (e_I)).
Definition kn_immb : list kentry :=
  [ KRange e_D 0 (2^62);
    KRange e_S 0 (2^62);
    KRange e_I 0 (2^40);
    KWord (SA SI 0) 1 e_bv;
    KWr (SA DI 0) (ELit 1) ].
Definition scr_immb : scripts := SCR [true] [] [].
Definition ss_immb := SS 0x73420 sr_immb [] kn_immb 36.
Definition RUN_immb := sym_exec SEGS 10 true [0x73420; 0x7343c] scr_immb ss_immb [].

Definition scr_pbc : scripts := SCR [true] [] [].
Definition RES_pbc := Eval vm_compute in sym_exec SEGS 10 true [0x73420; 0x7343c] scr_pbc ss_immb [].
Lemma RES_pbc_ok : sym_exec SEGS 10 true [0x73420; 0x7343c] scr_pbc (SS 0x73420 sr_immb [] kn_immb 36) [] = RES_pbc.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pbx : scripts := SCR [false] [] [].
Definition RES_pbx := Eval vm_compute in sym_exec SEGS 10 true [0x73420; 0x7343c] scr_pbx ss_immb [].
Lemma RES_pbx_ok : sym_exec SEGS 10 true [0x73420; 0x7343c] scr_pbx (SS 0x73420 sr_immb [] kn_immb 36) [] = RES_pbx.
Proof. vm_compute. reflexivity. Qed.
End AXF_immb.

Module AXF_immbz.
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

Section IMMB.
Context {fx : FPState}.

Definition VALS_immb (D S I bv : Z) : list Z := [D; S; I; bv].

Record immb_pre (regs : bvmap 5 word) (m : word -> option byte) (D S I bv : Z) : Prop := {
  immb_R10 : getr regs 10 = wa D ;
  immb_R11 : getr regs 11 = wa S ;
  immb_R12 : getr regs 12 = wa 1 ;
  immb_R13 : getr regs 13 = wa I ;
  immb_rng_D : 0 <= D <= 2^62 ;
  immb_rng_S : 0 <= S <= 2^62 ;
  immb_rng_I : 0 <= I <= 2^40 ;
  immb_rng_bv : 0 <= bv <= 255 ;
  immb_kw3 : rdn SEGS m (wa (S + I + 0)) 1 = Some (word_to_le_bytes 1 (wa bv)) ;
  immb_kwr4 : forall d k, 0 <= d -> d + Z.of_nat k <= 1 -> store_ok SEGS m (wa (D + I + 0 + d)) k = true
}.


#[using="Type"] Lemma immb_setup : forall regs m D S I bv, immb_pre regs m D S I bv ->
  regs_ok (Ez regs (VALS_immb D S I bv)) AXF_immb.sr_immb regs /\ know_ok SEGS (Ez regs (VALS_immb D S I bv)) m AXF_immb.kn_immb.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m D S I bv P. destruct P as [immb_R10 immb_R11 immb_R12 immb_R13 immb_rng_D immb_rng_S immb_rng_I immb_rng_bv immb_kw3 immb_kwr4].
  set (E := Ez regs (VALS_immb D S I bv)).
  assert (Z32 : bv_unsigned (ev E 32) = D) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = S) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = I) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = bv) by (apply zatom; [reflexivity | reflexivity | zrange]).

  split.
  { unfold AXF_immb.sr_immb.
    apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|]|]|].
    - rewrite immb_R10. reflexivity.
    - rewrite immb_R11. reflexivity.
    - rewrite immb_R12. reflexivity.
    - rewrite immb_R13. reflexivity. }
  unfold know_ok, AXF_immb.kn_immb.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_immb.e_D AXF_immb.e_S AXF_immb.e_I AXF_immb.e_bv AXF_immb.SI AXF_immb.DI a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range D _ _ immb_rng_D eq_refl eq_refl), ?(mod64_of_range S _ _ immb_rng_S eq_refl eq_refl), ?(mod64_of_range I _ _ immb_rng_I eq_refl eq_refl), ?(mod64_of_range bv _ _ immb_rng_bv eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply immb_kwr4]; assumption).
  all: try (clear - immb_rng_D immb_rng_S immb_rng_I immb_rng_bv; lia).
  all: first [lia].
Qed.


Definition immb_mem_pbc (m : word -> option byte) (regs : bvmap 5 word) (D S I bv : Z) : word -> option byte :=
  wbytes (m) (wa (D + I + 0)) (word_to_le_bytes 1 (wa (ext_Z false 0 1 bv))).

#[using="Type"] Theorem immb_pbc : forall regs m rom D S I bv, immb_pre regs m D S I bv ->
  scs_denot SEGS m (Ez regs (VALS_immb D S I bv)) (snd (fst AXF_immb.RES_pbc)) ->
  exists R, msteps SEGS (mkst regs (wa 0x73420) m rom) (mkst R (wa 0x73420) (immb_mem_pbc m regs D S I bv) rom) /\
    getr R 10 = wa D /\ getr R 11 = wa S /\ getr R 12 = wa 1 /\ getr R 13 = wa (I + -1) /\ getr R 14 = wa (ext_Z false 0 1 bv) /\ getr R 15 = wa (D + I) /\ getr R 16 = wa (I + 1) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom D S I bv P Hsc. destruct (immb_setup regs m D S I bv P) as [HR HK].
  set (E := Ez regs (VALS_immb D S I bv)) in *. destruct P as [immb_R10 immb_R11 immb_R12 immb_R13 immb_rng_D immb_rng_S immb_rng_I immb_rng_bv immb_kw3 immb_kwr4].
  assert (Z32 : bv_unsigned (ev E 32) = D) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = S) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = I) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = bv) by (apply zatom; [reflexivity | reflexivity | zrange]).

  destruct (run_sound SEGS 10 [0x73420; 0x7343c] AXF_immb.scr_pbc 0x73420 AXF_immb.sr_immb AXF_immb.kn_immb 36 _ _ _ E m rom regs AXF_immb.RES_pbc_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_immb.RES_pbc fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (immb_mem_pbc m regs D S I bv) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold immb_mem_pbc. repeat (apply (f_equal3 wbytes)); try reflexivity.
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


Definition immb_mem_pbx (m : word -> option byte) (regs : bvmap 5 word) (D S I bv : Z) : word -> option byte :=
  wbytes (m) (wa (D + I + 0)) (word_to_le_bytes 1 (wa (ext_Z false 0 1 bv))).

#[using="Type"] Theorem immb_pbx : forall regs m rom D S I bv, immb_pre regs m D S I bv ->
  scs_denot SEGS m (Ez regs (VALS_immb D S I bv)) (snd (fst AXF_immb.RES_pbx)) ->
  exists R, msteps SEGS (mkst regs (wa 0x73420) m rom) (mkst R (wa 0x7343c) (immb_mem_pbx m regs D S I bv) rom) /\
    getr R 10 = wa D /\ getr R 11 = wa S /\ getr R 12 = wa 1 /\ getr R 13 = wa (I + -1) /\ getr R 14 = wa (ext_Z false 0 1 bv) /\ getr R 15 = wa (D + I) /\ getr R 16 = wa (I + 1) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom D S I bv P Hsc. destruct (immb_setup regs m D S I bv P) as [HR HK].
  set (E := Ez regs (VALS_immb D S I bv)) in *. destruct P as [immb_R10 immb_R11 immb_R12 immb_R13 immb_rng_D immb_rng_S immb_rng_I immb_rng_bv immb_kw3 immb_kwr4].
  assert (Z32 : bv_unsigned (ev E 32) = D) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = S) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = I) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = bv) by (apply zatom; [reflexivity | reflexivity | zrange]).

  destruct (run_sound SEGS 10 [0x73420; 0x7343c] AXF_immb.scr_pbx 0x73420 AXF_immb.sr_immb AXF_immb.kn_immb 36 _ _ _ E m rom regs AXF_immb.RES_pbx_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_immb.RES_pbx fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (immb_mem_pbx m regs D S I bv) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold immb_mem_pbx. repeat (apply (f_equal3 wbytes)); try reflexivity.
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

End IMMB.
End AXF_immbz.

Module AXG_imm.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AxAsan AXG_put AXG_put2 AXG_np.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngZ.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AxAsan OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngZ.AxScChk.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
Definition KIMM : list nat := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.

(* [comment removed for export] *)
Definition mem_ext (m m' : word -> option byte) : Prop := forall w, m' w = m w \/ exists bb, m' w = Some bb.
Lemma mem_ext_refl : forall m, mem_ext m m.
Proof. intros m w. left. reflexivity. Qed.
Lemma mem_ext_trans : forall m1 m2 m3, mem_ext m1 m2 -> mem_ext m2 m3 -> mem_ext m1 m3.
Proof.
  intros m1 m2 m3 H12 H23 w. destruct (H23 w) as [E|E]; [|right; exact E].
  rewrite E. apply H12.
Qed.
Lemma mem_ext_wbytes : forall bs m a, mem_ext m (wbytes m a bs).
Proof.
  induction bs as [|b rest IH]; intros m a w; cbn [wbytes]; [left; reflexivity|].
  destruct (IH (fun x => if bv_eqb x a then Some b else m x) (a + 1)%bv w) as [H|H]; [|right; exact H].
  rewrite H. destruct (bv_eqb w a); [right; exists b; reflexivity | left; reflexivity].
Qed.

(* [comment removed for export] *)
Definition rdable (m : word -> option byte) (S N : Z) : Prop :=
  forall i, 0 <= i < N -> exists bv, 0 <= bv <= 255 /\ rdn SEGS m (wa (S + i)) 1 = Some (word_to_le_bytes 1 (wa bv)).

Definition LO47 : iv := (0, 2^62).
Ltac zat R := repeat match goal with |- context [bv_unsigned (ev (Ez R ?V) ?n)] =>
              lazymatch eval cbn in (Nat.ltb n 32) with
              | true => change (bv_unsigned (ev (Ez R V) n)) with (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat n))))
              | false => let v := eval cbn [nth Nat.sub] in (nth (n - 32) V 0) in rewrite (zatom R V n v eq_refl eq_refl) by lia
              end end.

Section IMM.
Context {fx : FPState}.
Variable rom : word -> option byte.

(* [comment removed for export] *)
Section SC.
Variables (R : bvmap 5 word) (m : word -> option byte).
#[using="Type"] Lemma sc_immf_c : forall DP SQ EN bv, 0 <= DP <= 2^62 /\ DP + 2 <= EN <= 2^62 ->
  scs_denot SEGS m (Ez R (AXF_immfz.VALS_immf DP SQ EN bv)) (snd (fst AXF_immf.RES_pfc)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros DP SQ EN bv HH. unfold AXF_immfz.VALS_immf.
  apply (scs_chk_sound [(EVar 32, LO47); (EVar 34, (1, 2^62))] [(EVar 34, EVar 32, 2)]);
    [ repeat (first [apply Forall_nil | apply Forall_cons]); unfold rf_ok, LO47; cbn [fst snd zeval edenot]; zat R; clear - HH; lia
    | repeat (first [apply Forall_nil | apply Forall_cons]); unfold df_ok; cbn [fst snd zeval edenot]; zat R; clear - HH; lia
    | vm_compute; reflexivity ].
Qed.
#[using="Type"] Lemma sc_immf_x : forall DP SQ EN bv, 0 <= DP <= 2^62 /\ EN = DP + 1 /\ EN <= 2^62 ->
  scs_denot SEGS m (Ez R (AXF_immfz.VALS_immf DP SQ EN bv)) (snd (fst AXF_immf.RES_pfx)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros DP SQ EN bv HH. unfold AXF_immfz.VALS_immf.
  apply (scs_chk_sound [(EVar 32, LO47); (EVar 34, (1, 2^62))] [(EVar 34, EVar 32, 1); (EVar 32, EVar 34, -1)]);
    [ repeat (first [apply Forall_nil | apply Forall_cons]); unfold rf_ok, LO47; cbn [fst snd zeval edenot]; zat R; clear - HH; lia
    | repeat (first [apply Forall_nil | apply Forall_cons]); unfold df_ok; cbn [fst snd zeval edenot]; zat R; clear - HH; lia
    | vm_compute; reflexivity ].
Qed.
#[using="Type"] Lemma sc_immb_c : forall D S I bv, 1 <= I <= 2^40 ->
  scs_denot SEGS m (Ez R (AXF_immbz.VALS_immb D S I bv)) (snd (fst AXF_immb.RES_pbc)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros D S I bv HH. unfold AXF_immbz.VALS_immb.
  apply (scs_chk_sound [(EVar 34, (1, 2^40))] []);
    [ repeat (first [apply Forall_nil | apply Forall_cons]); unfold rf_ok; cbn [fst snd zeval edenot]; zat R; clear - HH; lia
    | apply Forall_nil
    | vm_compute; reflexivity ].
Qed.
#[using="Type"] Lemma sc_immb_x : forall D S I bv, I = 0 ->
  scs_denot SEGS m (Ez R (AXF_immbz.VALS_immb D S I bv)) (snd (fst AXF_immb.RES_pbx)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros D S I bv HH. unfold AXF_immbz.VALS_immb.
  apply (scs_chk_sound [(EVar 34, (0, 0))] []);
    [ repeat (first [apply Forall_nil | apply Forall_cons]); unfold rf_ok; cbn [fst snd zeval edenot]; zat R; clear - HH; lia
    | apply Forall_nil
    | vm_compute; reflexivity ].
Qed.
#[using="Type"] Lemma sc_immh_f : forall D S N, 0 <= D <= 2^62 /\ 0 <= S <= 2^62 /\ D + 1 <= S ->
  scs_denot SEGS m (Ez R (AXF_immhz.VALS_immh D S N)) (snd (fst AXF_immh.RES_pfw)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros D S N HH. unfold AXF_immhz.VALS_immh.
  apply (scs_chk_sound [(EVar 32, LO47); (EVar 33, LO47)] [(EVar 33, EVar 32, 1)]);
    [ repeat (first [apply Forall_nil | apply Forall_cons]); unfold rf_ok, LO47; cbn [fst snd zeval edenot]; zat R; clear - HH; lia
    | repeat (first [apply Forall_nil | apply Forall_cons]); unfold df_ok; cbn [fst snd zeval edenot]; zat R; clear - HH; lia
    | vm_compute; reflexivity ].
Qed.
#[using="Type"] Lemma sc_immh_b : forall D S N, 0 <= D <= 2^62 /\ 0 <= S <= 2^62 /\ S + 1 <= D ->
  scs_denot SEGS m (Ez R (AXF_immhz.VALS_immh D S N)) (snd (fst AXF_immh.RES_pbw)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros D S N HH. unfold AXF_immhz.VALS_immh.
  apply (scs_chk_sound [(EVar 32, LO47); (EVar 33, LO47)] [(EVar 32, EVar 33, 1)]);
    [ repeat (first [apply Forall_nil | apply Forall_cons]); unfold rf_ok, LO47; cbn [fst snd zeval edenot]; zat R; clear - HH; lia
    | repeat (first [apply Forall_nil | apply Forall_cons]); unfold df_ok; cbn [fst snd zeval edenot]; zat R; clear - HH; lia
    | vm_compute; reflexivity ].
Qed.
End SC.

Local Ltac len1 := rewrite ?length_N_to_le_bytes; change (Z.of_nat 1) with 1 in *.
Definition KIMMF : list nat := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.
Definition KIMMB : list nat := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.

(* [comment removed for export] *)
#[using="Type"] Lemma immf_gen : forall (k : nat) regs m DP SQ EN, (1 <= k)%nat -> EN = DP + Z.of_nat k ->
  getr regs 11 = wa SQ -> getr regs 12 = wa EN -> getr regs 13 = wa DP ->
  0 <= DP -> EN <= 2^62 -> 0 <= SQ -> SQ + Z.of_nat k <= 2^62 ->
  (EN <= SQ \/ SQ + Z.of_nat k <= DP) ->
  rdable m SQ (Z.of_nat k) -> wr m DP (Z.of_nat k) ->
  exists R m', msteps SEGS (mkst regs (wa 0x733f8) m rom) (mkst R (wa 0x7343c) m' rom) /\
    (forall kk, In kk KIMMF -> getr R (Z_to_bv 5 (Z.of_nat kk)) = getr regs (Z_to_bv 5 (Z.of_nat kk))) /\
    (forall x, 0 <= x < 2^64 -> ~ (DP <= x < EN) -> m' (wa x) = m (wa x)) /\ mem_ext m m'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros k. induction k as [|k IH]; intros regs m DP SQ EN Hk HEN H11 H12 H13 HD HE HS HSk HDJ HRD HWR; [lia|].
  rewrite Nat2Z.inj_succ in *.
  destruct (HRD 0 ltac:(lia)) as (bv & Hbv & Rbv).
  assert (P : AXF_immfz.immf_pre regs m DP SQ EN bv).
  { constructor; try assumption; try lia.
    intros d kk Hd Hkk. replace (DP + 0 + d) with (DP + d) by ring. apply HWR; lia. }
  set (m1 := wbytes m (wa (DP + 0)) (word_to_le_bytes 1 (wa (ext_Z false 0 1 bv)))).
  assert (Hm1c : AXF_immfz.immf_mem_pfc m regs DP SQ EN bv = m1) by reflexivity.
  assert (Hm1x : AXF_immfz.immf_mem_pfx m regs DP SQ EN bv = m1) by reflexivity.
  assert (E1 : forall x, 0 <= x < 2^64 -> ~ (DP <= x < DP + 1) -> m1 (wa x) = m (wa x)).
  { intros x Hx Hn. unfold m1. apply wb_other; [exact Hx | lia | len1; lia | len1; lia]. }
  assert (X1 : mem_ext m m1) by (unfold m1; apply mem_ext_wbytes).
  destruct k as [|k'].
  - (* [comment removed for export] *)
    destruct (AXF_immfz.immf_pfx regs m rom DP SQ EN bv P (sc_immf_x regs m DP SQ EN bv ltac:(cbn in *; lia)))
      as (R & Hms & _ & _ & _ & _ & KK).
    rewrite Hm1x in Hms. exists R, m1. split; [exact Hms|].
    split; [intros kk Hkk; apply KK; exact Hkk|].
    split; [intros x Hx Hn; apply E1; [exact Hx | cbn in *; lia] | exact X1].
  - (* [comment removed for export] *)
    destruct (AXF_immfz.immf_pfc regs m rom DP SQ EN bv P (sc_immf_c regs m DP SQ EN bv ltac:(lia)))
      as (R & Hms & A11 & A12 & A13 & _ & KK).
    rewrite Hm1c in Hms.
    destruct (IH R m1 (DP + 1) (SQ + 1) EN ltac:(lia) ltac:(lia) A11 A12 A13 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
      as (R' & m' & Hms' & KK' & FR & X').
    { intros i Hi. destruct (HRD (i + 1) ltac:(lia)) as (b & Hb & Rb). exists b. split; [exact Hb|].
      replace (SQ + 1 + i) with (SQ + (i + 1)) by ring. rewrite <- Rb.
      apply rdn_frame; [lia | change (Z.of_nat 1) with 1; lia |]. intros x Hx. change (Z.of_nat 1) with 1 in Hx. apply E1; lia. }
    { intros d kk Hd Hkk. apply (store_ok_mono SEGS kk m m1 _ ltac:(unfold m1; apply wbytes_grows)).
      replace (DP + 1 + d) with (DP + (1 + d)) by ring. apply HWR; lia. }
    exists R', m'. split; [exact (msteps_trans SEGS _ _ _ Hms Hms')|].
    split; [intros kk Hkk; rewrite (KK' kk Hkk); apply KK; exact Hkk|].
    split; [intros x Hx Hn; rewrite FR by lia; apply E1; lia | exact (mem_ext_trans _ _ _ X1 X')].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma immb_gen : forall (k : nat) regs m D S,
  getr regs 10 = wa D -> getr regs 11 = wa S -> getr regs 12 = wa 1 -> getr regs 13 = wa (Z.of_nat k) ->
  0 <= D -> D + Z.of_nat k + 1 <= 2^62 -> 0 <= S -> S + Z.of_nat k + 1 <= 2^62 -> Z.of_nat k + 1 <= 2^40 ->
  (D + Z.of_nat k + 1 <= S \/ S + Z.of_nat k + 1 <= D) ->
  rdable m S (Z.of_nat k + 1) -> wr m D (Z.of_nat k + 1) ->
  exists R m', msteps SEGS (mkst regs (wa 0x73420) m rom) (mkst R (wa 0x7343c) m' rom) /\
    (forall kk, In kk KIMMB -> getr R (Z_to_bv 5 (Z.of_nat kk)) = getr regs (Z_to_bv 5 (Z.of_nat kk))) /\
    (forall x, 0 <= x < 2^64 -> ~ (D <= x < D + Z.of_nat k + 1) -> m' (wa x) = m (wa x)) /\ mem_ext m m'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros k. induction k as [|k IH]; intros regs m D S H10 H11 H12 H13 HD HDk HS HSk HK HDJ HRD HWR.
  - (* [comment removed for export] *)
    cbn [Z.of_nat] in *.
    destruct (HRD 0 ltac:(lia)) as (bv & Hbv & Rbv).
    assert (P : AXF_immbz.immb_pre regs m D S 0 bv).
    { constructor; try assumption; try lia.
      - rewrite Z.add_0_r. exact Rbv.
      - intros d kk Hd Hkk. replace (D + 0 + 0 + d) with (D + d) by ring. apply HWR; lia. }
    destruct (AXF_immbz.immb_pbx regs m rom D S 0 bv P (sc_immb_x regs m D S 0 bv eq_refl)) as (R & Hms & A10 & _ & _ & _ & _ & _ & _ & KK).
    exists R, (AXF_immbz.immb_mem_pbx m regs D S 0 bv). split; [exact Hms|].
    split.
    { intros kk Hkk. cbn [KIMMB In] in Hkk.
      repeat (destruct Hkk as [<-|Hkk]; [first [apply KK; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ] | (transitivity (wa D); [exact A10 | symmetry; exact H10])]|]).
      destruct Hkk. }
    split; [|unfold AXF_immbz.immb_mem_pbx; apply mem_ext_wbytes].
    intros x Hx Hn. unfold AXF_immbz.immb_mem_pbx. apply wb_other; [exact Hx | lia | len1; lia | len1; lia].
  - rewrite Nat2Z.inj_succ in *.
    set (I := Z.succ (Z.of_nat k)) in *.
    destruct (HRD I ltac:(lia)) as (bv & Hbv & Rbv).
    assert (P : AXF_immbz.immb_pre regs m D S I bv).
    { constructor; try assumption; try lia.
      - rewrite Z.add_0_r. exact Rbv.
      - intros d kk Hd Hkk. replace (D + I + 0 + d) with (D + (I + d)) by ring. apply HWR; lia. }
    set (m1 := wbytes m (wa (D + I + 0)) (word_to_le_bytes 1 (wa (ext_Z false 0 1 bv)))).
    assert (Hm1c : AXF_immbz.immb_mem_pbc m regs D S I bv = m1) by reflexivity.
    assert (E1 : forall x, 0 <= x < 2^64 -> ~ (D + I <= x < D + I + 1) -> m1 (wa x) = m (wa x)).
    { intros x Hx Hn. unfold m1. apply wb_other; [exact Hx | lia | len1; lia | len1; lia]. }
    assert (X1 : mem_ext m m1) by (unfold m1; apply mem_ext_wbytes).
    destruct (AXF_immbz.immb_pbc regs m rom D S I bv P (sc_immb_c regs m D S I bv ltac:(lia)))
      as (R & Hms & A10 & A11 & A12 & A13 & _ & _ & _ & KK).
    rewrite Hm1c in Hms.
    replace (I + -1) with (Z.of_nat k) in A13 by (unfold I; lia).
    destruct (IH R m1 D S A10 A11 A12 A13 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
      as (R' & m' & Hms' & KK' & FR & X').
    { intros i Hi. destruct (HRD i ltac:(lia)) as (b & Hb & Rb). exists b. split; [exact Hb|].
      rewrite <- Rb. apply rdn_frame; [lia | change (Z.of_nat 1) with 1; lia |]. intros x Hx. change (Z.of_nat 1) with 1 in Hx. apply E1; lia. }
    { intros d kk Hd Hkk. apply (store_ok_mono SEGS kk m m1 _ ltac:(unfold m1; apply wbytes_grows)). apply HWR; lia. }
    exists R', m'. split; [exact (msteps_trans SEGS _ _ _ Hms Hms')|].
    split.
    { intros kk Hkk. rewrite (KK' kk Hkk). cbn [KIMMB In] in Hkk.
      repeat (destruct Hkk as [<-|Hkk]; [first [apply KK; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ] | (transitivity (wa D); [exact A10 | symmetry; exact H10])]|]).
      destruct Hkk. }
    split; [intros x Hx Hn; rewrite FR by lia; apply E1; lia | exact (mem_ext_trans _ _ _ X1 X')].
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem imm_contract : forall regs m D S N,
  getr regs 10 = wa D -> getr regs 11 = wa S -> getr regs 12 = wa N ->
  1 <= N <= 2^40 -> 0 <= D -> D + N <= 2^62 -> 0 <= S -> S + N <= 2^62 -> (D + N <= S \/ S + N <= D) ->
  rdable m S N -> wr m D N ->
  exists R m', msteps SEGS (mkst regs (wa 0x733e8) m rom) (mkst R (wa 0x7343c) m' rom) /\
    (forall kk, In kk KIMM -> getr R (Z_to_bv 5 (Z.of_nat kk)) = getr regs (Z_to_bv 5 (Z.of_nat kk))) /\
    (forall x, 0 <= x < 2^64 -> ~ (D <= x < D + N) -> m' (wa x) = m (wa x)) /\ mem_ext m m'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m D S N H10 H11 H12 HN HD HDN HS HSN HDJ HRD HWR.
  assert (P : AXF_immhz.immh_pre regs m D S N) by (constructor; try assumption; lia).
  destruct HDJ as [HDJ|HDJ].
  - (* [comment removed for export] *)
    destruct (AXF_immhz.immh_pfw regs m rom D S N P (sc_immh_f regs m D S N ltac:(lia))) as (R0 & Hms0 & A10 & A11 & A12 & A13 & KK0).
    unfold AXF_immhz.immh_mem_pfw in Hms0.
    destruct (immf_gen (Z.to_nat N) R0 m D S (D + N) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; reflexivity) A11 A12 A13 HD HDN HS
                ltac:(rewrite Z2Nat.id by lia; exact HSN) ltac:(left; exact HDJ)
                ltac:(rewrite Z2Nat.id by lia; exact HRD) ltac:(rewrite Z2Nat.id by lia; exact HWR))
      as (R & m' & Hms & KK & FR & X).
    exists R, m'. split; [exact (msteps_trans SEGS _ _ _ Hms0 Hms)|].
    split; [|split; [exact FR | exact X]].
    intros kk Hkk. cbn [KIMM In] in Hkk.
    repeat (destruct Hkk as [<-|Hkk]; [etransitivity; [apply KK; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [KIMMF In]; tauto ] | first [apply KK0; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ] | (transitivity (wa D); [exact A10 | symmetry; exact H10])]]|]).
    destruct Hkk.
  - (* [comment removed for export] *)
    destruct (AXF_immhz.immh_pbw regs m rom D S N P (sc_immh_b regs m D S N ltac:(lia))) as (R0 & Hms0 & A10 & A11 & A12 & A13 & KK0).
    unfold AXF_immhz.immh_mem_pbw in Hms0.
    assert (EN : Z.of_nat (Z.to_nat (N - 1)) = N - 1) by (apply Z2Nat.id; lia).
    replace (N + -1) with (Z.of_nat (Z.to_nat (N - 1))) in A13 by lia.
    destruct (immb_gen (Z.to_nat (N - 1)) R0 m D S A10 A11 A12 A13 HD ltac:(lia) HS ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(rewrite EN; replace (N - 1 + 1) with N by ring; exact HRD) ltac:(rewrite EN; replace (N - 1 + 1) with N by ring; exact HWR))
      as (R & m' & Hms & KK & FR & X).
    exists R, m'. split; [exact (msteps_trans SEGS _ _ _ Hms0 Hms)|].
    split; [|split; [|exact X]].
    + intros kk Hkk. cbn [KIMM In] in Hkk.
      repeat (destruct Hkk as [<-|Hkk]; [etransitivity; [apply KK; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [KIMMB In]; tauto ] | first [apply KK0; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ] | (transitivity (wa D); [exact A10 | symmetry; exact H10])]]|]).
      destruct Hkk.
    + intros x Hx Hn. apply FR; [exact Hx | lia].
Qed.
End IMM.
End AXG_imm.

Import OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AxAsan OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngZ.AxScChk OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_ims.AXG_imm.

Module AXF_imsh.
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

Definition e_D := EVar 32.
Definition e_N := EVar 33.
Definition sr_imsh := (sr_upd (sr_upd (sr_upd sr_id 10 (e_D)) 11 (ELit 0)) 12 (e_N)).
Definition kn_imsh : list kentry :=
  [ KRange e_D 0 (2^62);
    KRange e_N 1 (2^40) ].
Definition scr_imsh : scripts := SCR [false; false] [] [].
Definition ss_imsh := SS 0x73440 sr_imsh [] kn_imsh 34.
Definition RUN_imsh := sym_exec SEGS 16 true [0x73458; 0x7348c; 0x7349c] scr_imsh ss_imsh [].

Definition scr_pby : scripts := SCR [false; false] [] [].
Definition RES_pby := Eval vm_compute in sym_exec SEGS 16 true [0x73458; 0x7348c; 0x7349c] scr_pby ss_imsh [].
Lemma RES_pby_ok : sym_exec SEGS 16 true [0x73458; 0x7348c; 0x7349c] scr_pby (SS 0x73440 sr_imsh [] kn_imsh 34) [] = RES_pby.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pwd : scripts := SCR [true; false] [] [].
Definition RES_pwd := Eval vm_compute in sym_exec SEGS 16 true [0x73458; 0x7348c; 0x7349c] scr_pwd ss_imsh [].
Lemma RES_pwd_ok : sym_exec SEGS 16 true [0x73458; 0x7348c; 0x7349c] scr_pwd (SS 0x73440 sr_imsh [] kn_imsh 34) [] = RES_pwd.
Proof. vm_compute. reflexivity. Qed.
End AXF_imsh.


Module AXF_imshz.
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

Section IMSH.
Context {fx : FPState}.

Definition VALS_imsh (D N : Z) : list Z := [D; N].

Record imsh_pre (regs : bvmap 5 word) (m : word -> option byte) (D N : Z) : Prop := {
  imsh_R10 : getr regs 10 = wa D ;
  imsh_R11 : getr regs 11 = wa 0 ;
  imsh_R12 : getr regs 12 = wa N ;
  imsh_rng_D : 0 <= D <= 2^62 ;
  imsh_rng_N : 1 <= N <= 2^40
}.


#[using="Type"] Lemma imsh_setup : forall regs m D N, imsh_pre regs m D N ->
  regs_ok (Ez regs (VALS_imsh D N)) AXF_imsh.sr_imsh regs /\ know_ok SEGS (Ez regs (VALS_imsh D N)) m AXF_imsh.kn_imsh.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m D N P. destruct P as [imsh_R10 imsh_R11 imsh_R12 imsh_rng_D imsh_rng_N].
  set (E := Ez regs (VALS_imsh D N)).
  assert (Z32 : bv_unsigned (ev E 32) = D) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = N) by (apply zatom; [reflexivity | reflexivity | zrange]).

  split.
  { unfold AXF_imsh.sr_imsh.
    apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|]|].
    - rewrite imsh_R10. reflexivity.
    - rewrite imsh_R11. reflexivity.
    - rewrite imsh_R12. reflexivity. }
  unfold know_ok, AXF_imsh.kn_imsh.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_imsh.e_D AXF_imsh.e_N a_base a_off].
  all: rewrite ?Z32, ?Z33.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range D _ _ imsh_rng_D eq_refl eq_refl), ?(mod64_of_range N _ _ imsh_rng_N eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - imsh_rng_D imsh_rng_N; lia).
  all: first [lia].
Qed.


Definition imsh_mem_pby (m : word -> option byte) (regs : bvmap 5 word) (D N : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem imsh_pby : forall regs m rom D N, imsh_pre regs m D N ->
  scs_denot SEGS m (Ez regs (VALS_imsh D N)) (snd (fst AXF_imsh.RES_pby)) ->
  exists R, msteps SEGS (mkst regs (wa 0x73440) m rom) (mkst R (wa 0x73458) (imsh_mem_pby m regs D N) rom) /\
    getr R 10 = wa D /\ getr R 11 = wa 0 /\ getr R 12 = wa (D + N) /\ getr R 13 = wa D /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom D N P Hsc. destruct (imsh_setup regs m D N P) as [HR HK].
  set (E := Ez regs (VALS_imsh D N)) in *. destruct P as [imsh_R10 imsh_R11 imsh_R12 imsh_rng_D imsh_rng_N].
  assert (Z32 : bv_unsigned (ev E 32) = D) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = N) by (apply zatom; [reflexivity | reflexivity | zrange]).

  destruct (run_sound SEGS 16 [0x73458; 0x7348c; 0x7349c] AXF_imsh.scr_pby 0x73440 AXF_imsh.sr_imsh AXF_imsh.kn_imsh 34 _ _ _ E m rom regs AXF_imsh.RES_pby_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_imsh.RES_pby fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (imsh_mem_pby m regs D N) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold imsh_mem_pby. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition imsh_mem_pwd (m : word -> option byte) (regs : bvmap 5 word) (D N : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem imsh_pwd : forall regs m rom D N, imsh_pre regs m D N ->
  scs_denot SEGS m (Ez regs (VALS_imsh D N)) (snd (fst AXF_imsh.RES_pwd)) ->
  exists R, msteps SEGS (mkst regs (wa 0x73440) m rom) (mkst R (wa 0x7348c) (imsh_mem_pwd m regs D N) rom) /\
    getr R 10 = wa D /\ getr R 11 = wa 0 /\ getr R 12 = wa (D + N) /\ getr R 13 = wa D /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom D N P Hsc. destruct (imsh_setup regs m D N P) as [HR HK].
  set (E := Ez regs (VALS_imsh D N)) in *. destruct P as [imsh_R10 imsh_R11 imsh_R12 imsh_rng_D imsh_rng_N].
  assert (Z32 : bv_unsigned (ev E 32) = D) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = N) by (apply zatom; [reflexivity | reflexivity | zrange]).

  destruct (run_sound SEGS 16 [0x73458; 0x7348c; 0x7349c] AXF_imsh.scr_pwd 0x73440 AXF_imsh.sr_imsh AXF_imsh.kn_imsh 34 _ _ _ E m rom regs AXF_imsh.RES_pwd_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_imsh.RES_pwd fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (imsh_mem_pwd m regs D N) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold imsh_mem_pwd. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End IMSH.
End AXF_imshz.


Module AXF_imsb.
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

Definition e_DP := EVar 32.
Definition e_EN := EVar 33.
Definition sr_imsb := (sr_upd (sr_upd (sr_upd sr_id 11 (ELit 0)) 12 (e_EN)) 13 (e_DP)).
Definition kn_imsb : list kentry :=
  [ KRange e_DP 0 (2^62);
    KRange e_EN 1 (2^62);
    KWr (SA e_DP 0) (ELit 1) ].
Definition scr_imsb : scripts := SCR [true] [] [].
Definition ss_imsb := SS 0x73458 sr_imsb [] kn_imsb 34.
Definition RUN_imsb := sym_exec SEGS 10 true [0x73458; 0x7349c] scr_imsb ss_imsb [].

Definition scr_pbc : scripts := SCR [true] [] [].
Definition RES_pbc := Eval vm_compute in sym_exec SEGS 10 true [0x73458; 0x7349c] scr_pbc ss_imsb [].
Lemma RES_pbc_ok : sym_exec SEGS 10 true [0x73458; 0x7349c] scr_pbc (SS 0x73458 sr_imsb [] kn_imsb 34) [] = RES_pbc.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pbx : scripts := SCR [false] [] [].
Definition RES_pbx := Eval vm_compute in sym_exec SEGS 10 true [0x73458; 0x7349c] scr_pbx ss_imsb [].
Lemma RES_pbx_ok : sym_exec SEGS 10 true [0x73458; 0x7349c] scr_pbx (SS 0x73458 sr_imsb [] kn_imsb 34) [] = RES_pbx.
Proof. vm_compute. reflexivity. Qed.
End AXF_imsb.


Module AXF_imsbz.
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

Section IMSB.
Context {fx : FPState}.

Definition VALS_imsb (DP EN : Z) : list Z := [DP; EN].

Record imsb_pre (regs : bvmap 5 word) (m : word -> option byte) (DP EN : Z) : Prop := {
  imsb_R11 : getr regs 11 = wa 0 ;
  imsb_R12 : getr regs 12 = wa EN ;
  imsb_R13 : getr regs 13 = wa DP ;
  imsb_rng_DP : 0 <= DP <= 2^62 ;
  imsb_rng_EN : 1 <= EN <= 2^62 ;
  imsb_kwr2 : forall d k, 0 <= d -> d + Z.of_nat k <= 1 -> store_ok SEGS m (wa (DP + 0 + d)) k = true
}.


#[using="Type"] Lemma imsb_setup : forall regs m DP EN, imsb_pre regs m DP EN ->
  regs_ok (Ez regs (VALS_imsb DP EN)) AXF_imsb.sr_imsb regs /\ know_ok SEGS (Ez regs (VALS_imsb DP EN)) m AXF_imsb.kn_imsb.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m DP EN P. destruct P as [imsb_R11 imsb_R12 imsb_R13 imsb_rng_DP imsb_rng_EN imsb_kwr2].
  set (E := Ez regs (VALS_imsb DP EN)).
  assert (Z32 : bv_unsigned (ev E 32) = DP) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = EN) by (apply zatom; [reflexivity | reflexivity | zrange]).

  split.
  { unfold AXF_imsb.sr_imsb.
    apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply regs_ok_id|]|]|].
    - rewrite imsb_R11. reflexivity.
    - rewrite imsb_R12. reflexivity.
    - rewrite imsb_R13. reflexivity. }
  unfold know_ok, AXF_imsb.kn_imsb.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_imsb.e_DP AXF_imsb.e_EN a_base a_off].
  all: rewrite ?Z32, ?Z33.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range DP _ _ imsb_rng_DP eq_refl eq_refl), ?(mod64_of_range EN _ _ imsb_rng_EN eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply imsb_kwr2]; assumption).
  all: try (clear - imsb_rng_DP imsb_rng_EN; lia).
  all: first [lia].
Qed.


Definition imsb_mem_pbc (m : word -> option byte) (regs : bvmap 5 word) (DP EN : Z) : word -> option byte :=
  wbytes (m) (wa (DP + 0)) (word_to_le_bytes 1 (wa 0)).

#[using="Type"] Theorem imsb_pbc : forall regs m rom DP EN, imsb_pre regs m DP EN ->
  scs_denot SEGS m (Ez regs (VALS_imsb DP EN)) (snd (fst AXF_imsb.RES_pbc)) ->
  exists R, msteps SEGS (mkst regs (wa 0x73458) m rom) (mkst R (wa 0x73458) (imsb_mem_pbc m regs DP EN) rom) /\
    getr R 11 = wa 0 /\ getr R 12 = wa EN /\ getr R 13 = wa (DP + 1) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom DP EN P Hsc. destruct (imsb_setup regs m DP EN P) as [HR HK].
  set (E := Ez regs (VALS_imsb DP EN)) in *. destruct P as [imsb_R11 imsb_R12 imsb_R13 imsb_rng_DP imsb_rng_EN imsb_kwr2].
  assert (Z32 : bv_unsigned (ev E 32) = DP) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = EN) by (apply zatom; [reflexivity | reflexivity | zrange]).

  destruct (run_sound SEGS 10 [0x73458; 0x7349c] AXF_imsb.scr_pbc 0x73458 AXF_imsb.sr_imsb AXF_imsb.kn_imsb 34 _ _ _ E m rom regs AXF_imsb.RES_pbc_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_imsb.RES_pbc fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (imsb_mem_pbc m regs DP EN) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold imsb_mem_pbc. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition imsb_mem_pbx (m : word -> option byte) (regs : bvmap 5 word) (DP EN : Z) : word -> option byte :=
  wbytes (m) (wa (DP + 0)) (word_to_le_bytes 1 (wa 0)).

#[using="Type"] Theorem imsb_pbx : forall regs m rom DP EN, imsb_pre regs m DP EN ->
  scs_denot SEGS m (Ez regs (VALS_imsb DP EN)) (snd (fst AXF_imsb.RES_pbx)) ->
  exists R, msteps SEGS (mkst regs (wa 0x73458) m rom) (mkst R (wa 0x7349c) (imsb_mem_pbx m regs DP EN) rom) /\
    getr R 11 = wa 0 /\ getr R 12 = wa EN /\ getr R 13 = wa (DP + 1) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom DP EN P Hsc. destruct (imsb_setup regs m DP EN P) as [HR HK].
  set (E := Ez regs (VALS_imsb DP EN)) in *. destruct P as [imsb_R11 imsb_R12 imsb_R13 imsb_rng_DP imsb_rng_EN imsb_kwr2].
  assert (Z32 : bv_unsigned (ev E 32) = DP) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = EN) by (apply zatom; [reflexivity | reflexivity | zrange]).

  destruct (run_sound SEGS 10 [0x73458; 0x7349c] AXF_imsb.scr_pbx 0x73458 AXF_imsb.sr_imsb AXF_imsb.kn_imsb 34 _ _ _ E m rom regs AXF_imsb.RES_pbx_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_imsb.RES_pbx fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (imsb_mem_pbx m regs DP EN) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold imsb_mem_pbx. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End IMSB.
End AXF_imsbz.


Module AXF_imsw.
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

Definition e_DP := EVar 32.
Definition e_EN := EVar 33.
Definition sr_imsw := (sr_upd (sr_upd (sr_upd sr_id 11 (ELit 0)) 12 (e_EN)) 13 (e_DP)).
Definition kn_imsw : list kentry :=
  [ KRange e_DP 0 (2^62);
    KRange e_EN 1 (2^62);
    KWr (SA e_DP 0) (ELit 16) ].
Definition scr_imsw : scripts := SCR [true] [] [].
Definition ss_imsw := SS 0x7348c sr_imsw [] kn_imsw 34.
Definition RUN_imsw := sym_exec SEGS 10 true [0x7348c; 0x7349c] scr_imsw ss_imsw [].

Definition scr_pwc : scripts := SCR [true] [] [].
Definition RES_pwc := Eval vm_compute in sym_exec SEGS 10 true [0x7348c; 0x7349c] scr_pwc ss_imsw [].
Lemma RES_pwc_ok : sym_exec SEGS 10 true [0x7348c; 0x7349c] scr_pwc (SS 0x7348c sr_imsw [] kn_imsw 34) [] = RES_pwc.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pwx : scripts := SCR [false] [] [].
Definition RES_pwx := Eval vm_compute in sym_exec SEGS 10 true [0x7348c; 0x7349c] scr_pwx ss_imsw [].
Lemma RES_pwx_ok : sym_exec SEGS 10 true [0x7348c; 0x7349c] scr_pwx (SS 0x7348c sr_imsw [] kn_imsw 34) [] = RES_pwx.
Proof. vm_compute. reflexivity. Qed.
End AXF_imsw.


Module AXF_imswz.
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

Section IMSW.
Context {fx : FPState}.

Definition VALS_imsw (DP EN : Z) : list Z := [DP; EN].

Record imsw_pre (regs : bvmap 5 word) (m : word -> option byte) (DP EN : Z) : Prop := {
  imsw_R11 : getr regs 11 = wa 0 ;
  imsw_R12 : getr regs 12 = wa EN ;
  imsw_R13 : getr regs 13 = wa DP ;
  imsw_rng_DP : 0 <= DP <= 2^62 ;
  imsw_rng_EN : 1 <= EN <= 2^62 ;
  imsw_kwr2 : forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m (wa (DP + 0 + d)) k = true
}.


#[using="Type"] Lemma imsw_setup : forall regs m DP EN, imsw_pre regs m DP EN ->
  regs_ok (Ez regs (VALS_imsw DP EN)) AXF_imsw.sr_imsw regs /\ know_ok SEGS (Ez regs (VALS_imsw DP EN)) m AXF_imsw.kn_imsw.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m DP EN P. destruct P as [imsw_R11 imsw_R12 imsw_R13 imsw_rng_DP imsw_rng_EN imsw_kwr2].
  set (E := Ez regs (VALS_imsw DP EN)).
  assert (Z32 : bv_unsigned (ev E 32) = DP) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = EN) by (apply zatom; [reflexivity | reflexivity | zrange]).

  split.
  { unfold AXF_imsw.sr_imsw.
    apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply regs_ok_id|]|]|].
    - rewrite imsw_R11. reflexivity.
    - rewrite imsw_R12. reflexivity.
    - rewrite imsw_R13. reflexivity. }
  unfold know_ok, AXF_imsw.kn_imsw.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_imsw.e_DP AXF_imsw.e_EN a_base a_off].
  all: rewrite ?Z32, ?Z33.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range DP _ _ imsw_rng_DP eq_refl eq_refl), ?(mod64_of_range EN _ _ imsw_rng_EN eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply imsw_kwr2]; assumption).
  all: try (clear - imsw_rng_DP imsw_rng_EN; lia).
  all: first [lia].
Qed.


Definition imsw_mem_pwc (m : word -> option byte) (regs : bvmap 5 word) (DP EN : Z) : word -> option byte :=
  wbytes (wbytes (m) (wa (DP + 0)) (word_to_le_bytes 8 (wa 0))) (wa (DP + 8)) (word_to_le_bytes 8 (wa 0)).

#[using="Type"] Theorem imsw_pwc : forall regs m rom DP EN, imsw_pre regs m DP EN ->
  scs_denot SEGS m (Ez regs (VALS_imsw DP EN)) (snd (fst AXF_imsw.RES_pwc)) ->
  exists R, msteps SEGS (mkst regs (wa 0x7348c) m rom) (mkst R (wa 0x7348c) (imsw_mem_pwc m regs DP EN) rom) /\
    getr R 11 = wa 0 /\ getr R 12 = wa EN /\ getr R 13 = wa (DP + 16) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom DP EN P Hsc. destruct (imsw_setup regs m DP EN P) as [HR HK].
  set (E := Ez regs (VALS_imsw DP EN)) in *. destruct P as [imsw_R11 imsw_R12 imsw_R13 imsw_rng_DP imsw_rng_EN imsw_kwr2].
  assert (Z32 : bv_unsigned (ev E 32) = DP) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = EN) by (apply zatom; [reflexivity | reflexivity | zrange]).

  destruct (run_sound SEGS 10 [0x7348c; 0x7349c] AXF_imsw.scr_pwc 0x7348c AXF_imsw.sr_imsw AXF_imsw.kn_imsw 34 _ _ _ E m rom regs AXF_imsw.RES_pwc_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_imsw.RES_pwc fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (imsw_mem_pwc m regs DP EN) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold imsw_mem_pwc. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition imsw_mem_pwx (m : word -> option byte) (regs : bvmap 5 word) (DP EN : Z) : word -> option byte :=
  wbytes (wbytes (m) (wa (DP + 0)) (word_to_le_bytes 8 (wa 0))) (wa (DP + 8)) (word_to_le_bytes 8 (wa 0)).

#[using="Type"] Theorem imsw_pwx : forall regs m rom DP EN, imsw_pre regs m DP EN ->
  scs_denot SEGS m (Ez regs (VALS_imsw DP EN)) (snd (fst AXF_imsw.RES_pwx)) ->
  exists R, msteps SEGS (mkst regs (wa 0x7348c) m rom) (mkst R (wa 0x7349c) (imsw_mem_pwx m regs DP EN) rom) /\
    getr R 11 = wa 0 /\ getr R 12 = wa EN /\ getr R 13 = wa (DP + 16) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom DP EN P Hsc. destruct (imsw_setup regs m DP EN P) as [HR HK].
  set (E := Ez regs (VALS_imsw DP EN)) in *. destruct P as [imsw_R11 imsw_R12 imsw_R13 imsw_rng_DP imsw_rng_EN imsw_kwr2].
  assert (Z32 : bv_unsigned (ev E 32) = DP) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = EN) by (apply zatom; [reflexivity | reflexivity | zrange]).

  destruct (run_sound SEGS 10 [0x7348c; 0x7349c] AXF_imsw.scr_pwx 0x7348c AXF_imsw.sr_imsw AXF_imsw.kn_imsw 34 _ _ _ E m rom regs AXF_imsw.RES_pwx_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_imsw.RES_pwx fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (imsw_mem_pwx m regs DP EN) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold imsw_mem_pwx. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End IMSW.
End AXF_imswz.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
Definition KIMS : list nat := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.

(* [comment removed for export] *)
Definition zeroed (m : word -> option byte) (D N : Z) : Prop := forall i, 0 <= i < N -> m (wa (D + i)) = Some (Z_to_bv 8 0).

Lemma le0_1 : word_to_le_bytes 1 (wa 0) = [Z_to_bv 8 0].
Proof. apply eq_sym. vm_compute. reflexivity. Qed.
Lemma le0_8 : word_to_le_bytes 8 (wa 0) = List.repeat (Z_to_bv 8 0) 8.
Proof. apply eq_sym. vm_compute. reflexivity. Qed.

Section IMS.
Context {fx : FPState}.
Variable rom : word -> option byte.

Section SC.
Variables (R : bvmap 5 word) (m : word -> option byte).
#[using="Type"] Lemma sc_imsb_c : forall DP EN, 0 <= DP <= 2^62 /\ DP + 2 <= EN <= 2^62 ->
  scs_denot SEGS m (Ez R (AXF_imsbz.VALS_imsb DP EN)) (snd (fst AXF_imsb.RES_pbc)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros DP EN HH. unfold AXF_imsbz.VALS_imsb.
  apply (scs_chk_sound [(EVar 32, LO47); (EVar 33, (1, 2^62))] [(EVar 33, EVar 32, 2)]);
    [ repeat (first [apply Forall_nil | apply Forall_cons]); unfold rf_ok, LO47; cbn [fst snd zeval edenot]; zat R; clear - HH; lia
    | repeat (first [apply Forall_nil | apply Forall_cons]); unfold df_ok; cbn [fst snd zeval edenot]; zat R; clear - HH; lia
    | vm_compute; reflexivity ].
Qed.
#[using="Type"] Lemma sc_imsb_x : forall DP EN, 0 <= DP <= 2^62 /\ EN = DP + 1 /\ EN <= 2^62 ->
  scs_denot SEGS m (Ez R (AXF_imsbz.VALS_imsb DP EN)) (snd (fst AXF_imsb.RES_pbx)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros DP EN HH. unfold AXF_imsbz.VALS_imsb.
  apply (scs_chk_sound [(EVar 32, LO47); (EVar 33, (1, 2^62))] [(EVar 33, EVar 32, 1); (EVar 32, EVar 33, -1)]);
    [ repeat (first [apply Forall_nil | apply Forall_cons]); unfold rf_ok, LO47; cbn [fst snd zeval edenot]; zat R; clear - HH; lia
    | repeat (first [apply Forall_nil | apply Forall_cons]); unfold df_ok; cbn [fst snd zeval edenot]; zat R; clear - HH; lia
    | vm_compute; reflexivity ].
Qed.
#[using="Type"] Lemma sc_imsw_c : forall DP EN, 0 <= DP <= 2^62 /\ DP + 17 <= EN <= 2^62 ->
  scs_denot SEGS m (Ez R (AXF_imswz.VALS_imsw DP EN)) (snd (fst AXF_imsw.RES_pwc)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros DP EN HH. unfold AXF_imswz.VALS_imsw.
  apply (scs_chk_sound [(EVar 32, LO47); (EVar 33, (1, 2^62))] [(EVar 33, EVar 32, 17)]);
    [ repeat (first [apply Forall_nil | apply Forall_cons]); unfold rf_ok, LO47; cbn [fst snd zeval edenot]; zat R; clear - HH; lia
    | repeat (first [apply Forall_nil | apply Forall_cons]); unfold df_ok; cbn [fst snd zeval edenot]; zat R; clear - HH; lia
    | vm_compute; reflexivity ].
Qed.
#[using="Type"] Lemma sc_imsw_x : forall DP EN, 0 <= DP <= 2^62 /\ EN = DP + 16 /\ EN <= 2^62 ->
  scs_denot SEGS m (Ez R (AXF_imswz.VALS_imsw DP EN)) (snd (fst AXF_imsw.RES_pwx)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros DP EN HH. unfold AXF_imswz.VALS_imsw.
  apply (scs_chk_sound [(EVar 32, LO47); (EVar 33, (1, 2^62))] [(EVar 33, EVar 32, 16); (EVar 32, EVar 33, -16)]);
    [ repeat (first [apply Forall_nil | apply Forall_cons]); unfold rf_ok, LO47; cbn [fst snd zeval edenot]; zat R; clear - HH; lia
    | repeat (first [apply Forall_nil | apply Forall_cons]); unfold df_ok; cbn [fst snd zeval edenot]; zat R; clear - HH; lia
    | vm_compute; reflexivity ].
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma lor15 : forall N D, 0 <= N -> 0 <= D -> (Z.land (Z.lor N D) 15 = 0 <-> (N mod 16 = 0 /\ D mod 16 = 0)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros N D HN HD. rewrite Z.land_lor_distr_l. change 15 with (Z.ones 4). rewrite !Z.land_ones by lia. change (2^4) with 16.
  apply Z.lor_eq_0_iff.
Qed.
#[using="Type"] Lemma land15_mod : forall X, 0 <= X -> (Z.land (X mod 2^64) (15 mod 2^64)) mod 2^64 = Z.land X 15.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros X HX. change (15 mod 2^64) with 15. rewrite <- (Z.land_ones X 64) by lia. rewrite <- Z.land_assoc.
  change (Z.land (Z.ones 64) 15) with 15. apply Z.mod_small. change 15 with (Z.ones 4). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound X (2^4) ltac:(lia)). lia.
Qed.
#[using="Type"] Lemma sc_imsh_b : forall D N, 0 <= D <= 2^62 /\ 1 <= N <= 2^40 /\ ~ (N mod 16 = 0 /\ D mod 16 = 0) ->
  scs_denot SEGS m (Ez R (AXF_imshz.VALS_imsh D N)) (snd (fst AXF_imsh.RES_pby)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros D N HH. unfold AXF_imshz.VALS_imsh.
  change (snd (fst AXF_imsh.RES_pby)) with [SCBr false BC_EQ (EAlu ALU_AND (EAlu ALU_OR (EVar 33) (EVar 32)) (ELit 15)) (ELit 0)].
  constructor; [|constructor]. apply sc_br_z. rewrite br_eq_z. cbn [zeval edenot]. zat R.
  rewrite !(Z.mod_small N), !(Z.mod_small D) by lia. rewrite land15_mod by (apply Z.lor_nonneg; lia).
  change (0 mod 2^64) with 0. apply Z.eqb_neq. intros Hc. apply (lor15 N D ltac:(lia) ltac:(lia)) in Hc. tauto.
Qed.
#[using="Type"] Lemma sc_imsh_w : forall D N, 0 <= D <= 2^62 /\ 1 <= N <= 2^40 /\ N mod 16 = 0 /\ D mod 16 = 0 ->
  scs_denot SEGS m (Ez R (AXF_imshz.VALS_imsh D N)) (snd (fst AXF_imsh.RES_pwd)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros D N HH. unfold AXF_imshz.VALS_imsh.
  change (snd (fst AXF_imsh.RES_pwd)) with [SCBr true BC_EQ (EAlu ALU_AND (EAlu ALU_OR (EVar 33) (EVar 32)) (ELit 15)) (ELit 0)].
  constructor; [|constructor]. apply sc_br_z. rewrite br_eq_z. cbn [zeval edenot]. zat R.
  rewrite !(Z.mod_small N), !(Z.mod_small D) by lia. rewrite land15_mod by (apply Z.lor_nonneg; lia).
  change (0 mod 2^64) with 0. apply Z.eqb_eq. apply (lor15 N D ltac:(lia) ltac:(lia)). tauto.
Qed.
End SC.

Local Ltac len1 := rewrite ?length_N_to_le_bytes; change (Z.of_nat 1) with 1 in *; change (Z.of_nat 8) with 8 in *.

(* [comment removed for export] *)
#[using="Type"] Lemma imsb_gen : forall (k : nat) regs m DP EN, (1 <= k)%nat -> EN = DP + Z.of_nat k ->
  getr regs 11 = wa 0 -> getr regs 12 = wa EN -> getr regs 13 = wa DP ->
  0 <= DP -> EN <= 2^62 -> wr m DP (Z.of_nat k) ->
  exists R m', msteps SEGS (mkst regs (wa 0x73458) m rom) (mkst R (wa 0x7349c) m' rom) /\
    (forall kk, In kk KIMS -> getr R (Z_to_bv 5 (Z.of_nat kk)) = getr regs (Z_to_bv 5 (Z.of_nat kk))) /\
    getr R 11 = wa 0 /\ getr R 12 = wa EN /\ getr R 13 = wa EN /\
    (forall x, 0 <= x < 2^64 -> ~ (DP <= x < EN) -> m' (wa x) = m (wa x)) /\ mem_ext m m' /\ zeroed m' DP (Z.of_nat k).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros k. induction k as [|k IH]; intros regs m DP EN Hk HEN H11 H12 H13 HD HE HWR; [lia|].
  rewrite Nat2Z.inj_succ in *.
  assert (P : AXF_imsbz.imsb_pre regs m DP EN).
  { constructor; try assumption; try lia.
    intros d kk Hd Hkk. replace (DP + 0 + d) with (DP + d) by ring. apply HWR; lia. }
  set (m1 := wbytes m (wa (DP + 0)) (word_to_le_bytes 1 (wa 0))).
  assert (Hm1c : AXF_imsbz.imsb_mem_pbc m regs DP EN = m1) by reflexivity.
  assert (Hm1x : AXF_imsbz.imsb_mem_pbx m regs DP EN = m1) by reflexivity.
  assert (E1 : forall x, 0 <= x < 2^64 -> ~ (DP <= x < DP + 1) -> m1 (wa x) = m (wa x)).
  { intros x Hx Hn. unfold m1. apply wb_other; [exact Hx | lia | len1; lia | len1; lia]. }
  assert (Z1 : m1 (wa DP) = Some (Z_to_bv 8 0)).
  { unfold m1. rewrite Z.add_0_r. rewrite le0_1. rewrite (wbytes_at_wa0 [Z_to_bv 8 0] m DP ltac:(lia) ltac:(cbn [length]; lia) ltac:(cbn [length]; lia)). reflexivity. }
  assert (X1 : mem_ext m m1) by (unfold m1; apply mem_ext_wbytes).
  destruct k as [|k'].
  - (* [comment removed for export] *)
    destruct (AXF_imsbz.imsb_pbx regs m rom DP EN P (sc_imsb_x regs m DP EN ltac:(cbn in *; lia)))
      as (R & Hms & A11 & A12 & A13 & KK).
    rewrite Hm1x in Hms. exists R, m1. split; [exact Hms|].
    split; [intros kk Hkk; apply KK; exact Hkk|].
    split; [exact A11|]. split; [exact A12|]. split; [rewrite A13; f_equal; cbn in *; lia|].
    split; [intros x Hx Hn; apply E1; [exact Hx | cbn in *; lia]|]. split; [exact X1|].
    intros i Hi. replace (DP + i) with DP by (cbn in *; lia). exact Z1.
  - (* [comment removed for export] *)
    destruct (AXF_imsbz.imsb_pbc regs m rom DP EN P (sc_imsb_c regs m DP EN ltac:(lia)))
      as (R & Hms & A11 & A12 & A13 & KK).
    rewrite Hm1c in Hms.
    destruct (IH R m1 (DP + 1) EN ltac:(lia) ltac:(lia) A11 A12 A13 ltac:(lia) ltac:(lia))
      as (R' & m' & Hms' & KK' & B11 & B12 & B13 & FR & X' & ZZ).
    { intros d kk Hd Hkk. apply (store_ok_mono SEGS kk m m1 _ ltac:(unfold m1; apply wbytes_grows)).
      replace (DP + 1 + d) with (DP + (1 + d)) by ring. apply HWR; lia. }
    exists R', m'. split; [exact (msteps_trans SEGS _ _ _ Hms Hms')|].
    split; [intros kk Hkk; rewrite (KK' kk Hkk); apply KK; exact Hkk|].
    split; [exact B11|]. split; [exact B12|]. split; [exact B13|].
    split; [intros x Hx Hn; rewrite FR by lia; apply E1; lia|]. split; [exact (mem_ext_trans _ _ _ X1 X')|].
    intros i Hi. destruct (Z.eq_dec i 0) as [->|Hi0].
    + rewrite Z.add_0_r. rewrite FR by lia. exact Z1.
    + replace (DP + i) with (DP + 1 + (i - 1)) by ring. apply ZZ. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma imsw_gen : forall (k : nat) regs m DP EN, (1 <= k)%nat -> EN = DP + 16 * Z.of_nat k ->
  getr regs 11 = wa 0 -> getr regs 12 = wa EN -> getr regs 13 = wa DP ->
  0 <= DP -> EN <= 2^62 -> wr m DP (16 * Z.of_nat k) ->
  exists R m', msteps SEGS (mkst regs (wa 0x7348c) m rom) (mkst R (wa 0x7349c) m' rom) /\
    (forall kk, In kk KIMS -> getr R (Z_to_bv 5 (Z.of_nat kk)) = getr regs (Z_to_bv 5 (Z.of_nat kk))) /\
    getr R 11 = wa 0 /\ getr R 12 = wa EN /\ getr R 13 = wa EN /\
    (forall x, 0 <= x < 2^64 -> ~ (DP <= x < EN) -> m' (wa x) = m (wa x)) /\ mem_ext m m' /\ zeroed m' DP (16 * Z.of_nat k).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros k. induction k as [|k IH]; intros regs m DP EN Hk HEN H11 H12 H13 HD HE HWR; [lia|].
  rewrite Nat2Z.inj_succ in *.
  assert (P : AXF_imswz.imsw_pre regs m DP EN).
  { constructor; try assumption; try lia.
    intros d kk Hd Hkk. replace (DP + 0 + d) with (DP + d) by ring. apply HWR; lia. }
  set (m0 := wbytes m (wa (DP + 0)) (word_to_le_bytes 8 (wa 0))).
  set (m1 := wbytes m0 (wa (DP + 8)) (word_to_le_bytes 8 (wa 0))).
  assert (Hm1c : AXF_imswz.imsw_mem_pwc m regs DP EN = m1) by reflexivity.
  assert (Hm1x : AXF_imswz.imsw_mem_pwx m regs DP EN = m1) by reflexivity.
  assert (E1 : forall x, 0 <= x < 2^64 -> ~ (DP <= x < DP + 16) -> m1 (wa x) = m (wa x)).
  { intros x Hx Hn. unfold m1, m0. rewrite wb_other; [|exact Hx | lia | len1; lia | len1; lia].
    apply wb_other; [exact Hx | lia | len1; lia | len1; lia]. }
  assert (Z1 : forall i, 0 <= i < 16 -> m1 (wa (DP + i)) = Some (Z_to_bv 8 0)).
  { intros i Hi. unfold m1, m0. rewrite le0_8. destruct (Z_lt_le_dec i 8) as [Hl|Hl].
    - rewrite wb_other; [| lia | lia | rewrite repeat_length; lia | rewrite repeat_length; lia].
      rewrite Z.add_0_r. replace (DP + i) with (DP + Z.of_nat (Z.to_nat i)) by lia.
      rewrite wbytes_at_wa; [| lia | rewrite repeat_length; lia | rewrite repeat_length; lia].
      rewrite nth_repeat. reflexivity.
    - replace (DP + i) with (DP + 8 + Z.of_nat (Z.to_nat (i - 8))) by lia.
      rewrite wbytes_at_wa; [| lia | rewrite repeat_length; lia | rewrite repeat_length; lia].
      rewrite nth_repeat. reflexivity. }
  assert (X1 : mem_ext m m1) by (unfold m1, m0; eapply mem_ext_trans; apply mem_ext_wbytes).
  assert (G1 : mem_grows m m1) by (unfold m1, m0; intros a Ha; apply wbytes_grows; apply wbytes_grows; exact Ha).
  destruct k as [|k'].
  - (* [comment removed for export] *)
    destruct (AXF_imswz.imsw_pwx regs m rom DP EN P (sc_imsw_x regs m DP EN ltac:(cbn in *; lia)))
      as (R & Hms & A11 & A12 & A13 & KK).
    rewrite Hm1x in Hms. exists R, m1. split; [exact Hms|].
    split; [intros kk Hkk; apply KK; exact Hkk|].
    split; [exact A11|]. split; [exact A12|]. split; [rewrite A13; f_equal; cbn in *; lia|].
    split; [intros x Hx Hn; apply E1; [exact Hx | cbn in *; lia]|]. split; [exact X1|].
    intros i Hi. apply Z1. cbn in *; lia.
  - (* [comment removed for export] *)
    destruct (AXF_imswz.imsw_pwc regs m rom DP EN P (sc_imsw_c regs m DP EN ltac:(lia)))
      as (R & Hms & A11 & A12 & A13 & KK).
    rewrite Hm1c in Hms.
    destruct (IH R m1 (DP + 16) EN ltac:(lia) ltac:(lia) A11 A12 A13 ltac:(lia) ltac:(lia))
      as (R' & m' & Hms' & KK' & B11 & B12 & B13 & FR & X' & ZZ).
    { intros d kk Hd Hkk. apply (store_ok_mono SEGS kk m m1 _ G1).
      replace (DP + 16 + d) with (DP + (16 + d)) by ring. apply HWR; lia. }
    exists R', m'. split; [exact (msteps_trans SEGS _ _ _ Hms Hms')|].
    split; [intros kk Hkk; rewrite (KK' kk Hkk); apply KK; exact Hkk|].
    split; [exact B11|]. split; [exact B12|]. split; [exact B13|].
    split; [intros x Hx Hn; rewrite FR by lia; apply E1; lia|]. split; [exact (mem_ext_trans _ _ _ X1 X')|].
    intros i Hi. destruct (Z_lt_le_dec i 16) as [Hl|Hl].
    + rewrite FR by lia. apply Z1. lia.
    + replace (DP + i) with (DP + 16 + (i - 16)) by ring. apply ZZ. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem ims_contract : forall regs m D N,
  getr regs 10 = wa D -> getr regs 11 = wa 0 -> getr regs 12 = wa N ->
  1 <= N <= 2^40 -> 0 <= D -> D + N <= 2^62 -> wr m D N ->
  exists R m', msteps SEGS (mkst regs (wa 0x73440) m rom) (mkst R (wa 0x7349c) m' rom) /\
    (forall kk, In kk KIMS -> getr R (Z_to_bv 5 (Z.of_nat kk)) = getr regs (Z_to_bv 5 (Z.of_nat kk))) /\
    getr R 11 = wa 0 /\ getr R 12 = wa (D + N) /\ getr R 13 = wa (D + N) /\
    (forall x, 0 <= x < 2^64 -> ~ (D <= x < D + N) -> m' (wa x) = m (wa x)) /\ mem_ext m m' /\ zeroed m' D N.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m D N H10 H11 H12 HN HD HDN HWR.
  assert (P : AXF_imshz.imsh_pre regs m D N) by (constructor; try assumption; lia).
  destruct (Z.eq_dec (N mod 16) 0) as [HaN|HaN]; [destruct (Z.eq_dec (D mod 16) 0) as [HaD|HaD]|].
  - (* [comment removed for export] *)
    destruct (AXF_imshz.imsh_pwd regs m rom D N P (sc_imsh_w regs m D N ltac:(lia))) as (R0 & Hms0 & A10 & A11 & A12 & A13 & KK0).
    unfold AXF_imshz.imsh_mem_pwd in Hms0.
    assert (EN : 16 * Z.of_nat (Z.to_nat (N / 16)) = N).
    { rewrite Z2Nat.id by (apply Z.div_pos; lia). pose proof (Z.div_mod N 16 ltac:(lia)). lia. }
    destruct (imsw_gen (Z.to_nat (N / 16)) R0 m D (D + N) ltac:(lia) ltac:(lia) A11 A12 A13 HD HDN ltac:(rewrite EN; exact HWR))
      as (R & m' & Hms & KK & B11 & B12 & B13 & FR & X & ZZ).
    exists R, m'. split; [exact (msteps_trans SEGS _ _ _ Hms0 Hms)|].
    split; [|split; [exact B11|split; [exact B12|split; [exact B13|split; [exact FR|split; [exact X| rewrite EN in ZZ; exact ZZ]]]]]].
    intros kk Hkk. cbn [KIMS In] in Hkk.
    repeat (destruct Hkk as [<-|Hkk]; [etransitivity; [apply KK; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [KIMS In]; tauto ] | first [apply KK0; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ] | (transitivity (wa D); [exact A10 | symmetry; exact H10])]]|]).
    destruct Hkk.
  - (* [comment removed for export] *)
    destruct (AXF_imshz.imsh_pby regs m rom D N P (sc_imsh_b regs m D N ltac:(lia))) as (R0 & Hms0 & A10 & A11 & A12 & A13 & KK0).
    unfold AXF_imshz.imsh_mem_pby in Hms0.
    destruct (imsb_gen (Z.to_nat N) R0 m D (D + N) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; reflexivity) A11 A12 A13 HD HDN
                ltac:(rewrite Z2Nat.id by lia; exact HWR))
      as (R & m' & Hms & KK & B11 & B12 & B13 & FR & X & ZZ).
    exists R, m'. split; [exact (msteps_trans SEGS _ _ _ Hms0 Hms)|].
    split; [|split; [exact B11|split; [exact B12|split; [exact B13|split; [exact FR|split; [exact X| rewrite Z2Nat.id in ZZ by lia; exact ZZ]]]]]].
    intros kk Hkk. cbn [KIMS In] in Hkk.
    repeat (destruct Hkk as [<-|Hkk]; [etransitivity; [apply KK; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [KIMS In]; tauto ] | first [apply KK0; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ] | (transitivity (wa D); [exact A10 | symmetry; exact H10])]]|]).
    destruct Hkk.
  - (* [comment removed for export] *)
    destruct (AXF_imshz.imsh_pby regs m rom D N P (sc_imsh_b regs m D N ltac:(lia))) as (R0 & Hms0 & A10 & A11 & A12 & A13 & KK0).
    unfold AXF_imshz.imsh_mem_pby in Hms0.
    destruct (imsb_gen (Z.to_nat N) R0 m D (D + N) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; reflexivity) A11 A12 A13 HD HDN
                ltac:(rewrite Z2Nat.id by lia; exact HWR))
      as (R & m' & Hms & KK & B11 & B12 & B13 & FR & X & ZZ).
    exists R, m'. split; [exact (msteps_trans SEGS _ _ _ Hms0 Hms)|].
    split; [|split; [exact B11|split; [exact B12|split; [exact B13|split; [exact FR|split; [exact X| rewrite Z2Nat.id in ZZ by lia; exact ZZ]]]]]].
    intros kk Hkk. cbn [KIMS In] in Hkk.
    repeat (destruct Hkk as [<-|Hkk]; [etransitivity; [apply KK; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [KIMS In]; tauto ] | first [apply KK0; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ] | (transitivity (wa D); [exact A10 | symmetry; exact H10])]]|]).
    destruct Hkk.
Qed.
End IMS.
