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

Module AXF_mb2b.
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

Definition e_n := EVar 32.
Definition e_sc := EVar 33.
Definition e_u1 := EVar 34.
Definition e_H := EVar 35.
Definition e_av := EVar 36.
Definition e_fr := EVar 37.
Definition ACT := EMd M_MUL (ELit 8) e_sc.
Definition sr_mb2b := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (e_n)) 9 (ELit 621712)) 19 (ELit 98952)) 20 (e_sc)).
Definition kn_mb2b : list kentry :=
  [ KRange e_n 1 131051;
    KRange e_sc 4 30;
    KRange e_u1 0 (2^40);
    KAlign e_sc 2;
    KRange e_H 1 (2^63-1);
    KAlign e_H 8;
    KRange e_av 0 (2^32-1);
    KRange e_fr 0 (2^32-1);
    KWord (SA ACT 621800) 8 (ELit 0);
    KWord (SA ACT 621808) 8 e_H;
    KWord (SA ACT 622192) 8 e_u1;
    KWord (SA e_H 24) 4 e_av;
    KWord (SA e_H 28) 4 e_fr ].
Definition scr_mb2b : scripts := SCR [] [] [].
Definition ss_mb2b := SS 0x53fa0 sr_mb2b [] kn_mb2b 38.
Definition RUN_mb2b := sym_exec SEGS 100 true [0x53ff0] scr_mb2b ss_mb2b [].

Definition scr_pb2b1 : scripts := SCR [true; true] [] [].
Definition RES_pb2b1 := Eval vm_compute in sym_exec SEGS 100 true [0x53ff0] scr_pb2b1 ss_mb2b [].
Lemma RES_pb2b1_ok : sym_exec SEGS 100 true [0x53ff0] scr_pb2b1 (SS 0x53fa0 sr_mb2b [] kn_mb2b 38) [] = RES_pb2b1.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pb2b2 : scripts := SCR [true; false] [] [].
Definition RES_pb2b2 := Eval vm_compute in sym_exec SEGS 100 true [0x53ff0] scr_pb2b2 ss_mb2b [].
Lemma RES_pb2b2_ok : sym_exec SEGS 100 true [0x53ff0] scr_pb2b2 (SS 0x53fa0 sr_mb2b [] kn_mb2b 38) [] = RES_pb2b2.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pb2b3 : scripts := SCR [false; true; true] [] [].
Definition RES_pb2b3 := Eval vm_compute in sym_exec SEGS 100 true [0x53ff0] scr_pb2b3 ss_mb2b [].
Lemma RES_pb2b3_ok : sym_exec SEGS 100 true [0x53ff0] scr_pb2b3 (SS 0x53fa0 sr_mb2b [] kn_mb2b 38) [] = RES_pb2b3.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pb2b4 : scripts := SCR [false; true; false] [] [].
Definition RES_pb2b4 := Eval vm_compute in sym_exec SEGS 100 true [0x53ff0] scr_pb2b4 ss_mb2b [].
Lemma RES_pb2b4_ok : sym_exec SEGS 100 true [0x53ff0] scr_pb2b4 (SS 0x53fa0 sr_mb2b [] kn_mb2b 38) [] = RES_pb2b4.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pb2b5 : scripts := SCR [false; false; true] [] [].
Definition RES_pb2b5 := Eval vm_compute in sym_exec SEGS 100 true [0x53ff0] scr_pb2b5 ss_mb2b [].
Lemma RES_pb2b5_ok : sym_exec SEGS 100 true [0x53ff0] scr_pb2b5 (SS 0x53fa0 sr_mb2b [] kn_mb2b 38) [] = RES_pb2b5.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pb2b6 : scripts := SCR [false; false; false] [] [].
Definition RES_pb2b6 := Eval vm_compute in sym_exec SEGS 100 true [0x53ff0] scr_pb2b6 ss_mb2b [].
Lemma RES_pb2b6_ok : sym_exec SEGS 100 true [0x53ff0] scr_pb2b6 (SS 0x53fa0 sr_mb2b [] kn_mb2b 38) [] = RES_pb2b6.
Proof. vm_compute. reflexivity. Qed.
End AXF_mb2b.

Import ListNotations AX2 AX2S.

Module AXF_mb1.
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

Definition e_n := EVar 32.
Definition e_sc := EVar 33.
Definition e_u := EVar 34.
Definition ACT := EMd M_MUL (ELit 8) e_sc.
Definition sr_mb1 := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (e_n)) 9 (ELit 621712)) 19 (ELit 98952)) 20 (e_sc)).
Definition kn_mb1 : list kentry :=
  [ KRange e_n 1 131051;
    KRange e_sc 0 47;
    KRange e_u 0 (2^40);
    KWord (SA (ELit 0) 0x97c23) 1 (ELit 0);
    KWord (SA ACT 621800) 8 (ELit 0);
    KWord (SA ACT 622184) 8 e_u ].
Definition scr_mb1 : scripts := SCR [] [] [].
Definition ss_mb1 := SS 0x53f2c sr_mb1 [] kn_mb1 35.
Definition RUN_mb1 := sym_exec SEGS 100 true [0x5405c; 0x54044; 0x53fa0] scr_mb1 ss_mb1 [].

Definition scr_pb1a : scripts := SCR [true] [] [].
Definition RES_pb1a := Eval vm_compute in sym_exec SEGS 100 true [0x5405c; 0x54044; 0x53fa0] scr_pb1a ss_mb1 [].
Lemma RES_pb1a_ok : sym_exec SEGS 100 true [0x5405c; 0x54044; 0x53fa0] scr_pb1a (SS 0x53f2c sr_mb1 [] kn_mb1 35) [] = RES_pb1a.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pb1b : scripts := SCR [false; true] [] [].
Definition RES_pb1b := Eval vm_compute in sym_exec SEGS 100 true [0x5405c; 0x54044; 0x53fa0] scr_pb1b ss_mb1 [].
Lemma RES_pb1b_ok : sym_exec SEGS 100 true [0x5405c; 0x54044; 0x53fa0] scr_pb1b (SS 0x53f2c sr_mb1 [] kn_mb1 35) [] = RES_pb1b.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pb1c : scripts := SCR [false; false; true] [] [].
Definition RES_pb1c := Eval vm_compute in sym_exec SEGS 100 true [0x5405c; 0x54044; 0x53fa0] scr_pb1c ss_mb1 [].
Lemma RES_pb1c_ok : sym_exec SEGS 100 true [0x5405c; 0x54044; 0x53fa0] scr_pb1c (SS 0x53f2c sr_mb1 [] kn_mb1 35) [] = RES_pb1c.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pb1d : scripts := SCR [false; false; false; false] [] [].
Definition RES_pb1d := Eval vm_compute in sym_exec SEGS 100 true [0x5405c; 0x54044; 0x53fa0] scr_pb1d ss_mb1 [].
Lemma RES_pb1d_ok : sym_exec SEGS 100 true [0x5405c; 0x54044; 0x53fa0] scr_pb1d (SS 0x53f2c sr_mb1 [] kn_mb1 35) [] = RES_pb1d.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pb1e : scripts := SCR [false; false; false; true] [] [].
Definition RES_pb1e := Eval vm_compute in sym_exec SEGS 100 true [0x5405c; 0x54044; 0x53fa0] scr_pb1e ss_mb1 [].
Lemma RES_pb1e_ok : sym_exec SEGS 100 true [0x5405c; 0x54044; 0x53fa0] scr_pb1e (SS 0x53f2c sr_mb1 [] kn_mb1 35) [] = RES_pb1e.
Proof. vm_compute. reflexivity. Qed.
End AXF_mb1.

Module AXF_mb1z.
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

Section MB1.
Context {fx : FPState}.

Definition VALS_mb1 (n sc u : Z) : list Z := [n; sc; u].

Record mb1_pre (regs : bvmap 5 word) (m : word -> option byte) (n sc u : Z) : Prop := {
  mb1_R8 : getr regs 8 = wa n ;
  mb1_R9 : getr regs 9 = wa 621712 ;
  mb1_R19 : getr regs 19 = wa 98952 ;
  mb1_R20 : getr regs 20 = wa sc ;
  mb1_rng_n : 1 <= n <= 131051 ;
  mb1_rng_sc : 0 <= sc <= 47 ;
  mb1_rng_u : 0 <= u <= 2^40 ;
  mb1_kw3 : rdn SEGS m (wa (0 + 621603)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  mb1_kw4 : rdn SEGS m (wa (8 * sc + 621800)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  mb1_kw5 : rdn SEGS m (wa (8 * sc + 622184)) 8 = Some (word_to_le_bytes 8 (wa u))
}.


#[using="Type"] Lemma mb1_setup : forall regs m n sc u, mb1_pre regs m n sc u ->
  regs_ok (Ez regs (VALS_mb1 n sc u)) AXF_mb1.sr_mb1 regs /\ know_ok SEGS (Ez regs (VALS_mb1 n sc u)) m AXF_mb1.kn_mb1.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m n sc u P. destruct P as [mb1_R8 mb1_R9 mb1_R19 mb1_R20 mb1_rng_n mb1_rng_sc mb1_rng_u mb1_kw3 mb1_kw4 mb1_kw5].
  set (E := Ez regs (VALS_mb1 n sc u)).
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = u) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mb1.sr_mb1.
    apply (regs_ok_pin E _ regs 20); [apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|]|].
    - rewrite mb1_R8. reflexivity.
    - rewrite mb1_R9. reflexivity.
    - rewrite mb1_R19. reflexivity.
    - rewrite mb1_R20. reflexivity. }
  unfold know_ok, AXF_mb1.kn_mb1.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mb1.e_n AXF_mb1.e_sc AXF_mb1.e_u AXF_mb1.ACT a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range n _ _ mb1_rng_n eq_refl eq_refl), ?(mod64_of_range sc _ _ mb1_rng_sc eq_refl eq_refl), ?(mod64_of_range u _ _ mb1_rng_u eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - mb1_rng_n mb1_rng_sc mb1_rng_u; lia).
  all: first [lia].
Qed.


Definition mb1_mem_pb1a (m : word -> option byte) (regs : bvmap 5 word) (n sc u : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mb1_pb1a : forall regs m rom n sc u, mb1_pre regs m n sc u ->
  scs_denot SEGS m (Ez regs (VALS_mb1 n sc u)) (snd (fst AXF_mb1.RES_pb1a)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53f2c) m rom) (mkst R (wa 0x54044) (mb1_mem_pb1a m regs n sc u) rom) /\
    getr R 8 = wa n /\ getr R 9 = wa 621712 /\ getr R 10 = wa sc /\ getr R 11 = wa n /\ getr R 12 = wa 6 /\ getr R 18 = wa sc /\ getr R 19 = wa 98952 /\ getr R 20 = wa sc /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n sc u P Hsc. destruct (mb1_setup regs m n sc u P) as [HR HK].
  set (E := Ez regs (VALS_mb1 n sc u)) in *. destruct P as [mb1_R8 mb1_R9 mb1_R19 mb1_R20 mb1_rng_n mb1_rng_sc mb1_rng_u mb1_kw3 mb1_kw4 mb1_kw5].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = u) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x5405c; 0x54044; 0x53fa0] AXF_mb1.scr_pb1a 0x53f2c AXF_mb1.sr_mb1 AXF_mb1.kn_mb1 35 _ _ _ E m rom regs AXF_mb1.RES_pb1a_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mb1.RES_pb1a fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mb1_mem_pb1a m regs n sc u) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mb1_mem_pb1a. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition mb1_mem_pb1b (m : word -> option byte) (regs : bvmap 5 word) (n sc u : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mb1_pb1b : forall regs m rom n sc u, mb1_pre regs m n sc u ->
  scs_denot SEGS m (Ez regs (VALS_mb1 n sc u)) (snd (fst AXF_mb1.RES_pb1b)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53f2c) m rom) (mkst R (wa 0x54044) (mb1_mem_pb1b m regs n sc u) rom) /\
    getr R 8 = wa n /\ getr R 9 = wa 621712 /\ getr R 10 = wa sc /\ getr R 11 = wa n /\ getr R 12 = wa 27 /\ getr R 18 = wa sc /\ getr R 19 = wa 98952 /\ getr R 20 = wa sc /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n sc u P Hsc. destruct (mb1_setup regs m n sc u P) as [HR HK].
  set (E := Ez regs (VALS_mb1 n sc u)) in *. destruct P as [mb1_R8 mb1_R9 mb1_R19 mb1_R20 mb1_rng_n mb1_rng_sc mb1_rng_u mb1_kw3 mb1_kw4 mb1_kw5].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = u) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x5405c; 0x54044; 0x53fa0] AXF_mb1.scr_pb1b 0x53f2c AXF_mb1.sr_mb1 AXF_mb1.kn_mb1 35 _ _ _ E m rom regs AXF_mb1.RES_pb1b_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mb1.RES_pb1b fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mb1_mem_pb1b m regs n sc u) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mb1_mem_pb1b. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition mb1_mem_pb1c (m : word -> option byte) (regs : bvmap 5 word) (n sc u : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mb1_pb1c : forall regs m rom n sc u, mb1_pre regs m n sc u ->
  scs_denot SEGS m (Ez regs (VALS_mb1 n sc u)) (snd (fst AXF_mb1.RES_pb1c)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53f2c) m rom) (mkst R (wa 0x54044) (mb1_mem_pb1c m regs n sc u) rom) /\
    getr R 8 = wa n /\ getr R 9 = wa 621712 /\ getr R 10 = wa sc /\ getr R 11 = wa n /\ getr R 12 = wa 27 /\ getr R 18 = wa sc /\ getr R 19 = wa 98952 /\ getr R 20 = wa sc /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n sc u P Hsc. destruct (mb1_setup regs m n sc u P) as [HR HK].
  set (E := Ez regs (VALS_mb1 n sc u)) in *. destruct P as [mb1_R8 mb1_R9 mb1_R19 mb1_R20 mb1_rng_n mb1_rng_sc mb1_rng_u mb1_kw3 mb1_kw4 mb1_kw5].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = u) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x5405c; 0x54044; 0x53fa0] AXF_mb1.scr_pb1c 0x53f2c AXF_mb1.sr_mb1 AXF_mb1.kn_mb1 35 _ _ _ E m rom regs AXF_mb1.RES_pb1c_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mb1.RES_pb1c fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mb1_mem_pb1c m regs n sc u) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mb1_mem_pb1c. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition mb1_mem_pb1d (m : word -> option byte) (regs : bvmap 5 word) (n sc u : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mb1_pb1d : forall regs m rom n sc u, mb1_pre regs m n sc u ->
  scs_denot SEGS m (Ez regs (VALS_mb1 n sc u)) (snd (fst AXF_mb1.RES_pb1d)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53f2c) m rom) (mkst R (wa 0x54044) (mb1_mem_pb1d m regs n sc u) rom) /\
    getr R 8 = wa n /\ getr R 9 = wa 621712 /\ getr R 10 = wa sc /\ getr R 11 = wa n /\ getr R 12 = wa 27 /\ getr R 18 = wa sc /\ getr R 19 = wa 98952 /\ getr R 20 = wa sc /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n sc u P Hsc. destruct (mb1_setup regs m n sc u P) as [HR HK].
  set (E := Ez regs (VALS_mb1 n sc u)) in *. destruct P as [mb1_R8 mb1_R9 mb1_R19 mb1_R20 mb1_rng_n mb1_rng_sc mb1_rng_u mb1_kw3 mb1_kw4 mb1_kw5].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = u) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x5405c; 0x54044; 0x53fa0] AXF_mb1.scr_pb1d 0x53f2c AXF_mb1.sr_mb1 AXF_mb1.kn_mb1 35 _ _ _ E m rom regs AXF_mb1.RES_pb1d_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mb1.RES_pb1d fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mb1_mem_pb1d m regs n sc u) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mb1_mem_pb1d. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition mb1_mem_pb1e (m : word -> option byte) (regs : bvmap 5 word) (n sc u : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mb1_pb1e : forall regs m rom n sc u, mb1_pre regs m n sc u ->
  scs_denot SEGS m (Ez regs (VALS_mb1 n sc u)) (snd (fst AXF_mb1.RES_pb1e)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53f2c) m rom) (mkst R (wa 0x53fa0) (mb1_mem_pb1e m regs n sc u) rom) /\
    getr R 8 = wa n /\ getr R 9 = wa 621712 /\ getr R 10 = wa u /\ getr R 11 = wa (Z.land sc 1) /\ getr R 12 = wa 27 /\ getr R 18 = wa 0 /\ getr R 19 = wa 98952 /\ getr R 20 = wa sc /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n sc u P Hsc. destruct (mb1_setup regs m n sc u P) as [HR HK].
  set (E := Ez regs (VALS_mb1 n sc u)) in *. destruct P as [mb1_R8 mb1_R9 mb1_R19 mb1_R20 mb1_rng_n mb1_rng_sc mb1_rng_u mb1_kw3 mb1_kw4 mb1_kw5].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = u) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x5405c; 0x54044; 0x53fa0] AXF_mb1.scr_pb1e 0x53f2c AXF_mb1.sr_mb1 AXF_mb1.kn_mb1 35 _ _ _ E m rom regs AXF_mb1.RES_pb1e_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mb1.RES_pb1e fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mb1_mem_pb1e m regs n sc u) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mb1_mem_pb1e. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MB1.
End AXF_mb1z.

Module AXF_mb2a.
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

Definition e_n := EVar 32.
Definition e_sc := EVar 33.
Definition e_u1 := EVar 34.
Definition ACT := EMd M_MUL (ELit 8) e_sc.
Definition sr_mb2a := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (e_n)) 9 (ELit 621712)) 19 (ELit 98952)) 20 (e_sc)).
Definition kn_mb2a : list kentry :=
  [ KRange e_n 1 131051;
    KRange e_sc 4 30;
    KRange e_u1 0 (2^40);
    KAlign e_sc 2;
    KWord (SA ACT 621800) 8 (ELit 0);
    KWord (SA ACT 621808) 8 (ELit 0);
    KWord (SA ACT 622192) 8 e_u1 ].
Definition scr_mb2a : scripts := SCR [] [] [].
Definition ss_mb2a := SS 0x53fa0 sr_mb2a [] kn_mb2a 35.
Definition RUN_mb2a := sym_exec SEGS 100 true [0x5405c; 0x54044] scr_mb2a ss_mb2a [].

Definition scr_pb2at : scripts := SCR [true] [] [].
Definition RES_pb2at := Eval vm_compute in sym_exec SEGS 100 true [0x5405c; 0x54044] scr_pb2at ss_mb2a [].
Lemma RES_pb2at_ok : sym_exec SEGS 100 true [0x5405c; 0x54044] scr_pb2at (SS 0x53fa0 sr_mb2a [] kn_mb2a 35) [] = RES_pb2at.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pb2af : scripts := SCR [false] [] [].
Definition RES_pb2af := Eval vm_compute in sym_exec SEGS 100 true [0x5405c; 0x54044] scr_pb2af ss_mb2a [].
Lemma RES_pb2af_ok : sym_exec SEGS 100 true [0x5405c; 0x54044] scr_pb2af (SS 0x53fa0 sr_mb2a [] kn_mb2a 35) [] = RES_pb2af.
Proof. vm_compute. reflexivity. Qed.
End AXF_mb2a.

Module AXF_mb2az.
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

Section MB2A.
Context {fx : FPState}.

Definition VALS_mb2a (n sc u1 : Z) : list Z := [n; sc; u1].

Record mb2a_pre (regs : bvmap 5 word) (m : word -> option byte) (n sc u1 : Z) : Prop := {
  mb2a_R8 : getr regs 8 = wa n ;
  mb2a_R9 : getr regs 9 = wa 621712 ;
  mb2a_R19 : getr regs 19 = wa 98952 ;
  mb2a_R20 : getr regs 20 = wa sc ;
  mb2a_rng_n : 1 <= n <= 131051 ;
  mb2a_rng_sc : 4 <= sc <= 30 ;
  mb2a_rng_u1 : 0 <= u1 <= 2^40 ;
  mb2a_ka3 : sc mod 2 = 0 ;
  mb2a_kw4 : rdn SEGS m (wa (8 * sc + 621800)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  mb2a_kw5 : rdn SEGS m (wa (8 * sc + 621808)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  mb2a_kw6 : rdn SEGS m (wa (8 * sc + 622192)) 8 = Some (word_to_le_bytes 8 (wa u1))
}.


#[using="Type"] Lemma mb2a_setup : forall regs m n sc u1, mb2a_pre regs m n sc u1 ->
  regs_ok (Ez regs (VALS_mb2a n sc u1)) AXF_mb2a.sr_mb2a regs /\ know_ok SEGS (Ez regs (VALS_mb2a n sc u1)) m AXF_mb2a.kn_mb2a.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m n sc u1 P. destruct P as [mb2a_R8 mb2a_R9 mb2a_R19 mb2a_R20 mb2a_rng_n mb2a_rng_sc mb2a_rng_u1 mb2a_ka3 mb2a_kw4 mb2a_kw5 mb2a_kw6].
  set (E := Ez regs (VALS_mb2a n sc u1)).
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = u1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mb2a.sr_mb2a.
    apply (regs_ok_pin E _ regs 20); [apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|]|].
    - rewrite mb2a_R8. reflexivity.
    - rewrite mb2a_R9. reflexivity.
    - rewrite mb2a_R19. reflexivity.
    - rewrite mb2a_R20. reflexivity. }
  unfold know_ok, AXF_mb2a.kn_mb2a.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mb2a.e_n AXF_mb2a.e_sc AXF_mb2a.e_u1 AXF_mb2a.ACT a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range n _ _ mb2a_rng_n eq_refl eq_refl), ?(mod64_of_range sc _ _ mb2a_rng_sc eq_refl eq_refl), ?(mod64_of_range u1 _ _ mb2a_rng_u1 eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - mb2a_rng_n mb2a_rng_sc mb2a_rng_u1 mb2a_ka3; lia).
  all: first [lia].
Qed.


Definition mb2a_mem_pb2at (m : word -> option byte) (regs : bvmap 5 word) (n sc u1 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mb2a_pb2at : forall regs m rom n sc u1, mb2a_pre regs m n sc u1 ->
  scs_denot SEGS m (Ez regs (VALS_mb2a n sc u1)) (snd (fst AXF_mb2a.RES_pb2at)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53fa0) m rom) (mkst R (wa 0x54044) (mb2a_mem_pb2at m regs n sc u1) rom) /\
    getr R 8 = wa n /\ getr R 9 = wa 621712 /\ getr R 10 = wa (sc + 1) /\ getr R 11 = wa n /\ getr R 12 = wa 13 /\ getr R 18 = wa (sc + 1) /\ getr R 19 = wa 98952 /\ getr R 20 = wa (sc + 1) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n sc u1 P Hsc. destruct (mb2a_setup regs m n sc u1 P) as [HR HK].
  set (E := Ez regs (VALS_mb2a n sc u1)) in *. destruct P as [mb2a_R8 mb2a_R9 mb2a_R19 mb2a_R20 mb2a_rng_n mb2a_rng_sc mb2a_rng_u1 mb2a_ka3 mb2a_kw4 mb2a_kw5 mb2a_kw6].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = u1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x5405c; 0x54044] AXF_mb2a.scr_pb2at 0x53fa0 AXF_mb2a.sr_mb2a AXF_mb2a.kn_mb2a 35 _ _ _ E m rom regs AXF_mb2a.RES_pb2at_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mb2a.RES_pb2at fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mb2a_mem_pb2at m regs n sc u1) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mb2a_mem_pb2at. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition mb2a_mem_pb2af (m : word -> option byte) (regs : bvmap 5 word) (n sc u1 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mb2a_pb2af : forall regs m rom n sc u1, mb2a_pre regs m n sc u1 ->
  scs_denot SEGS m (Ez regs (VALS_mb2a n sc u1)) (snd (fst AXF_mb2a.RES_pb2af)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53fa0) m rom) (mkst R (wa 0x54044) (mb2a_mem_pb2af m regs n sc u1) rom) /\
    getr R 8 = wa n /\ getr R 9 = wa 621712 /\ getr R 10 = wa sc /\ getr R 11 = wa n /\ getr R 12 = wa 13 /\ getr R 18 = wa sc /\ getr R 19 = wa 98952 /\ getr R 20 = wa sc /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n sc u1 P Hsc. destruct (mb2a_setup regs m n sc u1 P) as [HR HK].
  set (E := Ez regs (VALS_mb2a n sc u1)) in *. destruct P as [mb2a_R8 mb2a_R9 mb2a_R19 mb2a_R20 mb2a_rng_n mb2a_rng_sc mb2a_rng_u1 mb2a_ka3 mb2a_kw4 mb2a_kw5 mb2a_kw6].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = u1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x5405c; 0x54044] AXF_mb2a.scr_pb2af 0x53fa0 AXF_mb2a.sr_mb2a AXF_mb2a.kn_mb2a 35 _ _ _ E m rom regs AXF_mb2a.RES_pb2af_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mb2a.RES_pb2af fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mb2a_mem_pb2af m regs n sc u1) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mb2a_mem_pb2af. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MB2A.
End AXF_mb2az.

Module AXF_mbz.
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

Definition e_n := EVar 32.
Definition e_sc := EVar 33.
Definition sr_mbz := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (e_n)) 9 (ELit 621712)) 18 (ELit 0)) 19 (ELit 98952)) 20 (e_sc)).
Definition kn_mbz : list kentry :=
  [ KRange e_n 1 131051;
    KRange e_sc 0 47 ].
Definition scr_mbz : scripts := SCR [] [] [].
Definition ss_mbz := SS 0x53ff0 sr_mbz [] kn_mbz 34.
Definition RUN_mbz := sym_exec SEGS 100 true [0x5405c; 0x54044] scr_mbz ss_mbz [].

Definition scr_pbz : scripts := SCR [true; true] [] [].
Definition RES_pbz := Eval vm_compute in sym_exec SEGS 100 true [0x5405c; 0x54044] scr_pbz ss_mbz [].
Lemma RES_pbz_ok : sym_exec SEGS 100 true [0x5405c; 0x54044] scr_pbz (SS 0x53ff0 sr_mbz [] kn_mbz 34) [] = RES_pbz.
Proof. vm_compute. reflexivity. Qed.
End AXF_mbz.

Module AXF_mbzz.
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

Section MBZ.
Context {fx : FPState}.

Definition VALS_mbz (n sc : Z) : list Z := [n; sc].

Record mbz_pre (regs : bvmap 5 word) (m : word -> option byte) (n sc : Z) : Prop := {
  mbz_R8 : getr regs 8 = wa n ;
  mbz_R9 : getr regs 9 = wa 621712 ;
  mbz_R18 : getr regs 18 = wa 0 ;
  mbz_R19 : getr regs 19 = wa 98952 ;
  mbz_R20 : getr regs 20 = wa sc ;
  mbz_rng_n : 1 <= n <= 131051 ;
  mbz_rng_sc : 0 <= sc <= 47
}.


#[using="Type"] Lemma mbz_setup : forall regs m n sc, mbz_pre regs m n sc ->
  regs_ok (Ez regs (VALS_mbz n sc)) AXF_mbz.sr_mbz regs /\ know_ok SEGS (Ez regs (VALS_mbz n sc)) m AXF_mbz.kn_mbz.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m n sc P. destruct P as [mbz_R8 mbz_R9 mbz_R18 mbz_R19 mbz_R20 mbz_rng_n mbz_rng_sc].
  set (E := Ez regs (VALS_mbz n sc)).
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mbz.sr_mbz.
    apply (regs_ok_pin E _ regs 20); [apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|]|]|].
    - rewrite mbz_R8. reflexivity.
    - rewrite mbz_R9. reflexivity.
    - rewrite mbz_R18. reflexivity.
    - rewrite mbz_R19. reflexivity.
    - rewrite mbz_R20. reflexivity. }
  unfold know_ok, AXF_mbz.kn_mbz.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mbz.e_n AXF_mbz.e_sc a_base a_off].
  all: rewrite ?Z32, ?Z33.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range n _ _ mbz_rng_n eq_refl eq_refl), ?(mod64_of_range sc _ _ mbz_rng_sc eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - mbz_rng_n mbz_rng_sc; lia).
  all: first [lia].
Qed.


Definition mbz_mem_pbz (m : word -> option byte) (regs : bvmap 5 word) (n sc : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mbz_pbz : forall regs m rom n sc, mbz_pre regs m n sc ->
  scs_denot SEGS m (Ez regs (VALS_mbz n sc)) (snd (fst AXF_mbz.RES_pbz)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53ff0) m rom) (mkst R (wa 0x54044) (mbz_mem_pbz m regs n sc) rom) /\
    getr R 8 = wa n /\ getr R 9 = wa 621712 /\ getr R 10 = wa sc /\ getr R 11 = wa n /\ getr R 18 = wa sc /\ getr R 19 = wa 98952 /\ getr R 20 = wa sc /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 12; 13; 14; 15; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n sc P Hsc. destruct (mbz_setup regs m n sc P) as [HR HK].
  set (E := Ez regs (VALS_mbz n sc)) in *. destruct P as [mbz_R8 mbz_R9 mbz_R18 mbz_R19 mbz_R20 mbz_rng_n mbz_rng_sc].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x5405c; 0x54044] AXF_mbz.scr_pbz 0x53ff0 AXF_mbz.sr_mbz AXF_mbz.kn_mbz 34 _ _ _ E m rom regs AXF_mbz.RES_pbz_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mbz.RES_pbz fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mbz_mem_pbz m regs n sc) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mbz_mem_pbz. repeat (apply (f_equal3 wbytes)); try reflexivity.
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

End MBZ.
End AXF_mbzz.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section MB2B.
Context {fx : FPState}.

Definition VALS_mb2b (n sc u1 H av fr : Z) : list Z := [n; sc; u1; H; av; fr].

Record mb2b_pre (regs : bvmap 5 word) (m : word -> option byte) (n sc u1 H av fr : Z) : Prop := {
  mb2b_R8 : getr regs 8 = wa n ;
  mb2b_R9 : getr regs 9 = wa 621712 ;
  mb2b_R19 : getr regs 19 = wa 98952 ;
  mb2b_R20 : getr regs 20 = wa sc ;
  mb2b_rng_n : 1 <= n <= 131051 ;
  mb2b_rng_sc : 4 <= sc <= 30 ;
  mb2b_rng_u1 : 0 <= u1 <= 2^40 ;
  mb2b_rng_H : 1 <= H <= 2^63-1 ;
  mb2b_rng_av : 0 <= av <= 2^32-1 ;
  mb2b_rng_fr : 0 <= fr <= 2^32-1 ;
  mb2b_ka3 : sc mod 2 = 0 ;
  mb2b_ka5 : H mod 8 = 0 ;
  mb2b_kw8 : rdn SEGS m (wa (8 * sc + 621800)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  mb2b_kw9 : rdn SEGS m (wa (8 * sc + 621808)) 8 = Some (word_to_le_bytes 8 (wa H)) ;
  mb2b_kw10 : rdn SEGS m (wa (8 * sc + 622192)) 8 = Some (word_to_le_bytes 8 (wa u1)) ;
  mb2b_kw11 : rdn SEGS m (wa (H + 24)) 4 = Some (word_to_le_bytes 4 (wa av)) ;
  mb2b_kw12 : rdn SEGS m (wa (H + 28)) 4 = Some (word_to_le_bytes 4 (wa fr))
}.


#[using="Type"] Lemma mb2b_setup : forall regs m n sc u1 H av fr, mb2b_pre regs m n sc u1 H av fr ->
  regs_ok (Ez regs (VALS_mb2b n sc u1 H av fr)) AXF_mb2b.sr_mb2b regs /\ know_ok SEGS (Ez regs (VALS_mb2b n sc u1 H av fr)) m AXF_mb2b.kn_mb2b.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m n sc u1 H av fr P. destruct P as [mb2b_R8 mb2b_R9 mb2b_R19 mb2b_R20 mb2b_rng_n mb2b_rng_sc mb2b_rng_u1 mb2b_rng_H mb2b_rng_av mb2b_rng_fr mb2b_ka3 mb2b_ka5 mb2b_kw8 mb2b_kw9 mb2b_kw10 mb2b_kw11 mb2b_kw12].
  set (E := Ez regs (VALS_mb2b n sc u1 H av fr)).
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = u1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = H) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = av) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = fr) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mb2b.sr_mb2b.
    apply (regs_ok_pin E _ regs 20); [apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|]|].
    - rewrite mb2b_R8. reflexivity.
    - rewrite mb2b_R9. reflexivity.
    - rewrite mb2b_R19. reflexivity.
    - rewrite mb2b_R20. reflexivity. }
  unfold know_ok, AXF_mb2b.kn_mb2b.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mb2b.e_n AXF_mb2b.e_sc AXF_mb2b.e_u1 AXF_mb2b.e_H AXF_mb2b.e_av AXF_mb2b.e_fr AXF_mb2b.ACT a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range n _ _ mb2b_rng_n eq_refl eq_refl), ?(mod64_of_range sc _ _ mb2b_rng_sc eq_refl eq_refl), ?(mod64_of_range u1 _ _ mb2b_rng_u1 eq_refl eq_refl), ?(mod64_of_range H _ _ mb2b_rng_H eq_refl eq_refl), ?(mod64_of_range av _ _ mb2b_rng_av eq_refl eq_refl), ?(mod64_of_range fr _ _ mb2b_rng_fr eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - mb2b_rng_n mb2b_rng_sc mb2b_rng_u1 mb2b_rng_H mb2b_rng_av mb2b_rng_fr mb2b_ka3 mb2b_ka5; lia).
  all: first [lia].
Qed.


Definition mb2b_mem_pb2b1 (m : word -> option byte) (regs : bvmap 5 word) (n sc u1 H av fr : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mb2b_pb2b1 : forall regs m rom n sc u1 H av fr, mb2b_pre regs m n sc u1 H av fr ->
  scs_denot SEGS m (Ez regs (VALS_mb2b n sc u1 H av fr)) (snd (fst AXF_mb2b.RES_pb2b1)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53fa0) m rom) (mkst R (wa 0x53ff0) (mb2b_mem_pb2b1 m regs n sc u1 H av fr) rom) /\
    getr R 8 = wa n /\ getr R 9 = wa 621712 /\ getr R 10 = wa (sc + 1) /\ getr R 11 = wa ((8 * sc) + 621720) /\ getr R 12 = wa 13 /\ getr R 13 = wa (ext_Z true 0 4 av) /\ getr R 18 = wa H /\ getr R 19 = wa 98952 /\ getr R 20 = wa (sc + 1) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 14; 15; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n sc u1 H av fr P Hsc. destruct (mb2b_setup regs m n sc u1 H av fr P) as [HR HK].
  set (E := Ez regs (VALS_mb2b n sc u1 H av fr)) in *. destruct P as [mb2b_R8 mb2b_R9 mb2b_R19 mb2b_R20 mb2b_rng_n mb2b_rng_sc mb2b_rng_u1 mb2b_rng_H mb2b_rng_av mb2b_rng_fr mb2b_ka3 mb2b_ka5 mb2b_kw8 mb2b_kw9 mb2b_kw10 mb2b_kw11 mb2b_kw12].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = u1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = H) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = av) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = fr) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53ff0] AXF_mb2b.scr_pb2b1 0x53fa0 AXF_mb2b.sr_mb2b AXF_mb2b.kn_mb2b 38 _ _ _ E m rom regs AXF_mb2b.RES_pb2b1_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mb2b.RES_pb2b1 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mb2b_mem_pb2b1 m regs n sc u1 H av fr) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mb2b_mem_pb2b1. repeat (apply (f_equal3 wbytes)); try reflexivity.
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


Definition mb2b_mem_pb2b2 (m : word -> option byte) (regs : bvmap 5 word) (n sc u1 H av fr : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mb2b_pb2b2 : forall regs m rom n sc u1 H av fr, mb2b_pre regs m n sc u1 H av fr ->
  scs_denot SEGS m (Ez regs (VALS_mb2b n sc u1 H av fr)) (snd (fst AXF_mb2b.RES_pb2b2)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53fa0) m rom) (mkst R (wa 0x53ff0) (mb2b_mem_pb2b2 m regs n sc u1 H av fr) rom) /\
    getr R 8 = wa n /\ getr R 9 = wa 621712 /\ getr R 10 = wa sc /\ getr R 11 = wa ((8 * sc) + 621712) /\ getr R 12 = wa 13 /\ getr R 13 = wa (ext_Z true 0 4 av) /\ getr R 18 = wa 0 /\ getr R 19 = wa 98952 /\ getr R 20 = wa sc /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 14; 15; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n sc u1 H av fr P Hsc. destruct (mb2b_setup regs m n sc u1 H av fr P) as [HR HK].
  set (E := Ez regs (VALS_mb2b n sc u1 H av fr)) in *. destruct P as [mb2b_R8 mb2b_R9 mb2b_R19 mb2b_R20 mb2b_rng_n mb2b_rng_sc mb2b_rng_u1 mb2b_rng_H mb2b_rng_av mb2b_rng_fr mb2b_ka3 mb2b_ka5 mb2b_kw8 mb2b_kw9 mb2b_kw10 mb2b_kw11 mb2b_kw12].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = u1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = H) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = av) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = fr) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53ff0] AXF_mb2b.scr_pb2b2 0x53fa0 AXF_mb2b.sr_mb2b AXF_mb2b.kn_mb2b 38 _ _ _ E m rom regs AXF_mb2b.RES_pb2b2_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mb2b.RES_pb2b2 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mb2b_mem_pb2b2 m regs n sc u1 H av fr) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mb2b_mem_pb2b2. repeat (apply (f_equal3 wbytes)); try reflexivity.
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


Definition mb2b_mem_pb2b3 (m : word -> option byte) (regs : bvmap 5 word) (n sc u1 H av fr : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mb2b_pb2b3 : forall regs m rom n sc u1 H av fr, mb2b_pre regs m n sc u1 H av fr ->
  scs_denot SEGS m (Ez regs (VALS_mb2b n sc u1 H av fr)) (snd (fst AXF_mb2b.RES_pb2b3)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53fa0) m rom) (mkst R (wa 0x53ff0) (mb2b_mem_pb2b3 m regs n sc u1 H av fr) rom) /\
    getr R 8 = wa n /\ getr R 9 = wa 621712 /\ getr R 10 = wa (sc + 1) /\ getr R 11 = wa ((8 * sc) + 621720) /\ getr R 12 = wa 13 /\ getr R 13 = wa (ext_Z true 0 4 av) /\ getr R 18 = wa H /\ getr R 19 = wa 98952 /\ getr R 20 = wa (sc + 1) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 14; 15; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n sc u1 H av fr P Hsc. destruct (mb2b_setup regs m n sc u1 H av fr P) as [HR HK].
  set (E := Ez regs (VALS_mb2b n sc u1 H av fr)) in *. destruct P as [mb2b_R8 mb2b_R9 mb2b_R19 mb2b_R20 mb2b_rng_n mb2b_rng_sc mb2b_rng_u1 mb2b_rng_H mb2b_rng_av mb2b_rng_fr mb2b_ka3 mb2b_ka5 mb2b_kw8 mb2b_kw9 mb2b_kw10 mb2b_kw11 mb2b_kw12].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = u1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = H) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = av) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = fr) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53ff0] AXF_mb2b.scr_pb2b3 0x53fa0 AXF_mb2b.sr_mb2b AXF_mb2b.kn_mb2b 38 _ _ _ E m rom regs AXF_mb2b.RES_pb2b3_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mb2b.RES_pb2b3 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mb2b_mem_pb2b3 m regs n sc u1 H av fr) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mb2b_mem_pb2b3. repeat (apply (f_equal3 wbytes)); try reflexivity.
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


Definition mb2b_mem_pb2b4 (m : word -> option byte) (regs : bvmap 5 word) (n sc u1 H av fr : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mb2b_pb2b4 : forall regs m rom n sc u1 H av fr, mb2b_pre regs m n sc u1 H av fr ->
  scs_denot SEGS m (Ez regs (VALS_mb2b n sc u1 H av fr)) (snd (fst AXF_mb2b.RES_pb2b4)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53fa0) m rom) (mkst R (wa 0x53ff0) (mb2b_mem_pb2b4 m regs n sc u1 H av fr) rom) /\
    getr R 8 = wa n /\ getr R 9 = wa 621712 /\ getr R 10 = wa sc /\ getr R 11 = wa ((8 * sc) + 621712) /\ getr R 12 = wa 13 /\ getr R 13 = wa (ext_Z true 0 4 av) /\ getr R 18 = wa 0 /\ getr R 19 = wa 98952 /\ getr R 20 = wa sc /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 14; 15; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n sc u1 H av fr P Hsc. destruct (mb2b_setup regs m n sc u1 H av fr P) as [HR HK].
  set (E := Ez regs (VALS_mb2b n sc u1 H av fr)) in *. destruct P as [mb2b_R8 mb2b_R9 mb2b_R19 mb2b_R20 mb2b_rng_n mb2b_rng_sc mb2b_rng_u1 mb2b_rng_H mb2b_rng_av mb2b_rng_fr mb2b_ka3 mb2b_ka5 mb2b_kw8 mb2b_kw9 mb2b_kw10 mb2b_kw11 mb2b_kw12].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = u1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = H) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = av) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = fr) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53ff0] AXF_mb2b.scr_pb2b4 0x53fa0 AXF_mb2b.sr_mb2b AXF_mb2b.kn_mb2b 38 _ _ _ E m rom regs AXF_mb2b.RES_pb2b4_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mb2b.RES_pb2b4 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mb2b_mem_pb2b4 m regs n sc u1 H av fr) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mb2b_mem_pb2b4. repeat (apply (f_equal3 wbytes)); try reflexivity.
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


Definition mb2b_mem_pb2b5 (m : word -> option byte) (regs : bvmap 5 word) (n sc u1 H av fr : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mb2b_pb2b5 : forall regs m rom n sc u1 H av fr, mb2b_pre regs m n sc u1 H av fr ->
  scs_denot SEGS m (Ez regs (VALS_mb2b n sc u1 H av fr)) (snd (fst AXF_mb2b.RES_pb2b5)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53fa0) m rom) (mkst R (wa 0x53ff0) (mb2b_mem_pb2b5 m regs n sc u1 H av fr) rom) /\
    getr R 8 = wa n /\ getr R 9 = wa 621712 /\ getr R 10 = wa (sc + 1) /\ getr R 11 = wa ((8 * sc) + 621720) /\ getr R 12 = wa 13 /\ getr R 13 = wa (ext_Z true 0 4 av) /\ getr R 18 = wa H /\ getr R 19 = wa 98952 /\ getr R 20 = wa (sc + 1) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 14; 15; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n sc u1 H av fr P Hsc. destruct (mb2b_setup regs m n sc u1 H av fr P) as [HR HK].
  set (E := Ez regs (VALS_mb2b n sc u1 H av fr)) in *. destruct P as [mb2b_R8 mb2b_R9 mb2b_R19 mb2b_R20 mb2b_rng_n mb2b_rng_sc mb2b_rng_u1 mb2b_rng_H mb2b_rng_av mb2b_rng_fr mb2b_ka3 mb2b_ka5 mb2b_kw8 mb2b_kw9 mb2b_kw10 mb2b_kw11 mb2b_kw12].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = u1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = H) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = av) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = fr) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53ff0] AXF_mb2b.scr_pb2b5 0x53fa0 AXF_mb2b.sr_mb2b AXF_mb2b.kn_mb2b 38 _ _ _ E m rom regs AXF_mb2b.RES_pb2b5_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mb2b.RES_pb2b5 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mb2b_mem_pb2b5 m regs n sc u1 H av fr) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mb2b_mem_pb2b5. repeat (apply (f_equal3 wbytes)); try reflexivity.
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


Definition mb2b_mem_pb2b6 (m : word -> option byte) (regs : bvmap 5 word) (n sc u1 H av fr : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mb2b_pb2b6 : forall regs m rom n sc u1 H av fr, mb2b_pre regs m n sc u1 H av fr ->
  scs_denot SEGS m (Ez regs (VALS_mb2b n sc u1 H av fr)) (snd (fst AXF_mb2b.RES_pb2b6)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53fa0) m rom) (mkst R (wa 0x53ff0) (mb2b_mem_pb2b6 m regs n sc u1 H av fr) rom) /\
    getr R 8 = wa n /\ getr R 9 = wa 621712 /\ getr R 10 = wa sc /\ getr R 11 = wa ((8 * sc) + 621712) /\ getr R 12 = wa 13 /\ getr R 13 = wa (ext_Z true 0 4 av) /\ getr R 18 = wa 0 /\ getr R 19 = wa 98952 /\ getr R 20 = wa sc /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 14; 15; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n sc u1 H av fr P Hsc. destruct (mb2b_setup regs m n sc u1 H av fr P) as [HR HK].
  set (E := Ez regs (VALS_mb2b n sc u1 H av fr)) in *. destruct P as [mb2b_R8 mb2b_R9 mb2b_R19 mb2b_R20 mb2b_rng_n mb2b_rng_sc mb2b_rng_u1 mb2b_rng_H mb2b_rng_av mb2b_rng_fr mb2b_ka3 mb2b_ka5 mb2b_kw8 mb2b_kw9 mb2b_kw10 mb2b_kw11 mb2b_kw12].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = u1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = H) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = av) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = fr) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53ff0] AXF_mb2b.scr_pb2b6 0x53fa0 AXF_mb2b.sr_mb2b AXF_mb2b.kn_mb2b 38 _ _ _ E m rom regs AXF_mb2b.RES_pb2b6_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mb2b.RES_pb2b6 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mb2b_mem_pb2b6 m regs n sc u1 H av fr) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mb2b_mem_pb2b6. repeat (apply (f_equal3 wbytes)); try reflexivity.
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

End MB2B.
