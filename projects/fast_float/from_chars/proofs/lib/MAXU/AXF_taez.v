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

Module AXF_tae.
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

Definition e_can := EVar 32.
Definition e_ra0 := EVar 33.
Definition e_s00 := EVar 34.
Definition e_s10 := EVar 35.
Definition e_s20 := EVar 36.
Definition e_s30 := EVar 37.
Definition e_s40 := EVar 38.
Definition e_s50 := EVar 39.
Definition e_s60 := EVar 40.
Definition e_s70 := EVar 41.
Definition e_s80 := EVar 42.
Definition e_s90 := EVar 43.
Definition e_sp0 := EVar 44.
Definition sr_tae := (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-144)))) 20 (ELit 621568)).
Definition kn_tae : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWord (SA (ELit 0) 621568) 8 e_can;
    KWord (SA e_sp0 (-96)) 8 e_can;
    KWord (SA e_sp0 (-8)) 8 e_ra0;
    KWord (SA e_sp0 (-16)) 8 e_s00;
    KWord (SA e_sp0 (-24)) 8 e_s10;
    KWord (SA e_sp0 (-32)) 8 e_s20;
    KWord (SA e_sp0 (-40)) 8 e_s30;
    KWord (SA e_sp0 (-48)) 8 e_s40;
    KWord (SA e_sp0 (-56)) 8 e_s50;
    KWord (SA e_sp0 (-64)) 8 e_s60;
    KWord (SA e_sp0 (-72)) 8 e_s70;
    KWord (SA e_sp0 (-80)) 8 e_s80;
    KWord (SA e_sp0 (-88)) 8 e_s90 ].
Definition scr_tae : scripts := SCR [false] [] [].
Definition ss_tae := SS 0x54908 sr_tae [] kn_tae 45.
Definition RUN_tae := sym_exec SEGS 100 true [0x54944] scr_tae ss_tae [].

Definition scr_ptae : scripts := SCR [false] [] [].
Definition RES_ptae := Eval vm_compute in sym_exec SEGS 100 true [0x54944] scr_ptae ss_tae [].
Lemma RES_ptae_ok : sym_exec SEGS 100 true [0x54944] scr_ptae (SS 0x54908 sr_tae [] kn_tae 45) [] = RES_ptae.
Proof. vm_compute. reflexivity. Qed.
End AXF_tae.

Import ListNotations AX2 AX2S.

Module AXF_ins2.
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

Definition e_mt := EVar 32.
Definition e_sc := EVar 33.
Definition e_av := EVar 34.
Definition ACT := SA (EMd M_MUL (ELit 8) e_sc) 621800.
Definition sr_ins2 := (sr_upd (sr_upd sr_id 9 (e_mt)) 21 (EAlu ALU_ADD (EMd M_MUL (ELit 8) e_sc) (ELit 621800))).
Definition kn_ins2 : list kentry :=
  [ KRange e_mt 1 (2^63-1);
    KAlign e_mt 8;
    KRange e_sc 0 47;
    KRange e_av 1 (2^32-1);
    KWord (SA e_mt 24) 4 e_av;
    KWord ACT 8 (ELit 0);
    KWord (SA e_mt 0) 8 (ELit 0);
    KWord (SA e_mt 8) 8 (ELit 0);
    KWr (SA e_mt 0) (ELit 40);
    KWr ACT (ELit 8);
    KDisj ACT (ELit 8) (SA e_mt 0) (ELit 40) ].
Definition scr_ins2 : scripts := SCR [false; false; true] [] [].
Definition ss_ins2 := SS 0x54828 sr_ins2 [] kn_ins2 35.
Definition RUN_ins2 := sym_exec SEGS 100 true [0x54908] scr_ins2 ss_ins2 [].

Definition scr_pins2 : scripts := SCR [false; false; true] [] [].
Definition RES_pins2 := Eval vm_compute in sym_exec SEGS 100 true [0x54908] scr_pins2 ss_ins2 [].
Lemma RES_pins2_ok : sym_exec SEGS 100 true [0x54908] scr_pins2 (SS 0x54828 sr_ins2 [] kn_ins2 35) [] = RES_pins2.
Proof. vm_compute. reflexivity. Qed.
End AXF_ins2.

Module AXF_ins2z.
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

Section INS2.
Context {fx : FPState}.

Definition VALS_ins2 (mt sc av : Z) : list Z := [mt; sc; av].

Record ins2_pre (regs : bvmap 5 word) (m : word -> option byte) (mt sc av : Z) : Prop := {
  ins2_R9 : getr regs 9 = wa mt ;
  ins2_R21 : getr regs 21 = wa ((8 * sc) + 621800) ;
  ins2_rng_mt : 1 <= mt <= 2^63-1 ;
  ins2_rng_sc : 0 <= sc <= 47 ;
  ins2_rng_av : 1 <= av <= 2^32-1 ;
  ins2_ka1 : mt mod 8 = 0 ;
  ins2_kw4 : rdn SEGS m (wa (mt + 24)) 4 = Some (word_to_le_bytes 4 (wa av)) ;
  ins2_kw5 : rdn SEGS m (wa (8 * sc + 621800)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  ins2_kw6 : rdn SEGS m (wa (mt + 0)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  ins2_kw7 : rdn SEGS m (wa (mt + 8)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  ins2_kwr8 : forall d k, 0 <= d -> d + Z.of_nat k <= 40 -> store_ok SEGS m (wa (mt + 0 + d)) k = true ;
  ins2_kwr9 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (8 * sc + 621800 + d)) k = true ;
  ins2_kd10 : 8 * sc + 621800 + 8 <= mt + 0 \/ mt + 0 + 40 <= 8 * sc + 621800
}.


#[using="Type"] Lemma ins2_setup : forall regs m mt sc av, ins2_pre regs m mt sc av ->
  regs_ok (Ez regs (VALS_ins2 mt sc av)) AXF_ins2.sr_ins2 regs /\ know_ok SEGS (Ez regs (VALS_ins2 mt sc av)) m AXF_ins2.kn_ins2.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m mt sc av P. destruct P as [ins2_R9 ins2_R21 ins2_rng_mt ins2_rng_sc ins2_rng_av ins2_ka1 ins2_kw4 ins2_kw5 ins2_kw6 ins2_kw7 ins2_kwr8 ins2_kwr9 ins2_kd10].
  set (E := Ez regs (VALS_ins2 mt sc av)).
  assert (Z32 : bv_unsigned (ev E 32) = mt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = av) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_ins2.sr_ins2.
    apply (regs_ok_pin E _ regs 21); [apply (regs_ok_pin E _ regs 9); [apply regs_ok_id|]|].
    - rewrite ins2_R9. reflexivity.
    - rewrite ins2_R21, zeval_sound. cbn [zeval edenot AXF_ins2.e_mt AXF_ins2.e_sc AXF_ins2.e_av AXF_ins2.ACT]. rewrite ?Z32, ?Z33, ?Z34. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)]. }
  unfold know_ok, AXF_ins2.kn_ins2.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_ins2.e_mt AXF_ins2.e_sc AXF_ins2.e_av AXF_ins2.ACT a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range mt _ _ ins2_rng_mt eq_refl eq_refl), ?(mod64_of_range sc _ _ ins2_rng_sc eq_refl eq_refl), ?(mod64_of_range av _ _ ins2_rng_av eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply ins2_kwr8 | apply ins2_kwr9]; assumption).
  all: try (clear - ins2_rng_mt ins2_rng_sc ins2_rng_av ins2_ka1; lia).
  all: first [(clear - ins2_rng_mt ins2_rng_sc ins2_rng_av ins2_ka1 ins2_kd10; lia) | lia].
Qed.


Definition ins2_mem_pins2 (m : word -> option byte) (regs : bvmap 5 word) (mt sc av : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (m) (wa (mt + 24)) (word_to_le_bytes 4 (wa (ext_Z true 0 4 av + -1)))) (wa (mt + 0)) (word_to_le_bytes 8 (wa mt))) (wa (mt + 8)) (word_to_le_bytes 8 (wa mt))) (wa (8 * sc + 621800)) (word_to_le_bytes 8 (wa mt)).

#[using="Type"] Theorem ins2_pins2 : forall regs m rom mt sc av, ins2_pre regs m mt sc av ->
  scs_denot SEGS m (Ez regs (VALS_ins2 mt sc av)) (snd (fst AXF_ins2.RES_pins2)) ->
  exists R, msteps SEGS (mkst regs (wa 0x54828) m rom) (mkst R (wa 0x54908) (ins2_mem_pins2 m regs mt sc av) rom) /\
    getr R 9 = wa mt /\ getr R 10 = wa 0 /\ getr R 21 = wa ((8 * sc) + 621800) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom mt sc av P Hsc. destruct (ins2_setup regs m mt sc av P) as [HR HK].
  set (E := Ez regs (VALS_ins2 mt sc av)) in *. destruct P as [ins2_R9 ins2_R21 ins2_rng_mt ins2_rng_sc ins2_rng_av ins2_ka1 ins2_kw4 ins2_kw5 ins2_kw6 ins2_kw7 ins2_kwr8 ins2_kwr9 ins2_kd10].
  assert (Z32 : bv_unsigned (ev E 32) = mt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = av) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x54908] AXF_ins2.scr_pins2 0x54828 AXF_ins2.sr_ins2 AXF_ins2.kn_ins2 35 _ _ _ E m rom regs AXF_ins2.RES_pins2_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_ins2.RES_pins2 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (ins2_mem_pins2 m regs mt sc av) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold ins2_mem_pins2. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End INS2.
End AXF_ins2z.

Module AXF_mmb.
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

Definition e_res := EVar 32.
Definition sr_mmb := (sr_upd (sr_upd sr_id 10 (e_res)) 18 (ELit 18446744073709551615)).
Definition kn_mmb : list kentry :=
  [ KRange e_res 4096 (2^47) ].
Definition scr_mmb : scripts := SCR [false] [] [].
Definition ss_mmb := SS 0x54758 sr_mmb [] kn_mmb 33.
Definition RUN_mmb := sym_exec SEGS 10 true [0x5475c] scr_mmb ss_mmb [].

Definition scr_pmmb : scripts := SCR [false] [] [].
Definition RES_pmmb := Eval vm_compute in sym_exec SEGS 10 true [0x5475c] scr_pmmb ss_mmb [].
Lemma RES_pmmb_ok : sym_exec SEGS 10 true [0x5475c] scr_pmmb (SS 0x54758 sr_mmb [] kn_mmb 33) [] = RES_pmmb.
Proof. vm_compute. reflexivity. Qed.
End AXF_mmb.

Module AXF_mmbz.
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

Section MMB.
Context {fx : FPState}.

Definition VALS_mmb (res : Z) : list Z := [res].

Record mmb_pre (regs : bvmap 5 word) (m : word -> option byte) (res : Z) : Prop := {
  mmb_R10 : getr regs 10 = wa res ;
  mmb_R18 : getr regs 18 = wa 18446744073709551615 ;
  mmb_rng_res : 4096 <= res <= 2^47
}.


#[using="Type"] Lemma mmb_setup : forall regs m res, mmb_pre regs m res ->
  regs_ok (Ez regs (VALS_mmb res)) AXF_mmb.sr_mmb regs /\ know_ok SEGS (Ez regs (VALS_mmb res)) m AXF_mmb.kn_mmb.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m res P. destruct P as [mmb_R10 mmb_R18 mmb_rng_res].
  set (E := Ez regs (VALS_mmb res)).
  assert (Z32 : bv_unsigned (ev E 32) = res) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mmb.sr_mmb.
    apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|].
    - rewrite mmb_R10. reflexivity.
    - rewrite mmb_R18. reflexivity. }
  unfold know_ok, AXF_mmb.kn_mmb.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mmb.e_res a_base a_off].
  all: rewrite ?Z32.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range res _ _ mmb_rng_res eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - mmb_rng_res; lia).
  all: first [lia].
Qed.


Definition mmb_mem_pmmb (m : word -> option byte) (regs : bvmap 5 word) (res : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mmb_pmmb : forall regs m rom res, mmb_pre regs m res ->
  scs_denot SEGS m (Ez regs (VALS_mmb res)) (snd (fst AXF_mmb.RES_pmmb)) ->
  exists R, msteps SEGS (mkst regs (wa 0x54758) m rom) (mkst R (wa 0x5475c) (mmb_mem_pmmb m regs res) rom) /\
    getr R 10 = wa res /\ getr R 18 = wa 18446744073709551615 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom res P Hsc. destruct (mmb_setup regs m res P) as [HR HK].
  set (E := Ez regs (VALS_mmb res)) in *. destruct P as [mmb_R10 mmb_R18 mmb_rng_res].
  assert (Z32 : bv_unsigned (ev E 32) = res) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 10 [0x5475c] AXF_mmb.scr_pmmb 0x54758 AXF_mmb.sr_mmb AXF_mmb.kn_mmb 33 _ _ _ E m rom regs AXF_mmb.RES_pmmb_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mmb.RES_pmmb fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mmb_mem_pmmb m regs res) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mmb_mem_pmmb. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MMB.
End AXF_mmbz.

Module AXF_mmr.
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
Definition e_res := EVar 33.
Definition e_ad := EVar 34.
Definition e_s00 := EVar 35.
Definition e_s10 := EVar 36.
Definition e_s20 := EVar 37.
Definition e_s30 := EVar 38.
Definition e_s40 := EVar 39.
Definition e_s50 := EVar 40.
Definition sr_mmr := (sr_upd (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-64)))) 10 (e_res)) 16 (e_ad)).
Definition kn_mmr : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KRange e_res 4096 (2^47);
    KRange e_ad 0 (2^63-1);
    KWord (SA e_sp0 (-8)) 8 (ELit 345944);
    KWord (SA e_sp0 (-16)) 8 e_s00;
    KWord (SA e_sp0 (-24)) 8 e_s10;
    KWord (SA e_sp0 (-32)) 8 e_s20;
    KWord (SA e_sp0 (-40)) 8 e_s30;
    KWord (SA e_sp0 (-48)) 8 e_s40;
    KWord (SA e_sp0 (-56)) 8 e_s50;
    KRange e_s00 0 (2^64-1);
    KRange e_s10 0 (2^64-1);
    KRange e_s20 0 (2^64-1);
    KRange e_s30 0 (2^64-1);
    KRange e_s40 0 (2^64-1);
    KRange e_s50 0 (2^64-1) ].
Definition scr_mmr : scripts := SCR [] [] [].
Definition ss_mmr := SS 0x551a8 sr_mmr [] kn_mmr 41.
Definition RUN_mmr := sym_exec SEGS 100 true [0x54758] scr_mmr ss_mmr [].

Definition scr_pmr : scripts := SCR [] [] [].
Definition RES_pmr := Eval vm_compute in sym_exec SEGS 100 true [0x54758] scr_pmr ss_mmr [].
Lemma RES_pmr_ok : sym_exec SEGS 100 true [0x54758] scr_pmr (SS 0x551a8 sr_mmr [] kn_mmr 41) [] = RES_pmr.
Proof. vm_compute. reflexivity. Qed.
End AXF_mmr.

Module AXF_mmrz.
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

Section MMR.
Context {fx : FPState}.

Definition VALS_mmr (sp0 res ad s00 s10 s20 s30 s40 s50 : Z) : list Z := [sp0; res; ad; s00; s10; s20; s30; s40; s50].

Record mmr_pre (regs : bvmap 5 word) (m : word -> option byte) (sp0 res ad s00 s10 s20 s30 s40 s50 : Z) : Prop := {
  mmr_R2 : getr regs 2 = wa (sp0 + -64) ;
  mmr_R10 : getr regs 10 = wa res ;
  mmr_R16 : getr regs 16 = wa ad ;
  mmr_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  mmr_rng_res : 4096 <= res <= 2^47 ;
  mmr_rng_ad : 0 <= ad <= 2^63-1 ;
  mmr_rng_s00 : 0 <= s00 <= 2^64-1 ;
  mmr_rng_s10 : 0 <= s10 <= 2^64-1 ;
  mmr_rng_s20 : 0 <= s20 <= 2^64-1 ;
  mmr_rng_s30 : 0 <= s30 <= 2^64-1 ;
  mmr_rng_s40 : 0 <= s40 <= 2^64-1 ;
  mmr_rng_s50 : 0 <= s50 <= 2^64-1 ;
  mmr_ka1 : sp0 mod 16 = 0 ;
  mmr_kw4 : rdn SEGS m (wa (sp0 + -8)) 8 = Some (word_to_le_bytes 8 (wa 345944)) ;
  mmr_kw5 : rdn SEGS m (wa (sp0 + -16)) 8 = Some (word_to_le_bytes 8 (wa s00)) ;
  mmr_kw6 : rdn SEGS m (wa (sp0 + -24)) 8 = Some (word_to_le_bytes 8 (wa s10)) ;
  mmr_kw7 : rdn SEGS m (wa (sp0 + -32)) 8 = Some (word_to_le_bytes 8 (wa s20)) ;
  mmr_kw8 : rdn SEGS m (wa (sp0 + -40)) 8 = Some (word_to_le_bytes 8 (wa s30)) ;
  mmr_kw9 : rdn SEGS m (wa (sp0 + -48)) 8 = Some (word_to_le_bytes 8 (wa s40)) ;
  mmr_kw10 : rdn SEGS m (wa (sp0 + -56)) 8 = Some (word_to_le_bytes 8 (wa s50))
}.


#[using="Type"] Lemma mmr_setup : forall regs m sp0 res ad s00 s10 s20 s30 s40 s50, mmr_pre regs m sp0 res ad s00 s10 s20 s30 s40 s50 ->
  regs_ok (Ez regs (VALS_mmr sp0 res ad s00 s10 s20 s30 s40 s50)) AXF_mmr.sr_mmr regs /\ know_ok SEGS (Ez regs (VALS_mmr sp0 res ad s00 s10 s20 s30 s40 s50)) m AXF_mmr.kn_mmr.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sp0 res ad s00 s10 s20 s30 s40 s50 P. destruct P as [mmr_R2 mmr_R10 mmr_R16 mmr_rng_sp0 mmr_rng_res mmr_rng_ad mmr_rng_s00 mmr_rng_s10 mmr_rng_s20 mmr_rng_s30 mmr_rng_s40 mmr_rng_s50 mmr_ka1 mmr_kw4 mmr_kw5 mmr_kw6 mmr_kw7 mmr_kw8 mmr_kw9 mmr_kw10].
  set (E := Ez regs (VALS_mmr sp0 res ad s00 s10 s20 s30 s40 s50)).
  assert (Z32 : bv_unsigned (ev E 32) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = res) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = ad) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = s00) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = s10) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = s20) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = s30) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = s40) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = s50) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mmr.sr_mmr.
    apply (regs_ok_pin E _ regs 16); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|]|]|].
    - rewrite mmr_R2, zeval_sound. cbn [zeval edenot AXF_mmr.e_sp0 AXF_mmr.e_res AXF_mmr.e_ad AXF_mmr.e_s00 AXF_mmr.e_s10 AXF_mmr.e_s20 AXF_mmr.e_s30 AXF_mmr.e_s40 AXF_mmr.e_s50]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite mmr_R10. reflexivity.
    - rewrite mmr_R16. reflexivity. }
  unfold know_ok, AXF_mmr.kn_mmr.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_mmr.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mmr.e_sp0 AXF_mmr.e_res AXF_mmr.e_ad AXF_mmr.e_s00 AXF_mmr.e_s10 AXF_mmr.e_s20 AXF_mmr.e_s30 AXF_mmr.e_s40 AXF_mmr.e_s50 a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sp0 _ _ mmr_rng_sp0 eq_refl eq_refl), ?(mod64_of_range res _ _ mmr_rng_res eq_refl eq_refl), ?(mod64_of_range ad _ _ mmr_rng_ad eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - mmr_rng_sp0 mmr_rng_res mmr_rng_ad mmr_rng_s00 mmr_rng_s10 mmr_rng_s20 mmr_rng_s30 mmr_rng_s40 mmr_rng_s50 mmr_ka1; lia).
  all: first [lia].
Qed.


Definition mmr_mem_pmr (m : word -> option byte) (regs : bvmap 5 word) (sp0 res ad s00 s10 s20 s30 s40 s50 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mmr_pmr : forall regs m rom sp0 res ad s00 s10 s20 s30 s40 s50, mmr_pre regs m sp0 res ad s00 s10 s20 s30 s40 s50 ->
  scs_denot SEGS m (Ez regs (VALS_mmr sp0 res ad s00 s10 s20 s30 s40 s50)) (snd (fst AXF_mmr.RES_pmr)) ->
  exists R, msteps SEGS (mkst regs (wa 0x551a8) m rom) (mkst R (wa 0x54758) (mmr_mem_pmr m regs sp0 res ad s00 s10 s20 s30 s40 s50) rom) /\
    getr R 1 = wa 345944 /\ getr R 2 = wa sp0 /\ getr R 8 = wa s00 /\ getr R 9 = wa s10 /\ getr R 10 = wa res /\ getr R 11 = wa 18446744073709547521 /\ getr R 16 = wa ad /\ getr R 18 = wa s20 /\ getr R 19 = wa s30 /\ getr R 20 = wa s40 /\ getr R 21 = wa s50 /\ (forall k, In k [3; 4; 5; 6; 7; 12; 13; 14; 15; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sp0 res ad s00 s10 s20 s30 s40 s50 P Hsc. destruct (mmr_setup regs m sp0 res ad s00 s10 s20 s30 s40 s50 P) as [HR HK].
  set (E := Ez regs (VALS_mmr sp0 res ad s00 s10 s20 s30 s40 s50)) in *. destruct P as [mmr_R2 mmr_R10 mmr_R16 mmr_rng_sp0 mmr_rng_res mmr_rng_ad mmr_rng_s00 mmr_rng_s10 mmr_rng_s20 mmr_rng_s30 mmr_rng_s40 mmr_rng_s50 mmr_ka1 mmr_kw4 mmr_kw5 mmr_kw6 mmr_kw7 mmr_kw8 mmr_kw9 mmr_kw10].
  assert (Z32 : bv_unsigned (ev E 32) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = res) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = ad) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = s00) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = s10) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = s20) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = s30) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = s40) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = s50) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x54758] AXF_mmr.scr_pmr 0x551a8 AXF_mmr.sr_mmr AXF_mmr.kn_mmr 41 _ _ _ E m rom regs AXF_mmr.RES_pmr_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mmr.RES_pmr fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mmr_mem_pmr m regs sp0 res ad s00 s10 s20 s30 s40 s50) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mmr_mem_pmr. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MMR.
End AXF_mmrz.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section TAE.
Context {fx : FPState}.

Definition VALS_tae (can ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 sp0 : Z) : list Z := [can; ra0; s00; s10; s20; s30; s40; s50; s60; s70; s80; s90; sp0].

Record tae_pre (regs : bvmap 5 word) (m : word -> option byte) (can ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 sp0 : Z) : Prop := {
  tae_R2 : getr regs 2 = wa (sp0 + -144) ;
  tae_R20 : getr regs 20 = wa 621568 ;
  tae_rng_can : 0 <= can <= 2^64-1 ;
  tae_rng_ra0 : 0 <= ra0 <= 2^64-1 ;
  tae_rng_s00 : 0 <= s00 <= 2^64-1 ;
  tae_rng_s10 : 0 <= s10 <= 2^64-1 ;
  tae_rng_s20 : 0 <= s20 <= 2^64-1 ;
  tae_rng_s30 : 0 <= s30 <= 2^64-1 ;
  tae_rng_s40 : 0 <= s40 <= 2^64-1 ;
  tae_rng_s50 : 0 <= s50 <= 2^64-1 ;
  tae_rng_s60 : 0 <= s60 <= 2^64-1 ;
  tae_rng_s70 : 0 <= s70 <= 2^64-1 ;
  tae_rng_s80 : 0 <= s80 <= 2^64-1 ;
  tae_rng_s90 : 0 <= s90 <= 2^64-1 ;
  tae_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  tae_ka1 : sp0 mod 16 = 0 ;
  tae_kw2 : rdn SEGS m (wa (0 + 621568)) 8 = Some (word_to_le_bytes 8 (wa can)) ;
  tae_kw3 : rdn SEGS m (wa (sp0 + -96)) 8 = Some (word_to_le_bytes 8 (wa can)) ;
  tae_kw4 : rdn SEGS m (wa (sp0 + -8)) 8 = Some (word_to_le_bytes 8 (wa ra0)) ;
  tae_kw5 : rdn SEGS m (wa (sp0 + -16)) 8 = Some (word_to_le_bytes 8 (wa s00)) ;
  tae_kw6 : rdn SEGS m (wa (sp0 + -24)) 8 = Some (word_to_le_bytes 8 (wa s10)) ;
  tae_kw7 : rdn SEGS m (wa (sp0 + -32)) 8 = Some (word_to_le_bytes 8 (wa s20)) ;
  tae_kw8 : rdn SEGS m (wa (sp0 + -40)) 8 = Some (word_to_le_bytes 8 (wa s30)) ;
  tae_kw9 : rdn SEGS m (wa (sp0 + -48)) 8 = Some (word_to_le_bytes 8 (wa s40)) ;
  tae_kw10 : rdn SEGS m (wa (sp0 + -56)) 8 = Some (word_to_le_bytes 8 (wa s50)) ;
  tae_kw11 : rdn SEGS m (wa (sp0 + -64)) 8 = Some (word_to_le_bytes 8 (wa s60)) ;
  tae_kw12 : rdn SEGS m (wa (sp0 + -72)) 8 = Some (word_to_le_bytes 8 (wa s70)) ;
  tae_kw13 : rdn SEGS m (wa (sp0 + -80)) 8 = Some (word_to_le_bytes 8 (wa s80)) ;
  tae_kw14 : rdn SEGS m (wa (sp0 + -88)) 8 = Some (word_to_le_bytes 8 (wa s90))
}.


#[using="Type"] Lemma tae_setup : forall regs m can ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 sp0, tae_pre regs m can ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 sp0 ->
  regs_ok (Ez regs (VALS_tae can ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 sp0)) AXF_tae.sr_tae regs /\ know_ok SEGS (Ez regs (VALS_tae can ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 sp0)) m AXF_tae.kn_tae.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m can ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 sp0 P. destruct P as [tae_R2 tae_R20 tae_rng_can tae_rng_ra0 tae_rng_s00 tae_rng_s10 tae_rng_s20 tae_rng_s30 tae_rng_s40 tae_rng_s50 tae_rng_s60 tae_rng_s70 tae_rng_s80 tae_rng_s90 tae_rng_sp0 tae_ka1 tae_kw2 tae_kw3 tae_kw4 tae_kw5 tae_kw6 tae_kw7 tae_kw8 tae_kw9 tae_kw10 tae_kw11 tae_kw12 tae_kw13 tae_kw14].
  set (E := Ez regs (VALS_tae can ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 sp0)).
  assert (Z32 : bv_unsigned (ev E 32) = can) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ra0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = s00) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = s10) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = s20) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = s30) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = s40) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = s50) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = s60) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = s70) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = s80) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = s90) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z44 : bv_unsigned (ev E 44) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_tae.sr_tae.
    apply (regs_ok_pin E _ regs 20); [apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|]|].
    - rewrite tae_R2, zeval_sound. cbn [zeval edenot AXF_tae.e_can AXF_tae.e_ra0 AXF_tae.e_s00 AXF_tae.e_s10 AXF_tae.e_s20 AXF_tae.e_s30 AXF_tae.e_s40 AXF_tae.e_s50 AXF_tae.e_s60 AXF_tae.e_s70 AXF_tae.e_s80 AXF_tae.e_s90 AXF_tae.e_sp0]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42, ?Z43, ?Z44. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite tae_R20. reflexivity. }
  unfold know_ok, AXF_tae.kn_tae.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_tae.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_tae.e_can AXF_tae.e_ra0 AXF_tae.e_s00 AXF_tae.e_s10 AXF_tae.e_s20 AXF_tae.e_s30 AXF_tae.e_s40 AXF_tae.e_s50 AXF_tae.e_s60 AXF_tae.e_s70 AXF_tae.e_s80 AXF_tae.e_s90 AXF_tae.e_sp0 a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42, ?Z43, ?Z44.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sp0 _ _ tae_rng_sp0 eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - tae_rng_can tae_rng_ra0 tae_rng_s00 tae_rng_s10 tae_rng_s20 tae_rng_s30 tae_rng_s40 tae_rng_s50 tae_rng_s60 tae_rng_s70 tae_rng_s80 tae_rng_s90 tae_rng_sp0 tae_ka1; lia).
  all: first [lia].
Qed.


Definition tae_mem_ptae (m : word -> option byte) (regs : bvmap 5 word) (can ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 sp0 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem tae_ptae : forall regs m rom can ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 sp0, tae_pre regs m can ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 sp0 ->
  scs_denot SEGS m (Ez regs (VALS_tae can ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 sp0)) (snd (fst AXF_tae.RES_ptae)) ->
  exists R, msteps SEGS (mkst regs (wa 0x54908) m rom) (mkst R (wa 0x54944) (tae_mem_ptae m regs can ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 sp0) rom) /\
    getr R 1 = wa ra0 /\ getr R 2 = wa sp0 /\ getr R 8 = wa s00 /\ getr R 9 = wa s10 /\ getr R 11 = wa can /\ getr R 12 = wa can /\ getr R 18 = wa s20 /\ getr R 19 = wa s30 /\ getr R 20 = wa s40 /\ getr R 21 = wa s50 /\ getr R 22 = wa s60 /\ getr R 23 = wa s70 /\ getr R 24 = wa s80 /\ getr R 25 = wa s90 /\ (forall k, In k [3; 4; 5; 6; 7; 10; 13; 14; 15; 16; 17; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom can ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 sp0 P Hsc. destruct (tae_setup regs m can ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 sp0 P) as [HR HK].
  set (E := Ez regs (VALS_tae can ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 sp0)) in *. destruct P as [tae_R2 tae_R20 tae_rng_can tae_rng_ra0 tae_rng_s00 tae_rng_s10 tae_rng_s20 tae_rng_s30 tae_rng_s40 tae_rng_s50 tae_rng_s60 tae_rng_s70 tae_rng_s80 tae_rng_s90 tae_rng_sp0 tae_ka1 tae_kw2 tae_kw3 tae_kw4 tae_kw5 tae_kw6 tae_kw7 tae_kw8 tae_kw9 tae_kw10 tae_kw11 tae_kw12 tae_kw13 tae_kw14].
  assert (Z32 : bv_unsigned (ev E 32) = can) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ra0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = s00) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = s10) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = s20) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = s30) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = s40) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = s50) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = s60) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = s70) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = s80) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = s90) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z44 : bv_unsigned (ev E 44) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x54944] AXF_tae.scr_ptae 0x54908 AXF_tae.sr_tae AXF_tae.kn_tae 45 _ _ _ E m rom regs AXF_tae.RES_ptae_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_tae.RES_ptae fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (tae_mem_ptae m regs can ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 sp0) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold tae_mem_ptae. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End TAE.
