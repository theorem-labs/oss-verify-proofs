(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng AxBits MngZ MngHeap AxTry.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngHeap.

Module AXF_agcs.
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

Definition e_sc := EVar 32.
Definition e_mt := EVar 33.
Definition e_usage := EVar 34.
Definition e_units := EVar 35.
Definition e_r0 := EVar 36.
Definition e_r1 := EVar 37.
Definition e_r2 := EVar 38.
Definition sr_agcs := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (e_sc)) 10 (e_mt)) 19 (EMd M_MUL (ELit 2) e_sc)) 23 (EAlu ALU_ADD (EMd M_MUL (ELit 8) e_sc) (ELit 614096))) 24 (e_units)) 25 (ELit 98984)).
Definition kn_agcs : list kentry :=
  [ KRange e_sc 0 8;
    KRange e_mt 1 (2^63-1);
    KRange e_usage 0 (2^60);
    KRange e_units 1 8191;
    KRange e_r0 4 31;
    KRange e_r1 4 31;
    KRange e_r2 4 31;
    KWord (SA (EMd M_MUL (ELit 8) e_sc) 614568) 8 e_usage;
    KWord (SA (ELit 0) 614032) 8 (ELit 4096);
    KWord (SA (EMd M_MUL (ELit 3) e_sc) 99080) 1 e_r0;
    KWord (SA (EMd M_MUL (ELit 3) e_sc) 99081) 1 e_r1;
    KWord (SA (EMd M_MUL (ELit 3) e_sc) 99082) 1 e_r2 ].
Definition scr_agcs : scripts := SCR [true; false] [] [].
Definition ss_agcs := SS 0x524e8 sr_agcs [] kn_agcs 39.
Definition RUN_agcs := sym_exec SEGS 100 true [0x525bc; 0x52600] scr_agcs ss_agcs [].

Definition scr_pr0m : scripts := SCR [true; false] [] [].
Definition RES_pr0m := Eval vm_compute in sym_exec SEGS 100 true [0x525bc; 0x52600] scr_pr0m ss_agcs [].
Lemma RES_pr0m_ok : sym_exec SEGS 100 true [0x525bc; 0x52600] scr_pr0m (SS 0x524e8 sr_agcs [] kn_agcs 39) [] = RES_pr0m.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pr0n : scripts := SCR [true; true] [] [].
Definition RES_pr0n := Eval vm_compute in sym_exec SEGS 100 true [0x525bc; 0x52600] scr_pr0n ss_agcs [].
Lemma RES_pr0n_ok : sym_exec SEGS 100 true [0x525bc; 0x52600] scr_pr0n (SS 0x524e8 sr_agcs [] kn_agcs 39) [] = RES_pr0n.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pr1m : scripts := SCR [false; true; false] [] [].
Definition RES_pr1m := Eval vm_compute in sym_exec SEGS 100 true [0x525bc; 0x52600] scr_pr1m ss_agcs [].
Lemma RES_pr1m_ok : sym_exec SEGS 100 true [0x525bc; 0x52600] scr_pr1m (SS 0x524e8 sr_agcs [] kn_agcs 39) [] = RES_pr1m.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pr1n : scripts := SCR [false; true; true] [] [].
Definition RES_pr1n := Eval vm_compute in sym_exec SEGS 100 true [0x525bc; 0x52600] scr_pr1n ss_agcs [].
Lemma RES_pr1n_ok : sym_exec SEGS 100 true [0x525bc; 0x52600] scr_pr1n (SS 0x524e8 sr_agcs [] kn_agcs 39) [] = RES_pr1n.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pr2m : scripts := SCR [false; false; false] [] [].
Definition RES_pr2m := Eval vm_compute in sym_exec SEGS 100 true [0x525bc; 0x52600] scr_pr2m ss_agcs [].
Lemma RES_pr2m_ok : sym_exec SEGS 100 true [0x525bc; 0x52600] scr_pr2m (SS 0x524e8 sr_agcs [] kn_agcs 39) [] = RES_pr2m.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pr2n : scripts := SCR [false; false; true] [] [].
Definition RES_pr2n := Eval vm_compute in sym_exec SEGS 100 true [0x525bc; 0x52600] scr_pr2n ss_agcs [].
Lemma RES_pr2n_ok : sym_exec SEGS 100 true [0x525bc; 0x52600] scr_pr2n (SS 0x524e8 sr_agcs [] kn_agcs 39) [] = RES_pr2n.
Proof. vm_compute. reflexivity. Qed.
End AXF_agcs.

Module AXF_agcsz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section AGCS.
Context {fx : FPState}.

Definition VALS_agcs (sc mt usage units r0 r1 r2 : Z) : list Z := [sc; mt; usage; units; r0; r1; r2].

Record agcs_pre (regs : bvmap 5 word) (m : word -> option byte) (sc mt usage units r0 r1 r2 : Z) : Prop := {
  agcs_R8 : getr regs 8 = wa sc ;
  agcs_R10 : getr regs 10 = wa mt ;
  agcs_R19 : getr regs 19 = wa (2 * sc) ;
  agcs_R23 : getr regs 23 = wa ((8 * sc) + 614096) ;
  agcs_R24 : getr regs 24 = wa units ;
  agcs_R25 : getr regs 25 = wa 98984 ;
  agcs_rng_sc : 0 <= sc <= 8 ;
  agcs_rng_mt : 1 <= mt <= 2^63-1 ;
  agcs_rng_usage : 0 <= usage <= 2^60 ;
  agcs_rng_units : 1 <= units <= 8191 ;
  agcs_rng_r0 : 4 <= r0 <= 31 ;
  agcs_rng_r1 : 4 <= r1 <= 31 ;
  agcs_rng_r2 : 4 <= r2 <= 31 ;
  agcs_kw7 : rdn SEGS m (wa (8 * sc + 614568)) 8 = Some (word_to_le_bytes 8 (wa usage)) ;
  agcs_kw8 : rdn SEGS m (wa (0 + 614032)) 8 = Some (word_to_le_bytes 8 (wa 4096)) ;
  agcs_kw9 : rdn SEGS m (wa (3 * sc + 99080)) 1 = Some (word_to_le_bytes 1 (wa r0)) ;
  agcs_kw10 : rdn SEGS m (wa (3 * sc + 99081)) 1 = Some (word_to_le_bytes 1 (wa r1)) ;
  agcs_kw11 : rdn SEGS m (wa (3 * sc + 99082)) 1 = Some (word_to_le_bytes 1 (wa r2))
}.


#[using="Type"] Lemma agcs_setup : forall regs m sc mt usage units r0 r1 r2, agcs_pre regs m sc mt usage units r0 r1 r2 ->
  regs_ok (Ez regs (VALS_agcs sc mt usage units r0 r1 r2)) AXF_agcs.sr_agcs regs /\ know_ok SEGS (Ez regs (VALS_agcs sc mt usage units r0 r1 r2)) m AXF_agcs.kn_agcs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sc mt usage units r0 r1 r2 P. destruct P as [agcs_R8 agcs_R10 agcs_R19 agcs_R23 agcs_R24 agcs_R25 agcs_rng_sc agcs_rng_mt agcs_rng_usage agcs_rng_units agcs_rng_r0 agcs_rng_r1 agcs_rng_r2 agcs_kw7 agcs_kw8 agcs_kw9 agcs_kw10 agcs_kw11].
  set (E := Ez regs (VALS_agcs sc mt usage units r0 r1 r2)).
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = mt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = usage) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = units) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = r0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = r1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = r2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_agcs.sr_agcs.
    apply (regs_ok_pin E _ regs 25); [apply (regs_ok_pin E _ regs 24); [apply (regs_ok_pin E _ regs 23); [apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|]|]|]|].
    - rewrite agcs_R8. reflexivity.
    - rewrite agcs_R10. reflexivity.
    - rewrite agcs_R19, zeval_sound. cbn [zeval edenot AXF_agcs.e_sc AXF_agcs.e_mt AXF_agcs.e_usage AXF_agcs.e_units AXF_agcs.e_r0 AXF_agcs.e_r1 AXF_agcs.e_r2]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite agcs_R23, zeval_sound. cbn [zeval edenot AXF_agcs.e_sc AXF_agcs.e_mt AXF_agcs.e_usage AXF_agcs.e_units AXF_agcs.e_r0 AXF_agcs.e_r1 AXF_agcs.e_r2]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite agcs_R24. reflexivity.
    - rewrite agcs_R25. reflexivity. }
  unfold know_ok, AXF_agcs.kn_agcs.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_agcs.e_sc AXF_agcs.e_mt AXF_agcs.e_usage AXF_agcs.e_units AXF_agcs.e_r0 AXF_agcs.e_r1 AXF_agcs.e_r2 a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sc _ _ agcs_rng_sc eq_refl eq_refl), ?(mod64_of_range mt _ _ agcs_rng_mt eq_refl eq_refl), ?(mod64_of_range usage _ _ agcs_rng_usage eq_refl eq_refl), ?(mod64_of_range units _ _ agcs_rng_units eq_refl eq_refl), ?(mod64_of_range r0 _ _ agcs_rng_r0 eq_refl eq_refl), ?(mod64_of_range r1 _ _ agcs_rng_r1 eq_refl eq_refl), ?(mod64_of_range r2 _ _ agcs_rng_r2 eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - agcs_rng_sc agcs_rng_mt agcs_rng_usage agcs_rng_units agcs_rng_r0 agcs_rng_r1 agcs_rng_r2; lia).
  all: first [lia].
Qed.


Definition agcs_mem_pr0m (m : word -> option byte) (regs : bvmap 5 word) (sc mt usage units r0 r1 r2 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem agcs_pr0m : forall regs m rom sc mt usage units r0 r1 r2, agcs_pre regs m sc mt usage units r0 r1 r2 ->
  scs_denot SEGS m (Ez regs (VALS_agcs sc mt usage units r0 r1 r2)) (snd (fst AXF_agcs.RES_pr0m)) ->
  exists R, msteps SEGS (mkst regs (wa 0x524e8) m rom) (mkst R (wa 0x525bc) (agcs_mem_pr0m m regs sc mt usage units r0 r1 r2) rom) /\
    getr R 8 = wa sc /\ getr R 9 = wa mt /\ getr R 10 = wa usage /\ getr R 11 = wa 4096 /\ getr R 12 = wa ((16 * units) + 16) /\ getr R 13 = wa 2048 /\ getr R 14 = wa ((16 * units) * r0) /\ getr R 15 = wa (((16 * units) * r0) + 16) /\ getr R 19 = wa r0 /\ getr R 23 = wa ((8 * sc) + 614096) /\ getr R 24 = wa (16 * units) /\ getr R 25 = wa 98984 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 16; 17; 18; 20; 21; 22; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc mt usage units r0 r1 r2 P Hsc. destruct (agcs_setup regs m sc mt usage units r0 r1 r2 P) as [HR HK].
  set (E := Ez regs (VALS_agcs sc mt usage units r0 r1 r2)) in *. destruct P as [agcs_R8 agcs_R10 agcs_R19 agcs_R23 agcs_R24 agcs_R25 agcs_rng_sc agcs_rng_mt agcs_rng_usage agcs_rng_units agcs_rng_r0 agcs_rng_r1 agcs_rng_r2 agcs_kw7 agcs_kw8 agcs_kw9 agcs_kw10 agcs_kw11].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = mt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = usage) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = units) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = r0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = r1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = r2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x525bc; 0x52600] AXF_agcs.scr_pr0m 0x524e8 AXF_agcs.sr_agcs AXF_agcs.kn_agcs 39 _ _ _ E m rom regs AXF_agcs.RES_pr0m_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_agcs.RES_pr0m fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (agcs_mem_pr0m m regs sc mt usage units r0 r1 r2) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold agcs_mem_pr0m. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition agcs_mem_pr0n (m : word -> option byte) (regs : bvmap 5 word) (sc mt usage units r0 r1 r2 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem agcs_pr0n : forall regs m rom sc mt usage units r0 r1 r2, agcs_pre regs m sc mt usage units r0 r1 r2 ->
  scs_denot SEGS m (Ez regs (VALS_agcs sc mt usage units r0 r1 r2)) (snd (fst AXF_agcs.RES_pr0n)) ->
  exists R, msteps SEGS (mkst regs (wa 0x524e8) m rom) (mkst R (wa 0x52600) (agcs_mem_pr0n m regs sc mt usage units r0 r1 r2) rom) /\
    getr R 8 = wa sc /\ getr R 9 = wa mt /\ getr R 10 = wa usage /\ getr R 11 = wa 4096 /\ getr R 12 = wa ((16 * units) + 16) /\ getr R 13 = wa 2048 /\ getr R 14 = wa ((16 * units) * r0) /\ getr R 15 = wa (((16 * units) * r0) + 16) /\ getr R 19 = wa r0 /\ getr R 23 = wa ((8 * sc) + 614096) /\ getr R 24 = wa (16 * units) /\ getr R 25 = wa 98984 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 16; 17; 18; 20; 21; 22; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc mt usage units r0 r1 r2 P Hsc. destruct (agcs_setup regs m sc mt usage units r0 r1 r2 P) as [HR HK].
  set (E := Ez regs (VALS_agcs sc mt usage units r0 r1 r2)) in *. destruct P as [agcs_R8 agcs_R10 agcs_R19 agcs_R23 agcs_R24 agcs_R25 agcs_rng_sc agcs_rng_mt agcs_rng_usage agcs_rng_units agcs_rng_r0 agcs_rng_r1 agcs_rng_r2 agcs_kw7 agcs_kw8 agcs_kw9 agcs_kw10 agcs_kw11].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = mt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = usage) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = units) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = r0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = r1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = r2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x525bc; 0x52600] AXF_agcs.scr_pr0n 0x524e8 AXF_agcs.sr_agcs AXF_agcs.kn_agcs 39 _ _ _ E m rom regs AXF_agcs.RES_pr0n_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_agcs.RES_pr0n fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (agcs_mem_pr0n m regs sc mt usage units r0 r1 r2) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold agcs_mem_pr0n. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition agcs_mem_pr1m (m : word -> option byte) (regs : bvmap 5 word) (sc mt usage units r0 r1 r2 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem agcs_pr1m : forall regs m rom sc mt usage units r0 r1 r2, agcs_pre regs m sc mt usage units r0 r1 r2 ->
  scs_denot SEGS m (Ez regs (VALS_agcs sc mt usage units r0 r1 r2)) (snd (fst AXF_agcs.RES_pr1m)) ->
  exists R, msteps SEGS (mkst regs (wa 0x524e8) m rom) (mkst R (wa 0x525bc) (agcs_mem_pr1m m regs sc mt usage units r0 r1 r2) rom) /\
    getr R 8 = wa sc /\ getr R 9 = wa mt /\ getr R 10 = wa usage /\ getr R 11 = wa 4096 /\ getr R 12 = wa ((16 * units) + 16) /\ getr R 13 = wa 2048 /\ getr R 14 = wa ((16 * units) * r1) /\ getr R 15 = wa (((16 * units) * r1) + 16) /\ getr R 19 = wa r1 /\ getr R 23 = wa ((8 * sc) + 614096) /\ getr R 24 = wa (16 * units) /\ getr R 25 = wa 98984 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 16; 17; 18; 20; 21; 22; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc mt usage units r0 r1 r2 P Hsc. destruct (agcs_setup regs m sc mt usage units r0 r1 r2 P) as [HR HK].
  set (E := Ez regs (VALS_agcs sc mt usage units r0 r1 r2)) in *. destruct P as [agcs_R8 agcs_R10 agcs_R19 agcs_R23 agcs_R24 agcs_R25 agcs_rng_sc agcs_rng_mt agcs_rng_usage agcs_rng_units agcs_rng_r0 agcs_rng_r1 agcs_rng_r2 agcs_kw7 agcs_kw8 agcs_kw9 agcs_kw10 agcs_kw11].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = mt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = usage) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = units) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = r0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = r1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = r2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x525bc; 0x52600] AXF_agcs.scr_pr1m 0x524e8 AXF_agcs.sr_agcs AXF_agcs.kn_agcs 39 _ _ _ E m rom regs AXF_agcs.RES_pr1m_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_agcs.RES_pr1m fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (agcs_mem_pr1m m regs sc mt usage units r0 r1 r2) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold agcs_mem_pr1m. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition agcs_mem_pr1n (m : word -> option byte) (regs : bvmap 5 word) (sc mt usage units r0 r1 r2 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem agcs_pr1n : forall regs m rom sc mt usage units r0 r1 r2, agcs_pre regs m sc mt usage units r0 r1 r2 ->
  scs_denot SEGS m (Ez regs (VALS_agcs sc mt usage units r0 r1 r2)) (snd (fst AXF_agcs.RES_pr1n)) ->
  exists R, msteps SEGS (mkst regs (wa 0x524e8) m rom) (mkst R (wa 0x52600) (agcs_mem_pr1n m regs sc mt usage units r0 r1 r2) rom) /\
    getr R 8 = wa sc /\ getr R 9 = wa mt /\ getr R 10 = wa usage /\ getr R 11 = wa 4096 /\ getr R 12 = wa ((16 * units) + 16) /\ getr R 13 = wa 2048 /\ getr R 14 = wa ((16 * units) * r1) /\ getr R 15 = wa (((16 * units) * r1) + 16) /\ getr R 19 = wa r1 /\ getr R 23 = wa ((8 * sc) + 614096) /\ getr R 24 = wa (16 * units) /\ getr R 25 = wa 98984 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 16; 17; 18; 20; 21; 22; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc mt usage units r0 r1 r2 P Hsc. destruct (agcs_setup regs m sc mt usage units r0 r1 r2 P) as [HR HK].
  set (E := Ez regs (VALS_agcs sc mt usage units r0 r1 r2)) in *. destruct P as [agcs_R8 agcs_R10 agcs_R19 agcs_R23 agcs_R24 agcs_R25 agcs_rng_sc agcs_rng_mt agcs_rng_usage agcs_rng_units agcs_rng_r0 agcs_rng_r1 agcs_rng_r2 agcs_kw7 agcs_kw8 agcs_kw9 agcs_kw10 agcs_kw11].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = mt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = usage) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = units) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = r0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = r1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = r2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x525bc; 0x52600] AXF_agcs.scr_pr1n 0x524e8 AXF_agcs.sr_agcs AXF_agcs.kn_agcs 39 _ _ _ E m rom regs AXF_agcs.RES_pr1n_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_agcs.RES_pr1n fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (agcs_mem_pr1n m regs sc mt usage units r0 r1 r2) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold agcs_mem_pr1n. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition agcs_mem_pr2m (m : word -> option byte) (regs : bvmap 5 word) (sc mt usage units r0 r1 r2 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem agcs_pr2m : forall regs m rom sc mt usage units r0 r1 r2, agcs_pre regs m sc mt usage units r0 r1 r2 ->
  scs_denot SEGS m (Ez regs (VALS_agcs sc mt usage units r0 r1 r2)) (snd (fst AXF_agcs.RES_pr2m)) ->
  exists R, msteps SEGS (mkst regs (wa 0x524e8) m rom) (mkst R (wa 0x525bc) (agcs_mem_pr2m m regs sc mt usage units r0 r1 r2) rom) /\
    getr R 8 = wa sc /\ getr R 9 = wa mt /\ getr R 10 = wa usage /\ getr R 11 = wa 4096 /\ getr R 12 = wa ((16 * units) + 16) /\ getr R 13 = wa 2048 /\ getr R 14 = wa ((16 * units) * r2) /\ getr R 15 = wa (((16 * units) * r2) + 16) /\ getr R 19 = wa r2 /\ getr R 23 = wa ((8 * sc) + 614096) /\ getr R 24 = wa (16 * units) /\ getr R 25 = wa 98984 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 16; 17; 18; 20; 21; 22; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc mt usage units r0 r1 r2 P Hsc. destruct (agcs_setup regs m sc mt usage units r0 r1 r2 P) as [HR HK].
  set (E := Ez regs (VALS_agcs sc mt usage units r0 r1 r2)) in *. destruct P as [agcs_R8 agcs_R10 agcs_R19 agcs_R23 agcs_R24 agcs_R25 agcs_rng_sc agcs_rng_mt agcs_rng_usage agcs_rng_units agcs_rng_r0 agcs_rng_r1 agcs_rng_r2 agcs_kw7 agcs_kw8 agcs_kw9 agcs_kw10 agcs_kw11].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = mt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = usage) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = units) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = r0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = r1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = r2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x525bc; 0x52600] AXF_agcs.scr_pr2m 0x524e8 AXF_agcs.sr_agcs AXF_agcs.kn_agcs 39 _ _ _ E m rom regs AXF_agcs.RES_pr2m_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_agcs.RES_pr2m fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (agcs_mem_pr2m m regs sc mt usage units r0 r1 r2) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold agcs_mem_pr2m. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition agcs_mem_pr2n (m : word -> option byte) (regs : bvmap 5 word) (sc mt usage units r0 r1 r2 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem agcs_pr2n : forall regs m rom sc mt usage units r0 r1 r2, agcs_pre regs m sc mt usage units r0 r1 r2 ->
  scs_denot SEGS m (Ez regs (VALS_agcs sc mt usage units r0 r1 r2)) (snd (fst AXF_agcs.RES_pr2n)) ->
  exists R, msteps SEGS (mkst regs (wa 0x524e8) m rom) (mkst R (wa 0x52600) (agcs_mem_pr2n m regs sc mt usage units r0 r1 r2) rom) /\
    getr R 8 = wa sc /\ getr R 9 = wa mt /\ getr R 10 = wa usage /\ getr R 11 = wa 4096 /\ getr R 12 = wa ((16 * units) + 16) /\ getr R 13 = wa 2048 /\ getr R 14 = wa ((16 * units) * r2) /\ getr R 15 = wa (((16 * units) * r2) + 16) /\ getr R 19 = wa r2 /\ getr R 23 = wa ((8 * sc) + 614096) /\ getr R 24 = wa (16 * units) /\ getr R 25 = wa 98984 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 16; 17; 18; 20; 21; 22; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc mt usage units r0 r1 r2 P Hsc. destruct (agcs_setup regs m sc mt usage units r0 r1 r2 P) as [HR HK].
  set (E := Ez regs (VALS_agcs sc mt usage units r0 r1 r2)) in *. destruct P as [agcs_R8 agcs_R10 agcs_R19 agcs_R23 agcs_R24 agcs_R25 agcs_rng_sc agcs_rng_mt agcs_rng_usage agcs_rng_units agcs_rng_r0 agcs_rng_r1 agcs_rng_r2 agcs_kw7 agcs_kw8 agcs_kw9 agcs_kw10 agcs_kw11].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = mt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = usage) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = units) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = r0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = r1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = r2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x525bc; 0x52600] AXF_agcs.scr_pr2n 0x524e8 AXF_agcs.sr_agcs AXF_agcs.kn_agcs 39 _ _ _ E m rom regs AXF_agcs.RES_pr2n_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_agcs.RES_pr2n fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (agcs_mem_pr2n m regs sc mt usage units r0 r1 r2) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold agcs_mem_pr2n. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End AGCS.
End AXF_agcsz.


Module AXF_agcm.
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

Definition e_sc := EVar 32.
Definition e_mt := EVar 33.
Definition e_usage := EVar 34.
Definition e_units := EVar 35.
Definition e_c0 := EVar 36.
Definition sr_agcm := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (e_sc)) 10 (e_mt)) 19 (EMd M_MUL (ELit 2) e_sc)) 23 (EAlu ALU_ADD (EMd M_MUL (ELit 8) e_sc) (ELit 614096))) 24 (e_units)) 25 (ELit 98984)).
Definition kn_agcm : list kentry :=
  [ KRange e_sc 9 47;
    KRange e_mt 1 (2^63-1);
    KRange e_usage 0 (2^60);
    KRange e_units 1 8191;
    KRange e_c0 4 32;
    KAlign e_c0 2;
    KWord (SA (EMd M_MUL (ELit 8) e_sc) 614568) 8 e_usage;
    KWord (SA (ELit 0) 614032) 8 (ELit 4096);
    KWord (SA (EAlu ALU_AND e_sc (ELit 3)) 99107) 1 e_c0 ].
Definition scr_agcm : scripts := SCR [] [] [].
Definition ss_agcm := SS 0x524e8 sr_agcm [] kn_agcm 37.
Definition RUN_agcm := sym_exec SEGS 100 true [0x52558] scr_agcm ss_agcm [].

Definition scr_pagcm : scripts := SCR [] [] [].
Definition RES_pagcm := Eval vm_compute in sym_exec SEGS 100 true [0x52558] scr_pagcm ss_agcm [].
Lemma RES_pagcm_ok : sym_exec SEGS 100 true [0x52558] scr_pagcm (SS 0x524e8 sr_agcm [] kn_agcm 37) [] = RES_pagcm.
Proof. vm_compute. reflexivity. Qed.
End AXF_agcm.

Module AXF_agcmz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ AxTry.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section AGCM.
Context {fx : FPState}.

Definition VALS_agcm (sc mt usage units c0 : Z) : list Z := [sc; mt; usage; units; c0].

Record agcm_pre (regs : bvmap 5 word) (m : word -> option byte) (sc mt usage units c0 : Z) : Prop := {
  agcm_R8 : getr regs 8 = wa sc ;
  agcm_R10 : getr regs 10 = wa mt ;
  agcm_R19 : getr regs 19 = wa (2 * sc) ;
  agcm_R23 : getr regs 23 = wa ((8 * sc) + 614096) ;
  agcm_R24 : getr regs 24 = wa units ;
  agcm_R25 : getr regs 25 = wa 98984 ;
  agcm_rng_sc : 9 <= sc <= 47 ;
  agcm_rng_mt : 1 <= mt <= 2^63-1 ;
  agcm_rng_usage : 0 <= usage <= 2^60 ;
  agcm_rng_units : 1 <= units <= 8191 ;
  agcm_rng_c0 : 4 <= c0 <= 32 ;
  agcm_ka5 : c0 mod 2 = 0 ;
  agcm_kw6 : rdn SEGS m (wa (8 * sc + 614568)) 8 = Some (word_to_le_bytes 8 (wa usage)) ;
  agcm_kw7 : rdn SEGS m (wa (0 + 614032)) 8 = Some (word_to_le_bytes 8 (wa 4096)) ;
  agcm_kw8 : rdn SEGS m (wa (Z.land sc 3 + 99107)) 1 = Some (word_to_le_bytes 1 (wa c0))
}.


#[using="Type"] Lemma agcm_setup : forall regs m sc mt usage units c0, agcm_pre regs m sc mt usage units c0 ->
  regs_ok (Ez regs (VALS_agcm sc mt usage units c0)) AXF_agcm.sr_agcm regs /\ know_ok SEGS (Ez regs (VALS_agcm sc mt usage units c0)) m AXF_agcm.kn_agcm.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sc mt usage units c0 P. destruct P as [agcm_R8 agcm_R10 agcm_R19 agcm_R23 agcm_R24 agcm_R25 agcm_rng_sc agcm_rng_mt agcm_rng_usage agcm_rng_units agcm_rng_c0 agcm_ka5 agcm_kw6 agcm_kw7 agcm_kw8].
  set (E := Ez regs (VALS_agcm sc mt usage units c0)).
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = mt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = usage) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = units) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = c0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_agcm.sr_agcm.
    apply (regs_ok_pin E _ regs 25); [apply (regs_ok_pin E _ regs 24); [apply (regs_ok_pin E _ regs 23); [apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|]|]|]|].
    - rewrite agcm_R8. reflexivity.
    - rewrite agcm_R10. reflexivity.
    - rewrite agcm_R19, zeval_sound. cbn [zeval edenot AXF_agcm.e_sc AXF_agcm.e_mt AXF_agcm.e_usage AXF_agcm.e_units AXF_agcm.e_c0]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite agcm_R23, zeval_sound. cbn [zeval edenot AXF_agcm.e_sc AXF_agcm.e_mt AXF_agcm.e_usage AXF_agcm.e_units AXF_agcm.e_c0]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite agcm_R24. reflexivity.
    - rewrite agcm_R25. reflexivity. }
  unfold know_ok, AXF_agcm.kn_agcm.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_agcm.e_sc AXF_agcm.e_mt AXF_agcm.e_usage AXF_agcm.e_units AXF_agcm.e_c0 a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sc _ _ agcm_rng_sc eq_refl eq_refl), ?(mod64_of_range mt _ _ agcm_rng_mt eq_refl eq_refl), ?(mod64_of_range usage _ _ agcm_rng_usage eq_refl eq_refl), ?(mod64_of_range units _ _ agcm_rng_units eq_refl eq_refl), ?(mod64_of_range c0 _ _ agcm_rng_c0 eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try (pose proof (land3_bound sc); lia).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - agcm_rng_sc agcm_rng_mt agcm_rng_usage agcm_rng_units agcm_rng_c0 agcm_ka5; lia).
  all: first [lia].
Qed.


Definition agcm_mem_pagcm (m : word -> option byte) (regs : bvmap 5 word) (sc mt usage units c0 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem agcm_pagcm : forall regs m rom sc mt usage units c0, agcm_pre regs m sc mt usage units c0 ->
  scs_denot SEGS m (Ez regs (VALS_agcm sc mt usage units c0)) (snd (fst AXF_agcm.RES_pagcm)) ->
  exists R, msteps SEGS (mkst regs (wa 0x524e8) m rom) (mkst R (wa 0x52558) (agcm_mem_pagcm m regs sc mt usage units c0) rom) /\
    getr R 8 = wa sc /\ getr R 9 = wa mt /\ getr R 10 = wa usage /\ getr R 11 = wa 4096 /\ getr R 12 = wa 0 /\ getr R 13 = wa c0 /\ getr R 19 = wa (2 * sc) /\ getr R 23 = wa ((8 * sc) + 614096) /\ getr R 24 = wa (16 * units) /\ getr R 25 = wa 98984 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 14; 15; 16; 17; 18; 20; 21; 22; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc mt usage units c0 P Hsc. destruct (agcm_setup regs m sc mt usage units c0 P) as [HR HK].
  set (E := Ez regs (VALS_agcm sc mt usage units c0)) in *. destruct P as [agcm_R8 agcm_R10 agcm_R19 agcm_R23 agcm_R24 agcm_R25 agcm_rng_sc agcm_rng_mt agcm_rng_usage agcm_rng_units agcm_rng_c0 agcm_ka5 agcm_kw6 agcm_kw7 agcm_kw8].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = mt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = usage) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = units) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = c0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x52558] AXF_agcm.scr_pagcm 0x524e8 AXF_agcm.sr_agcm AXF_agcm.kn_agcm 37 _ _ _ E m rom regs AXF_agcm.RES_pagcm_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_agcm.RES_pagcm fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (agcm_mem_pagcm m regs sc mt usage units c0) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold agcm_mem_pagcm. repeat (apply (f_equal3 wbytes)); try reflexivity.
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

End AGCM.
End AXF_agcmz.


Module AXF_hwe.
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

Definition e_cnt := EVar 32.
Definition e_usage := EVar 33.
Definition sr_hwe := (sr_upd (sr_upd sr_id 10 (e_usage)) 13 (e_cnt)).
Definition kn_hwe : list kentry :=
  [ KRange e_cnt 2 32;
    KAlign e_cnt 2;
    KRange e_usage 0 (2^60) ].
Definition scr_hwe : scripts := SCR [true] [] [].
Definition ss_hwe := SS 0x52558 sr_hwe [] kn_hwe 34.
Definition RUN_hwe := sym_exec SEGS 100 true [0x52558; 0x52580] scr_hwe ss_hwe [].

Definition scr_phwu : scripts := SCR [true] [] [].
Definition RES_phwu := Eval vm_compute in sym_exec SEGS 100 true [0x52558; 0x52580] scr_phwu ss_hwe [].
Lemma RES_phwu_ok : sym_exec SEGS 100 true [0x52558; 0x52580] scr_phwu (SS 0x52558 sr_hwe [] kn_hwe 34) [] = RES_phwu.
Proof. vm_compute. reflexivity. Qed.

Definition scr_phwo : scripts := SCR [false; false] [] [].
Definition RES_phwo := Eval vm_compute in sym_exec SEGS 100 true [0x52558; 0x52580] scr_phwo ss_hwe [].
Lemma RES_phwo_ok : sym_exec SEGS 100 true [0x52558; 0x52580] scr_phwo (SS 0x52558 sr_hwe [] kn_hwe 34) [] = RES_phwo.
Proof. vm_compute. reflexivity. Qed.

Definition scr_phwc : scripts := SCR [false; true] [] [].
Definition RES_phwc := Eval vm_compute in sym_exec SEGS 100 true [0x52558; 0x52580] scr_phwc ss_hwe [].
Lemma RES_phwc_ok : sym_exec SEGS 100 true [0x52558; 0x52580] scr_phwc (SS 0x52558 sr_hwe [] kn_hwe 34) [] = RES_phwc.
Proof. vm_compute. reflexivity. Qed.
End AXF_hwe.

Module AXF_hwez.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngHeap.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap.AxTry2.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section HWE.
Context {fx : FPState}.

Definition VALS_hwe (cnt usage : Z) : list Z := [cnt; usage].

Record hwe_pre (regs : bvmap 5 word) (m : word -> option byte) (cnt usage : Z) : Prop := {
  hwe_R10 : getr regs 10 = wa usage ;
  hwe_R13 : getr regs 13 = wa cnt ;
  hwe_rng_cnt : 2 <= cnt <= 32 ;
  hwe_rng_usage : 0 <= usage <= 2^60 ;
  hwe_ka1 : cnt mod 2 = 0
}.


#[using="Type"] Lemma hwe_setup : forall regs m cnt usage, hwe_pre regs m cnt usage ->
  regs_ok (Ez regs (VALS_hwe cnt usage)) AXF_hwe.sr_hwe regs /\ know_ok SEGS (Ez regs (VALS_hwe cnt usage)) m AXF_hwe.kn_hwe.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m cnt usage P. destruct P as [hwe_R10 hwe_R13 hwe_rng_cnt hwe_rng_usage hwe_ka1].
  set (E := Ez regs (VALS_hwe cnt usage)).
  assert (Z32 : bv_unsigned (ev E 32) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = usage) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_hwe.sr_hwe.
    apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|].
    - rewrite hwe_R10. reflexivity.
    - rewrite hwe_R13. reflexivity. }
  unfold know_ok, AXF_hwe.kn_hwe.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_hwe.e_cnt AXF_hwe.e_usage a_base a_off].
  all: rewrite ?Z32, ?Z33.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range cnt _ _ hwe_rng_cnt eq_refl eq_refl), ?(mod64_of_range usage _ _ hwe_rng_usage eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - hwe_rng_cnt hwe_rng_usage hwe_ka1; lia).
  all: first [lia].
Qed.


Definition hwe_mem_phwu (m : word -> option byte) (regs : bvmap 5 word) (cnt usage : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem hwe_phwu : forall regs m rom cnt usage, hwe_pre regs m cnt usage ->
  scs_denot SEGS m (Ez regs (VALS_hwe cnt usage)) (snd (fst AXF_hwe.RES_phwu)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52558) m rom) (mkst R (wa 0x52580) (hwe_mem_phwu m regs cnt usage) rom) /\
    getr R 10 = wa usage /\ getr R 12 = wa cnt /\ getr R 13 = wa cnt /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom cnt usage P Hsc. destruct (hwe_setup regs m cnt usage P) as [HR HK].
  set (E := Ez regs (VALS_hwe cnt usage)) in *. destruct P as [hwe_R10 hwe_R13 hwe_rng_cnt hwe_rng_usage hwe_ka1].
  assert (Z32 : bv_unsigned (ev E 32) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = usage) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x52558; 0x52580] AXF_hwe.scr_phwu 0x52558 AXF_hwe.sr_hwe AXF_hwe.kn_hwe 34 _ _ _ E m rom regs AXF_hwe.RES_phwu_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_hwe.RES_phwu fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (hwe_mem_phwu m regs cnt usage) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold hwe_mem_phwu. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [first [zpost_reg HR' | (srg HR'; cbn [edenot]; rewrite <- (wa_u (ev E 32)), Z32; apply srlw1_small; lia)]|].
    split; [first [zpost_reg HR' | (srg HR'; cbn [edenot]; rewrite <- (wa_u (ev E 32)), Z32; apply srlw1_small; lia)]|].
    split; [first [zpost_reg HR' | (srg HR'; cbn [edenot]; rewrite <- (wa_u (ev E 32)), Z32; apply srlw1_small; lia)]|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition hwe_mem_phwo (m : word -> option byte) (regs : bvmap 5 word) (cnt usage : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem hwe_phwo : forall regs m rom cnt usage, hwe_pre regs m cnt usage ->
  scs_denot SEGS m (Ez regs (VALS_hwe cnt usage)) (snd (fst AXF_hwe.RES_phwo)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52558) m rom) (mkst R (wa 0x52580) (hwe_mem_phwo m regs cnt usage) rom) /\
    getr R 10 = wa usage /\ getr R 12 = wa (cnt / 2) /\ getr R 13 = wa (cnt / 2) /\ getr R 14 = wa (Z.land cnt 2) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom cnt usage P Hsc. destruct (hwe_setup regs m cnt usage P) as [HR HK].
  set (E := Ez regs (VALS_hwe cnt usage)) in *. destruct P as [hwe_R10 hwe_R13 hwe_rng_cnt hwe_rng_usage hwe_ka1].
  assert (Z32 : bv_unsigned (ev E 32) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = usage) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x52558; 0x52580] AXF_hwe.scr_phwo 0x52558 AXF_hwe.sr_hwe AXF_hwe.kn_hwe 34 _ _ _ E m rom regs AXF_hwe.RES_phwo_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_hwe.RES_phwo fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (hwe_mem_phwo m regs cnt usage) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold hwe_mem_phwo. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [first [zpost_reg HR' | (srg HR'; cbn [edenot]; rewrite <- (wa_u (ev E 32)), Z32; apply srlw1_small; lia)]|].
    split; [first [zpost_reg HR' | (srg HR'; cbn [edenot]; rewrite <- (wa_u (ev E 32)), Z32; apply srlw1_small; lia)]|].
    split; [first [zpost_reg HR' | (srg HR'; cbn [edenot]; rewrite <- (wa_u (ev E 32)), Z32; apply srlw1_small; lia)]|].
    split; [first [zpost_reg HR' | (srg HR'; cbn [edenot]; rewrite <- (wa_u (ev E 32)), Z32; apply srlw1_small; lia)]|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition hwe_mem_phwc (m : word -> option byte) (regs : bvmap 5 word) (cnt usage : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem hwe_phwc : forall regs m rom cnt usage, hwe_pre regs m cnt usage ->
  scs_denot SEGS m (Ez regs (VALS_hwe cnt usage)) (snd (fst AXF_hwe.RES_phwc)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52558) m rom) (mkst R (wa 0x52558) (hwe_mem_phwc m regs cnt usage) rom) /\
    getr R 10 = wa usage /\ getr R 13 = wa (cnt / 2) /\ getr R 14 = wa (Z.land cnt 2) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom cnt usage P Hsc. destruct (hwe_setup regs m cnt usage P) as [HR HK].
  set (E := Ez regs (VALS_hwe cnt usage)) in *. destruct P as [hwe_R10 hwe_R13 hwe_rng_cnt hwe_rng_usage hwe_ka1].
  assert (Z32 : bv_unsigned (ev E 32) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = usage) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x52558; 0x52580] AXF_hwe.scr_phwc 0x52558 AXF_hwe.sr_hwe AXF_hwe.kn_hwe 34 _ _ _ E m rom regs AXF_hwe.RES_phwc_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_hwe.RES_phwc fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (hwe_mem_phwc m regs cnt usage) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold hwe_mem_phwc. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [first [zpost_reg HR' | (srg HR'; cbn [edenot]; rewrite <- (wa_u (ev E 32)), Z32; apply srlw1_small; lia)]|].
    split; [first [zpost_reg HR' | (srg HR'; cbn [edenot]; rewrite <- (wa_u (ev E 32)), Z32; apply srlw1_small; lia)]|].
    split; [first [zpost_reg HR' | (srg HR'; cbn [edenot]; rewrite <- (wa_u (ev E 32)), Z32; apply srlw1_small; lia)]|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End HWE.
End AXF_hwez.


Module AXF_hwb.
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

Definition e_cnt := EVar 32.
Definition e_size := EVar 33.
Definition sr_hwb := (sr_upd (sr_upd sr_id 12 (e_cnt)) 24 (e_size)).
Definition kn_hwb : list kentry :=
  [ KRange e_cnt 1 32;
    KRange e_size 16 131056 ].
Definition scr_hwb : scripts := SCR [true] [] [].
Definition ss_hwb := SS 0x52580 sr_hwb [] kn_hwb 34.
Definition RUN_hwb := sym_exec SEGS 100 true [0x52580; 0x52594] scr_hwb ss_hwb [].

Definition scr_phbc : scripts := SCR [true] [] [].
Definition RES_phbc := Eval vm_compute in sym_exec SEGS 100 true [0x52580; 0x52594] scr_phbc ss_hwb [].
Lemma RES_phbc_ok : sym_exec SEGS 100 true [0x52580; 0x52594] scr_phbc (SS 0x52580 sr_hwb [] kn_hwb 34) [] = RES_phbc.
Proof. vm_compute. reflexivity. Qed.

Definition scr_phbx : scripts := SCR [false] [] [].
Definition RES_phbx := Eval vm_compute in sym_exec SEGS 100 true [0x52580; 0x52594] scr_phbx ss_hwb [].
Lemma RES_phbx_ok : sym_exec SEGS 100 true [0x52580; 0x52594] scr_phbx (SS 0x52580 sr_hwb [] kn_hwb 34) [] = RES_phbx.
Proof. vm_compute. reflexivity. Qed.
End AXF_hwb.

Module AXF_hwbz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngHeap.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap.AxTry2.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section HWB.
Context {fx : FPState}.

Definition VALS_hwb (cnt size : Z) : list Z := [cnt; size].

Record hwb_pre (regs : bvmap 5 word) (m : word -> option byte) (cnt size : Z) : Prop := {
  hwb_R12 : getr regs 12 = wa cnt ;
  hwb_R24 : getr regs 24 = wa size ;
  hwb_rng_cnt : 1 <= cnt <= 32 ;
  hwb_rng_size : 16 <= size <= 131056
}.


#[using="Type"] Lemma hwb_setup : forall regs m cnt size, hwb_pre regs m cnt size ->
  regs_ok (Ez regs (VALS_hwb cnt size)) AXF_hwb.sr_hwb regs /\ know_ok SEGS (Ez regs (VALS_hwb cnt size)) m AXF_hwb.kn_hwb.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m cnt size P. destruct P as [hwb_R12 hwb_R24 hwb_rng_cnt hwb_rng_size].
  set (E := Ez regs (VALS_hwb cnt size)).
  assert (Z32 : bv_unsigned (ev E 32) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = size) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_hwb.sr_hwb.
    apply (regs_ok_pin E _ regs 24); [apply (regs_ok_pin E _ regs 12); [apply regs_ok_id|]|].
    - rewrite hwb_R12. reflexivity.
    - rewrite hwb_R24. reflexivity. }
  unfold know_ok, AXF_hwb.kn_hwb.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_hwb.e_cnt AXF_hwb.e_size a_base a_off].
  all: rewrite ?Z32, ?Z33.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range cnt _ _ hwb_rng_cnt eq_refl eq_refl), ?(mod64_of_range size _ _ hwb_rng_size eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - hwb_rng_cnt hwb_rng_size; lia).
  all: first [lia].
Qed.


Definition hwb_mem_phbc (m : word -> option byte) (regs : bvmap 5 word) (cnt size : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem hwb_phbc : forall regs m rom cnt size, hwb_pre regs m cnt size ->
  scs_denot SEGS m (Ez regs (VALS_hwb cnt size)) (snd (fst AXF_hwb.RES_phbc)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52580) m rom) (mkst R (wa 0x52580) (hwb_mem_phbc m regs cnt size) rom) /\
    getr R 12 = wa (cnt / 2) /\ getr R 13 = wa (Z.shiftr (((size * cnt)) mod 2^64) 20) /\ getr R 19 = wa cnt /\ getr R 24 = wa size /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 14; 15; 16; 17; 18; 20; 21; 22; 23; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom cnt size P Hsc. destruct (hwb_setup regs m cnt size P) as [HR HK].
  set (E := Ez regs (VALS_hwb cnt size)) in *. destruct P as [hwb_R12 hwb_R24 hwb_rng_cnt hwb_rng_size].
  assert (Z32 : bv_unsigned (ev E 32) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = size) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x52580; 0x52594] AXF_hwb.scr_phbc 0x52580 AXF_hwb.sr_hwb AXF_hwb.kn_hwb 34 _ _ _ E m rom regs AXF_hwb.RES_phbc_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_hwb.RES_phbc fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (hwb_mem_phbc m regs cnt size) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold hwb_mem_phbc. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [first [zpost_reg HR' | (srg HR'; cbn [edenot]; rewrite <- (wa_u (ev E 32)), Z32; apply srlw1_small; lia)]|].
    split; [first [zpost_reg HR' | (srg HR'; cbn [edenot]; rewrite <- (wa_u (ev E 32)), Z32; apply srlw1_small; lia)]|].
    split; [first [zpost_reg HR' | (srg HR'; cbn [edenot]; rewrite <- (wa_u (ev E 32)), Z32; apply srlw1_small; lia)]|].
    split; [first [zpost_reg HR' | (srg HR'; cbn [edenot]; rewrite <- (wa_u (ev E 32)), Z32; apply srlw1_small; lia)]|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition hwb_mem_phbx (m : word -> option byte) (regs : bvmap 5 word) (cnt size : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem hwb_phbx : forall regs m rom cnt size, hwb_pre regs m cnt size ->
  scs_denot SEGS m (Ez regs (VALS_hwb cnt size)) (snd (fst AXF_hwb.RES_phbx)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52580) m rom) (mkst R (wa 0x52594) (hwb_mem_phbx m regs cnt size) rom) /\
    getr R 13 = wa (Z.shiftr (((size * cnt)) mod 2^64) 20) /\ getr R 19 = wa cnt /\ getr R 24 = wa size /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 14; 15; 16; 17; 18; 20; 21; 22; 23; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom cnt size P Hsc. destruct (hwb_setup regs m cnt size P) as [HR HK].
  set (E := Ez regs (VALS_hwb cnt size)) in *. destruct P as [hwb_R12 hwb_R24 hwb_rng_cnt hwb_rng_size].
  assert (Z32 : bv_unsigned (ev E 32) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = size) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x52580; 0x52594] AXF_hwb.scr_phbx 0x52580 AXF_hwb.sr_hwb AXF_hwb.kn_hwb 34 _ _ _ E m rom regs AXF_hwb.RES_phbx_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_hwb.RES_phbx fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (hwb_mem_phbx m regs cnt size) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold hwb_mem_phbx. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [first [zpost_reg HR' | (srg HR'; cbn [edenot]; rewrite <- (wa_u (ev E 32)), Z32; apply srlw1_small; lia)]|].
    split; [first [zpost_reg HR' | (srg HR'; cbn [edenot]; rewrite <- (wa_u (ev E 32)), Z32; apply srlw1_small; lia)]|].
    split; [first [zpost_reg HR' | (srg HR'; cbn [edenot]; rewrite <- (wa_u (ev E 32)), Z32; apply srlw1_small; lia)]|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End HWB.
End AXF_hwbz.


Module AXF_agad.
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

Definition e_cnt := EVar 32.
Definition e_size := EVar 33.
Definition sr_agad := (sr_upd (sr_upd (sr_upd sr_id 11 (ELit 4096)) 19 (e_cnt)) 24 (e_size)).
Definition kn_agad : list kentry :=
  [ KRange e_cnt 2 32;
    KRange e_size 16 131056 ].
Definition scr_agad : scripts := SCR [false] [] [].
Definition ss_agad := SS 0x52594 sr_agad [] kn_agad 34.
Definition RUN_agad := sym_exec SEGS 100 true [0x525bc; 0x52600] scr_agad ss_agad [].

Definition scr_padm : scripts := SCR [false] [] [].
Definition RES_padm := Eval vm_compute in sym_exec SEGS 100 true [0x525bc; 0x52600] scr_padm ss_agad [].
Lemma RES_padm_ok : sym_exec SEGS 100 true [0x525bc; 0x52600] scr_padm (SS 0x52594 sr_agad [] kn_agad 34) [] = RES_padm.
Proof. vm_compute. reflexivity. Qed.

Definition scr_padn : scripts := SCR [true] [] [].
Definition RES_padn := Eval vm_compute in sym_exec SEGS 100 true [0x525bc; 0x52600] scr_padn ss_agad [].
Lemma RES_padn_ok : sym_exec SEGS 100 true [0x525bc; 0x52600] scr_padn (SS 0x52594 sr_agad [] kn_agad 34) [] = RES_padn.
Proof. vm_compute. reflexivity. Qed.
End AXF_agad.

Module AXF_agadz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section AGAD.
Context {fx : FPState}.

Definition VALS_agad (cnt size : Z) : list Z := [cnt; size].

Record agad_pre (regs : bvmap 5 word) (m : word -> option byte) (cnt size : Z) : Prop := {
  agad_R11 : getr regs 11 = wa 4096 ;
  agad_R19 : getr regs 19 = wa cnt ;
  agad_R24 : getr regs 24 = wa size ;
  agad_rng_cnt : 2 <= cnt <= 32 ;
  agad_rng_size : 16 <= size <= 131056
}.


#[using="Type"] Lemma agad_setup : forall regs m cnt size, agad_pre regs m cnt size ->
  regs_ok (Ez regs (VALS_agad cnt size)) AXF_agad.sr_agad regs /\ know_ok SEGS (Ez regs (VALS_agad cnt size)) m AXF_agad.kn_agad.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m cnt size P. destruct P as [agad_R11 agad_R19 agad_R24 agad_rng_cnt agad_rng_size].
  set (E := Ez regs (VALS_agad cnt size)).
  assert (Z32 : bv_unsigned (ev E 32) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = size) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_agad.sr_agad.
    apply (regs_ok_pin E _ regs 24); [apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 11); [apply regs_ok_id|]|]|].
    - rewrite agad_R11. reflexivity.
    - rewrite agad_R19. reflexivity.
    - rewrite agad_R24. reflexivity. }
  unfold know_ok, AXF_agad.kn_agad.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_agad.e_cnt AXF_agad.e_size a_base a_off].
  all: rewrite ?Z32, ?Z33.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range cnt _ _ agad_rng_cnt eq_refl eq_refl), ?(mod64_of_range size _ _ agad_rng_size eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - agad_rng_cnt agad_rng_size; lia).
  all: first [lia].
Qed.


Definition agad_mem_padm (m : word -> option byte) (regs : bvmap 5 word) (cnt size : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem agad_padm : forall regs m rom cnt size, agad_pre regs m cnt size ->
  scs_denot SEGS m (Ez regs (VALS_agad cnt size)) (snd (fst AXF_agad.RES_padm)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52594) m rom) (mkst R (wa 0x525bc) (agad_mem_padm m regs cnt size) rom) /\
    getr R 11 = wa 4096 /\ getr R 12 = wa (size + 16) /\ getr R 13 = wa 2048 /\ getr R 14 = wa (size * cnt) /\ getr R 15 = wa ((size * cnt) + 16) /\ getr R 19 = wa cnt /\ getr R 24 = wa size /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 16; 17; 18; 20; 21; 22; 23; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom cnt size P Hsc. destruct (agad_setup regs m cnt size P) as [HR HK].
  set (E := Ez regs (VALS_agad cnt size)) in *. destruct P as [agad_R11 agad_R19 agad_R24 agad_rng_cnt agad_rng_size].
  assert (Z32 : bv_unsigned (ev E 32) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = size) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x525bc; 0x52600] AXF_agad.scr_padm 0x52594 AXF_agad.sr_agad AXF_agad.kn_agad 34 _ _ _ E m rom regs AXF_agad.RES_padm_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_agad.RES_padm fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (agad_mem_padm m regs cnt size) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold agad_mem_padm. repeat (apply (f_equal3 wbytes)); try reflexivity.
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


Definition agad_mem_padn (m : word -> option byte) (regs : bvmap 5 word) (cnt size : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem agad_padn : forall regs m rom cnt size, agad_pre regs m cnt size ->
  scs_denot SEGS m (Ez regs (VALS_agad cnt size)) (snd (fst AXF_agad.RES_padn)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52594) m rom) (mkst R (wa 0x52600) (agad_mem_padn m regs cnt size) rom) /\
    getr R 11 = wa 4096 /\ getr R 12 = wa (size + 16) /\ getr R 13 = wa 2048 /\ getr R 14 = wa (size * cnt) /\ getr R 15 = wa ((size * cnt) + 16) /\ getr R 19 = wa cnt /\ getr R 24 = wa size /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 16; 17; 18; 20; 21; 22; 23; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom cnt size P Hsc. destruct (agad_setup regs m cnt size P) as [HR HK].
  set (E := Ez regs (VALS_agad cnt size)) in *. destruct P as [agad_R11 agad_R19 agad_R24 agad_rng_cnt agad_rng_size].
  assert (Z32 : bv_unsigned (ev E 32) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = size) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x525bc; 0x52600] AXF_agad.scr_padn 0x52594 AXF_agad.sr_agad AXF_agad.kn_agad 34 _ _ _ E m rom regs AXF_agad.RES_padn_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_agad.RES_padn fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (agad_mem_padn m regs cnt size) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold agad_mem_padn. repeat (apply (f_equal3 wbytes)); try reflexivity.
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

End AGAD.
End AXF_agadz.


Module AXF_agad1s.
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

Definition e_size := EVar 32.
Definition sr_agad1s := (sr_upd (sr_upd (sr_upd sr_id 11 (ELit 4096)) 19 (ELit 1)) 24 (e_size)).
Definition kn_agad1s : list kentry :=
  [ KRange e_size 16 2032 ].
Definition scr_agad1s : scripts := SCR [false] [] [].
Definition ss_agad1s := SS 0x52594 sr_agad1s [] kn_agad1s 33.
Definition RUN_agad1s := sym_exec SEGS 100 true [0x525bc; 0x52600] scr_agad1s ss_agad1s [].

Definition scr_pasm : scripts := SCR [false] [] [].
Definition RES_pasm := Eval vm_compute in sym_exec SEGS 100 true [0x525bc; 0x52600] scr_pasm ss_agad1s [].
Lemma RES_pasm_ok : sym_exec SEGS 100 true [0x525bc; 0x52600] scr_pasm (SS 0x52594 sr_agad1s [] kn_agad1s 33) [] = RES_pasm.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pasn : scripts := SCR [true] [] [].
Definition RES_pasn := Eval vm_compute in sym_exec SEGS 100 true [0x525bc; 0x52600] scr_pasn ss_agad1s [].
Lemma RES_pasn_ok : sym_exec SEGS 100 true [0x525bc; 0x52600] scr_pasn (SS 0x52594 sr_agad1s [] kn_agad1s 33) [] = RES_pasn.
Proof. vm_compute. reflexivity. Qed.
End AXF_agad1s.

Module AXF_agad1sz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section AGAD1S.
Context {fx : FPState}.

Definition VALS_agad1s (size : Z) : list Z := [size].

Record agad1s_pre (regs : bvmap 5 word) (m : word -> option byte) (size : Z) : Prop := {
  agad1s_R11 : getr regs 11 = wa 4096 ;
  agad1s_R19 : getr regs 19 = wa 1 ;
  agad1s_R24 : getr regs 24 = wa size ;
  agad1s_rng_size : 16 <= size <= 2032
}.


#[using="Type"] Lemma agad1s_setup : forall regs m size, agad1s_pre regs m size ->
  regs_ok (Ez regs (VALS_agad1s size)) AXF_agad1s.sr_agad1s regs /\ know_ok SEGS (Ez regs (VALS_agad1s size)) m AXF_agad1s.kn_agad1s.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m size P. destruct P as [agad1s_R11 agad1s_R19 agad1s_R24 agad1s_rng_size].
  set (E := Ez regs (VALS_agad1s size)).
  assert (Z32 : bv_unsigned (ev E 32) = size) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_agad1s.sr_agad1s.
    apply (regs_ok_pin E _ regs 24); [apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 11); [apply regs_ok_id|]|]|].
    - rewrite agad1s_R11. reflexivity.
    - rewrite agad1s_R19. reflexivity.
    - rewrite agad1s_R24. reflexivity. }
  unfold know_ok, AXF_agad1s.kn_agad1s.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_agad1s.e_size a_base a_off].
  all: rewrite ?Z32.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range size _ _ agad1s_rng_size eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - agad1s_rng_size; lia).
  all: first [lia].
Qed.


Definition agad1s_mem_pasm (m : word -> option byte) (regs : bvmap 5 word) (size : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem agad1s_pasm : forall regs m rom size, agad1s_pre regs m size ->
  scs_denot SEGS m (Ez regs (VALS_agad1s size)) (snd (fst AXF_agad1s.RES_pasm)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52594) m rom) (mkst R (wa 0x525bc) (agad1s_mem_pasm m regs size) rom) /\
    getr R 11 = wa 4096 /\ getr R 12 = wa (size + 16) /\ getr R 13 = wa 2048 /\ getr R 14 = wa (2 * size) /\ getr R 15 = wa ((2 * size) + 16) /\ getr R 19 = wa 2 /\ getr R 24 = wa size /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 16; 17; 18; 20; 21; 22; 23; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom size P Hsc. destruct (agad1s_setup regs m size P) as [HR HK].
  set (E := Ez regs (VALS_agad1s size)) in *. destruct P as [agad1s_R11 agad1s_R19 agad1s_R24 agad1s_rng_size].
  assert (Z32 : bv_unsigned (ev E 32) = size) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x525bc; 0x52600] AXF_agad1s.scr_pasm 0x52594 AXF_agad1s.sr_agad1s AXF_agad1s.kn_agad1s 33 _ _ _ E m rom regs AXF_agad1s.RES_pasm_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_agad1s.RES_pasm fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (agad1s_mem_pasm m regs size) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold agad1s_mem_pasm. repeat (apply (f_equal3 wbytes)); try reflexivity.
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


Definition agad1s_mem_pasn (m : word -> option byte) (regs : bvmap 5 word) (size : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem agad1s_pasn : forall regs m rom size, agad1s_pre regs m size ->
  scs_denot SEGS m (Ez regs (VALS_agad1s size)) (snd (fst AXF_agad1s.RES_pasn)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52594) m rom) (mkst R (wa 0x52600) (agad1s_mem_pasn m regs size) rom) /\
    getr R 11 = wa 4096 /\ getr R 12 = wa (size + 16) /\ getr R 13 = wa 2048 /\ getr R 14 = wa (2 * size) /\ getr R 15 = wa ((2 * size) + 16) /\ getr R 19 = wa 2 /\ getr R 24 = wa size /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 16; 17; 18; 20; 21; 22; 23; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom size P Hsc. destruct (agad1s_setup regs m size P) as [HR HK].
  set (E := Ez regs (VALS_agad1s size)) in *. destruct P as [agad1s_R11 agad1s_R19 agad1s_R24 agad1s_rng_size].
  assert (Z32 : bv_unsigned (ev E 32) = size) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x525bc; 0x52600] AXF_agad1s.scr_pasn 0x52594 AXF_agad1s.sr_agad1s AXF_agad1s.kn_agad1s 33 _ _ _ E m rom regs AXF_agad1s.RES_pasn_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_agad1s.RES_pasn fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (agad1s_mem_pasn m regs size) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold agad1s_mem_pasn. repeat (apply (f_equal3 wbytes)); try reflexivity.
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

End AGAD1S.
End AXF_agad1sz.


Module AXF_agad1b.
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

Definition e_size := EVar 32.
Definition sr_agad1b := (sr_upd (sr_upd (sr_upd sr_id 11 (ELit 4096)) 19 (ELit 1)) 24 (e_size)).
Definition kn_agad1b : list kentry :=
  [ KRange e_size 2033 131056 ].
Definition scr_agad1b : scripts := SCR [false] [] [].
Definition ss_agad1b := SS 0x52594 sr_agad1b [] kn_agad1b 33.
Definition RUN_agad1b := sym_exec SEGS 100 true [0x525bc; 0x52600] scr_agad1b ss_agad1b [].

Definition scr_pabm : scripts := SCR [false] [] [].
Definition RES_pabm := Eval vm_compute in sym_exec SEGS 100 true [0x525bc; 0x52600] scr_pabm ss_agad1b [].
Lemma RES_pabm_ok : sym_exec SEGS 100 true [0x525bc; 0x52600] scr_pabm (SS 0x52594 sr_agad1b [] kn_agad1b 33) [] = RES_pabm.
Proof. vm_compute. reflexivity. Qed.
End AXF_agad1b.

Module AXF_agad1bz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section AGAD1B.
Context {fx : FPState}.

Definition VALS_agad1b (size : Z) : list Z := [size].

Record agad1b_pre (regs : bvmap 5 word) (m : word -> option byte) (size : Z) : Prop := {
  agad1b_R11 : getr regs 11 = wa 4096 ;
  agad1b_R19 : getr regs 19 = wa 1 ;
  agad1b_R24 : getr regs 24 = wa size ;
  agad1b_rng_size : 2033 <= size <= 131056
}.


#[using="Type"] Lemma agad1b_setup : forall regs m size, agad1b_pre regs m size ->
  regs_ok (Ez regs (VALS_agad1b size)) AXF_agad1b.sr_agad1b regs /\ know_ok SEGS (Ez regs (VALS_agad1b size)) m AXF_agad1b.kn_agad1b.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m size P. destruct P as [agad1b_R11 agad1b_R19 agad1b_R24 agad1b_rng_size].
  set (E := Ez regs (VALS_agad1b size)).
  assert (Z32 : bv_unsigned (ev E 32) = size) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_agad1b.sr_agad1b.
    apply (regs_ok_pin E _ regs 24); [apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 11); [apply regs_ok_id|]|]|].
    - rewrite agad1b_R11. reflexivity.
    - rewrite agad1b_R19. reflexivity.
    - rewrite agad1b_R24. reflexivity. }
  unfold know_ok, AXF_agad1b.kn_agad1b.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_agad1b.e_size a_base a_off].
  all: rewrite ?Z32.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range size _ _ agad1b_rng_size eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - agad1b_rng_size; lia).
  all: first [lia].
Qed.


Definition agad1b_mem_pabm (m : word -> option byte) (regs : bvmap 5 word) (size : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem agad1b_pabm : forall regs m rom size, agad1b_pre regs m size ->
  scs_denot SEGS m (Ez regs (VALS_agad1b size)) (snd (fst AXF_agad1b.RES_pabm)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52594) m rom) (mkst R (wa 0x525bc) (agad1b_mem_pabm m regs size) rom) /\
    getr R 11 = wa 4096 /\ getr R 12 = wa (size + 16) /\ getr R 13 = wa 2048 /\ getr R 14 = wa size /\ getr R 15 = wa (size + 16) /\ getr R 19 = wa 1 /\ getr R 24 = wa size /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 16; 17; 18; 20; 21; 22; 23; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom size P Hsc. destruct (agad1b_setup regs m size P) as [HR HK].
  set (E := Ez regs (VALS_agad1b size)) in *. destruct P as [agad1b_R11 agad1b_R19 agad1b_R24 agad1b_rng_size].
  assert (Z32 : bv_unsigned (ev E 32) = size) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x525bc; 0x52600] AXF_agad1b.scr_pabm 0x52594 AXF_agad1b.sr_agad1b AXF_agad1b.kn_agad1b 33 _ _ _ E m rom regs AXF_agad1b.RES_pabm_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_agad1b.RES_pabm fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (agad1b_mem_pabm m regs size) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold agad1b_mem_pabm. repeat (apply (f_equal3 wbytes)); try reflexivity.
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

End AGAD1B.
End AXF_agad1bz.

Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxTry OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap.AxTry2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag1.AXF_agcsz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag1.AXF_agcmz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag1.AXF_hwez OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag1.AXF_hwbz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag1.AXF_agadz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag1.AXF_agad1sz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag1.AXF_agad1bz.
Import ListNotations AX2 AX2S.

Module AXF_agm.
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

Definition e_sc := EVar 32.
Definition e_units := EVar 33.
Definition sr_agm := (sr_upd sr_id 8 (e_sc)).
Definition kn_agm : list kentry :=
  [ KRange e_sc 0 47;
    KRange e_units 1 8191;
    KWord (SA (EMd M_MUL (ELit 2) e_sc) 98984) 2 e_units ].
Definition scr_agm : scripts := SCR [] [] [].
Definition ss_agm := SS 0x524d0 sr_agm [] kn_agm 34.
Definition RUN_agm := sym_exec SEGS 100 true [0x51ca8] scr_agm ss_agm [].

Definition scr_pagm : scripts := SCR [] [] [].
Definition RES_pagm := Eval vm_compute in sym_exec SEGS 100 true [0x51ca8] scr_pagm ss_agm [].
Lemma RES_pagm_ok : sym_exec SEGS 100 true [0x51ca8] scr_pagm (SS 0x524d0 sr_agm [] kn_agm 34) [] = RES_pagm.
Proof. vm_compute. reflexivity. Qed.
End AXF_agm.

Module AXF_agmz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section AGM.
Context {fx : FPState}.

Definition VALS_agm (sc units : Z) : list Z := [sc; units].

Record agm_pre (regs : bvmap 5 word) (m : word -> option byte) (sc units : Z) : Prop := {
  agm_R8 : getr regs 8 = wa sc ;
  agm_rng_sc : 0 <= sc <= 47 ;
  agm_rng_units : 1 <= units <= 8191 ;
  agm_kw2 : rdn SEGS m (wa (2 * sc + 98984)) 2 = Some (word_to_le_bytes 2 (wa units))
}.


#[using="Type"] Lemma agm_setup : forall regs m sc units, agm_pre regs m sc units ->
  regs_ok (Ez regs (VALS_agm sc units)) AXF_agm.sr_agm regs /\ know_ok SEGS (Ez regs (VALS_agm sc units)) m AXF_agm.kn_agm.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sc units P. destruct P as [agm_R8 agm_rng_sc agm_rng_units agm_kw2].
  set (E := Ez regs (VALS_agm sc units)).
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = units) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_agm.sr_agm.
    apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|].
    - rewrite agm_R8. reflexivity. }
  unfold know_ok, AXF_agm.kn_agm.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_agm.e_sc AXF_agm.e_units a_base a_off].
  all: rewrite ?Z32, ?Z33.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sc _ _ agm_rng_sc eq_refl eq_refl), ?(mod64_of_range units _ _ agm_rng_units eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - agm_rng_sc agm_rng_units; lia).
  all: first [lia].
Qed.


Definition agm_mem_pagm (m : word -> option byte) (regs : bvmap 5 word) (sc units : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem agm_pagm : forall regs m rom sc units, agm_pre regs m sc units ->
  scs_denot SEGS m (Ez regs (VALS_agm sc units)) (snd (fst AXF_agm.RES_pagm)) ->
  exists R, msteps SEGS (mkst regs (wa 0x524d0) m rom) (mkst R (wa 0x51ca8) (agm_mem_pagm m regs sc units) rom) /\
    getr R 1 = wa 337128 /\ getr R 8 = wa sc /\ getr R 10 = wa ((2 * sc) + 98984) /\ getr R 19 = wa (2 * sc) /\ getr R 24 = wa units /\ getr R 25 = wa 98984 /\ (forall k, In k [2; 3; 4; 5; 6; 7; 9; 11; 12; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc units P Hsc. destruct (agm_setup regs m sc units P) as [HR HK].
  set (E := Ez regs (VALS_agm sc units)) in *. destruct P as [agm_R8 agm_rng_sc agm_rng_units agm_kw2].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = units) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51ca8] AXF_agm.scr_pagm 0x524d0 AXF_agm.sr_agm AXF_agm.kn_agm 34 _ _ _ E m rom regs AXF_agm.RES_pagm_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_agm.RES_pagm fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (agm_mem_pagm m regs sc units) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold agm_mem_pagm. repeat (apply (f_equal3 wbytes)); try reflexivity.
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

End AGM.
End AXF_agmz.

Module AXF_ai.
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

Definition e_mem := EVar 32.
Definition e_mt := EVar 33.
Definition e_len := EVar 34.
Definition e_size := EVar 35.
Definition e_cnt := EVar 36.
Definition e_ctr := EVar 37.
Definition e_W := EVar 38.
Definition sr_ai := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 9 (e_mt)) 10 (e_mem)) 18 (ELit 18446744073709551615)) 19 (e_len)) 22 (ELit 614096)) 24 (e_size)) 25 (e_cnt)).
Definition kn_ai : list kentry :=
  [ KRange e_mem 4096 (2^47);
    KRange e_mt 1 (2^63-1);
    KAlign e_mt 8;
    KRange e_len 4096 (2^40);
    KRange e_size 16 4080;
    KRange e_cnt 1 32;
    KRange e_ctr 0 (2^32-1);
    KRange e_W 0 (2^63-1);
    KWord (SA e_mt 32) 8 e_W;
    KWord (SA (ELit 0) 614116) 4 e_ctr;
    KWr (SA e_mt 32) (ELit 8);
    KWr (SA (ELit 0) 614116) (ELit 4);
    KDisj (SA e_mt 32) (ELit 8) (SA (ELit 0) 614116) (ELit 4) ].
Definition scr_ai : scripts := SCR [true] [] [].
Definition ss_ai := SS 0x529a4 sr_ai [] kn_ai 39.
Definition RUN_ai := sym_exec SEGS 100 true [0x529f8] scr_ai ss_ai [].

Definition scr_pail : scripts := SCR [true] [] [].
Definition RES_pail := Eval vm_compute in sym_exec SEGS 100 true [0x529f8] scr_pail ss_ai [].
Lemma RES_pail_ok : sym_exec SEGS 100 true [0x529f8] scr_pail (SS 0x529a4 sr_ai [] kn_ai 39) [] = RES_pail.
Proof. vm_compute. reflexivity. Qed.

Definition scr_paig : scripts := SCR [false] [] [].
Definition RES_paig := Eval vm_compute in sym_exec SEGS 100 true [0x529f8] scr_paig ss_ai [].
Lemma RES_paig_ok : sym_exec SEGS 100 true [0x529f8] scr_paig (SS 0x529a4 sr_ai [] kn_ai 39) [] = RES_paig.
Proof. vm_compute. reflexivity. Qed.
End AXF_ai.

Module AXF_ai0.
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

Definition e_mem := EVar 32.
Definition e_mt := EVar 33.
Definition e_len := EVar 34.
Definition e_size := EVar 35.
Definition e_cnt := EVar 36.
Definition e_ctr := EVar 37.
Definition e_W := EVar 38.
Definition sr_ai0 := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 9 (e_mt)) 10 (e_mem)) 18 (ELit 18446744073709551615)) 19 (e_len)) 22 (ELit 614096)) 24 (e_size)) 25 (e_cnt)).
Definition kn_ai0 : list kentry :=
  [ KRange e_mem 4096 (2^47);
    KRange e_mt 1 (2^63-1);
    KAlign e_mt 8;
    KRange e_len 4096 (2^40);
    KRange e_size 4081 131056;
    KRange e_cnt 1 32;
    KRange e_ctr 0 (2^32-1);
    KRange e_W 0 (2^63-1);
    KWord (SA e_mt 32) 8 e_W;
    KWord (SA (ELit 0) 614116) 4 e_ctr;
    KWr (SA e_mt 32) (ELit 8);
    KWr (SA (ELit 0) 614116) (ELit 4);
    KDisj (SA e_mt 32) (ELit 8) (SA (ELit 0) 614116) (ELit 4) ].
Definition scr_ai0 : scripts := SCR [false] [] [].
Definition ss_ai0 := SS 0x529a4 sr_ai0 [] kn_ai0 39.
Definition RUN_ai0 := sym_exec SEGS 100 true [0x529f8] scr_ai0 ss_ai0 [].

Definition scr_pai0 : scripts := SCR [false] [] [].
Definition RES_pai0 := Eval vm_compute in sym_exec SEGS 100 true [0x529f8] scr_pai0 ss_ai0 [].
Lemma RES_pai0_ok : sym_exec SEGS 100 true [0x529f8] scr_pai0 (SS 0x529a4 sr_ai0 [] kn_ai0 39) [] = RES_pai0.
Proof. vm_compute. reflexivity. Qed.
End AXF_ai0.

Module AXF_ai0z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ AxTry.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section AI0.
Context {fx : FPState}.

Definition VALS_ai0 (mem mt len size cnt ctr W : Z) : list Z := [mem; mt; len; size; cnt; ctr; W].

Record ai0_pre (regs : bvmap 5 word) (m : word -> option byte) (mem mt len size cnt ctr W : Z) : Prop := {
  ai0_R9 : getr regs 9 = wa mt ;
  ai0_R10 : getr regs 10 = wa mem ;
  ai0_R18 : getr regs 18 = wa 18446744073709551615 ;
  ai0_R19 : getr regs 19 = wa len ;
  ai0_R22 : getr regs 22 = wa 614096 ;
  ai0_R24 : getr regs 24 = wa size ;
  ai0_R25 : getr regs 25 = wa cnt ;
  ai0_rng_mem : 4096 <= mem <= 2^47 ;
  ai0_rng_mt : 1 <= mt <= 2^63-1 ;
  ai0_rng_len : 4096 <= len <= 2^40 ;
  ai0_rng_size : 4081 <= size <= 131056 ;
  ai0_rng_cnt : 1 <= cnt <= 32 ;
  ai0_rng_ctr : 0 <= ctr <= 2^32-1 ;
  ai0_rng_W : 0 <= W <= 2^63-1 ;
  ai0_ka2 : mt mod 8 = 0 ;
  ai0_kw8 : rdn SEGS m (wa (mt + 32)) 8 = Some (word_to_le_bytes 8 (wa W)) ;
  ai0_kw9 : rdn SEGS m (wa (0 + 614116)) 4 = Some (word_to_le_bytes 4 (wa ctr)) ;
  ai0_kwr10 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (mt + 32 + d)) k = true ;
  ai0_kwr11 : forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (0 + 614116 + d)) k = true ;
  ai0_kd12 : mt + 32 + 8 <= 0 + 614116 \/ 0 + 614116 + 4 <= mt + 32
}.


#[using="Type"] Lemma ai0_setup : forall regs m mem mt len size cnt ctr W, ai0_pre regs m mem mt len size cnt ctr W ->
  regs_ok (Ez regs (VALS_ai0 mem mt len size cnt ctr W)) AXF_ai0.sr_ai0 regs /\ know_ok SEGS (Ez regs (VALS_ai0 mem mt len size cnt ctr W)) m AXF_ai0.kn_ai0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m mem mt len size cnt ctr W P. destruct P as [ai0_R9 ai0_R10 ai0_R18 ai0_R19 ai0_R22 ai0_R24 ai0_R25 ai0_rng_mem ai0_rng_mt ai0_rng_len ai0_rng_size ai0_rng_cnt ai0_rng_ctr ai0_rng_W ai0_ka2 ai0_kw8 ai0_kw9 ai0_kwr10 ai0_kwr11 ai0_kd12].
  set (E := Ez regs (VALS_ai0 mem mt len size cnt ctr W)).
  assert (Z32 : bv_unsigned (ev E 32) = mem) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = mt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = len) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = size) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = ctr) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_ai0.sr_ai0.
    apply (regs_ok_pin E _ regs 25); [apply (regs_ok_pin E _ regs 24); [apply (regs_ok_pin E _ regs 22); [apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply regs_ok_id|]|]|]|]|]|]|].
    - rewrite ai0_R9. reflexivity.
    - rewrite ai0_R10. reflexivity.
    - rewrite ai0_R18. reflexivity.
    - rewrite ai0_R19. reflexivity.
    - rewrite ai0_R22. reflexivity.
    - rewrite ai0_R24. reflexivity.
    - rewrite ai0_R25. reflexivity. }
  unfold know_ok, AXF_ai0.kn_ai0.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_ai0.e_mem AXF_ai0.e_mt AXF_ai0.e_len AXF_ai0.e_size AXF_ai0.e_cnt AXF_ai0.e_ctr AXF_ai0.e_W a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range mem _ _ ai0_rng_mem eq_refl eq_refl), ?(mod64_of_range mt _ _ ai0_rng_mt eq_refl eq_refl), ?(mod64_of_range len _ _ ai0_rng_len eq_refl eq_refl), ?(mod64_of_range size _ _ ai0_rng_size eq_refl eq_refl), ?(mod64_of_range cnt _ _ ai0_rng_cnt eq_refl eq_refl), ?(mod64_of_range ctr _ _ ai0_rng_ctr eq_refl eq_refl), ?(mod64_of_range W _ _ ai0_rng_W eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply ai0_kwr10 | apply ai0_kwr11]; assumption).
  all: try (clear - ai0_rng_mem ai0_rng_mt ai0_rng_len ai0_rng_size ai0_rng_cnt ai0_rng_ctr ai0_rng_W ai0_ka2; lia).
  all: first [(clear - ai0_rng_mem ai0_rng_mt ai0_rng_len ai0_rng_size ai0_rng_cnt ai0_rng_ctr ai0_rng_W ai0_ka2 ai0_kd12; lia) | lia].
Qed.


Definition ai0_mem_pai0 (m : word -> option byte) (regs : bvmap 5 word) (mem mt len size cnt ctr W : Z) : word -> option byte :=
  wbytes (wbytes (m) (wa (mt + 32)) (word_to_le_bytes 8 (wa (Z.lor ((Z.shiftr (((4503599627370496 * W)) mod 2^64) 52) mod 2^64) (((4096 * Z.shiftr len 12)) mod 2^64))))) (wa (0 + 614116)) (word_to_le_bytes 4 (wa (ext_Z true 0 4 ctr + 1))).

#[using="Type"] Theorem ai0_pai0 : forall regs m rom mem mt len size cnt ctr W, ai0_pre regs m mem mt len size cnt ctr W ->
  scs_denot SEGS m (Ez regs (VALS_ai0 mem mt len size cnt ctr W)) (snd (fst AXF_ai0.RES_pai0)) ->
  exists R, msteps SEGS (mkst regs (wa 0x529a4) m rom) (mkst R (wa 0x529f8) (ai0_mem_pai0 m regs mem mt len size cnt ctr W) rom) /\
    getr R 9 = wa mt /\ getr R 10 = wa mem /\ getr R 11 = wa (cnt + -1) /\ getr R 12 = wa 0 /\ getr R 13 = wa (4096 * Z.shiftr len 12) /\ getr R 14 = wa (ext_Z true 0 4 ctr + 1) /\ getr R 18 = wa 18446744073709551615 /\ getr R 19 = wa len /\ getr R 22 = wa 614096 /\ getr R 24 = wa size /\ getr R 25 = wa cnt /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 15; 16; 17; 20; 21; 23; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom mem mt len size cnt ctr W P Hsc. destruct (ai0_setup regs m mem mt len size cnt ctr W P) as [HR HK].
  set (E := Ez regs (VALS_ai0 mem mt len size cnt ctr W)) in *. destruct P as [ai0_R9 ai0_R10 ai0_R18 ai0_R19 ai0_R22 ai0_R24 ai0_R25 ai0_rng_mem ai0_rng_mt ai0_rng_len ai0_rng_size ai0_rng_cnt ai0_rng_ctr ai0_rng_W ai0_ka2 ai0_kw8 ai0_kw9 ai0_kwr10 ai0_kwr11 ai0_kd12].
  assert (Z32 : bv_unsigned (ev E 32) = mem) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = mt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = len) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = size) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = ctr) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x529f8] AXF_ai0.scr_pai0 0x529a4 AXF_ai0.sr_ai0 AXF_ai0.kn_ai0 39 _ _ _ E m rom regs AXF_ai0.RES_pai0_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_ai0.RES_pai0 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (ai0_mem_pai0 m regs mem mt len size cnt ctr W) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold ai0_mem_pai0. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; assert (D : mul_div M_DIVU (Z_to_bv 64 4080) (ev E 35) = Z_to_bv 64 0) by (apply bv_eq; rewrite (divu_lit _ size 4080 Z35) by lia; rewrite Z.div_small by lia; reflexivity); rewrite !D; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; assert (D : mul_div M_DIVU (Z_to_bv 64 4080) (ev E 35) = Z_to_bv 64 0) by (apply bv_eq; rewrite (divu_lit _ size 4080 Z35) by lia; rewrite Z.div_small by lia; reflexivity); rewrite !D; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; assert (D : mul_div M_DIVU (Z_to_bv 64 4080) (ev E 35) = Z_to_bv 64 0) by (apply bv_eq; rewrite (divu_lit _ size 4080 Z35) by lia; rewrite Z.div_small by lia; reflexivity); rewrite !D; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; assert (D : mul_div M_DIVU (Z_to_bv 64 4080) (ev E 35) = Z_to_bv 64 0) by (apply bv_eq; rewrite (divu_lit _ size 4080 Z35) by lia; rewrite Z.div_small by lia; reflexivity); rewrite !D; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; assert (D : mul_div M_DIVU (Z_to_bv 64 4080) (ev E 35) = Z_to_bv 64 0) by (apply bv_eq; rewrite (divu_lit _ size 4080 Z35) by lia; rewrite Z.div_small by lia; reflexivity); rewrite !D; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; assert (D : mul_div M_DIVU (Z_to_bv 64 4080) (ev E 35) = Z_to_bv 64 0) by (apply bv_eq; rewrite (divu_lit _ size 4080 Z35) by lia; rewrite Z.div_small by lia; reflexivity); rewrite !D; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; assert (D : mul_div M_DIVU (Z_to_bv 64 4080) (ev E 35) = Z_to_bv 64 0) by (apply bv_eq; rewrite (divu_lit _ size 4080 Z35) by lia; rewrite Z.div_small by lia; reflexivity); rewrite !D; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; assert (D : mul_div M_DIVU (Z_to_bv 64 4080) (ev E 35) = Z_to_bv 64 0) by (apply bv_eq; rewrite (divu_lit _ size 4080 Z35) by lia; rewrite Z.div_small by lia; reflexivity); rewrite !D; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; assert (D : mul_div M_DIVU (Z_to_bv 64 4080) (ev E 35) = Z_to_bv 64 0) by (apply bv_eq; rewrite (divu_lit _ size 4080 Z35) by lia; rewrite Z.div_small by lia; reflexivity); rewrite !D; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; assert (D : mul_div M_DIVU (Z_to_bv 64 4080) (ev E 35) = Z_to_bv 64 0) by (apply bv_eq; rewrite (divu_lit _ size 4080 Z35) by lia; rewrite Z.div_small by lia; reflexivity); rewrite !D; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; assert (D : mul_div M_DIVU (Z_to_bv 64 4080) (ev E 35) = Z_to_bv 64 0) by (apply bv_eq; rewrite (divu_lit _ size 4080 Z35) by lia; rewrite Z.div_small by lia; reflexivity); rewrite !D; reflexivity)]|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End AI0.
End AXF_ai0z.

Module AXF_aiz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ AxTry.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section AI.
Context {fx : FPState}.

Definition VALS_ai (mem mt len size cnt ctr W : Z) : list Z := [mem; mt; len; size; cnt; ctr; W].

Record ai_pre (regs : bvmap 5 word) (m : word -> option byte) (mem mt len size cnt ctr W : Z) : Prop := {
  ai_R9 : getr regs 9 = wa mt ;
  ai_R10 : getr regs 10 = wa mem ;
  ai_R18 : getr regs 18 = wa 18446744073709551615 ;
  ai_R19 : getr regs 19 = wa len ;
  ai_R22 : getr regs 22 = wa 614096 ;
  ai_R24 : getr regs 24 = wa size ;
  ai_R25 : getr regs 25 = wa cnt ;
  ai_rng_mem : 4096 <= mem <= 2^47 ;
  ai_rng_mt : 1 <= mt <= 2^63-1 ;
  ai_rng_len : 4096 <= len <= 2^40 ;
  ai_rng_size : 16 <= size <= 4080 ;
  ai_rng_cnt : 1 <= cnt <= 32 ;
  ai_rng_ctr : 0 <= ctr <= 2^32-1 ;
  ai_rng_W : 0 <= W <= 2^63-1 ;
  ai_ka2 : mt mod 8 = 0 ;
  ai_kw8 : rdn SEGS m (wa (mt + 32)) 8 = Some (word_to_le_bytes 8 (wa W)) ;
  ai_kw9 : rdn SEGS m (wa (0 + 614116)) 4 = Some (word_to_le_bytes 4 (wa ctr)) ;
  ai_kwr10 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (mt + 32 + d)) k = true ;
  ai_kwr11 : forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (0 + 614116 + d)) k = true ;
  ai_kd12 : mt + 32 + 8 <= 0 + 614116 \/ 0 + 614116 + 4 <= mt + 32
}.


#[using="Type"] Lemma ai_setup : forall regs m mem mt len size cnt ctr W, ai_pre regs m mem mt len size cnt ctr W ->
  regs_ok (Ez regs (VALS_ai mem mt len size cnt ctr W)) AXF_ai.sr_ai regs /\ know_ok SEGS (Ez regs (VALS_ai mem mt len size cnt ctr W)) m AXF_ai.kn_ai.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m mem mt len size cnt ctr W P. destruct P as [ai_R9 ai_R10 ai_R18 ai_R19 ai_R22 ai_R24 ai_R25 ai_rng_mem ai_rng_mt ai_rng_len ai_rng_size ai_rng_cnt ai_rng_ctr ai_rng_W ai_ka2 ai_kw8 ai_kw9 ai_kwr10 ai_kwr11 ai_kd12].
  set (E := Ez regs (VALS_ai mem mt len size cnt ctr W)).
  assert (Z32 : bv_unsigned (ev E 32) = mem) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = mt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = len) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = size) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = ctr) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_ai.sr_ai.
    apply (regs_ok_pin E _ regs 25); [apply (regs_ok_pin E _ regs 24); [apply (regs_ok_pin E _ regs 22); [apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply regs_ok_id|]|]|]|]|]|]|].
    - rewrite ai_R9. reflexivity.
    - rewrite ai_R10. reflexivity.
    - rewrite ai_R18. reflexivity.
    - rewrite ai_R19. reflexivity.
    - rewrite ai_R22. reflexivity.
    - rewrite ai_R24. reflexivity.
    - rewrite ai_R25. reflexivity. }
  unfold know_ok, AXF_ai.kn_ai.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_ai.e_mem AXF_ai.e_mt AXF_ai.e_len AXF_ai.e_size AXF_ai.e_cnt AXF_ai.e_ctr AXF_ai.e_W a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range mem _ _ ai_rng_mem eq_refl eq_refl), ?(mod64_of_range mt _ _ ai_rng_mt eq_refl eq_refl), ?(mod64_of_range len _ _ ai_rng_len eq_refl eq_refl), ?(mod64_of_range size _ _ ai_rng_size eq_refl eq_refl), ?(mod64_of_range cnt _ _ ai_rng_cnt eq_refl eq_refl), ?(mod64_of_range ctr _ _ ai_rng_ctr eq_refl eq_refl), ?(mod64_of_range W _ _ ai_rng_W eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply ai_kwr10 | apply ai_kwr11]; assumption).
  all: try (clear - ai_rng_mem ai_rng_mt ai_rng_len ai_rng_size ai_rng_cnt ai_rng_ctr ai_rng_W ai_ka2; lia).
  all: first [(clear - ai_rng_mem ai_rng_mt ai_rng_len ai_rng_size ai_rng_cnt ai_rng_ctr ai_rng_W ai_ka2 ai_kd12; lia) | lia].
Qed.


Definition ai_mem_pail (m : word -> option byte) (regs : bvmap 5 word) (mem mt len size cnt ctr W : Z) : word -> option byte :=
  wbytes (wbytes (m) (wa (mt + 32)) (word_to_le_bytes 8 (wa (Z.lor ((Z.shiftr (((4503599627370496 * W)) mod 2^64) 52) mod 2^64) (((4096 * Z.shiftr len 12)) mod 2^64))))) (wa (0 + 614116)) (word_to_le_bytes 4 (wa (ext_Z true 0 4 ctr + 1))).

#[using="Type"] Theorem ai_pail : forall regs m rom mem mt len size cnt ctr W, ai_pre regs m mem mt len size cnt ctr W ->
  scs_denot SEGS m (Ez regs (VALS_ai mem mt len size cnt ctr W)) (snd (fst AXF_ai.RES_pail)) ->
  exists R, msteps SEGS (mkst regs (wa 0x529a4) m rom) (mkst R (wa 0x529f8) (ai_mem_pail m regs mem mt len size cnt ctr W) rom) /\
    getr R 9 = wa mt /\ getr R 10 = wa mem /\ getr R 11 = wa (cnt + -1) /\ getr R 12 = wa (cnt + -1) /\ getr R 13 = wa (4096 * Z.shiftr len 12) /\ getr R 14 = wa (ext_Z true 0 4 ctr + 1) /\ getr R 18 = wa 18446744073709551615 /\ getr R 19 = wa len /\ getr R 22 = wa 614096 /\ getr R 24 = wa size /\ getr R 25 = wa cnt /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 15; 16; 17; 20; 21; 23; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom mem mt len size cnt ctr W P Hsc. destruct (ai_setup regs m mem mt len size cnt ctr W P) as [HR HK].
  set (E := Ez regs (VALS_ai mem mt len size cnt ctr W)) in *. destruct P as [ai_R9 ai_R10 ai_R18 ai_R19 ai_R22 ai_R24 ai_R25 ai_rng_mem ai_rng_mt ai_rng_len ai_rng_size ai_rng_cnt ai_rng_ctr ai_rng_W ai_ka2 ai_kw8 ai_kw9 ai_kwr10 ai_kwr11 ai_kd12].
  assert (Z32 : bv_unsigned (ev E 32) = mem) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = mt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = len) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = size) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = ctr) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x529f8] AXF_ai.scr_pail 0x529a4 AXF_ai.sr_ai AXF_ai.kn_ai 39 _ _ _ E m rom regs AXF_ai.RES_pail_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_ai.RES_pail fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (ai_mem_pail m regs mem mt len size cnt ctr W) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold ai_mem_pail. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (divu_lit _ size 4080 Z35) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (divu_lit _ size 4080 Z35) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (divu_lit _ size 4080 Z35) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (divu_lit _ size 4080 Z35) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (divu_lit _ size 4080 Z35) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (divu_lit _ size 4080 Z35) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (divu_lit _ size 4080 Z35) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (divu_lit _ size 4080 Z35) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (divu_lit _ size 4080 Z35) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (divu_lit _ size 4080 Z35) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (divu_lit _ size 4080 Z35) by lia; reflexivity)]|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition ai_mem_paig (m : word -> option byte) (regs : bvmap 5 word) (mem mt len size cnt ctr W : Z) : word -> option byte :=
  wbytes (wbytes (m) (wa (mt + 32)) (word_to_le_bytes 8 (wa (Z.lor ((Z.shiftr (((4503599627370496 * W)) mod 2^64) 52) mod 2^64) (((4096 * Z.shiftr len 12)) mod 2^64))))) (wa (0 + 614116)) (word_to_le_bytes 4 (wa (ext_Z true 0 4 ctr + 1))).

#[using="Type"] Theorem ai_paig : forall regs m rom mem mt len size cnt ctr W, ai_pre regs m mem mt len size cnt ctr W ->
  scs_denot SEGS m (Ez regs (VALS_ai mem mt len size cnt ctr W)) (snd (fst AXF_ai.RES_paig)) ->
  exists R, msteps SEGS (mkst regs (wa 0x529a4) m rom) (mkst R (wa 0x529f8) (ai_mem_paig m regs mem mt len size cnt ctr W) rom) /\
    getr R 9 = wa mt /\ getr R 10 = wa mem /\ getr R 11 = wa (cnt + -1) /\ getr R 12 = wa (4080 / size + -1) /\ getr R 13 = wa (4096 * Z.shiftr len 12) /\ getr R 14 = wa (ext_Z true 0 4 ctr + 1) /\ getr R 18 = wa 18446744073709551615 /\ getr R 19 = wa len /\ getr R 22 = wa 614096 /\ getr R 24 = wa size /\ getr R 25 = wa cnt /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 15; 16; 17; 20; 21; 23; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom mem mt len size cnt ctr W P Hsc. destruct (ai_setup regs m mem mt len size cnt ctr W P) as [HR HK].
  set (E := Ez regs (VALS_ai mem mt len size cnt ctr W)) in *. destruct P as [ai_R9 ai_R10 ai_R18 ai_R19 ai_R22 ai_R24 ai_R25 ai_rng_mem ai_rng_mt ai_rng_len ai_rng_size ai_rng_cnt ai_rng_ctr ai_rng_W ai_ka2 ai_kw8 ai_kw9 ai_kwr10 ai_kwr11 ai_kd12].
  assert (Z32 : bv_unsigned (ev E 32) = mem) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = mt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = len) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = size) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = ctr) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x529f8] AXF_ai.scr_paig 0x529a4 AXF_ai.sr_ai AXF_ai.kn_ai 39 _ _ _ E m rom regs AXF_ai.RES_paig_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_ai.RES_paig fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (ai_mem_paig m regs mem mt len size cnt ctr W) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold ai_mem_paig. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (divu_lit _ size 4080 Z35) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (divu_lit _ size 4080 Z35) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (divu_lit _ size 4080 Z35) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (divu_lit _ size 4080 Z35) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (divu_lit _ size 4080 Z35) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (divu_lit _ size 4080 Z35) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (divu_lit _ size 4080 Z35) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (divu_lit _ size 4080 Z35) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (divu_lit _ size 4080 Z35) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (divu_lit _ size 4080 Z35) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (divu_lit _ size 4080 Z35) by lia; reflexivity)]|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End AI.
End AXF_aiz.

Module AXF_asrn.
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

Definition e_d := EVar 32.
Definition sr_asrn := (sr_upd sr_id 1 (ELit 337616)).
Definition kn_asrn : list kentry :=
  [  ].
Definition scr_asrn : scripts := SCR [] [] [].
Definition ss_asrn := SS 0x52b8c sr_asrn [] kn_asrn 33.
Definition RUN_asrn := sym_exec SEGS 10 true [0x526d0] scr_asrn ss_asrn [].

Definition scr_pasrn : scripts := SCR [] [] [].
Definition RES_pasrn := Eval vm_compute in sym_exec SEGS 10 true [0x526d0] scr_pasrn ss_asrn [].
Lemma RES_pasrn_ok : sym_exec SEGS 10 true [0x526d0] scr_pasrn (SS 0x52b8c sr_asrn [] kn_asrn 33) [] = RES_pasrn.
Proof. vm_compute. reflexivity. Qed.
End AXF_asrn.

Module AXF_asrnz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section ASRN.
Context {fx : FPState}.

Definition VALS_asrn (d : Z) : list Z := [d].

Record asrn_pre (regs : bvmap 5 word) (m : word -> option byte) (d : Z) : Prop := {
  asrn_R1 : getr regs 1 = wa 337616 ;
  asrn_rng_d : 0 <= d <= 1
}.


#[using="Type"] Lemma asrn_setup : forall regs m d, asrn_pre regs m d ->
  regs_ok (Ez regs (VALS_asrn d)) AXF_asrn.sr_asrn regs /\ know_ok SEGS (Ez regs (VALS_asrn d)) m AXF_asrn.kn_asrn.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m d P. destruct P as [asrn_R1 asrn_rng_d].
  set (E := Ez regs (VALS_asrn d)).
  assert (Z32 : bv_unsigned (ev E 32) = d) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_asrn.sr_asrn.
    apply (regs_ok_pin E _ regs 1); [apply regs_ok_id|].
    - rewrite asrn_R1. reflexivity. }
  unfold know_ok, AXF_asrn.kn_asrn.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ apply kword_z | apply krange_z | apply kalign_z | apply kdisj_z | apply kwr_z ].
  all: cbn [zeval edenot AXF_asrn.e_d a_base a_off].
  all: rewrite ?Z32.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range d _ _ asrn_rng_d eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - asrn_rng_d; lia).
  all: first [lia].
Qed.


Definition asrn_mem_pasrn (m : word -> option byte) (regs : bvmap 5 word) (d : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem asrn_pasrn : forall regs m rom d, asrn_pre regs m d ->
  scs_denot SEGS m (Ez regs (VALS_asrn d)) (snd (fst AXF_asrn.RES_pasrn)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52b8c) m rom) (mkst R (wa 0x526d0) (asrn_mem_pasrn m regs d) rom) /\
    getr R 1 = wa 337616 /\ (forall k, In k [2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom d P Hsc. destruct (asrn_setup regs m d P) as [HR HK].
  set (E := Ez regs (VALS_asrn d)) in *. destruct P as [asrn_R1 asrn_rng_d].
  assert (Z32 : bv_unsigned (ev E 32) = d) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 10 [0x526d0] AXF_asrn.scr_pasrn 0x52b8c AXF_asrn.sr_asrn AXF_asrn.kn_asrn 33 _ _ _ E m rom regs AXF_asrn.RES_pasrn_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_asrn.RES_pasrn fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (asrn_mem_pasrn m regs d) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold asrn_mem_pasrn. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End ASRN.
End AXF_asrnz.

Module AXF_efrn.
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

Definition e_d := EVar 32.
Definition sr_efrn := (sr_upd sr_id 1 (ELit 337664)).
Definition kn_efrn : list kentry :=
  [  ].
Definition scr_efrn : scripts := SCR [] [] [].
Definition ss_efrn := SS 0x52ce0 sr_efrn [] kn_efrn 33.
Definition RUN_efrn := sym_exec SEGS 10 true [0x52700] scr_efrn ss_efrn [].

Definition scr_pefrn : scripts := SCR [] [] [].
Definition RES_pefrn := Eval vm_compute in sym_exec SEGS 10 true [0x52700] scr_pefrn ss_efrn [].
Lemma RES_pefrn_ok : sym_exec SEGS 10 true [0x52700] scr_pefrn (SS 0x52ce0 sr_efrn [] kn_efrn 33) [] = RES_pefrn.
Proof. vm_compute. reflexivity. Qed.
End AXF_efrn.

Module AXF_efrnz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section EFRN.
Context {fx : FPState}.

Definition VALS_efrn (d : Z) : list Z := [d].

Record efrn_pre (regs : bvmap 5 word) (m : word -> option byte) (d : Z) : Prop := {
  efrn_R1 : getr regs 1 = wa 337664 ;
  efrn_rng_d : 0 <= d <= 1
}.


#[using="Type"] Lemma efrn_setup : forall regs m d, efrn_pre regs m d ->
  regs_ok (Ez regs (VALS_efrn d)) AXF_efrn.sr_efrn regs /\ know_ok SEGS (Ez regs (VALS_efrn d)) m AXF_efrn.kn_efrn.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m d P. destruct P as [efrn_R1 efrn_rng_d].
  set (E := Ez regs (VALS_efrn d)).
  assert (Z32 : bv_unsigned (ev E 32) = d) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_efrn.sr_efrn.
    apply (regs_ok_pin E _ regs 1); [apply regs_ok_id|].
    - rewrite efrn_R1. reflexivity. }
  unfold know_ok, AXF_efrn.kn_efrn.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ apply kword_z | apply krange_z | apply kalign_z | apply kdisj_z | apply kwr_z ].
  all: cbn [zeval edenot AXF_efrn.e_d a_base a_off].
  all: rewrite ?Z32.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range d _ _ efrn_rng_d eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - efrn_rng_d; lia).
  all: first [lia].
Qed.


Definition efrn_mem_pefrn (m : word -> option byte) (regs : bvmap 5 word) (d : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem efrn_pefrn : forall regs m rom d, efrn_pre regs m d ->
  scs_denot SEGS m (Ez regs (VALS_efrn d)) (snd (fst AXF_efrn.RES_pefrn)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52ce0) m rom) (mkst R (wa 0x52700) (efrn_mem_pefrn m regs d) rom) /\
    getr R 1 = wa 337664 /\ (forall k, In k [2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom d P Hsc. destruct (efrn_setup regs m d P) as [HR HK].
  set (E := Ez regs (VALS_efrn d)) in *. destruct P as [efrn_R1 efrn_rng_d].
  assert (Z32 : bv_unsigned (ev E 32) = d) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 10 [0x52700] AXF_efrn.scr_pefrn 0x52ce0 AXF_efrn.sr_efrn AXF_efrn.kn_efrn 33 _ _ _ E m rom regs AXF_efrn.RES_pefrn_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_efrn.RES_pefrn fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (efrn_mem_pefrn m regs d) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold efrn_mem_pefrn. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End EFRN.
End AXF_efrnz.

Module AXF_ins1.
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

Definition e_mem := EVar 32.
Definition e_mt := EVar 33.
Definition e_sc := EVar 34.
Definition e_cnt := EVar 35.
Definition e_aidx := EVar 36.
Definition e_usage := EVar 37.
Definition e_W := EVar 38.
Definition e_hb := EVar 39.
Definition ACT := SA (EMd M_MUL (ELit 8) e_sc) 614184.
Definition USG := SA (EMd M_MUL (ELit 8) e_sc) 614568.
Definition sr_ins1 := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (e_sc)) 9 (e_mt)) 10 (e_mem)) 11 (EAlu ALU_ADD e_cnt (ELit (-1)))) 12 (e_aidx)) 21 (EAlu ALU_ADD (EMd M_MUL (ELit 8) e_sc) (ELit 614184))) 23 (EAlu ALU_ADD (EMd M_MUL (ELit 8) e_sc) (ELit 614096))) 25 (e_cnt)).
Definition kn_ins1 : list kentry :=
  [ KRange e_mem 4096 (2^47);
    KAlign e_mem 16;
    KRange e_mt 1 (2^63-1);
    KAlign e_mt 8;
    KRange e_sc 0 47;
    KRange e_cnt 1 32;
    KRange e_aidx 0 31;
    KRange e_usage 0 (2^60);
    KRange e_W 0 (2^63-1);
    KRange e_hb 0 255;
    KWord USG 8 e_usage;
    KWord (SA e_mt 32) 8 e_W;
    KWord (SA e_mem 8) 1 e_hb;
    KWord ACT 8 (ELit 0);
    KWord (SA e_mt 0) 8 (ELit 0);
    KWord (SA e_mt 8) 8 (ELit 0);
    KWr USG (ELit 8);
    KWr (SA e_mt 0) (ELit 40);
    KWr (SA e_mem 0) (ELit 9);
    KWr ACT (ELit 8);
    KDisj USG (ELit 8) (SA e_mt 0) (ELit 40);
    KDisj USG (ELit 8) (SA e_mem 0) (ELit 9);
    KDisj (SA e_mt 0) (ELit 40) (SA e_mem 0) (ELit 9);
    KDisj ACT (ELit 8) (SA e_mt 0) (ELit 40);
    KDisj ACT (ELit 8) (SA e_mem 0) (ELit 9);
    KDisj ACT (ELit 8) USG (ELit 8) ].
Definition scr_ins1 : scripts := SCR [] [] [].
Definition ss_ins1 := SS 0x529f8 sr_ins1 [] kn_ins1 40.
Definition RUN_ins1 := sym_exec SEGS 200 true [0x52a70] scr_ins1 ss_ins1 [].

Definition scr_pins1 : scripts := SCR [] [] [].
Definition RES_pins1 := Eval vm_compute in sym_exec SEGS 200 true [0x52a70] scr_pins1 ss_ins1 [].
Lemma RES_pins1_ok : sym_exec SEGS 200 true [0x52a70] scr_pins1 (SS 0x529f8 sr_ins1 [] kn_ins1 40) [] = RES_pins1.
Proof. vm_compute. reflexivity. Qed.
End AXF_ins1.

Module AXF_ins1z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ AxTry.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section INS1.
Context {fx : FPState}.

Definition VALS_ins1 (mem mt sc cnt aidx usage W hb : Z) : list Z := [mem; mt; sc; cnt; aidx; usage; W; hb].

Record ins1_pre (regs : bvmap 5 word) (m : word -> option byte) (mem mt sc cnt aidx usage W hb : Z) : Prop := {
  ins1_R8 : getr regs 8 = wa sc ;
  ins1_R9 : getr regs 9 = wa mt ;
  ins1_R10 : getr regs 10 = wa mem ;
  ins1_R11 : getr regs 11 = wa (cnt + -1) ;
  ins1_R12 : getr regs 12 = wa aidx ;
  ins1_R21 : getr regs 21 = wa ((8 * sc) + 614184) ;
  ins1_R23 : getr regs 23 = wa ((8 * sc) + 614096) ;
  ins1_R25 : getr regs 25 = wa cnt ;
  ins1_rng_mem : 4096 <= mem <= 2^47 ;
  ins1_rng_mt : 1 <= mt <= 2^63-1 ;
  ins1_rng_sc : 0 <= sc <= 47 ;
  ins1_rng_cnt : 1 <= cnt <= 32 ;
  ins1_rng_aidx : 0 <= aidx <= 31 ;
  ins1_rng_usage : 0 <= usage <= 2^60 ;
  ins1_rng_W : 0 <= W <= 2^63-1 ;
  ins1_rng_hb : 0 <= hb <= 255 ;
  ins1_ka1 : mem mod 16 = 0 ;
  ins1_ka3 : mt mod 8 = 0 ;
  ins1_kw10 : rdn SEGS m (wa (8 * sc + 614568)) 8 = Some (word_to_le_bytes 8 (wa usage)) ;
  ins1_kw11 : rdn SEGS m (wa (mt + 32)) 8 = Some (word_to_le_bytes 8 (wa W)) ;
  ins1_kw12 : rdn SEGS m (wa (mem + 8)) 1 = Some (word_to_le_bytes 1 (wa hb)) ;
  ins1_kw13 : rdn SEGS m (wa (8 * sc + 614184)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  ins1_kw14 : rdn SEGS m (wa (mt + 0)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  ins1_kw15 : rdn SEGS m (wa (mt + 8)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  ins1_kwr16 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (8 * sc + 614568 + d)) k = true ;
  ins1_kwr17 : forall d k, 0 <= d -> d + Z.of_nat k <= 40 -> store_ok SEGS m (wa (mt + 0 + d)) k = true ;
  ins1_kwr18 : forall d k, 0 <= d -> d + Z.of_nat k <= 9 -> store_ok SEGS m (wa (mem + 0 + d)) k = true ;
  ins1_kwr19 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (8 * sc + 614184 + d)) k = true ;
  ins1_kd20 : 8 * sc + 614568 + 8 <= mt + 0 \/ mt + 0 + 40 <= 8 * sc + 614568 ;
  ins1_kd21 : 8 * sc + 614568 + 8 <= mem + 0 \/ mem + 0 + 9 <= 8 * sc + 614568 ;
  ins1_kd22 : mt + 0 + 40 <= mem + 0 \/ mem + 0 + 9 <= mt + 0 ;
  ins1_kd23 : 8 * sc + 614184 + 8 <= mt + 0 \/ mt + 0 + 40 <= 8 * sc + 614184 ;
  ins1_kd24 : 8 * sc + 614184 + 8 <= mem + 0 \/ mem + 0 + 9 <= 8 * sc + 614184 ;
  ins1_kd25 : 8 * sc + 614184 + 8 <= 8 * sc + 614568 \/ 8 * sc + 614568 + 8 <= 8 * sc + 614184
}.


#[using="Type"] Lemma ins1_setup : forall regs m mem mt sc cnt aidx usage W hb, ins1_pre regs m mem mt sc cnt aidx usage W hb ->
  regs_ok (Ez regs (VALS_ins1 mem mt sc cnt aidx usage W hb)) AXF_ins1.sr_ins1 regs /\ know_ok SEGS (Ez regs (VALS_ins1 mem mt sc cnt aidx usage W hb)) m AXF_ins1.kn_ins1.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m mem mt sc cnt aidx usage W hb P. destruct P as [ins1_R8 ins1_R9 ins1_R10 ins1_R11 ins1_R12 ins1_R21 ins1_R23 ins1_R25 ins1_rng_mem ins1_rng_mt ins1_rng_sc ins1_rng_cnt ins1_rng_aidx ins1_rng_usage ins1_rng_W ins1_rng_hb ins1_ka1 ins1_ka3 ins1_kw10 ins1_kw11 ins1_kw12 ins1_kw13 ins1_kw14 ins1_kw15 ins1_kwr16 ins1_kwr17 ins1_kwr18 ins1_kwr19 ins1_kd20 ins1_kd21 ins1_kd22 ins1_kd23 ins1_kd24 ins1_kd25].
  set (E := Ez regs (VALS_ins1 mem mt sc cnt aidx usage W hb)).
  assert (Z32 : bv_unsigned (ev E 32) = mem) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = mt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = aidx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = usage) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = hb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_ins1.sr_ins1.
    apply (regs_ok_pin E _ regs 25); [apply (regs_ok_pin E _ regs 23); [apply (regs_ok_pin E _ regs 21); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|]|]|]|]|]|].
    - rewrite ins1_R8. reflexivity.
    - rewrite ins1_R9. reflexivity.
    - rewrite ins1_R10. reflexivity.
    - rewrite ins1_R11, zeval_sound. cbn [zeval edenot AXF_ins1.e_mem AXF_ins1.e_mt AXF_ins1.e_sc AXF_ins1.e_cnt AXF_ins1.e_aidx AXF_ins1.e_usage AXF_ins1.e_W AXF_ins1.e_hb AXF_ins1.ACT AXF_ins1.USG]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite ins1_R12. reflexivity.
    - rewrite ins1_R21, zeval_sound. cbn [zeval edenot AXF_ins1.e_mem AXF_ins1.e_mt AXF_ins1.e_sc AXF_ins1.e_cnt AXF_ins1.e_aidx AXF_ins1.e_usage AXF_ins1.e_W AXF_ins1.e_hb AXF_ins1.ACT AXF_ins1.USG]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite ins1_R23, zeval_sound. cbn [zeval edenot AXF_ins1.e_mem AXF_ins1.e_mt AXF_ins1.e_sc AXF_ins1.e_cnt AXF_ins1.e_aidx AXF_ins1.e_usage AXF_ins1.e_W AXF_ins1.e_hb AXF_ins1.ACT AXF_ins1.USG]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite ins1_R25. reflexivity. }
  unfold know_ok, AXF_ins1.kn_ins1.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_ins1.e_mem AXF_ins1.e_mt AXF_ins1.e_sc AXF_ins1.e_cnt AXF_ins1.e_aidx AXF_ins1.e_usage AXF_ins1.e_W AXF_ins1.e_hb AXF_ins1.ACT AXF_ins1.USG a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range mem _ _ ins1_rng_mem eq_refl eq_refl), ?(mod64_of_range mt _ _ ins1_rng_mt eq_refl eq_refl), ?(mod64_of_range sc _ _ ins1_rng_sc eq_refl eq_refl), ?(mod64_of_range cnt _ _ ins1_rng_cnt eq_refl eq_refl), ?(mod64_of_range aidx _ _ ins1_rng_aidx eq_refl eq_refl), ?(mod64_of_range usage _ _ ins1_rng_usage eq_refl eq_refl), ?(mod64_of_range W _ _ ins1_rng_W eq_refl eq_refl), ?(mod64_of_range hb _ _ ins1_rng_hb eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply ins1_kwr16 | apply ins1_kwr17 | apply ins1_kwr18 | apply ins1_kwr19]; assumption).
  all: try (clear - ins1_rng_mem ins1_rng_mt ins1_rng_sc ins1_rng_cnt ins1_rng_aidx ins1_rng_usage ins1_rng_W ins1_rng_hb ins1_ka1 ins1_ka3; lia).
  all: first [(clear - ins1_rng_mem ins1_rng_mt ins1_rng_sc ins1_rng_cnt ins1_rng_aidx ins1_rng_usage ins1_rng_W ins1_rng_hb ins1_ka1 ins1_ka3 ins1_kd20; lia) | (clear - ins1_rng_mem ins1_rng_mt ins1_rng_sc ins1_rng_cnt ins1_rng_aidx ins1_rng_usage ins1_rng_W ins1_rng_hb ins1_ka1 ins1_ka3 ins1_kd21; lia) | (clear - ins1_rng_mem ins1_rng_mt ins1_rng_sc ins1_rng_cnt ins1_rng_aidx ins1_rng_usage ins1_rng_W ins1_rng_hb ins1_ka1 ins1_ka3 ins1_kd22; lia) | (clear - ins1_rng_mem ins1_rng_mt ins1_rng_sc ins1_rng_cnt ins1_rng_aidx ins1_rng_usage ins1_rng_W ins1_rng_hb ins1_ka1 ins1_ka3 ins1_kd23; lia) | (clear - ins1_rng_mem ins1_rng_mt ins1_rng_sc ins1_rng_cnt ins1_rng_aidx ins1_rng_usage ins1_rng_W ins1_rng_hb ins1_ka1 ins1_ka3 ins1_kd24; lia) | (clear - ins1_rng_mem ins1_rng_mt ins1_rng_sc ins1_rng_cnt ins1_rng_aidx ins1_rng_usage ins1_rng_W ins1_rng_hb ins1_ka1 ins1_ka3 ins1_kd25; lia) | lia].
Qed.


Definition ins1_mem_pins1 (m : word -> option byte) (regs : bvmap 5 word) (mem mt sc cnt aidx usage W hb : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (8 * sc + 614568)) (word_to_le_bytes 8 (wa (cnt + usage)))) (wa (mt + 24)) (word_to_le_bytes 4 (wa (2 ^ (aidx + 1) - 1)))) (wa (mt + 28)) (word_to_le_bytes 4 (wa ((2 ^ cnt - 1) - (2 ^ (aidx + 1) - 1))))) (wa (mt + 16)) (word_to_le_bytes 8 (wa mem))) (wa (mem + 0)) (word_to_le_bytes 8 (wa mt))) (wa (mem + 8)) (word_to_le_bytes 1 (wa (aidx + (32 * Z.shiftr hb 5))))) (wa (mt + 32)) (word_to_le_bytes 8 (wa (((64 * sc) + (cnt + (4096 * Z.shiftr W 12))) + 31))).

#[using="Type"] Theorem ins1_pins1 : forall regs m rom mem mt sc cnt aidx usage W hb, ins1_pre regs m mem mt sc cnt aidx usage W hb ->
  scs_denot SEGS m (Ez regs (VALS_ins1 mem mt sc cnt aidx usage W hb)) (snd (fst AXF_ins1.RES_pins1)) ->
  exists R, msteps SEGS (mkst regs (wa 0x529f8) m rom) (mkst R (wa 0x52a70) (ins1_mem_pins1 m regs mem mt sc cnt aidx usage W hb) rom) /\
    getr R 8 = wa (64 * sc) /\ getr R 9 = wa mt /\ getr R 10 = wa (((64 * sc) + (cnt + (4096 * Z.shiftr W 12))) + 31) /\ getr R 11 = wa (((64 * sc) + cnt) + -1) /\ getr R 12 = wa 18446744073709547520 /\ getr R 13 = wa (32 * Z.shiftr hb 5) /\ getr R 21 = wa ((8 * sc) + 614184) /\ getr R 23 = wa ((8 * sc) + 614096) /\ getr R 25 = wa cnt /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 15; 16; 17; 18; 19; 20; 22; 24; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom mem mt sc cnt aidx usage W hb P Hsc. destruct (ins1_setup regs m mem mt sc cnt aidx usage W hb P) as [HR HK].
  set (E := Ez regs (VALS_ins1 mem mt sc cnt aidx usage W hb)) in *. destruct P as [ins1_R8 ins1_R9 ins1_R10 ins1_R11 ins1_R12 ins1_R21 ins1_R23 ins1_R25 ins1_rng_mem ins1_rng_mt ins1_rng_sc ins1_rng_cnt ins1_rng_aidx ins1_rng_usage ins1_rng_W ins1_rng_hb ins1_ka1 ins1_ka3 ins1_kw10 ins1_kw11 ins1_kw12 ins1_kw13 ins1_kw14 ins1_kw15 ins1_kwr16 ins1_kwr17 ins1_kwr18 ins1_kwr19 ins1_kd20 ins1_kd21 ins1_kd22 ins1_kd23 ins1_kd24 ins1_kd25].
  assert (Z32 : bv_unsigned (ev E 32) = mem) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = mt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = aidx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = usage) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = hb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 200 [0x52a70] AXF_ins1.scr_pins1 0x529f8 AXF_ins1.sr_ins1 AXF_ins1.kn_ins1 40 _ _ _ E m rom regs AXF_ins1.RES_pins1_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_ins1.RES_pins1 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (ins1_mem_pins1 m regs mem mt sc cnt aidx usage W hb) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold ins1_mem_pins1. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.
    all: try (rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; apply ins_avail_le; assumption).
    all: try (rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; apply ins_freed_le; assumption).
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

End INS1.
End AXF_ins1z.

Module AXF_nen.
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

Definition e_idx := EVar 32.
Definition e_j := EVar 33.
Definition e_g := EVar 34.
Definition e_units := EVar 35.
Definition e_ctr := EVar 36.
Definition sr_nen := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (e_idx)) 18 (e_j)) 22 (ELit 614096)) 25 (ELit 98984)).
Definition kn_nen : list kentry :=
  [ KRange e_idx 0 31;
    KRange e_j 0 47;
    KRange e_g 1 (2^63-1);
    KRange e_units 1 8191;
    KRange e_ctr 0 (2^32-1);
    KWord (SA (EMd M_MUL (ELit 8) e_j) 614184) 8 e_g;
    KWord (SA (EMd M_MUL (ELit 2) e_j) 98984) 2 e_units;
    KWord (SA (ELit 0) 614116) 4 e_ctr ].
Definition scr_nen : scripts := SCR [false] [] [].
Definition ss_nen := SS 0x526d0 sr_nen [] kn_nen 37.
Definition RUN_nen := sym_exec SEGS 100 true [0x52b94] scr_nen ss_nen [].

Definition scr_pnen : scripts := SCR [false] [] [].
Definition RES_pnen := Eval vm_compute in sym_exec SEGS 100 true [0x52b94] scr_pnen ss_nen [].
Lemma RES_pnen_ok : sym_exec SEGS 100 true [0x52b94] scr_pnen (SS 0x526d0 sr_nen [] kn_nen 37) [] = RES_pnen.
Proof. vm_compute. reflexivity. Qed.
End AXF_nen.

Module AXF_nenz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section NEN.
Context {fx : FPState}.

Definition VALS_nen (idx j g units ctr : Z) : list Z := [idx; j; g; units; ctr].

Record nen_pre (regs : bvmap 5 word) (m : word -> option byte) (idx j g units ctr : Z) : Prop := {
  nen_R10 : getr regs 10 = wa idx ;
  nen_R18 : getr regs 18 = wa j ;
  nen_R22 : getr regs 22 = wa 614096 ;
  nen_R25 : getr regs 25 = wa 98984 ;
  nen_rng_idx : 0 <= idx <= 31 ;
  nen_rng_j : 0 <= j <= 47 ;
  nen_rng_g : 1 <= g <= 2^63-1 ;
  nen_rng_units : 1 <= units <= 8191 ;
  nen_rng_ctr : 0 <= ctr <= 2^32-1 ;
  nen_kw5 : rdn SEGS m (wa (8 * j + 614184)) 8 = Some (word_to_le_bytes 8 (wa g)) ;
  nen_kw6 : rdn SEGS m (wa (2 * j + 98984)) 2 = Some (word_to_le_bytes 2 (wa units)) ;
  nen_kw7 : rdn SEGS m (wa (0 + 614116)) 4 = Some (word_to_le_bytes 4 (wa ctr))
}.


#[using="Type"] Lemma nen_setup : forall regs m idx j g units ctr, nen_pre regs m idx j g units ctr ->
  regs_ok (Ez regs (VALS_nen idx j g units ctr)) AXF_nen.sr_nen regs /\ know_ok SEGS (Ez regs (VALS_nen idx j g units ctr)) m AXF_nen.kn_nen.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m idx j g units ctr P. destruct P as [nen_R10 nen_R18 nen_R22 nen_R25 nen_rng_idx nen_rng_j nen_rng_g nen_rng_units nen_rng_ctr nen_kw5 nen_kw6 nen_kw7].
  set (E := Ez regs (VALS_nen idx j g units ctr)).
  assert (Z32 : bv_unsigned (ev E 32) = idx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = j) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = g) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = units) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = ctr) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_nen.sr_nen.
    apply (regs_ok_pin E _ regs 25); [apply (regs_ok_pin E _ regs 22); [apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|]|]|].
    - rewrite nen_R10. reflexivity.
    - rewrite nen_R18. reflexivity.
    - rewrite nen_R22. reflexivity.
    - rewrite nen_R25. reflexivity. }
  unfold know_ok, AXF_nen.kn_nen.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_nen.e_idx AXF_nen.e_j AXF_nen.e_g AXF_nen.e_units AXF_nen.e_ctr a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range idx _ _ nen_rng_idx eq_refl eq_refl), ?(mod64_of_range j _ _ nen_rng_j eq_refl eq_refl), ?(mod64_of_range g _ _ nen_rng_g eq_refl eq_refl), ?(mod64_of_range units _ _ nen_rng_units eq_refl eq_refl), ?(mod64_of_range ctr _ _ nen_rng_ctr eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - nen_rng_idx nen_rng_j nen_rng_g nen_rng_units nen_rng_ctr; lia).
  all: first [lia].
Qed.


Definition nen_mem_pnen (m : word -> option byte) (regs : bvmap 5 word) (idx j g units ctr : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem nen_pnen : forall regs m rom idx j g units ctr, nen_pre regs m idx j g units ctr ->
  scs_denot SEGS m (Ez regs (VALS_nen idx j g units ctr)) (snd (fst AXF_nen.RES_pnen)) ->
  exists R, msteps SEGS (mkst regs (wa 0x526d0) m rom) (mkst R (wa 0x52b94) (nen_mem_pnen m regs idx j g units ctr) rom) /\
    getr R 1 = wa 337664 /\ getr R 10 = wa g /\ getr R 11 = wa idx /\ getr R 12 = wa ((16 * units) + -4) /\ getr R 13 = wa (ext_Z true 0 4 ctr) /\ getr R 18 = wa ((2 * j) + 98984) /\ getr R 22 = wa 614096 /\ getr R 25 = wa 98984 /\ (forall k, In k [2; 3; 4; 5; 6; 7; 8; 9; 14; 15; 16; 17; 19; 20; 21; 23; 24; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom idx j g units ctr P Hsc. destruct (nen_setup regs m idx j g units ctr P) as [HR HK].
  set (E := Ez regs (VALS_nen idx j g units ctr)) in *. destruct P as [nen_R10 nen_R18 nen_R22 nen_R25 nen_rng_idx nen_rng_j nen_rng_g nen_rng_units nen_rng_ctr nen_kw5 nen_kw6 nen_kw7].
  assert (Z32 : bv_unsigned (ev E 32) = idx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = j) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = g) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = units) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = ctr) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x52b94] AXF_nen.scr_pnen 0x526d0 AXF_nen.sr_nen AXF_nen.kn_nen 37 _ _ _ E m rom regs AXF_nen.RES_pnen_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_nen.RES_pnen fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (nen_mem_pnen m regs idx j g units ctr) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold nen_mem_pnen. repeat (apply (f_equal3 wbytes)); try reflexivity.
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

End NEN.
End AXF_nenz.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition TABS (m : word -> option byte) : Prop :=
  (forall sc k, 0 <= sc <= 8 -> 0 <= k <= 2 ->
     rdn SEGS m (wa (3 * sc + (99080 + k))) 1 = Some (word_to_le_bytes 1 (wa (znth k (nth (Z.to_nat sc) small_cnt_tab []))))) /\
  (forall k, 0 <= k <= 3 -> rdn SEGS m (wa (k + 99107)) 1 = Some (word_to_le_bytes 1 (wa (znth k med_cnt_tab)))).

Ltac klist H := first [ AxSymRun3.klist_refl H | (cbn [In] in H |- *; repeat (destruct H as [<-|H]; [first [solve [first [ AxSymRun3.memb_refl | repeat first [ (left; reflexivity) | right ] ]] | (exfalso; congruence)] |]); destruct H) ].      (* [comment removed for export] *)
Ltac regk KK k := match goal with |- getr _ ?r0 = _ => replace r0 with (Z_to_bv 5 (Z.of_nat k)) by (apply bv_eq; reflexivity) end;
  rewrite (KK k ltac:(cbn [In]; repeat first [ (left; reflexivity) | right ])).
Ltac litr2 H := match type of H with getr _ ?r = _ => match goal with |- getr _ ?r0 = _ => replace r0 with r by (apply bv_eq; reflexivity) end end; rewrite H.

(* [comment removed for export] *)
Ltac scs_go := cbn [fst snd]; repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z;
  rewrite ?br_eq_z, ?br_ne_z, ?br_geu_z, ?br_ltu_z; cbn [zeval edenot].
Ltac zat R V n v := rewrite (zatom R V n v eq_refl eq_refl) by lia.
Ltac zats := repeat (match goal with |- context [bv_unsigned (ev (Ez ?R ?V) ?n)] =>
  let v := eval cbn in (nth (n - 32) V 0) in rewrite (zatom R V n v eq_refl eq_refl) by lia end).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma small_rows : forall sc, 0 <= sc <= 8 -> forall k, 0 <= k <= 2 -> 4 <= znth k (nth (Z.to_nat sc) small_cnt_tab []) <= 31.
Proof.
  intros sc Hsc k Hk. assert (E : sc = 0 \/ sc = 1 \/ sc = 2 \/ sc = 3 \/ sc = 4 \/ sc = 5 \/ sc = 6 \/ sc = 7 \/ sc = 8) by lia.
  assert (F : k = 0 \/ k = 1 \/ k = 2) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; destruct F as [->|[-> | ->]]; cbv; split; discriminate.
Qed.

Lemma med_row : forall sc, 0 <= sc -> 4 <= znth (Z.land sc 3) med_cnt_tab <= 32 /\ znth (Z.land sc 3) med_cnt_tab mod 2 = 0.
Proof.
  intros sc Hsc. pose proof (land3_bound sc) as B. assert (E : Z.land sc 3 = 0 \/ Z.land sc 3 = 1 \/ Z.land sc 3 = 2 \/ Z.land sc 3 = 3) by lia.
  destruct E as [E|[E|[E|E]]]; rewrite E; cbv; split; try reflexivity; split; discriminate.
Qed.

Lemma initial_small : forall sc usage, 0 <= sc <= 8 -> initial_cnt sc usage = small_cnt sc usage.
Proof.
  intros sc usage Hsc. unfold initial_cnt. replace (sc <? 9) with true by (symmetry; apply Z.ltb_lt; lia).
  assert (R : 4 <= small_cnt sc usage <= 31).
  { unfold small_cnt. pose proof (small_rows sc Hsc 0 ltac:(lia)). pose proof (small_rows sc Hsc 1 ltac:(lia)). pose proof (small_rows sc Hsc 2 ltac:(lia)).
    destruct (negb _); [lia|]. destruct (negb _); lia. }
  replace (small_cnt sc usage =? 1) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Lemma hwe_step_stop : forall n c u, u >= 4 * c -> halve_while_even (S n) c u = c.
Proof. intros n c u H. cbn [halve_while_even]. replace (u <? 4 * c) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r. reflexivity. Qed.

Lemma hwe_step_go : forall n c u, c mod 2 = 0 -> u < 4 * c -> halve_while_even (S n) c u = halve_while_even n (c / 2) u.
Proof.
  intros n c u Hc H. cbn [halve_while_even]. replace (u <? 4 * c) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (Z.even c) with true by (symmetry; apply Z.even_spec; apply Z.mod_divide in Hc; [|lia]; destruct Hc as (k & ->); exists k; ring). reflexivity.
Qed.

Lemma hwe_odd : forall n c u, c mod 2 = 1 -> halve_while_even (S n) c u = c.
Proof.
  intros n c u Hc. cbn [halve_while_even]. replace (Z.even c) with false; [reflexivity|].
  symmetry. apply Bool.not_true_iff_false. intros E. apply Z.even_spec in E. destruct E as (k & ->). rewrite Z.mul_comm, Z.mod_mul in Hc by lia. discriminate.
Qed.

Lemma hwb_step_stop : forall n c size, size * c < 2^20 -> halve_while_big (S n) c size = c.
Proof. intros n c size H. cbn [halve_while_big]. unfold UNIT. replace (65536 * 16 <=? size * c) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. Qed.

Lemma hwb_step_go : forall n c size, 2^20 <= size * c -> halve_while_big (S n) c size = halve_while_big n (c / 2) size.
Proof. intros n c size H. cbn [halve_while_big]. unfold UNIT. replace (65536 * 16 <=? size * c) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section LOOPS.
Context {fx : FPState}.

#[using="Type"] Lemma pow_succ_half : forall n c, 0 <= c <= 2 ^ Z.of_nat (S n) -> c / 2 <= 2 ^ Z.of_nat n.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n c H. rewrite Nat2Z.inj_succ, Z.pow_succ_r in H by lia. apply Z.div_le_upper_bound; lia.
Qed.

#[using="Type"] Theorem hwe_run : forall n R m rom c u, 2 <= c <= 32 -> c mod 2 = 0 -> c <= 2 ^ Z.of_nat n -> 0 <= u <= 2^60 ->
  getr R 13 = wa c -> getr R 10 = wa u ->
  exists R', msteps SEGS (mkst R (wa 0x52558) m rom) (mkst R' (wa 0x52580) m rom) /\ getr R' 12 = wa (halve_while_even (S n) c u) /\
    getr R' 10 = wa u /\
    (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat ->
       getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  induction n as [|n IH]; intros R m rom c u Hc Ae Hn Hu R13 R10.
  { cbn in Hn. lia. }
  assert (P : hwe_pre R m c u) by (constructor; assumption).
  destruct (Z_le_gt_dec (4 * c) u) as [Hge|Hlt].
  - destruct (hwe_phwu R m rom c u P) as (R' & Hms & Q10 & Q12 & Q13 & QK).
    { scs_go. zat R (VALS_hwe c u) 33%nat u. zat R (VALS_hwe c u) 32%nat c. rewrite sllw2_small by lia. rewrite Z.mod_small by lia.
      apply negb_true_iff. apply Z.ltb_ge. lia. }
    exists R'. split; [exact Hms|]. split; [rewrite hwe_step_stop by lia; exact Q12|]. split; [exact Q10|].
    intros k Hk. apply QK. clear - Hk. klist Hk.
  - assert (L2 : Z.land c 2 = 2 * ((c mod 4) / 2)) by (apply land2_small; lia).
    assert (E4 : c mod 4 = 0 \/ c mod 4 = 2).
    { clear - Ae. lia. }
    destruct E4 as [E4|E4].
    + (* [comment removed for export] *)
      destruct (hwe_phwc R m rom c u P) as (R' & Hms & Q10 & Q13 & Q14 & QK).
      { scs_go.
        - zat R (VALS_hwe c u) 32%nat c. rewrite (Z.mod_small c) by lia. change (2 mod 2^64) with 2. rewrite L2, E4. reflexivity.
        - zat R (VALS_hwe c u) 33%nat u. zat R (VALS_hwe c u) 32%nat c. rewrite sllw2_small by lia. rewrite Z.mod_small by lia.
          apply negb_false_iff. apply Z.ltb_lt. lia. }
      assert (Hc2 : c / 2 mod 2 = 0).
      { rewrite (Z.div_mod c 4) by lia. rewrite E4, Z.add_0_r. replace (4 * (c / 4)) with ((c / 4) * 2 * 2) by ring.
        rewrite Z.div_mul by lia. apply Z.mod_mul. lia. }
      assert (Hc2' : 2 <= c / 2 <= 32).
      { split; [|apply Z.div_le_upper_bound; lia]. apply Z.div_le_lower_bound; [lia|]. destruct (Z.eq_dec c 2) as [->|Ne]; [discriminate E4|].
        pose proof (Z.mod_pos_bound c 4 ltac:(lia)). rewrite (Z.div_mod c 4) by lia. rewrite E4. lia. }
      destruct (IH R' m rom (c / 2) u Hc2' Hc2 (pow_succ_half n c ltac:(lia)) Hu Q13 Q10) as (R'' & Hms' & S12 & S10 & SK).
      exists R''. split; [exact (msteps_trans SEGS _ _ _ Hms Hms')|]. split; [rewrite hwe_step_go by lia; exact S12|]. split; [exact S10|].
      intros k Hk. rewrite (SK k Hk). apply QK. clear - Hk. klist Hk.
    + (* [comment removed for export] *)
      destruct (hwe_phwo R m rom c u P) as (R' & Hms & Q10 & Q12 & Q13 & Q14 & QK).
      { scs_go.
        - zat R (VALS_hwe c u) 32%nat c. rewrite (Z.mod_small c) by lia. change (2 mod 2^64) with 2. rewrite L2, E4. reflexivity.
        - zat R (VALS_hwe c u) 33%nat u. zat R (VALS_hwe c u) 32%nat c. rewrite sllw2_small by lia. rewrite Z.mod_small by lia.
          apply negb_false_iff. apply Z.ltb_lt. lia. }
      assert (Hc2 : c / 2 mod 2 = 1).
      { rewrite (Z.div_mod c 4) by lia. rewrite E4. replace (4 * (c / 4) + 2) with ((2 * (c / 4) + 1) * 2) by ring.
        rewrite Z.div_mul by lia. rewrite Z.add_comm, Z.mul_comm, Z.mod_add by lia. reflexivity. }
      exists R'. split; [exact Hms|]. split; [rewrite hwe_step_go by lia; rewrite hwe_odd by exact Hc2; exact Q12|].
      split; [exact Q10|]. intros k Hk. apply QK. clear - Hk. klist Hk.
Qed.

#[using="Type"] Lemma shr20 : forall x, 0 <= x < 2^40 -> (Z.shiftr (x mod 2^64) (20 mod 64) mod 2^64 =? 0 mod 2^64) = (x <? 2^20).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros x Hx. rewrite (Z.mod_small x) by lia. change (20 mod 64) with 20. rewrite Z.shiftr_div_pow2 by lia.
  rewrite (Z.mod_small (x / 2^20)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). change (0 mod 2^64) with 0.
  destruct (x <? 2^20) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E].
  - apply Z.eqb_eq. apply Z.div_small. lia.
  - apply Z.eqb_neq. intros H. pose proof (Z.div_le_lower_bound x (2^20) 1 ltac:(lia) ltac:(lia)). lia.
Qed.

#[using="Type"] Theorem hwb_run : forall n R m rom c size, 1 <= c <= 32 -> c <= 2 ^ Z.of_nat n -> 16 <= size <= 131056 ->
  getr R 12 = wa c -> getr R 24 = wa size ->
  exists R', msteps SEGS (mkst R (wa 0x52580) m rom) (mkst R' (wa 0x52594) m rom) /\ getr R' 19 = wa (halve_while_big (S n) c size) /\
    getr R' 24 = wa size /\
    (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 14; 15; 16; 17; 18; 20; 21; 22; 23; 25; 26; 27; 28; 29; 30; 31]%nat ->
       getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  induction n as [|n IH]; intros R m rom c size Hc Hn Hs R12 R24.
  - assert (P : hwb_pre R m c size) by (constructor; assumption).
    cbn in Hn. assert (c = 1) by lia. subst c.
    destruct (hwb_phbx R m rom 1 size P) as (R' & Hms & Q13 & Q19 & Q24 & QK).
    { scs_go. zat R (VALS_hwb 1 size) 33%nat size. zat R (VALS_hwb 1 size) 32%nat 1. rewrite shr20 by lia. rewrite negb_false_iff. apply Z.ltb_lt. lia. }
    exists R'. split; [exact Hms|]. split; [rewrite hwb_step_stop by lia; exact Q19|]. split; [exact Q24|].
    intros k Hk. apply QK. clear - Hk. klist Hk.
  - assert (P : hwb_pre R m c size) by (constructor; assumption).
    destruct (Z_lt_le_dec (size * c) (2^20)) as [Hlt|Hge].
    + destruct (hwb_phbx R m rom c size P) as (R' & Hms & Q13 & Q19 & Q24 & QK).
      { scs_go. zat R (VALS_hwb c size) 33%nat size. zat R (VALS_hwb c size) 32%nat c. rewrite shr20 by (clear - Hs Hc; nia). rewrite negb_false_iff. apply Z.ltb_lt. exact Hlt. }
      exists R'. split; [exact Hms|]. split; [rewrite hwb_step_stop by lia; exact Q19|]. split; [exact Q24|].
      intros k Hk. apply QK. clear - Hk. klist Hk.
    + destruct (hwb_phbc R m rom c size P) as (R' & Hms & Q12 & Q13 & Q19 & Q24 & QK).
      { scs_go. zat R (VALS_hwb c size) 33%nat size. zat R (VALS_hwb c size) 32%nat c. rewrite shr20 by (clear - Hs Hc; nia). rewrite negb_true_iff. apply Z.ltb_ge. exact Hge. }
      assert (Hc8 : 8 <= c) by (clear - Hge Hs; nia).
      assert (Hc2 : 1 <= c / 2 <= 32) by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
      destruct (IH R' m rom (c / 2) size Hc2 (pow_succ_half n c ltac:(lia)) Hs Q12 Q24) as (R'' & Hms' & S19 & S24 & SK).
      exists R''. split; [exact (msteps_trans SEGS _ _ _ Hms Hms')|]. split; [rewrite hwb_step_go by lia; exact S19|]. split; [exact S24|].
      intros k Hk. rewrite (SK k Hk). apply QK. clear - Hk. klist Hk.
Qed.
End LOOPS.

Lemma geu_z : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> negb (x mod 2^64 <? y mod 2^64) = (y <=? x).
Proof.
  intros x y Hx Hy. rewrite !Z.mod_small by assumption. destruct (y <=? x) eqn:E; [apply Z.leb_le in E | apply Z.leb_gt in E].
  - apply negb_true_iff. apply Z.ltb_ge. lia.
  - apply negb_false_iff. apply Z.ltb_lt. lia.
Qed.

Lemma class_units : forall sc, class_size sc = 16 * znth sc size_classes.
Proof. intros sc. reflexivity. Qed.

Section CNT.
Context {fx : FPState}.

#[using="Type"] Theorem seg_agc_small : forall R m rom sc mt usage,
  getr R 8 = wa sc -> getr R 10 = wa mt -> getr R 19 = wa (2 * sc) -> getr R 23 = wa (8 * sc + 614096) ->
  getr R 24 = wa (znth sc size_classes) -> getr R 25 = wa 98984 ->
  0 <= sc <= 8 -> 1 <= mt <= 2^63-1 -> 0 <= usage <= 2^60 ->
  rdn SEGS m (wa (8 * sc + 614568)) 8 = Some (word_to_le_bytes 8 (wa usage)) ->
  rdn SEGS m (wa (0 + 614032)) 8 = Some (word_to_le_bytes 8 (wa 4096)) -> TABS m ->
  exists R', msteps SEGS (mkst R (wa 0x524e8) m rom)
               (mkst R' (wa (if PGSZ / 2 <? class_size sc * initial_cnt sc usage + UNIT then 0x525bc else 0x52600)) m rom) /\
    getr R' 8 = wa sc /\ getr R' 9 = wa mt /\ getr R' 10 = wa usage /\ getr R' 11 = wa 4096 /\ getr R' 19 = wa (initial_cnt sc usage) /\
    getr R' 24 = wa (class_size sc) /\ getr R' 23 = wa (8 * sc + 614096) /\ getr R' 25 = wa 98984 /\
    getr R' 12 = wa (class_size sc + 16) /\ getr R' 14 = wa (class_size sc * initial_cnt sc usage) /\
    (forall k, In k [1;2;3;4;18;20;21;22;26;27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R m rom sc mt usage R8 R10 R19 R23 R24 R25 Hsc Hmt Hu Mu Mpg [TS _].
  assert (Hun : 1 <= znth sc size_classes <= 9).
  { assert (E : sc = 0 \/ sc = 1 \/ sc = 2 \/ sc = 3 \/ sc = 4 \/ sc = 5 \/ sc = 6 \/ sc = 7 \/ sc = 8) by lia.
    destruct E as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; cbv; split; discriminate. }
  pose proof (small_rows sc Hsc 0 ltac:(lia)) as Hr0. pose proof (small_rows sc Hsc 1 ltac:(lia)) as Hr1. pose proof (small_rows sc Hsc 2 ltac:(lia)) as Hr2.
  pose proof (TS sc 0 Hsc ltac:(lia)) as T0. pose proof (TS sc 1 Hsc ltac:(lia)) as T1. pose proof (TS sc 2 Hsc ltac:(lia)) as T2. clear TS.
  rewrite initial_small by exact Hsc. unfold small_cnt. rewrite class_units.
  remember (znth sc size_classes) as units eqn:Eu. remember (znth 0 (nth (Z.to_nat sc) small_cnt_tab [])) as r0 eqn:Er0.
  remember (znth 1 (nth (Z.to_nat sc) small_cnt_tab [])) as r1 eqn:Er1. remember (znth 2 (nth (Z.to_nat sc) small_cnt_tab [])) as r2 eqn:Er2.
  clear Eu Er0 Er1 Er2.
  assert (P : agcs_pre R m sc mt usage units r0 r1 r2) by (constructor; try assumption; lia).
  assert (G : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> negb (a mod 2^64 <? b mod 2^64) = (b <=? a)) by exact geu_z.
  assert (POST : forall R' r, getr R' 8 = wa sc -> getr R' 9 = wa mt -> getr R' 10 = wa usage -> getr R' 11 = wa 4096 -> getr R' 19 = wa r ->
     getr R' 23 = wa (8 * sc + 614096) -> getr R' 24 = wa (16 * units) -> getr R' 25 = wa 98984 ->
     getr R' 12 = wa (16 * units + 16) -> getr R' 14 = wa (16 * units * r) ->
     (forall k, In k [1; 2; 3; 4; 5; 6; 7; 16; 17; 18; 20; 21; 22; 26; 27; 28; 29; 30; 31]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) ->
     getr R' 8 = wa sc /\ getr R' 9 = wa mt /\ getr R' 10 = wa usage /\ getr R' 11 = wa 4096 /\ getr R' 19 = wa r /\
     getr R' 24 = wa (16 * units) /\ getr R' 23 = wa (8 * sc + 614096) /\ getr R' 25 = wa 98984 /\
     getr R' 12 = wa (16 * units + 16) /\ getr R' 14 = wa (16 * units * r) /\
     (forall k, In k [1;2;3;4;18;20;21;22;26;27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k)))).
  { intros R' r Q8 Q9 Q10 Q11 Q19 Q23 Q24 Q25 Q12 Q14 QK. repeat (split; [assumption|]). intros k Hk. apply QK. clear - Hk. klist Hk. }
  set (V := VALS_agcs sc mt usage units r0 r1 r2).
  destruct (usage <? 4 * r0) eqn:E0; [apply Z.ltb_lt in E0 | apply Z.ltb_ge in E0]; cbn [negb].
  - destruct (usage <? 4 * r1) eqn:E1; [apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1]; cbn [negb].
    + destruct (PGSZ / 2 <? 16 * units * r2 + UNIT) eqn:ED; [apply Z.ltb_lt in ED | apply Z.ltb_ge in ED]; unfold PGSZ, UNIT in ED.
      * destruct (agcs_pr2m R m rom sc mt usage units r0 r1 r2 P) as (R' & Hms & Q8 & Q9 & Q10 & Q11 & Q12 & _ & Q14 & _ & Q19 & Q23 & Q24 & Q25 & QK).
        { scs_go; zats; rewrite ?G by (clear - Hun Hr0 Hr1 Hr2 Hu; nia); first [apply Z.leb_le | apply Z.leb_gt]; clear - Hun Hr0 Hr1 Hr2 Hu E0 E1 ED; nia. }
        exists R'. split; [exact Hms | exact (POST R' r2 Q8 Q9 Q10 Q11 Q19 Q23 Q24 Q25 Q12 Q14 QK)].
      * destruct (agcs_pr2n R m rom sc mt usage units r0 r1 r2 P) as (R' & Hms & Q8 & Q9 & Q10 & Q11 & Q12 & _ & Q14 & _ & Q19 & Q23 & Q24 & Q25 & QK).
        { scs_go; zats; rewrite ?G by (clear - Hun Hr0 Hr1 Hr2 Hu; nia); first [apply Z.leb_le | apply Z.leb_gt]; clear - Hun Hr0 Hr1 Hr2 Hu E0 E1 ED; nia. }
        exists R'. split; [exact Hms | exact (POST R' r2 Q8 Q9 Q10 Q11 Q19 Q23 Q24 Q25 Q12 Q14 QK)].
    + destruct (PGSZ / 2 <? 16 * units * r1 + UNIT) eqn:ED; [apply Z.ltb_lt in ED | apply Z.ltb_ge in ED]; unfold PGSZ, UNIT in ED.
      * destruct (agcs_pr1m R m rom sc mt usage units r0 r1 r2 P) as (R' & Hms & Q8 & Q9 & Q10 & Q11 & Q12 & _ & Q14 & _ & Q19 & Q23 & Q24 & Q25 & QK).
        { scs_go; zats; rewrite ?G by (clear - Hun Hr0 Hr1 Hr2 Hu; nia); first [apply Z.leb_le | apply Z.leb_gt]; clear - Hun Hr0 Hr1 Hr2 Hu E0 E1 ED; nia. }
        exists R'. split; [exact Hms | exact (POST R' r1 Q8 Q9 Q10 Q11 Q19 Q23 Q24 Q25 Q12 Q14 QK)].
      * destruct (agcs_pr1n R m rom sc mt usage units r0 r1 r2 P) as (R' & Hms & Q8 & Q9 & Q10 & Q11 & Q12 & _ & Q14 & _ & Q19 & Q23 & Q24 & Q25 & QK).
        { scs_go; zats; rewrite ?G by (clear - Hun Hr0 Hr1 Hr2 Hu; nia); first [apply Z.leb_le | apply Z.leb_gt]; clear - Hun Hr0 Hr1 Hr2 Hu E0 E1 ED; nia. }
        exists R'. split; [exact Hms | exact (POST R' r1 Q8 Q9 Q10 Q11 Q19 Q23 Q24 Q25 Q12 Q14 QK)].
  - destruct (PGSZ / 2 <? 16 * units * r0 + UNIT) eqn:ED; [apply Z.ltb_lt in ED | apply Z.ltb_ge in ED]; unfold PGSZ, UNIT in ED.
    + destruct (agcs_pr0m R m rom sc mt usage units r0 r1 r2 P) as (R' & Hms & Q8 & Q9 & Q10 & Q11 & Q12 & _ & Q14 & _ & Q19 & Q23 & Q24 & Q25 & QK).
      { scs_go; zats; rewrite ?G by (clear - Hun Hr0 Hr1 Hr2 Hu; nia); first [apply Z.leb_le | apply Z.leb_gt]; clear - Hun Hr0 Hr1 Hr2 Hu E0 ED; nia. }
      exists R'. split; [exact Hms | exact (POST R' r0 Q8 Q9 Q10 Q11 Q19 Q23 Q24 Q25 Q12 Q14 QK)].
    + destruct (agcs_pr0n R m rom sc mt usage units r0 r1 r2 P) as (R' & Hms & Q8 & Q9 & Q10 & Q11 & Q12 & _ & Q14 & _ & Q19 & Q23 & Q24 & Q25 & QK).
      { scs_go; zats; rewrite ?G by (clear - Hun Hr0 Hr1 Hr2 Hu; nia); first [apply Z.leb_le | apply Z.leb_gt]; clear - Hun Hr0 Hr1 Hr2 Hu E0 ED; nia. }
      exists R'. split; [exact Hms | exact (POST R' r0 Q8 Q9 Q10 Q11 Q19 Q23 Q24 Q25 Q12 Q14 QK)].
Qed.

#[using="Type"] Lemma hwe_range : forall f c u, 1 <= c <= 32 -> 1 <= halve_while_even f c u <= 32.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction f as [|f IH]; intros c u Hc; [exact Hc|]. cbn [halve_while_even].
  destruct (Z.even c && (u <? 4 * c)) eqn:E; [|exact Hc].
  apply andb_true_iff in E as [E1 _]. apply Z.even_spec in E1. destruct E1 as (k & ->). apply IH.
  rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

#[using="Type"] Lemma hwb_range : forall f c size, 1 <= c <= 32 -> 16 <= size <= 131056 -> 1 <= halve_while_big f c size <= 32.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction f as [|f IH]; intros c size Hc Hs; [exact Hc|]. cbn [halve_while_big]. unfold UNIT.
  destruct (65536 * 16 <=? size * c) eqn:E; [|exact Hc]. apply Z.leb_le in E.
  apply IH; [|exact Hs]. assert (8 <= c) by (clear - E Hs; nia). split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia].
Qed.

#[using="Type"] Theorem seg_agc_med : forall R m rom sc mt usage,
  getr R 8 = wa sc -> getr R 10 = wa mt -> getr R 19 = wa (2 * sc) -> getr R 23 = wa (8 * sc + 614096) ->
  getr R 24 = wa (znth sc size_classes) -> getr R 25 = wa 98984 ->
  9 <= sc <= 47 -> 1 <= mt <= 2^63-1 -> 0 <= usage <= 2^60 ->
  rdn SEGS m (wa (8 * sc + 614568)) 8 = Some (word_to_le_bytes 8 (wa usage)) ->
  rdn SEGS m (wa (0 + 614032)) 8 = Some (word_to_le_bytes 8 (wa 4096)) -> TABS m ->
  exists R', msteps SEGS (mkst R (wa 0x524e8) m rom)
               (mkst R' (wa (if PGSZ / 2 <? class_size sc * initial_cnt sc usage + UNIT then 0x525bc else 0x52600)) m rom) /\
    getr R' 8 = wa sc /\ getr R' 9 = wa mt /\ getr R' 10 = wa usage /\ getr R' 11 = wa 4096 /\ getr R' 19 = wa (initial_cnt sc usage) /\
    getr R' 24 = wa (class_size sc) /\ getr R' 23 = wa (8 * sc + 614096) /\ getr R' 25 = wa 98984 /\
    getr R' 12 = wa (class_size sc + 16) /\ getr R' 14 = wa (class_size sc * initial_cnt sc usage) /\
    (forall k, In k [1;2;3;4;18;20;21;22;26;27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R m rom sc mt usage R8 R10 R19 R23 R24 R25 Hsc Hmt Hu Mu Mpg [_ TM].
  pose proof (size_classes_range sc ltac:(lia)) as Hun.
  pose proof (med_row sc ltac:(lia)) as (Hc0 & Ac0).
  pose proof (TM (Z.land sc 3) ltac:(pose proof (land3_bound sc); lia)) as T0. clear TM.
  unfold initial_cnt. replace (sc <? 9) with false by (symmetry; apply Z.ltb_ge; lia). rewrite class_units.
  set (units := znth sc size_classes) in *. set (c0 := znth (Z.land sc 3) med_cnt_tab) in *. clearbody units c0.
  assert (P : agcm_pre R m sc mt usage units c0) by (constructor; try assumption; lia).
  destruct (agcm_pagcm R m rom sc mt usage units c0 P ltac:(constructor)) as (R1 & Hms1 & A8 & A9 & A10 & A11 & A12 & A13 & A19 & A23 & A24 & A25 & AK).
  change (agcm_mem_pagcm m R sc mt usage units c0) with m in Hms1.
  destruct (hwe_run 7 R1 m rom c0 usage ltac:(lia) Ac0 ltac:(change (2 ^ Z.of_nat 7) with 128; lia) Hu A13 A10) as (R2 & Hms2 & B12 & B10 & BK).
  set (he := halve_while_even 8 c0 usage) in *. pose proof (hwe_range 8 c0 usage ltac:(lia)) as Hhe. fold he in Hhe. clearbody he.
  assert (B24 : getr R2 24 = wa (16 * units)) by (regk BK 24%nat; exact A24).
  destruct (hwb_run 7 R2 m rom he (16 * units) Hhe ltac:(change (2 ^ Z.of_nat 7) with 128; lia) ltac:(lia) B12 B24) as (R3 & Hms3 & C19 & C24 & CK).
  set (hb := halve_while_big 8 he (16 * units)) in *. pose proof (hwb_range 8 he (16 * units) Hhe ltac:(lia)) as Hhb. fold hb in Hhb. clearbody hb.
  assert (C11 : getr R3 11 = wa 4096) by (regk CK 11%nat; regk BK 11%nat; exact A11).
  assert (POST : forall R4 r pc, msteps SEGS (mkst R3 (wa 0x52594) m rom) (mkst R4 (wa pc) m rom) ->
     getr R4 19 = wa r -> getr R4 24 = wa (16 * units) -> getr R4 11 = wa 4096 -> getr R4 12 = wa (16 * units + 16) -> getr R4 14 = wa (16 * units * r) ->
     (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 16; 17; 18; 20; 21; 22; 23; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R4 (Z_to_bv 5 (Z.of_nat k)) = getr R3 (Z_to_bv 5 (Z.of_nat k))) ->
     exists R', msteps SEGS (mkst R (wa 0x524e8) m rom) (mkst R' (wa pc) m rom) /\
     getr R' 8 = wa sc /\ getr R' 9 = wa mt /\ getr R' 10 = wa usage /\ getr R' 11 = wa 4096 /\ getr R' 19 = wa r /\
     getr R' 24 = wa (16 * units) /\ getr R' 23 = wa (8 * sc + 614096) /\ getr R' 25 = wa 98984 /\
     getr R' 12 = wa (16 * units + 16) /\ getr R' 14 = wa (16 * units * r) /\
     (forall k, In k [1;2;3;4;18;20;21;22;26;27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k)))).
  { intros R4 r pc Hms4 D19 D24 D11 D12 D14 DK. exists R4. split; [exact (msteps_trans SEGS _ _ _ Hms1 (msteps_trans SEGS _ _ _ Hms2 (msteps_trans SEGS _ _ _ Hms3 Hms4)))|].
    split; [regk DK 8%nat; regk CK 8%nat; regk BK 8%nat; exact A8|]. split; [regk DK 9%nat; regk CK 9%nat; regk BK 9%nat; exact A9|].
    split; [regk DK 10%nat; regk CK 10%nat; exact B10|]. split; [exact D11|]. split; [exact D19|]. split; [exact D24|].
    split; [regk DK 23%nat; regk CK 23%nat; regk BK 23%nat; exact A23|]. split; [regk DK 25%nat; regk CK 25%nat; regk BK 25%nat; exact A25|].
    split; [exact D12|]. split; [exact D14|].
    intros k Hk. rewrite (DK k ltac:(clear - Hk; klist Hk)), (CK k ltac:(clear - Hk; klist Hk)), (BK k ltac:(clear - Hk; klist Hk)). apply AK. clear - Hk. klist Hk. }
  assert (G : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> negb (a mod 2^64 <? b mod 2^64) = (b <=? a)) by exact geu_z.
  destruct (Z.eq_dec hb 1) as [E1|E1].
  - rewrite E1, Z.eqb_refl. cbn [andb]. rewrite E1 in C19.
    destruct (Z_le_gt_dec (16 * units) 2032) as [Hs|Hs].
    + replace (16 * units * 1 + UNIT <=? PGSZ / 2) with true by (symmetry; apply Z.leb_le; unfold UNIT, PGSZ; lia).
      assert (P1 : agad1s_pre R3 m (16 * units)) by (constructor; try assumption; lia).
      destruct (PGSZ / 2 <? 16 * units * 2 + UNIT) eqn:ED; [apply Z.ltb_lt in ED | apply Z.ltb_ge in ED]; unfold PGSZ, UNIT in ED.
      * destruct (agad1s_pasm R3 m rom (16 * units) P1) as (R4 & Hms4 & D11 & D12 & _ & D14 & _ & D19 & D24 & DK).
        { scs_go; zats; rewrite ?G by (clear - Hun Hs; lia); first [apply Z.leb_le | apply Z.leb_gt]; clear - Hun Hs ED; lia. }
        exact (POST R4 2 _ Hms4 D19 D24 D11 D12 ltac:(rewrite D14; f_equal; ring) DK).
      * destruct (agad1s_pasn R3 m rom (16 * units) P1) as (R4 & Hms4 & D11 & D12 & _ & D14 & _ & D19 & D24 & DK).
        { scs_go; zats; rewrite ?G by (clear - Hun Hs; lia); first [apply Z.leb_le | apply Z.leb_gt]; clear - Hun Hs ED; lia. }
        exact (POST R4 2 _ Hms4 D19 D24 D11 D12 ltac:(rewrite D14; f_equal; ring) DK).
    + replace (16 * units * 1 + UNIT <=? PGSZ / 2) with false by (symmetry; apply Z.leb_gt; unfold UNIT, PGSZ; lia).
      assert (P1 : agad1b_pre R3 m (16 * units)) by (constructor; try assumption; lia).
      destruct (agad1b_pabm R3 m rom (16 * units) P1 ltac:(constructor)) as (R4 & Hms4 & D11 & D12 & _ & D14 & _ & D19 & D24 & DK).
      cbn beta iota. replace (PGSZ / 2 <? 16 * units * 1 + UNIT) with true by (symmetry; apply Z.ltb_lt; unfold PGSZ, UNIT; lia).
      exact (POST R4 1 _ Hms4 D19 D24 D11 D12 ltac:(rewrite D14; f_equal; ring) DK).
  - replace (hb =? 1) with false by (symmetry; apply Z.eqb_neq; exact E1). cbn [andb].
    assert (P1 : agad_pre R3 m hb (16 * units)) by (constructor; try assumption; lia).
    destruct (PGSZ / 2 <? 16 * units * hb + UNIT) eqn:ED; [apply Z.ltb_lt in ED | apply Z.ltb_ge in ED]; unfold PGSZ, UNIT in ED.
    + destruct (agad_padm R3 m rom hb (16 * units) P1) as (R4 & Hms4 & D11 & D12 & _ & D14 & _ & D19 & D24 & DK).
      { scs_go; zats; rewrite ?G by (clear - Hun Hhb; nia); first [apply Z.leb_le | apply Z.leb_gt]; clear - Hun Hhb ED; nia. }
      exact (POST R4 hb _ Hms4 D19 D24 D11 D12 ltac:(rewrite D14; f_equal; ring) DK).
    + destruct (agad_padn R3 m rom hb (16 * units) P1) as (R4 & Hms4 & D11 & D12 & _ & D14 & _ & D19 & D24 & DK).
      { scs_go; zats; rewrite ?G by (clear - Hun Hhb; nia); first [apply Z.leb_le | apply Z.leb_gt]; clear - Hun Hhb ED; nia. }
      exact (POST R4 hb _ Hms4 D19 D24 D11 D12 ltac:(rewrite D14; f_equal; ring) DK).
Qed.

#[using="Type"] Theorem seg_agc : forall R m rom sc mt usage,
  getr R 8 = wa sc -> getr R 10 = wa mt -> getr R 19 = wa (2 * sc) -> getr R 23 = wa (8 * sc + 614096) ->
  getr R 24 = wa (znth sc size_classes) -> getr R 25 = wa 98984 ->
  0 <= sc <= 47 -> 1 <= mt <= 2^63-1 -> 0 <= usage <= 2^60 ->
  rdn SEGS m (wa (8 * sc + 614568)) 8 = Some (word_to_le_bytes 8 (wa usage)) ->
  rdn SEGS m (wa (0 + 614032)) 8 = Some (word_to_le_bytes 8 (wa 4096)) -> TABS m ->
  exists R', msteps SEGS (mkst R (wa 0x524e8) m rom)
               (mkst R' (wa (if PGSZ / 2 <? class_size sc * initial_cnt sc usage + UNIT then 0x525bc else 0x52600)) m rom) /\
    getr R' 8 = wa sc /\ getr R' 9 = wa mt /\ getr R' 10 = wa usage /\ getr R' 11 = wa 4096 /\ getr R' 19 = wa (initial_cnt sc usage) /\
    getr R' 24 = wa (class_size sc) /\ getr R' 23 = wa (8 * sc + 614096) /\ getr R' 25 = wa 98984 /\
    getr R' 12 = wa (class_size sc + 16) /\ getr R' 14 = wa (class_size sc * initial_cnt sc usage) /\
    (forall k, In k [1;2;3;4;18;20;21;22;26;27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R m rom sc mt usage R8 R10 R19 R23 R24 R25 Hsc Hmt Hu Mu Mpg T.
  destruct (Z_le_gt_dec sc 8) as [S|S].
  - exact (seg_agc_small R m rom sc mt usage R8 R10 R19 R23 R24 R25 ltac:(lia) Hmt Hu Mu Mpg T).
  - exact (seg_agc_med R m rom sc mt usage R8 R10 R19 R23 R24 R25 ltac:(lia) Hmt Hu Mu Mpg T).
Qed.
End CNT.
