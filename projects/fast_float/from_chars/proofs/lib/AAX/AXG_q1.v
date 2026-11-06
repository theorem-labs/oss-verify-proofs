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
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AxAsan AXG_put AXG_put2 AXG_np AXG_np2 AXG_np3 AXG_nf1.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_gp.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AxAsan OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np3 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngZ.AxScChk OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp.AXG_npb OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp.

Module AXF_qroom.
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

Definition e_QC := EVar 32.
Definition e_B := EVar 33.
Definition e_qn := EVar 34.
Definition e_qb := EVar 35.
Definition e_bsz := EVar 36.
Definition e_sz := EVar 37.
Definition e_mp := EVar 38.
Definition e_mx := EVar 39.
Definition STK := SA (EVar 2) (-1024).
Definition sr_qroom := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 1 (ELit 0x43af8)) 9 (e_QC)) 10 (e_QC)) 13 (e_mp)) 14 (e_sz)) 22 (e_mx)).
Definition kn_qroom : list kentry :=
  [ KRange e_QC 1 (2^47);
    KRange e_B 1 (2^47);
    KAlign e_B 8;
    KRange (EVar 2) (2^46) (2^47);
    KWord (SA e_QC 0) 8 (ELit 1);
    KWord (SA e_QC 16) 8 e_B;
    KWord (SA e_QC 24) 8 e_qb;
    KWr (SA e_QC 24) (ELit 8);
    KWord (SA e_B 16) 8 e_qn;
    KWord (SA e_B 8) 8 e_bsz;
    KWr (SA e_B 0) (ELit 24);
    KWr (SA (EAlu ALU_ADD e_B (EMd M_MUL (ELit 8) e_qn)) 24) (ELit 8);
    KWr STK (ELit 1024) ].
Definition scr_qroom : scripts := SCR [true; false; false] [] [].
Definition ss_qroom := SS 0x43b04 sr_qroom [] kn_qroom 40.
Definition RUN_qroom := sym_exec SEGS 80 true [0x43a30] scr_qroom ss_qroom [].

Definition scr_proom : scripts := SCR [true; false; false] [] [].
Definition RES_proom := Eval vm_compute in sym_exec SEGS 80 true [0x43a30] scr_proom ss_qroom [].
Lemma RES_proom_ok : sym_exec SEGS 80 true [0x43a30] scr_proom (SS 0x43b04 sr_qroom [] kn_qroom 40) [] = RES_proom.
Proof. vm_compute. reflexivity. Qed.
End AXF_qroom.


Module AXF_qroomz.
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

Section QROOM.
Context {fx : FPState}.

Definition VALS_qroom (QC B qn qb bsz sz mp mx : Z) : list Z := [QC; B; qn; qb; bsz; sz; mp; mx].

Record qroom_pre (regs : bvmap 5 word) (m : word -> option byte) (QC B qn qb bsz sz mp mx : Z) : Prop := {
  qroom_R1 : getr regs 1 = wa 277240 ;
  qroom_R9 : getr regs 9 = wa QC ;
  qroom_R10 : getr regs 10 = wa QC ;
  qroom_R13 : getr regs 13 = wa mp ;
  qroom_R14 : getr regs 14 = wa sz ;
  qroom_R22 : getr regs 22 = wa mx ;
  qroom_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  qroom_rng_QC : 1 <= QC <= 2^47 ;
  qroom_rng_B : 1 <= B <= 2^47 ;
  qroom_rng_qn : 1 <= qn <= 1020 ;
  qroom_rng_qb : 0 <= qb <= 2^62 ;
  qroom_rng_bsz : 0 <= bsz <= 2^62 ;
  qroom_rng_sz : 0 <= sz <= 2^40 ;
  qroom_rng_mp : 0 <= mp <= 2^64-1 ;
  qroom_rng_mx : 0 <= mx <= 2^62 ;
  qroom_ka2 : B mod 8 = 0 ;
  qroom_kr3 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  qroom_kw4 : rdn SEGS m (wa (QC + 0)) 8 = Some (word_to_le_bytes 8 (wa 1)) ;
  qroom_kw5 : rdn SEGS m (wa (QC + 16)) 8 = Some (word_to_le_bytes 8 (wa B)) ;
  qroom_kw6 : rdn SEGS m (wa (QC + 24)) 8 = Some (word_to_le_bytes 8 (wa qb)) ;
  qroom_kwr7 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (QC + 24 + d)) k = true ;
  qroom_kw8 : rdn SEGS m (wa (B + 16)) 8 = Some (word_to_le_bytes 8 (wa qn)) ;
  qroom_kw9 : rdn SEGS m (wa (B + 8)) 8 = Some (word_to_le_bytes 8 (wa bsz)) ;
  qroom_kwr10 : forall d k, 0 <= d -> d + Z.of_nat k <= 24 -> store_ok SEGS m (wa (B + 0 + d)) k = true ;
  qroom_kwr11 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (B + (8 * qn) + 24 + d)) k = true
}.


#[using="Type"] Lemma qroom_setup : forall regs m QC B qn qb bsz sz mp mx, qroom_pre regs m QC B qn qb bsz sz mp mx ->
  regs_ok (Ez regs (VALS_qroom QC B qn qb bsz sz mp mx)) AXF_qroom.sr_qroom regs /\ know_ok SEGS (Ez regs (VALS_qroom QC B qn qb bsz sz mp mx)) m AXF_qroom.kn_qroom.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m QC B qn qb bsz sz mp mx P. destruct P as [qroom_R1 qroom_R9 qroom_R10 qroom_R13 qroom_R14 qroom_R22 qroom_HSTK qroom_rng_QC qroom_rng_B qroom_rng_qn qroom_rng_qb qroom_rng_bsz qroom_rng_sz qroom_rng_mp qroom_rng_mx qroom_ka2 qroom_kr3 qroom_kw4 qroom_kw5 qroom_kw6 qroom_kwr7 qroom_kw8 qroom_kw9 qroom_kwr10 qroom_kwr11].
  set (E := Ez regs (VALS_qroom QC B qn qb bsz sz mp mx)).
  assert (Z32 : bv_unsigned (ev E 32) = QC) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = B) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = qn) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = qb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = bsz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = mp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = mx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  split.
  { unfold AXF_qroom.sr_qroom.
    apply (regs_ok_pin E _ regs 22); [apply (regs_ok_pin E _ regs 14); [apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 1); [apply regs_ok_id|]|]|]|]|]|].
    - rewrite qroom_R1. reflexivity.
    - rewrite qroom_R9. reflexivity.
    - rewrite qroom_R10. reflexivity.
    - rewrite qroom_R13. reflexivity.
    - rewrite qroom_R14. reflexivity.
    - rewrite qroom_R22. reflexivity. }
  unfold know_ok, AXF_qroom.kn_qroom.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_qroom.e_QC AXF_qroom.e_B AXF_qroom.e_qn AXF_qroom.e_qb AXF_qroom.e_bsz AXF_qroom.e_sz AXF_qroom.e_mp AXF_qroom.e_mx AXF_qroom.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range QC _ _ qroom_rng_QC eq_refl eq_refl), ?(mod64_of_range B _ _ qroom_rng_B eq_refl eq_refl), ?(mod64_of_range qn _ _ qroom_rng_qn eq_refl eq_refl), ?(mod64_of_range qb _ _ qroom_rng_qb eq_refl eq_refl), ?(mod64_of_range bsz _ _ qroom_rng_bsz eq_refl eq_refl), ?(mod64_of_range sz _ _ qroom_rng_sz eq_refl eq_refl), ?(mod64_of_range mx _ _ qroom_rng_mx eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply qroom_kwr7 | apply qroom_kwr10 | apply qroom_kwr11]; assumption).
  all: try (clear - qroom_rng_QC qroom_rng_B qroom_rng_qn qroom_rng_qb qroom_rng_bsz qroom_rng_sz qroom_rng_mp qroom_rng_mx qroom_ka2 qroom_kr3; lia).
  all: first [lia].
Qed.


Definition qroom_mem_proom (m : word -> option byte) (regs : bvmap 5 word) (QC B qn qb bsz sz mp mx : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa 277240))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa QC))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -48)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -56)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21))))))) (wa (B + 8)) (word_to_le_bytes 8 (wa (bsz + sz)))) (wa (B + 16)) (word_to_le_bytes 8 (wa (qn + 1)))) (wa (B + (8 * qn) + 24)) (word_to_le_bytes 8 (wa mp))) (wa (QC + 24)) (word_to_le_bytes 8 (wa (qb + sz))).

#[using="Type"] Theorem qroom_proom : forall regs m rom QC B qn qb bsz sz mp mx, qroom_pre regs m QC B qn qb bsz sz mp mx ->
  scs_denot SEGS m (Ez regs (VALS_qroom QC B qn qb bsz sz mp mx)) (snd (fst AXF_qroom.RES_proom)) ->
  exists R, msteps SEGS (mkst regs (wa 0x43b04) m rom) (mkst R (wa 0x43a30) (qroom_mem_proom m regs QC B qn qb bsz sz mp mx) rom) /\
    getr R 1 = wa 277240 /\ getr R 9 = wa QC /\ getr R 10 = wa (qb + sz) /\ getr R 11 = wa (qb + sz) /\ getr R 12 = wa (B + (8 * qn)) /\ getr R 13 = wa mp /\ getr R 14 = wa sz /\ getr R 15 = wa (qn + 1) /\ getr R 16 = wa B /\ getr R 17 = wa 1021 /\ getr R 22 = wa mx /\ (forall k, In k [2; 3; 4; 5; 6; 7; 8; 18; 19; 20; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom QC B qn qb bsz sz mp mx P Hsc. destruct (qroom_setup regs m QC B qn qb bsz sz mp mx P) as [HR HK].
  set (E := Ez regs (VALS_qroom QC B qn qb bsz sz mp mx)) in *. destruct P as [qroom_R1 qroom_R9 qroom_R10 qroom_R13 qroom_R14 qroom_R22 qroom_HSTK qroom_rng_QC qroom_rng_B qroom_rng_qn qroom_rng_qb qroom_rng_bsz qroom_rng_sz qroom_rng_mp qroom_rng_mx qroom_ka2 qroom_kr3 qroom_kw4 qroom_kw5 qroom_kw6 qroom_kwr7 qroom_kw8 qroom_kw9 qroom_kwr10 qroom_kwr11].
  assert (Z32 : bv_unsigned (ev E 32) = QC) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = B) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = qn) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = qb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = bsz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = mp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = mx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  destruct (run_sound SEGS 80 [0x43a30] AXF_qroom.scr_proom 0x43b04 AXF_qroom.sr_qroom AXF_qroom.kn_qroom 40 _ _ _ E m rom regs AXF_qroom.RES_proom_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_qroom.RES_proom fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (qroom_mem_proom m regs QC B qn qb bsz sz mp mx) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold qroom_mem_proom. repeat (apply (f_equal3 wbytes)); try reflexivity.
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

End QROOM.
End AXF_qroomz.


Module AXF_qnewp.
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

Definition e_QC := EVar 32.
Definition e_CA := EVar 33.
Definition e_cnt := EVar 34.
Definition e_qb := EVar 35.
Definition e_csz := EVar 36.
Definition e_sz := EVar 37.
Definition e_mp := EVar 38.
Definition e_mx := EVar 39.
Definition e_cp := EVar 40.
Definition e_SB := EVar 41.
Definition e_st := EVar 42.
Definition CHP := EAlu ALU_ADD e_CA (EAlu ALU_SRL (EAlu ALU_ADD (EMd M_MUL (ELit 4294967296) (EExt true 0 4 e_cnt)) (ELit (-4294967296))) (ELit 30)).
Definition BAT := EAlu ALU_ADD e_SB (EMd M_MUL (ELit 16) (EExt false 0 4 e_cp)).
Definition STK := SA (EVar 2) (-1024).
Definition sr_qnewp := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 1 (ELit 0x43af8)) 9 (e_QC)) 10 (e_QC)) 11 (e_CA)) 13 (e_mp)) 14 (e_sz)) 22 (e_mx)).
Definition kn_qnewp : list kentry :=
  [ KRange e_QC 1 (2^47);
    KRange e_CA 1 (2^47);
    KAlign e_CA 16;
    KRange (EVar 2) (2^46) (2^47);
    KRange e_SB 4194304 (2^47);
    KAlign e_SB 4096;
    KWord (SA e_QC 0) 8 (ELit 0);
    KWord (SA e_QC 24) 8 e_qb;
    KWr (SA e_QC 0) (ELit 32);
    KWord (SA e_CA 1920) 4 e_cnt;
    KWr (SA e_CA 1920) (ELit 4);
    KWord (SA e_CA 1928) 8 e_csz;
    KWord (SA CHP 1936) 4 e_cp;
    KWord (SA (ELit 0) 923512) 8 e_SB;
    KWord (SA e_CA 2576) 8 e_st;
    KWr (SA e_CA 2576) (ELit 8);
    KWr (SA BAT 103079215104) (ELit 8192);
    KWr STK (ELit 1024) ].
Definition scr_qnewp : scripts := SCR [false; false] [] [].
Definition ss_qnewp := SS 0x43b04 sr_qnewp [] kn_qnewp 43.
Definition RUN_qnewp := sym_exec SEGS 100 true [0x43a30] scr_qnewp ss_qnewp [].

Definition scr_pnewp : scripts := SCR [false; false] [] [].
Definition RES_pnewp := Eval vm_compute in sym_exec SEGS 100 true [0x43a30] scr_pnewp ss_qnewp [].
Lemma RES_pnewp_ok : sym_exec SEGS 100 true [0x43a30] scr_pnewp (SS 0x43b04 sr_qnewp [] kn_qnewp 43) [] = RES_pnewp.
Proof. vm_compute. reflexivity. Qed.
End AXF_qnewp.


Module AXF_qnewpz.
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

Section QNEWP.
Context {fx : FPState}.

Definition VALS_qnewp (QC CA cnt qb csz sz mp mx cp SB st : Z) : list Z := [QC; CA; cnt; qb; csz; sz; mp; mx; cp; SB; st].

Record qnewp_pre (regs : bvmap 5 word) (m : word -> option byte) (QC CA cnt qb csz sz mp mx cp SB st : Z) : Prop := {
  qnewp_R1 : getr regs 1 = wa 277240 ;
  qnewp_R9 : getr regs 9 = wa QC ;
  qnewp_R10 : getr regs 10 = wa QC ;
  qnewp_R11 : getr regs 11 = wa CA ;
  qnewp_R13 : getr regs 13 = wa mp ;
  qnewp_R14 : getr regs 14 = wa sz ;
  qnewp_R22 : getr regs 22 = wa mx ;
  qnewp_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  qnewp_rng_QC : 1 <= QC <= 2^47 ;
  qnewp_rng_CA : 1 <= CA <= 2^47 ;
  qnewp_rng_cnt : 1 <= cnt <= 16 ;
  qnewp_rng_qb : 0 <= qb <= 2^62 ;
  qnewp_rng_csz : 0 <= csz <= 2^64-1 ;
  qnewp_rng_sz : 0 <= sz <= 2^40 ;
  qnewp_rng_mp : 0 <= mp <= 2^64-1 ;
  qnewp_rng_mx : 0 <= mx <= 2^62 ;
  qnewp_rng_cp : 0 <= cp <= 2^32-1 ;
  qnewp_rng_SB : 4194304 <= SB <= 2^47 ;
  qnewp_rng_st : 0 <= st <= 2^64-1 ;
  qnewp_ka2 : CA mod 16 = 0 ;
  qnewp_kr3 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  qnewp_ka5 : SB mod 4096 = 0 ;
  qnewp_kw6 : rdn SEGS m (wa (QC + 0)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  qnewp_kw7 : rdn SEGS m (wa (QC + 24)) 8 = Some (word_to_le_bytes 8 (wa qb)) ;
  qnewp_kwr8 : forall d k, 0 <= d -> d + Z.of_nat k <= 32 -> store_ok SEGS m (wa (QC + 0 + d)) k = true ;
  qnewp_kw9 : rdn SEGS m (wa (CA + 1920)) 4 = Some (word_to_le_bytes 4 (wa cnt)) ;
  qnewp_kwr10 : forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (CA + 1920 + d)) k = true ;
  qnewp_kw11 : rdn SEGS m (wa (CA + 1928)) 8 = Some (word_to_le_bytes 8 (wa csz)) ;
  qnewp_kw12 : rdn SEGS m (wa (CA + Z.shiftr ((((4294967296 * ext_Z true 0 4 cnt) + -4294967296)) mod 2^64) 30 + 1936)) 4 = Some (word_to_le_bytes 4 (wa cp)) ;
  qnewp_kw13 : rdn SEGS m (wa (0 + 923512)) 8 = Some (word_to_le_bytes 8 (wa SB)) ;
  qnewp_kw14 : rdn SEGS m (wa (CA + 2576)) 8 = Some (word_to_le_bytes 8 (wa st)) ;
  qnewp_kwr15 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (CA + 2576 + d)) k = true ;
  qnewp_kwr16 : forall d k, 0 <= d -> d + Z.of_nat k <= 8192 -> store_ok SEGS m (wa (SB + (16 * ext_Z false 0 4 cp) + 103079215104 + d)) k = true
}.


#[using="Type"] Lemma qnewp_setup : forall regs m QC CA cnt qb csz sz mp mx cp SB st, qnewp_pre regs m QC CA cnt qb csz sz mp mx cp SB st ->
  regs_ok (Ez regs (VALS_qnewp QC CA cnt qb csz sz mp mx cp SB st)) AXF_qnewp.sr_qnewp regs /\ know_ok SEGS (Ez regs (VALS_qnewp QC CA cnt qb csz sz mp mx cp SB st)) m AXF_qnewp.kn_qnewp.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m QC CA cnt qb csz sz mp mx cp SB st P. destruct P as [qnewp_R1 qnewp_R9 qnewp_R10 qnewp_R11 qnewp_R13 qnewp_R14 qnewp_R22 qnewp_HSTK qnewp_rng_QC qnewp_rng_CA qnewp_rng_cnt qnewp_rng_qb qnewp_rng_csz qnewp_rng_sz qnewp_rng_mp qnewp_rng_mx qnewp_rng_cp qnewp_rng_SB qnewp_rng_st qnewp_ka2 qnewp_kr3 qnewp_ka5 qnewp_kw6 qnewp_kw7 qnewp_kwr8 qnewp_kw9 qnewp_kwr10 qnewp_kw11 qnewp_kw12 qnewp_kw13 qnewp_kw14 qnewp_kwr15 qnewp_kwr16].
  set (E := Ez regs (VALS_qnewp QC CA cnt qb csz sz mp mx cp SB st)).
  assert (Z32 : bv_unsigned (ev E 32) = QC) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = qb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = csz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = mp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = mx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = cp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = SB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = st) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  assert (HQ : 0 <= ext_Z false 0 4 cp < 2^32) by (unfold ext_Z; change (2 ^ (8 * Z.of_nat 0)) with 1; rewrite Z.div_1_r; change (2 ^ (8 * Z.of_nat 4)) with 4294967296; apply Z.mod_pos_bound; lia).
  assert (HP : 0 <= Z.shiftr ((4294967296 * ext_Z true 0 4 cnt + -4294967296) mod 2^64) 30 < 2^34) by (rewrite Z.shiftr_div_pow2 by lia; pose proof (Z.mod_pos_bound (4294967296 * ext_Z true 0 4 cnt + -4294967296) (2^64) ltac:(lia)); split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  split.
  { unfold AXF_qnewp.sr_qnewp.
    apply (regs_ok_pin E _ regs 22); [apply (regs_ok_pin E _ regs 14); [apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 1); [apply regs_ok_id|]|]|]|]|]|]|].
    - rewrite qnewp_R1. reflexivity.
    - rewrite qnewp_R9. reflexivity.
    - rewrite qnewp_R10. reflexivity.
    - rewrite qnewp_R11. reflexivity.
    - rewrite qnewp_R13. reflexivity.
    - rewrite qnewp_R14. reflexivity.
    - rewrite qnewp_R22. reflexivity. }
  unfold know_ok, AXF_qnewp.kn_qnewp.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_qnewp.e_QC AXF_qnewp.e_CA AXF_qnewp.e_cnt AXF_qnewp.e_qb AXF_qnewp.e_csz AXF_qnewp.e_sz AXF_qnewp.e_mp AXF_qnewp.e_mx AXF_qnewp.e_cp AXF_qnewp.e_SB AXF_qnewp.e_st AXF_qnewp.CHP AXF_qnewp.BAT AXF_qnewp.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range QC _ _ qnewp_rng_QC eq_refl eq_refl), ?(mod64_of_range CA _ _ qnewp_rng_CA eq_refl eq_refl), ?(mod64_of_range cnt _ _ qnewp_rng_cnt eq_refl eq_refl), ?(mod64_of_range qb _ _ qnewp_rng_qb eq_refl eq_refl), ?(mod64_of_range sz _ _ qnewp_rng_sz eq_refl eq_refl), ?(mod64_of_range mx _ _ qnewp_rng_mx eq_refl eq_refl), ?(mod64_of_range cp _ _ qnewp_rng_cp eq_refl eq_refl), ?(mod64_of_range SB _ _ qnewp_rng_SB eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply qnewp_kwr8 | apply qnewp_kwr10 | apply qnewp_kwr15 | apply qnewp_kwr16]; assumption).
  all: try (clear - qnewp_rng_QC qnewp_rng_CA qnewp_rng_cnt qnewp_rng_qb qnewp_rng_csz qnewp_rng_sz qnewp_rng_mp qnewp_rng_mx qnewp_rng_cp qnewp_rng_SB qnewp_rng_st qnewp_ka2 qnewp_kr3 qnewp_ka5 HQ HP; lia).
  all: first [lia].
Qed.


Definition qnewp_mem_pnewp (m : word -> option byte) (regs : bvmap 5 word) (QC CA cnt qb csz sz mp mx cp SB st : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa 277240))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa QC))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -48)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -56)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21))))))) (wa (CA + 1920)) (word_to_le_bytes 4 (wa (ext_Z true 0 4 cnt + -1)))) (wa (CA + 2576)) (word_to_le_bytes 8 (wa (csz + st)))) (wa (SB + (16 * ext_Z false 0 4 cp) + 103079215104)) (word_to_le_bytes 8 (wa 0))) (wa (SB + (16 * ext_Z false 0 4 cp) + 103079215112)) (word_to_le_bytes 8 (wa (sz + 8192)))) (wa (SB + (16 * ext_Z false 0 4 cp) + 103079215120)) (word_to_le_bytes 8 (wa 1))) (wa (SB + (16 * ext_Z false 0 4 cp) + 103079215128)) (word_to_le_bytes 8 (wa mp))) (wa (QC + 8)) (word_to_le_bytes 8 (wa ((SB + (16 * ext_Z false 0 4 cp)) + 103079215104)))) (wa (QC + 0)) (word_to_le_bytes 8 (wa 1))) (wa (QC + 16)) (word_to_le_bytes 8 (wa ((SB + (16 * ext_Z false 0 4 cp)) + 103079215104)))) (wa (QC + 24)) (word_to_le_bytes 8 (wa ((qb + sz) + 8192))).

#[using="Type"] Theorem qnewp_pnewp : forall regs m rom QC CA cnt qb csz sz mp mx cp SB st, qnewp_pre regs m QC CA cnt qb csz sz mp mx cp SB st ->
  scs_denot SEGS m (Ez regs (VALS_qnewp QC CA cnt qb csz sz mp mx cp SB st)) (snd (fst AXF_qnewp.RES_pnewp)) ->
  exists R, msteps SEGS (mkst regs (wa 0x43b04) m rom) (mkst R (wa 0x43a30) (qnewp_mem_pnewp m regs QC CA cnt qb csz sz mp mx cp SB st) rom) /\
    getr R 1 = wa 277240 /\ getr R 9 = wa QC /\ getr R 10 = wa ((qb + sz) + 8192) /\ getr R 11 = wa ((qb + sz) + 8192) /\ getr R 12 = wa 1 /\ getr R 13 = wa mp /\ getr R 14 = wa (sz + 8192) /\ getr R 15 = wa 0 /\ getr R 16 = wa 103079215104 /\ getr R 22 = wa mx /\ (forall k, In k [2; 3; 4; 5; 6; 7; 8; 17; 18; 19; 20; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom QC CA cnt qb csz sz mp mx cp SB st P Hsc. destruct (qnewp_setup regs m QC CA cnt qb csz sz mp mx cp SB st P) as [HR HK].
  set (E := Ez regs (VALS_qnewp QC CA cnt qb csz sz mp mx cp SB st)) in *. destruct P as [qnewp_R1 qnewp_R9 qnewp_R10 qnewp_R11 qnewp_R13 qnewp_R14 qnewp_R22 qnewp_HSTK qnewp_rng_QC qnewp_rng_CA qnewp_rng_cnt qnewp_rng_qb qnewp_rng_csz qnewp_rng_sz qnewp_rng_mp qnewp_rng_mx qnewp_rng_cp qnewp_rng_SB qnewp_rng_st qnewp_ka2 qnewp_kr3 qnewp_ka5 qnewp_kw6 qnewp_kw7 qnewp_kwr8 qnewp_kw9 qnewp_kwr10 qnewp_kw11 qnewp_kw12 qnewp_kw13 qnewp_kw14 qnewp_kwr15 qnewp_kwr16].
  assert (Z32 : bv_unsigned (ev E 32) = QC) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = qb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = csz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = mp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = mx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = cp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = SB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = st) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  assert (HQ : 0 <= ext_Z false 0 4 cp < 2^32) by (unfold ext_Z; change (2 ^ (8 * Z.of_nat 0)) with 1; rewrite Z.div_1_r; change (2 ^ (8 * Z.of_nat 4)) with 4294967296; apply Z.mod_pos_bound; lia).
  assert (HP : 0 <= Z.shiftr ((4294967296 * ext_Z true 0 4 cnt + -4294967296) mod 2^64) 30 < 2^34) by (rewrite Z.shiftr_div_pow2 by lia; pose proof (Z.mod_pos_bound (4294967296 * ext_Z true 0 4 cnt + -4294967296) (2^64) ltac:(lia)); split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  destruct (run_sound SEGS 100 [0x43a30] AXF_qnewp.scr_pnewp 0x43b04 AXF_qnewp.sr_qnewp AXF_qnewp.kn_qnewp 43 _ _ _ E m rom regs AXF_qnewp.RES_pnewp_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_qnewp.RES_pnewp fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (qnewp_mem_pnewp m regs QC CA cnt qb csz sz mp mx cp SB st) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold qnewp_mem_pnewp. repeat (apply (f_equal3 wbytes)); try reflexivity.
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

End QNEWP.
End AXF_qnewpz.


Module AXF_qhead.
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

Definition e_QC := EVar 32.
Definition e_CA := EVar 33.
Definition e_sz := EVar 34.
Definition e_mp := EVar 35.
Definition STK := SA (EVar 2) (-1024).
Definition sr_qhead := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (e_QC)) 11 (e_CA)) 13 (e_mp)) 14 (e_sz)).
Definition kn_qhead : list kentry :=
  [ KRange e_QC 1 (2^47);
    KRange e_CA 1 (2^47);
    KAlign e_CA 16;
    KRange (EVar 2) (2^46) (2^47);
    KWord (SA e_QC 0) 8 (ELit 0);
    KWord (SA e_CA 1920) 4 (ELit 0);
    KWr STK (ELit 1024) ].
Definition scr_qhead : scripts := SCR [] [] [].
Definition ss_qhead := SS 0x43b04 sr_qhead [] kn_qhead 36.
Definition RUN_qhead := sym_exec SEGS 60 true [0x43c54] scr_qhead ss_qhead [].

Definition scr_phead : scripts := SCR [] [] [].
Definition RES_phead := Eval vm_compute in sym_exec SEGS 60 true [0x43c54] scr_phead ss_qhead [].
Lemma RES_phead_ok : sym_exec SEGS 60 true [0x43c54] scr_phead (SS 0x43b04 sr_qhead [] kn_qhead 36) [] = RES_phead.
Proof. vm_compute. reflexivity. Qed.
End AXF_qhead.


Module AXF_qheadz.
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

Section QHEAD.
Context {fx : FPState}.

Definition VALS_qhead (QC CA sz mp : Z) : list Z := [QC; CA; sz; mp].

Record qhead_pre (regs : bvmap 5 word) (m : word -> option byte) (QC CA sz mp : Z) : Prop := {
  qhead_R10 : getr regs 10 = wa QC ;
  qhead_R11 : getr regs 11 = wa CA ;
  qhead_R13 : getr regs 13 = wa mp ;
  qhead_R14 : getr regs 14 = wa sz ;
  qhead_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  qhead_rng_QC : 1 <= QC <= 2^47 ;
  qhead_rng_CA : 1 <= CA <= 2^47 ;
  qhead_rng_sz : 0 <= sz <= 2^40 ;
  qhead_rng_mp : 0 <= mp <= 2^64-1 ;
  qhead_ka2 : CA mod 16 = 0 ;
  qhead_kr3 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  qhead_kw4 : rdn SEGS m (wa (QC + 0)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  qhead_kw5 : rdn SEGS m (wa (CA + 1920)) 4 = Some (word_to_le_bytes 4 (wa 0))
}.


#[using="Type"] Lemma qhead_setup : forall regs m QC CA sz mp, qhead_pre regs m QC CA sz mp ->
  regs_ok (Ez regs (VALS_qhead QC CA sz mp)) AXF_qhead.sr_qhead regs /\ know_ok SEGS (Ez regs (VALS_qhead QC CA sz mp)) m AXF_qhead.kn_qhead.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m QC CA sz mp P. destruct P as [qhead_R10 qhead_R11 qhead_R13 qhead_R14 qhead_HSTK qhead_rng_QC qhead_rng_CA qhead_rng_sz qhead_rng_mp qhead_ka2 qhead_kr3 qhead_kw4 qhead_kw5].
  set (E := Ez regs (VALS_qhead QC CA sz mp)).
  assert (Z32 : bv_unsigned (ev E 32) = QC) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = mp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  split.
  { unfold AXF_qhead.sr_qhead.
    apply (regs_ok_pin E _ regs 14); [apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|]|]|].
    - rewrite qhead_R10. reflexivity.
    - rewrite qhead_R11. reflexivity.
    - rewrite qhead_R13. reflexivity.
    - rewrite qhead_R14. reflexivity. }
  unfold know_ok, AXF_qhead.kn_qhead.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_qhead.e_QC AXF_qhead.e_CA AXF_qhead.e_sz AXF_qhead.e_mp AXF_qhead.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range QC _ _ qhead_rng_QC eq_refl eq_refl), ?(mod64_of_range CA _ _ qhead_rng_CA eq_refl eq_refl), ?(mod64_of_range sz _ _ qhead_rng_sz eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - qhead_rng_QC qhead_rng_CA qhead_rng_sz qhead_rng_mp qhead_ka2 qhead_kr3; lia).
  all: first [lia].
Qed.


Definition qhead_mem_phead (m : word -> option byte) (regs : bvmap 5 word) (QC CA sz mp : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -48)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -56)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))))).

#[using="Type"] Theorem qhead_phead : forall regs m rom QC CA sz mp, qhead_pre regs m QC CA sz mp ->
  scs_denot SEGS m (Ez regs (VALS_qhead QC CA sz mp)) (snd (fst AXF_qhead.RES_phead)) ->
  exists R, msteps SEGS (mkst regs (wa 0x43b04) m rom) (mkst R (wa 0x43c54) (qhead_mem_phead m regs QC CA sz mp) rom) /\
    getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -64) /\ getr R 8 = wa (CA + 1920) /\ getr R 9 = wa CA /\ getr R 10 = wa CA /\ getr R 11 = wa (CA + 1920) /\ getr R 12 = wa 923480 /\ getr R 13 = wa 24 /\ getr R 14 = wa sz /\ getr R 15 = wa 923480 /\ getr R 18 = wa mp /\ getr R 19 = wa QC /\ getr R 20 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 12)))) /\ getr R 21 = wa sz /\ (forall k, In k [1; 3; 4; 5; 6; 7; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom QC CA sz mp P Hsc. destruct (qhead_setup regs m QC CA sz mp P) as [HR HK].
  set (E := Ez regs (VALS_qhead QC CA sz mp)) in *. destruct P as [qhead_R10 qhead_R11 qhead_R13 qhead_R14 qhead_HSTK qhead_rng_QC qhead_rng_CA qhead_rng_sz qhead_rng_mp qhead_ka2 qhead_kr3 qhead_kw4 qhead_kw5].
  assert (Z32 : bv_unsigned (ev E 32) = QC) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = mp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  destruct (run_sound SEGS 60 [0x43c54] AXF_qhead.scr_phead 0x43b04 AXF_qhead.sr_qhead AXF_qhead.kn_qhead 36 _ _ _ E m rom regs AXF_qhead.RES_phead_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_qhead.RES_phead fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (qhead_mem_phead m regs QC CA sz mp) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold qhead_mem_phead. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End QHEAD.
End AXF_qheadz.


Module AXF_qnpr.
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

Definition e_CA := EVar 32.
Definition e_CLS := EVar 33.
Definition e_mc := EVar 34.
Definition REC := EAlu ALU_ADD e_CA (EMd M_MUL (ELit 80) e_CLS).
Definition STK := SA (EVar 2) (-1024).
Definition sr_qnpr := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (e_CA)) 11 (REC)) 12 (ELit 923480)) 13 (e_CLS)).
Definition kn_qnpr : list kentry :=
  [ KRange e_CA 1 (2^47);
    KAlign e_CA 16;
    KRange e_CLS 1 30;
    KRange (EVar 2) (2^46) (2^47);
    KWord (SA REC 4) 4 e_mc;
    KWr STK (ELit 1024) ].
Definition scr_qnpr : scripts := SCR [false] [] [].
Definition ss_qnpr := SS 0x43c54 sr_qnpr [] kn_qnpr 35.
Definition RUN_qnpr := sym_exec SEGS 40 true [0x44474] scr_qnpr ss_qnpr [].

Definition scr_pnpr : scripts := SCR [false] [] [].
Definition RES_pnpr := Eval vm_compute in sym_exec SEGS 40 true [0x44474] scr_pnpr ss_qnpr [].
Lemma RES_pnpr_ok : sym_exec SEGS 40 true [0x44474] scr_pnpr (SS 0x43c54 sr_qnpr [] kn_qnpr 35) [] = RES_pnpr.
Proof. vm_compute. reflexivity. Qed.
End AXF_qnpr.


Module AXF_qnprz.
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

Section QNPR.
Context {fx : FPState}.

Definition VALS_qnpr (CA CLS mc : Z) : list Z := [CA; CLS; mc].

Record qnpr_pre (regs : bvmap 5 word) (m : word -> option byte) (CA CLS mc : Z) : Prop := {
  qnpr_R10 : getr regs 10 = wa CA ;
  qnpr_R11 : getr regs 11 = wa (CA + (80 * CLS)) ;
  qnpr_R12 : getr regs 12 = wa 923480 ;
  qnpr_R13 : getr regs 13 = wa CLS ;
  qnpr_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  qnpr_rng_CA : 1 <= CA <= 2^47 ;
  qnpr_rng_CLS : 1 <= CLS <= 30 ;
  qnpr_rng_mc : 2 <= mc <= 16 ;
  qnpr_ka1 : CA mod 16 = 0 ;
  qnpr_kr3 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  qnpr_kw4 : rdn SEGS m (wa (CA + (80 * CLS) + 4)) 4 = Some (word_to_le_bytes 4 (wa mc))
}.


#[using="Type"] Lemma qnpr_setup : forall regs m CA CLS mc, qnpr_pre regs m CA CLS mc ->
  regs_ok (Ez regs (VALS_qnpr CA CLS mc)) AXF_qnpr.sr_qnpr regs /\ know_ok SEGS (Ez regs (VALS_qnpr CA CLS mc)) m AXF_qnpr.kn_qnpr.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m CA CLS mc P. destruct P as [qnpr_R10 qnpr_R11 qnpr_R12 qnpr_R13 qnpr_HSTK qnpr_rng_CA qnpr_rng_CLS qnpr_rng_mc qnpr_ka1 qnpr_kr3 qnpr_kw4].
  set (E := Ez regs (VALS_qnpr CA CLS mc)).
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = CLS) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = mc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  split.
  { unfold AXF_qnpr.sr_qnpr.
    apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|]|]|].
    - rewrite qnpr_R10. reflexivity.
    - rewrite qnpr_R11, zeval_sound. cbn [zeval edenot AXF_qnpr.e_CA AXF_qnpr.e_CLS AXF_qnpr.e_mc AXF_qnpr.REC AXF_qnpr.STK]. rewrite ?Z32, ?Z33, ?Z34, ?Z2. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite qnpr_R12. reflexivity.
    - rewrite qnpr_R13. reflexivity. }
  unfold know_ok, AXF_qnpr.kn_qnpr.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_qnpr.e_CA AXF_qnpr.e_CLS AXF_qnpr.e_mc AXF_qnpr.REC AXF_qnpr.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range CA _ _ qnpr_rng_CA eq_refl eq_refl), ?(mod64_of_range CLS _ _ qnpr_rng_CLS eq_refl eq_refl), ?(mod64_of_range mc _ _ qnpr_rng_mc eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - qnpr_rng_CA qnpr_rng_CLS qnpr_rng_mc qnpr_ka1 qnpr_kr3; lia).
  all: first [lia].
Qed.


Definition qnpr_mem_pnpr (m : word -> option byte) (regs : bvmap 5 word) (CA CLS mc : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa 277592))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))))).

#[using="Type"] Theorem qnpr_pnpr : forall regs m rom CA CLS mc, qnpr_pre regs m CA CLS mc ->
  scs_denot SEGS m (Ez regs (VALS_qnpr CA CLS mc)) (snd (fst AXF_qnpr.RES_pnpr)) ->
  exists R, msteps SEGS (mkst regs (wa 0x43c54) m rom) (mkst R (wa 0x44474) (qnpr_mem_pnpr m regs CA CLS mc) rom) /\
    getr R 1 = wa 277592 /\ getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -32) /\ getr R 8 = wa (CA + (80 * CLS)) /\ getr R 9 = wa (bv_unsigned (edenot (Ez regs (VALS_qnpr CA CLS mc)) (EAluw ALU_SRL (EExt true 0 4 (EVar 34)) (ELit 1)))) /\ getr R 10 = wa 923480 /\ getr R 11 = wa (CA + 2560) /\ getr R 12 = wa CLS /\ getr R 13 = wa ((CA + (80 * CLS)) + 16) /\ getr R 14 = wa (bv_unsigned (edenot (Ez regs (VALS_qnpr CA CLS mc)) (EAluw ALU_SRL (EExt true 0 4 (EVar 34)) (ELit 1)))) /\ (forall k, In k [3; 4; 5; 6; 7; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom CA CLS mc P Hsc. destruct (qnpr_setup regs m CA CLS mc P) as [HR HK].
  set (E := Ez regs (VALS_qnpr CA CLS mc)) in *. destruct P as [qnpr_R10 qnpr_R11 qnpr_R12 qnpr_R13 qnpr_HSTK qnpr_rng_CA qnpr_rng_CLS qnpr_rng_mc qnpr_ka1 qnpr_kr3 qnpr_kw4].
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = CLS) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = mc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  destruct (run_sound SEGS 40 [0x44474] AXF_qnpr.scr_pnpr 0x43c54 AXF_qnpr.sr_qnpr AXF_qnpr.kn_qnpr 35 _ _ _ E m rom regs AXF_qnpr.RES_pnpr_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_qnpr.RES_pnpr fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (qnpr_mem_pnpr m regs CA CLS mc) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold qnpr_mem_pnpr. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End QNPR.
End AXF_qnprz.


Module AXF_qnri.
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

Definition e_CA := EVar 32.
Definition e_CLS := EVar 33.
Definition REC := EAlu ALU_ADD e_CA (EMd M_MUL (ELit 80) e_CLS).
Definition STK := SA (EVar 2) (-1024).
Definition sr_qnri := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (e_CA)) 11 (REC)) 12 (ELit 923480)) 13 (e_CLS)).
Definition kn_qnri : list kentry :=
  [ KRange e_CA 1 (2^47);
    KAlign e_CA 16;
    KRange e_CLS 1 30;
    KRange (EVar 2) (2^46) (2^47);
    KWord (SA REC 4) 4 (ELit 0);
    KWr (SA e_CA 84) (ELit 2488);
    KWr STK (ELit 1024) ].
Definition scr_qnri : scripts := SCR [] [] [].
Definition ss_qnri := SS 0x43c54 sr_qnri [] kn_qnri 34.
Definition RUN_qnri := sym_exec SEGS 900 true [0x44530] scr_qnri ss_qnri [].

Definition scr_pnri : scripts := SCR [] [] [].
Definition RES_pnri := Eval vm_compute in sym_exec SEGS 900 true [0x44530] scr_pnri ss_qnri [].
Lemma RES_pnri_ok : sym_exec SEGS 900 true [0x44530] scr_pnri (SS 0x43c54 sr_qnri [] kn_qnri 34) [] = RES_pnri.
Proof. vm_compute. reflexivity. Qed.
End AXF_qnri.


Module AXF_qnriz.
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

Section QNRI.
Context {fx : FPState}.

Definition VALS_qnri (CA CLS : Z) : list Z := [CA; CLS].

Record qnri_pre (regs : bvmap 5 word) (m : word -> option byte) (CA CLS : Z) : Prop := {
  qnri_R10 : getr regs 10 = wa CA ;
  qnri_R11 : getr regs 11 = wa (CA + (80 * CLS)) ;
  qnri_R12 : getr regs 12 = wa 923480 ;
  qnri_R13 : getr regs 13 = wa CLS ;
  qnri_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  qnri_rng_CA : 1 <= CA <= 2^47 ;
  qnri_rng_CLS : 1 <= CLS <= 30 ;
  qnri_ka1 : CA mod 16 = 0 ;
  qnri_kr3 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  qnri_kw4 : rdn SEGS m (wa (CA + (80 * CLS) + 4)) 4 = Some (word_to_le_bytes 4 (wa 0)) ;
  qnri_kwr5 : forall d k, 0 <= d -> d + Z.of_nat k <= 2488 -> store_ok SEGS m (wa (CA + 84 + d)) k = true
}.


#[using="Type"] Lemma qnri_setup : forall regs m CA CLS, qnri_pre regs m CA CLS ->
  regs_ok (Ez regs (VALS_qnri CA CLS)) AXF_qnri.sr_qnri regs /\ know_ok SEGS (Ez regs (VALS_qnri CA CLS)) m AXF_qnri.kn_qnri.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m CA CLS P. destruct P as [qnri_R10 qnri_R11 qnri_R12 qnri_R13 qnri_HSTK qnri_rng_CA qnri_rng_CLS qnri_ka1 qnri_kr3 qnri_kw4 qnri_kwr5].
  set (E := Ez regs (VALS_qnri CA CLS)).
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = CLS) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  split.
  { unfold AXF_qnri.sr_qnri.
    apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|]|]|].
    - rewrite qnri_R10. reflexivity.
    - rewrite qnri_R11, zeval_sound. cbn [zeval edenot AXF_qnri.e_CA AXF_qnri.e_CLS AXF_qnri.REC AXF_qnri.STK]. rewrite ?Z32, ?Z33, ?Z2. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite qnri_R12. reflexivity.
    - rewrite qnri_R13. reflexivity. }
  unfold know_ok, AXF_qnri.kn_qnri.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_qnri.e_CA AXF_qnri.e_CLS AXF_qnri.REC AXF_qnri.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range CA _ _ qnri_rng_CA eq_refl eq_refl), ?(mod64_of_range CLS _ _ qnri_rng_CLS eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply qnri_kwr5]; assumption).
  all: try (clear - qnri_rng_CA qnri_rng_CLS qnri_ka1 qnri_kr3; lia).
  all: first [lia].
Qed.


Definition qnri_mem_pnri (m : word -> option byte) (regs : bvmap 5 word) (CA CLS : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa 277592))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))))))) (wa (CA + 84)) (word_to_le_bytes 4 (wa 16))) (wa (CA + 88)) (word_to_le_bytes 8 (wa 32))) (wa (CA + 164)) (word_to_le_bytes 4 (wa 16))) (wa (CA + 168)) (word_to_le_bytes 8 (wa 64))) (wa (CA + 244)) (word_to_le_bytes 4 (wa 16))) (wa (CA + 248)) (word_to_le_bytes 8 (wa 96))) (wa (CA + 324)) (word_to_le_bytes 4 (wa 16))) (wa (CA + 328)) (word_to_le_bytes 8 (wa 128))) (wa (CA + 404)) (word_to_le_bytes 4 (wa 12))) (wa (CA + 408)) (word_to_le_bytes 8 (wa 160))) (wa (CA + 484)) (word_to_le_bytes 4 (wa 10))) (wa (CA + 488)) (word_to_le_bytes 8 (wa 192))) (wa (CA + 564)) (word_to_le_bytes 4 (wa 8))) (wa (CA + 568)) (word_to_le_bytes 8 (wa 224))) (wa (CA + 644)) (word_to_le_bytes 4 (wa 8))) (wa (CA + 648)) (word_to_le_bytes 8 (wa 256))) (wa (CA + 724)) (word_to_le_bytes 4 (wa 6))) (wa (CA + 728)) (word_to_le_bytes 8 (wa 288))) (wa (CA + 804)) (word_to_le_bytes 4 (wa 6))) (wa (CA + 808)) (word_to_le_bytes 8 (wa 320))) (wa (CA + 884)) (word_to_le_bytes 4 (wa 4))) (wa (CA + 888)) (word_to_le_bytes 8 (wa 352))) (wa (CA + 964)) (word_to_le_bytes 4 (wa 4))) (wa (CA + 968)) (word_to_le_bytes 8 (wa 384))) (wa (CA + 1044)) (word_to_le_bytes 4 (wa 4))) (wa (CA + 1048)) (word_to_le_bytes 8 (wa 416))) (wa (CA + 1124)) (word_to_le_bytes 4 (wa 4))) (wa (CA + 1128)) (word_to_le_bytes 8 (wa 448))) (wa (CA + 1204)) (word_to_le_bytes 4 (wa 4))) (wa (CA + 1208)) (word_to_le_bytes 8 (wa 480))) (wa (CA + 1284)) (word_to_le_bytes 4 (wa 4))) (wa (CA + 1288)) (word_to_le_bytes 8 (wa 512))) (wa (CA + 1364)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 1368)) (word_to_le_bytes 8 (wa 768))) (wa (CA + 1444)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 1448)) (word_to_le_bytes 8 (wa 1024))) (wa (CA + 1524)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 1528)) (word_to_le_bytes 8 (wa 1536))) (wa (CA + 1604)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 1608)) (word_to_le_bytes 8 (wa 2048))) (wa (CA + 1684)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 1688)) (word_to_le_bytes 8 (wa 3072))) (wa (CA + 1764)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 1768)) (word_to_le_bytes 8 (wa 4096))) (wa (CA + 1844)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 1848)) (word_to_le_bytes 8 (wa 6144))) (wa (CA + 1924)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 1928)) (word_to_le_bytes 8 (wa 8192))) (wa (CA + 2004)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 2008)) (word_to_le_bytes 8 (wa 12288))) (wa (CA + 2084)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 2088)) (word_to_le_bytes 8 (wa 16384))) (wa (CA + 2164)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 2168)) (word_to_le_bytes 8 (wa 24576))) (wa (CA + 2244)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 2248)) (word_to_le_bytes 8 (wa 32768))) (wa (CA + 2324)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 2328)) (word_to_le_bytes 8 (wa 49152))) (wa (CA + 2404)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 2408)) (word_to_le_bytes 8 (wa 65536))) (wa (CA + 2484)) (word_to_le_bytes 4 (wa 16))) (wa (CA + 2488)) (word_to_le_bytes 8 (wa 64)).

#[using="Type"] Theorem qnri_pnri : forall regs m rom CA CLS, qnri_pre regs m CA CLS ->
  scs_denot SEGS m (Ez regs (VALS_qnri CA CLS)) (snd (fst AXF_qnri.RES_pnri)) ->
  exists R, msteps SEGS (mkst regs (wa 0x43c54) m rom) (mkst R (wa 0x44530) (qnri_mem_pnri m regs CA CLS) rom) /\
    getr R 1 = wa 277592 /\ getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -32) /\ getr R 5 = wa 16 /\ getr R 6 = wa 17 /\ getr R 7 = wa 512 /\ getr R 8 = wa (CA + (80 * CLS)) /\ getr R 10 = wa CA /\ getr R 11 = wa (CA + 2568) /\ getr R 12 = wa 923480 /\ getr R 13 = wa 1024 /\ getr R 14 = wa CLS /\ getr R 15 = wa 16 /\ getr R 16 = wa 15 /\ getr R 17 = wa 1024 /\ getr R 28 = wa 64 /\ getr R 29 = wa 16 /\ getr R 30 = wa 0 /\ (forall k, In k [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom CA CLS P Hsc. destruct (qnri_setup regs m CA CLS P) as [HR HK].
  set (E := Ez regs (VALS_qnri CA CLS)) in *. destruct P as [qnri_R10 qnri_R11 qnri_R12 qnri_R13 qnri_HSTK qnri_rng_CA qnri_rng_CLS qnri_ka1 qnri_kr3 qnri_kw4 qnri_kwr5].
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = CLS) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  destruct (run_sound SEGS 900 [0x44530] AXF_qnri.scr_pnri 0x43c54 AXF_qnri.sr_qnri AXF_qnri.kn_qnri 34 _ _ _ E m rom regs AXF_qnri.RES_pnri_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_qnri.RES_pnri fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (qnri_mem_pnri m regs CA CLS) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold qnri_mem_pnri. repeat (apply (f_equal3 wbytes)); try reflexivity.
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

End QNRI.
End AXF_qnriz.


Module AXF_qngt.
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

Definition e_CA := EVar 32.
Definition e_QC := EVar 33.
Definition e_n := EVar 34.
Definition e_SB := EVar 35.
Definition e_RIB := EVar 36.
Definition e_na := EVar 37.
Definition e_cp := EVar 38.
Definition e_csz := EVar 39.
Definition e_st := EVar 40.
Definition e_qb := EVar 41.
Definition e_sz := EVar 42.
Definition e_mp := EVar 43.
Definition e_mx := EVar 44.
Definition e_stk := EVar 45.
Definition e_g7 := EVar 46.
Definition e_g8 := EVar 47.
Definition e_g9 := EVar 48.
Definition e_g10 := EVar 49.
Definition e_g11 := EVar 50.
Definition e_c0 := EVar 51.
Definition e_c2 := EVar 52.
Definition e_c3 := EVar 53.
Definition e_c4 := EVar 54.
Definition e_c5 := EVar 55.
Definition REC := EAlu ALU_ADD e_CA (ELit 1920).
Definition RI := EAlu ALU_ADD e_RIB (ELit 3072).
Definition CHP := EAlu ALU_ADD e_CA (EAlu ALU_SRL (EAlu ALU_ADD (EMd M_MUL (ELit 4294967296) (EExt true 0 4 e_n)) (ELit (-4294967296))) (ELit 30)).
Definition BAT := EAlu ALU_ADD e_SB (EMd M_MUL (ELit 16) (EExt false 0 4 e_cp)).
Definition STK := SA (EVar 2) (-1024).
Definition sr_qngt := (sr_upd (sr_upd (sr_upd sr_id 8 (RI)) 14 (e_n)) 19 (ELit 2305843009213693952)).
Definition kn_qngt : list kentry :=
  [ KRange e_CA 1 (2^47);
    KAlign e_CA 16;
    KRange e_QC 1 (2^47);
    KRange (EVar 2) (2^46) (2^47);
    KRange e_RIB 1 (2^47);
    KAlign e_RIB 128;
    KRange e_SB 4194304 (2^47);
    KAlign e_SB 4096;
    KWord (SA e_RIB 3144) 8 e_na;
    KWr (SA e_RIB 3144) (ELit 8);
    KWord (SA e_RIB 3072) 8 (ELit 1152921504606846976);
    KWr (SA e_RIB 3072) (ELit 8);
    KWord (SA (EVar 2) 120) 8 (ELit 279672);
    KWord (SA (EVar 2) 112) 8 REC;
    KWord (SA (EVar 2) 104) 8 e_n;
    KWord (SA (EVar 2) 96) 8 e_mp;
    KWord (SA (EVar 2) 88) 8 e_QC;
    KWord (SA (EVar 2) 80) 8 e_stk;
    KWord (SA (EVar 2) 72) 8 e_sz;
    KWord (SA (EVar 2) 64) 8 e_mx;
    KWord (SA (EVar 2) 56) 8 e_g7;
    KWord (SA (EVar 2) 48) 8 e_g8;
    KWord (SA (EVar 2) 40) 8 e_g9;
    KWord (SA (EVar 2) 32) 8 e_g10;
    KWord (SA (EVar 2) 24) 8 e_g11;
    KWord (SA (EVar 2) 136) 8 e_CA;
    KWord (SA (EVar 2) 144) 8 REC;
    KWord (SA (EVar 2) 152) 8 (ELit 277592);
    KWord (SA (EVar 2) 168) 8 e_c5;
    KWord (SA (EVar 2) 176) 8 e_c4;
    KWord (SA (EVar 2) 184) 8 e_c3;
    KWord (SA (EVar 2) 192) 8 e_c2;
    KWord (SA (EVar 2) 200) 8 e_QC;
    KWord (SA (EVar 2) 208) 8 e_c0;
    KWord (SA (EVar 2) 216) 8 (ELit 277240);
    KWr (SA e_CA 1920) (ELit 4);
    KWord (SA e_CA 1928) 8 e_csz;
    KWord (SA CHP 1936) 4 e_cp;
    KWord (SA (ELit 0) 923512) 8 e_SB;
    KWord (SA e_CA 2576) 8 e_st;
    KWr (SA e_CA 2576) (ELit 8);
    KWord (SA e_QC 0) 8 (ELit 0);
    KWord (SA e_QC 24) 8 e_qb;
    KWr (SA e_QC 0) (ELit 32);
    KWr (SA BAT 103079215104) (ELit 8192);
    KImg 65536 143360;
    KWr STK (ELit 1024) ].
Definition scr_qngt : scripts := SCR [false] [] [].
Definition ss_qngt := SS 0x446c0 sr_qngt [] kn_qngt 56.
Definition RUN_qngt := sym_exec SEGS 160 true [0x43a30] scr_qngt ss_qngt [].

Definition scr_pngt : scripts := SCR [false] [] [].
Definition RES_pngt := Eval vm_compute in sym_exec SEGS 160 true [0x43a30] scr_pngt ss_qngt [].
Lemma RES_pngt_ok : sym_exec SEGS 160 true [0x43a30] scr_pngt (SS 0x446c0 sr_qngt [] kn_qngt 56) [] = RES_pngt.
Proof. vm_compute. reflexivity. Qed.
End AXF_qngt.


Module AXF_qngtz.
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

Section QNGT.
Context {fx : FPState}.

Definition VALS_qngt (CA QC n SB RIB na cp csz st qb sz mp mx stk g7 g8 g9 g10 g11 c0 c2 c3 c4 c5 : Z) : list Z := [CA; QC; n; SB; RIB; na; cp; csz; st; qb; sz; mp; mx; stk; g7; g8; g9; g10; g11; c0; c2; c3; c4; c5].

Record qngt_pre (regs : bvmap 5 word) (m : word -> option byte) (CA QC n SB RIB na cp csz st qb sz mp mx stk g7 g8 g9 g10 g11 c0 c2 c3 c4 c5 : Z) : Prop := {
  qngt_R8 : getr regs 8 = wa (RIB + 3072) ;
  qngt_R14 : getr regs 14 = wa n ;
  qngt_R19 : getr regs 19 = wa 2305843009213693952 ;
  qngt_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  qngt_rng_CA : 1 <= CA <= 2^47 ;
  qngt_rng_QC : 1 <= QC <= 2^47 ;
  qngt_rng_n : 1 <= n <= 8 ;
  qngt_rng_SB : 4194304 <= SB <= 2^47 ;
  qngt_rng_RIB : 1 <= RIB <= 2^47 ;
  qngt_rng_na : 0 <= na <= 2^64-1 ;
  qngt_rng_cp : 0 <= cp <= 2^32-1 ;
  qngt_rng_csz : 0 <= csz <= 2^64-1 ;
  qngt_rng_st : 0 <= st <= 2^64-1 ;
  qngt_rng_qb : 0 <= qb <= 2^62 ;
  qngt_rng_sz : 0 <= sz <= 2^40 ;
  qngt_rng_mp : 0 <= mp <= 2^64-1 ;
  qngt_rng_mx : 0 <= mx <= 2^62 ;
  qngt_rng_stk : 0 <= stk <= 2^64-1 ;
  qngt_rng_g7 : 0 <= g7 <= 2^64-1 ;
  qngt_rng_g8 : 0 <= g8 <= 2^64-1 ;
  qngt_rng_g9 : 0 <= g9 <= 2^64-1 ;
  qngt_rng_g10 : 0 <= g10 <= 2^64-1 ;
  qngt_rng_g11 : 0 <= g11 <= 2^64-1 ;
  qngt_rng_c0 : 0 <= c0 <= 2^64-1 ;
  qngt_rng_c2 : 0 <= c2 <= 2^64-1 ;
  qngt_rng_c3 : 0 <= c3 <= 2^64-1 ;
  qngt_rng_c4 : 0 <= c4 <= 2^64-1 ;
  qngt_rng_c5 : 0 <= c5 <= 2^64-1 ;
  qngt_ka1 : CA mod 16 = 0 ;
  qngt_kr3 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  qngt_ka5 : RIB mod 128 = 0 ;
  qngt_ka7 : SB mod 4096 = 0 ;
  qngt_kw8 : rdn SEGS m (wa (RIB + 3144)) 8 = Some (word_to_le_bytes 8 (wa na)) ;
  qngt_kwr9 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (RIB + 3144 + d)) k = true ;
  qngt_kw10 : rdn SEGS m (wa (RIB + 3072)) 8 = Some (word_to_le_bytes 8 (wa 1152921504606846976)) ;
  qngt_kwr11 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (RIB + 3072 + d)) k = true ;
  qngt_kw12 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 120)) 8 = Some (word_to_le_bytes 8 (wa 279672)) ;
  qngt_kw13 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 112)) 8 = Some (word_to_le_bytes 8 (wa (CA + 1920))) ;
  qngt_kw14 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 104)) 8 = Some (word_to_le_bytes 8 (wa n)) ;
  qngt_kw15 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 96)) 8 = Some (word_to_le_bytes 8 (wa mp)) ;
  qngt_kw16 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 88)) 8 = Some (word_to_le_bytes 8 (wa QC)) ;
  qngt_kw17 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 80)) 8 = Some (word_to_le_bytes 8 (wa stk)) ;
  qngt_kw18 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 72)) 8 = Some (word_to_le_bytes 8 (wa sz)) ;
  qngt_kw19 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 64)) 8 = Some (word_to_le_bytes 8 (wa mx)) ;
  qngt_kw20 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 56)) 8 = Some (word_to_le_bytes 8 (wa g7)) ;
  qngt_kw21 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 48)) 8 = Some (word_to_le_bytes 8 (wa g8)) ;
  qngt_kw22 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 40)) 8 = Some (word_to_le_bytes 8 (wa g9)) ;
  qngt_kw23 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 32)) 8 = Some (word_to_le_bytes 8 (wa g10)) ;
  qngt_kw24 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 24)) 8 = Some (word_to_le_bytes 8 (wa g11)) ;
  qngt_kw25 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 136)) 8 = Some (word_to_le_bytes 8 (wa CA)) ;
  qngt_kw26 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 144)) 8 = Some (word_to_le_bytes 8 (wa (CA + 1920))) ;
  qngt_kw27 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 152)) 8 = Some (word_to_le_bytes 8 (wa 277592)) ;
  qngt_kw28 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 168)) 8 = Some (word_to_le_bytes 8 (wa c5)) ;
  qngt_kw29 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 176)) 8 = Some (word_to_le_bytes 8 (wa c4)) ;
  qngt_kw30 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 184)) 8 = Some (word_to_le_bytes 8 (wa c3)) ;
  qngt_kw31 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 192)) 8 = Some (word_to_le_bytes 8 (wa c2)) ;
  qngt_kw32 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 200)) 8 = Some (word_to_le_bytes 8 (wa QC)) ;
  qngt_kw33 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 208)) 8 = Some (word_to_le_bytes 8 (wa c0)) ;
  qngt_kw34 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 216)) 8 = Some (word_to_le_bytes 8 (wa 277240)) ;
  qngt_kwr35 : forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (CA + 1920 + d)) k = true ;
  qngt_kw36 : rdn SEGS m (wa (CA + 1928)) 8 = Some (word_to_le_bytes 8 (wa csz)) ;
  qngt_kw37 : rdn SEGS m (wa (CA + Z.shiftr ((((4294967296 * ext_Z true 0 4 n) + -4294967296)) mod 2^64) 30 + 1936)) 4 = Some (word_to_le_bytes 4 (wa cp)) ;
  qngt_kw38 : rdn SEGS m (wa (0 + 923512)) 8 = Some (word_to_le_bytes 8 (wa SB)) ;
  qngt_kw39 : rdn SEGS m (wa (CA + 2576)) 8 = Some (word_to_le_bytes 8 (wa st)) ;
  qngt_kwr40 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (CA + 2576 + d)) k = true ;
  qngt_kw41 : rdn SEGS m (wa (QC + 0)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  qngt_kw42 : rdn SEGS m (wa (QC + 24)) 8 = Some (word_to_le_bytes 8 (wa qb)) ;
  qngt_kwr43 : forall d k, 0 <= d -> d + Z.of_nat k <= 32 -> store_ok SEGS m (wa (QC + 0 + d)) k = true ;
  qngt_kwr44 : forall d k, 0 <= d -> d + Z.of_nat k <= 8192 -> store_ok SEGS m (wa (SB + (16 * ext_Z false 0 4 cp) + 103079215104 + d)) k = true ;
  qngt_kimg45 : forall i, 65536 <= i < 143360 -> m (Z_to_bv 64 i) = None
}.


#[using="Type"] Lemma qngt_setup : forall regs m CA QC n SB RIB na cp csz st qb sz mp mx stk g7 g8 g9 g10 g11 c0 c2 c3 c4 c5, qngt_pre regs m CA QC n SB RIB na cp csz st qb sz mp mx stk g7 g8 g9 g10 g11 c0 c2 c3 c4 c5 ->
  regs_ok (Ez regs (VALS_qngt CA QC n SB RIB na cp csz st qb sz mp mx stk g7 g8 g9 g10 g11 c0 c2 c3 c4 c5)) AXF_qngt.sr_qngt regs /\ know_ok SEGS (Ez regs (VALS_qngt CA QC n SB RIB na cp csz st qb sz mp mx stk g7 g8 g9 g10 g11 c0 c2 c3 c4 c5)) m AXF_qngt.kn_qngt.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m CA QC n SB RIB na cp csz st qb sz mp mx stk g7 g8 g9 g10 g11 c0 c2 c3 c4 c5 P. destruct P as [qngt_R8 qngt_R14 qngt_R19 qngt_HSTK qngt_rng_CA qngt_rng_QC qngt_rng_n qngt_rng_SB qngt_rng_RIB qngt_rng_na qngt_rng_cp qngt_rng_csz qngt_rng_st qngt_rng_qb qngt_rng_sz qngt_rng_mp qngt_rng_mx qngt_rng_stk qngt_rng_g7 qngt_rng_g8 qngt_rng_g9 qngt_rng_g10 qngt_rng_g11 qngt_rng_c0 qngt_rng_c2 qngt_rng_c3 qngt_rng_c4 qngt_rng_c5 qngt_ka1 qngt_kr3 qngt_ka5 qngt_ka7 qngt_kw8 qngt_kwr9 qngt_kw10 qngt_kwr11 qngt_kw12 qngt_kw13 qngt_kw14 qngt_kw15 qngt_kw16 qngt_kw17 qngt_kw18 qngt_kw19 qngt_kw20 qngt_kw21 qngt_kw22 qngt_kw23 qngt_kw24 qngt_kw25 qngt_kw26 qngt_kw27 qngt_kw28 qngt_kw29 qngt_kw30 qngt_kw31 qngt_kw32 qngt_kw33 qngt_kw34 qngt_kwr35 qngt_kw36 qngt_kw37 qngt_kw38 qngt_kw39 qngt_kwr40 qngt_kw41 qngt_kw42 qngt_kwr43 qngt_kwr44 qngt_kimg45].
  set (E := Ez regs (VALS_qngt CA QC n SB RIB na cp csz st qb sz mp mx stk g7 g8 g9 g10 g11 c0 c2 c3 c4 c5)).
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = QC) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = SB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = RIB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = na) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = cp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = csz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = st) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = qb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = mp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z44 : bv_unsigned (ev E 44) = mx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z45 : bv_unsigned (ev E 45) = stk) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z46 : bv_unsigned (ev E 46) = g7) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z47 : bv_unsigned (ev E 47) = g8) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z48 : bv_unsigned (ev E 48) = g9) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z49 : bv_unsigned (ev E 49) = g10) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z50 : bv_unsigned (ev E 50) = g11) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z51 : bv_unsigned (ev E 51) = c0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z52 : bv_unsigned (ev E 52) = c2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z53 : bv_unsigned (ev E 53) = c3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z54 : bv_unsigned (ev E 54) = c4) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z55 : bv_unsigned (ev E 55) = c5) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  assert (HQ : 0 <= ext_Z false 0 4 cp < 2^32) by (unfold ext_Z; change (2 ^ (8 * Z.of_nat 0)) with 1; rewrite Z.div_1_r; change (2 ^ (8 * Z.of_nat 4)) with 4294967296; apply Z.mod_pos_bound; lia).
  assert (HP : 0 <= Z.shiftr ((4294967296 * ext_Z true 0 4 n + -4294967296) mod 2^64) 30 < 2^34) by (rewrite Z.shiftr_div_pow2 by lia; pose proof (Z.mod_pos_bound (4294967296 * ext_Z true 0 4 n + -4294967296) (2^64) ltac:(lia)); split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  split.
  { unfold AXF_qngt.sr_qngt.
    apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 14); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|].
    - rewrite qngt_R8, zeval_sound. cbn [zeval edenot AXF_qngt.e_CA AXF_qngt.e_QC AXF_qngt.e_n AXF_qngt.e_SB AXF_qngt.e_RIB AXF_qngt.e_na AXF_qngt.e_cp AXF_qngt.e_csz AXF_qngt.e_st AXF_qngt.e_qb AXF_qngt.e_sz AXF_qngt.e_mp AXF_qngt.e_mx AXF_qngt.e_stk AXF_qngt.e_g7 AXF_qngt.e_g8 AXF_qngt.e_g9 AXF_qngt.e_g10 AXF_qngt.e_g11 AXF_qngt.e_c0 AXF_qngt.e_c2 AXF_qngt.e_c3 AXF_qngt.e_c4 AXF_qngt.e_c5 AXF_qngt.REC AXF_qngt.RI AXF_qngt.CHP AXF_qngt.BAT AXF_qngt.STK]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42, ?Z43, ?Z44, ?Z45, ?Z46, ?Z47, ?Z48, ?Z49, ?Z50, ?Z51, ?Z52, ?Z53, ?Z54, ?Z55, ?Z2. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite qngt_R14. reflexivity.
    - rewrite qngt_R19. reflexivity. }
  unfold know_ok, AXF_qngt.kn_qngt.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_qngt.e_CA AXF_qngt.e_QC AXF_qngt.e_n AXF_qngt.e_SB AXF_qngt.e_RIB AXF_qngt.e_na AXF_qngt.e_cp AXF_qngt.e_csz AXF_qngt.e_st AXF_qngt.e_qb AXF_qngt.e_sz AXF_qngt.e_mp AXF_qngt.e_mx AXF_qngt.e_stk AXF_qngt.e_g7 AXF_qngt.e_g8 AXF_qngt.e_g9 AXF_qngt.e_g10 AXF_qngt.e_g11 AXF_qngt.e_c0 AXF_qngt.e_c2 AXF_qngt.e_c3 AXF_qngt.e_c4 AXF_qngt.e_c5 AXF_qngt.REC AXF_qngt.RI AXF_qngt.CHP AXF_qngt.BAT AXF_qngt.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42, ?Z43, ?Z44, ?Z45, ?Z46, ?Z47, ?Z48, ?Z49, ?Z50, ?Z51, ?Z52, ?Z53, ?Z54, ?Z55, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range CA _ _ qngt_rng_CA eq_refl eq_refl), ?(mod64_of_range QC _ _ qngt_rng_QC eq_refl eq_refl), ?(mod64_of_range n _ _ qngt_rng_n eq_refl eq_refl), ?(mod64_of_range SB _ _ qngt_rng_SB eq_refl eq_refl), ?(mod64_of_range RIB _ _ qngt_rng_RIB eq_refl eq_refl), ?(mod64_of_range cp _ _ qngt_rng_cp eq_refl eq_refl), ?(mod64_of_range qb _ _ qngt_rng_qb eq_refl eq_refl), ?(mod64_of_range sz _ _ qngt_rng_sz eq_refl eq_refl), ?(mod64_of_range mx _ _ qngt_rng_mx eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply qngt_kwr9 | apply qngt_kwr11 | apply qngt_kwr35 | apply qngt_kwr40 | apply qngt_kwr43 | apply qngt_kwr44]; assumption).
  all: try (clear - qngt_rng_CA qngt_rng_QC qngt_rng_n qngt_rng_SB qngt_rng_RIB qngt_rng_na qngt_rng_cp qngt_rng_csz qngt_rng_st qngt_rng_qb qngt_rng_sz qngt_rng_mp qngt_rng_mx qngt_rng_stk qngt_rng_g7 qngt_rng_g8 qngt_rng_g9 qngt_rng_g10 qngt_rng_g11 qngt_rng_c0 qngt_rng_c2 qngt_rng_c3 qngt_rng_c4 qngt_rng_c5 qngt_ka1 qngt_kr3 qngt_ka5 qngt_ka7 HQ HP; lia).
  all: first [lia].
Qed.


Definition qngt_mem_pngt (m : word -> option byte) (regs : bvmap 5 word) (CA QC n SB RIB na cp csz st qb sz mp mx stk g7 g8 g9 g10 g11 c0 c2 c3 c4 c5 : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (RIB + 3144)) (word_to_le_bytes 8 (wa (n + na)))) (wa (RIB + 3072)) (word_to_le_bytes 8 (wa 0))) (wa (CA + 1920)) (word_to_le_bytes 4 (wa n))) (wa (CA + 1920)) (word_to_le_bytes 4 (wa (ext_Z true 0 4 n + -1)))) (wa (CA + 2576)) (word_to_le_bytes 8 (wa (csz + st)))) (wa (SB + (16 * ext_Z false 0 4 cp) + 103079215104)) (word_to_le_bytes 8 (wa 0))) (wa (SB + (16 * ext_Z false 0 4 cp) + 103079215112)) (word_to_le_bytes 8 (wa (sz + 8192)))) (wa (SB + (16 * ext_Z false 0 4 cp) + 103079215120)) (word_to_le_bytes 8 (wa 1))) (wa (SB + (16 * ext_Z false 0 4 cp) + 103079215128)) (word_to_le_bytes 8 (wa mp))) (wa (QC + 8)) (word_to_le_bytes 8 (wa ((SB + (16 * ext_Z false 0 4 cp)) + 103079215104)))) (wa (QC + 0)) (word_to_le_bytes 8 (wa 1))) (wa (QC + 16)) (word_to_le_bytes 8 (wa ((SB + (16 * ext_Z false 0 4 cp)) + 103079215104)))) (wa (QC + 24)) (word_to_le_bytes 8 (wa ((qb + sz) + 8192))).

#[using="Type"] Theorem qngt_pngt : forall regs m rom CA QC n SB RIB na cp csz st qb sz mp mx stk g7 g8 g9 g10 g11 c0 c2 c3 c4 c5, qngt_pre regs m CA QC n SB RIB na cp csz st qb sz mp mx stk g7 g8 g9 g10 g11 c0 c2 c3 c4 c5 ->
  scs_denot SEGS m (Ez regs (VALS_qngt CA QC n SB RIB na cp csz st qb sz mp mx stk g7 g8 g9 g10 g11 c0 c2 c3 c4 c5)) (snd (fst AXF_qngt.RES_pngt)) ->
  exists R, msteps SEGS (mkst regs (wa 0x446c0) m rom) (mkst R (wa 0x43a30) (qngt_mem_pngt m regs CA QC n SB RIB na cp csz st qb sz mp mx stk g7 g8 g9 g10 g11 c0 c2 c3 c4 c5) rom) /\
    getr R 1 = wa 277240 /\ getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 224) /\ getr R 5 = wa 4611686018427387904 /\ getr R 6 = wa 0 /\ getr R 7 = wa 1152921504606846976 /\ getr R 8 = wa c0 /\ getr R 9 = wa QC /\ getr R 10 = wa ((qb + sz) + 8192) /\ getr R 11 = wa ((qb + sz) + 8192) /\ getr R 12 = wa 1 /\ getr R 13 = wa mp /\ getr R 14 = wa (sz + 8192) /\ getr R 15 = wa 0 /\ getr R 16 = wa 103079215104 /\ getr R 17 = wa 18446742974197923840 /\ getr R 18 = wa c2 /\ getr R 19 = wa c3 /\ getr R 20 = wa c4 /\ getr R 21 = wa c5 /\ getr R 22 = wa mx /\ getr R 23 = wa g7 /\ getr R 24 = wa g8 /\ getr R 25 = wa g9 /\ getr R 26 = wa g10 /\ getr R 27 = wa g11 /\ getr R 28 = wa 0 /\ (forall k, In k [3; 4; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom CA QC n SB RIB na cp csz st qb sz mp mx stk g7 g8 g9 g10 g11 c0 c2 c3 c4 c5 P Hsc. destruct (qngt_setup regs m CA QC n SB RIB na cp csz st qb sz mp mx stk g7 g8 g9 g10 g11 c0 c2 c3 c4 c5 P) as [HR HK].
  set (E := Ez regs (VALS_qngt CA QC n SB RIB na cp csz st qb sz mp mx stk g7 g8 g9 g10 g11 c0 c2 c3 c4 c5)) in *. destruct P as [qngt_R8 qngt_R14 qngt_R19 qngt_HSTK qngt_rng_CA qngt_rng_QC qngt_rng_n qngt_rng_SB qngt_rng_RIB qngt_rng_na qngt_rng_cp qngt_rng_csz qngt_rng_st qngt_rng_qb qngt_rng_sz qngt_rng_mp qngt_rng_mx qngt_rng_stk qngt_rng_g7 qngt_rng_g8 qngt_rng_g9 qngt_rng_g10 qngt_rng_g11 qngt_rng_c0 qngt_rng_c2 qngt_rng_c3 qngt_rng_c4 qngt_rng_c5 qngt_ka1 qngt_kr3 qngt_ka5 qngt_ka7 qngt_kw8 qngt_kwr9 qngt_kw10 qngt_kwr11 qngt_kw12 qngt_kw13 qngt_kw14 qngt_kw15 qngt_kw16 qngt_kw17 qngt_kw18 qngt_kw19 qngt_kw20 qngt_kw21 qngt_kw22 qngt_kw23 qngt_kw24 qngt_kw25 qngt_kw26 qngt_kw27 qngt_kw28 qngt_kw29 qngt_kw30 qngt_kw31 qngt_kw32 qngt_kw33 qngt_kw34 qngt_kwr35 qngt_kw36 qngt_kw37 qngt_kw38 qngt_kw39 qngt_kwr40 qngt_kw41 qngt_kw42 qngt_kwr43 qngt_kwr44 qngt_kimg45].
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = QC) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = SB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = RIB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = na) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = cp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = csz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = st) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = qb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = mp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z44 : bv_unsigned (ev E 44) = mx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z45 : bv_unsigned (ev E 45) = stk) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z46 : bv_unsigned (ev E 46) = g7) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z47 : bv_unsigned (ev E 47) = g8) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z48 : bv_unsigned (ev E 48) = g9) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z49 : bv_unsigned (ev E 49) = g10) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z50 : bv_unsigned (ev E 50) = g11) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z51 : bv_unsigned (ev E 51) = c0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z52 : bv_unsigned (ev E 52) = c2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z53 : bv_unsigned (ev E 53) = c3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z54 : bv_unsigned (ev E 54) = c4) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z55 : bv_unsigned (ev E 55) = c5) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  assert (HQ : 0 <= ext_Z false 0 4 cp < 2^32) by (unfold ext_Z; change (2 ^ (8 * Z.of_nat 0)) with 1; rewrite Z.div_1_r; change (2 ^ (8 * Z.of_nat 4)) with 4294967296; apply Z.mod_pos_bound; lia).
  assert (HP : 0 <= Z.shiftr ((4294967296 * ext_Z true 0 4 n + -4294967296) mod 2^64) 30 < 2^34) by (rewrite Z.shiftr_div_pow2 by lia; pose proof (Z.mod_pos_bound (4294967296 * ext_Z true 0 4 n + -4294967296) (2^64) ltac:(lia)); split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  destruct (run_sound SEGS 160 [0x43a30] AXF_qngt.scr_pngt 0x446c0 AXF_qngt.sr_qngt AXF_qngt.kn_qngt 56 _ _ _ E m rom regs AXF_qngt.RES_pngt_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_qngt.RES_pngt fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (qngt_mem_pngt m regs CA QC n SB RIB na cp csz st qb sz mp mx stk g7 g8 g9 g10 g11 c0 c2 c3 c4 c5) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold qngt_mem_pngt. repeat (apply (f_equal3 wbytes)); try reflexivity.
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

End QNGT.
End AXF_qngtz.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.
Local Ltac lenq := rewrite ?length_N_to_le_bytes; change (Z.of_nat 4) with 4 in *; change (Z.of_nat 8) with 8 in *.
Local Ltac znq := change (Z.of_nat 4) with 4 in *; change (Z.of_nat 8) with 8 in *.

(* [comment removed for export] *)
Definition q_inv (m0 : word -> option byte) (QC SB qj qn qb : Z) : Prop :=
  0 <= qb < 2^62 /\ rd m0 (QC + 24) 8 qb /\
  ((qn = 0 /\ qb = 0 /\ rd m0 QC 8 0) \/
   (1 <= qn <= 1021 /\ 0 <= qj < 32 /\ rd m0 QC 8 1 /\ rd m0 (QC + 8) 8 (SB + 103079215104 + 8192 * qj) /\ rd m0 (QC + 16) 8 (SB + 103079215104 + 8192 * qj) /\
    rd m0 (SB + 103079215104 + 8192 * qj + 8) 8 qb /\ rd m0 (SB + 103079215104 + 8192 * qj + 16) 8 qn /\
    wr m0 (SB + 103079215104 + 8192 * qj) 8192)).

(* [comment removed for export] *)
Definition LQD (v1 v8 v9 v18 v19 v20 v21 : Z) : list (Z * nat * Z) :=
  [(-56, 8%nat, v21); (-48, 8%nat, v20); (-40, 8%nat, v19); (-32, 8%nat, v18); (-24, 8%nat, v9); (-16, 8%nat, v8); (-8, 8%nat, v1)].

(* [comment removed for export] *)
Lemma sc_nodrain : forall {fx : FPState} segs base E a b, 0 <= zeval E a < 2^64 -> 0 <= zeval E b < 2^64 -> zeval E b <= zeval E a ->
  scs_denot segs base E [SCBr false BC_LTU a b].
Proof.
  intros fx segs base E a b Ha Hb Hle. unfold scs_denot. constructor; [|constructor].
  apply sc_br_z. rewrite br_ltu_z. rewrite !Z.mod_small by assumption. apply Z.ltb_ge. exact Hle.
Qed.
Lemma scs_res_sound' : forall {fx : FPState} rf df E, Forall (rf_ok E) rf -> Forall (df_ok E) df -> forall segs base l r,
  scs_res rf df l = r -> scs_denot segs base E r -> scs_denot segs base E l.
Proof. intros fx rf df E Hr Hdf segs base l r <- H. exact (scs_res_sound rf df E Hr Hdf segs base l H). Qed.


(* [comment removed for export] *)
Ltac sc_resid rf df R HSPa HX HH :=
  eapply (scs_res_sound' rf df); [ facts_go R HSPa HX HH | facts_go R HSPa HX HH | vm_compute; reflexivity | ].

Section SCQ.
Context {fx : FPState}.
Variables (R : bvmap 5 word) (m : word -> option byte).
Variable SPa : Z.
Hypothesis HSPa : bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 2))) = SPa.

(* [comment removed for export] *)
#[using="fx HSPa"] Lemma sc_qroom : forall QC B qn qb bsz sz mp mx,
  2^46 <= SPa <= 2^47 /\ ((4176 <= QC /\ QC + 4016 <= 65536) \/ 6529104 <= QC) /\ QC + 32 + 320 <= SPa /\ 17697412710400 <= B /\ B + 8192 + 320 <= SPa /\
  (QC + 32 <= B \/ B + 8192 <= QC) /\ 1 <= qn <= 1020 /\ 0 <= qb <= 2^62 /\ 0 <= sz <= 2^40 /\ 0 <= mx <= 2^62 /\ qb + sz <= mx ->
  scs_denot SEGS m (Ez R (AXF_qroomz.VALS_qroom QC B qn qb bsz sz mp mx)) (snd (fst AXF_qroom.RES_proom)).
Proof. LiaFast.lf_pins (fun (fx HSPa : LiaFast.U) => LiaFast.u0).
  intros QC B qn qb bsz sz mp mx HH. unfold AXF_qroomz.VALS_qroom.
  assert (HD : QC + 32 <= B \/ B + 8192 <= QC) by tauto.
  assert (HPL : (4176 <= QC /\ QC + 4016 <= 65536) \/ 6529104 <= QC) by tauto.
  assert (HND : scs_denot SEGS m (Ez R [QC; B; qn; qb; bsz; sz; mp; mx]) [SCBr false BC_LTU (EVar 39) (EAlu ALU_ADD (EVar 35) (EVar 37))]).
  { apply sc_nodrain; cbn [zeval edenot]; zat R; clear - HH; lia. }
  destruct HPL as [HPL|HPL].
  - assert (HD1 : QC + 32 <= B) by (clear - HPL HH; lia). assert (HH2 := conj HPL (conj HD1 HH)); clear HH HD HD1 HPL.
    sc_resid [SPr; (EVar 32, (4176, 61520)); (EVar 33, (17697412710400, 2^47)); (EVar 34, (1, 1020)); (EVar 35, (0, 2^62)); (EVar 37, (0, 2^40)); (EVar 39, (0, 2^62))]
             [(EVar 2, EVar 32, 352); (EVar 2, EVar 33, 8512); (EVar 33, EVar 32, 32)] R HSPa HSPa HH2. exact HND.
  - destruct HD as [HD|HD]; assert (HH2 := conj HPL (conj HD HH)); clear HH HD HPL.
    + sc_resid [SPr; (EVar 32, (6529104, 2^47)); (EVar 33, (17697412710400, 2^47)); (EVar 34, (1, 1020)); (EVar 35, (0, 2^62)); (EVar 37, (0, 2^40)); (EVar 39, (0, 2^62))]
               [(EVar 2, EVar 32, 352); (EVar 2, EVar 33, 8512); (EVar 33, EVar 32, 32)] R HSPa HSPa HH2. exact HND.
    + sc_resid [SPr; (EVar 32, (6529104, 2^47)); (EVar 33, (17697412710400, 2^47)); (EVar 34, (1, 1020)); (EVar 35, (0, 2^62)); (EVar 37, (0, 2^40)); (EVar 39, (0, 2^62))]
               [(EVar 2, EVar 32, 352); (EVar 2, EVar 33, 8512); (EVar 32, EVar 33, 8192)] R HSPa HSPa HH2. exact HND.
Qed.
End SCQ.

(* [comment removed for export] *)
Definition KQ : list nat := [1; 2; 3; 4; 5; 6; 7; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.
Lemma qd_frame : forall m SP v1 v8 v9 v18 v19 v20 v21 x, 2^20 <= SP <= 2^47 -> 0 <= x < 2^64 -> ~ (SP - 56 <= x < SP) ->
  wchainS m SP (LQD v1 v8 v9 v18 v19 v20 v21) (wa x) = m (wa x).
Proof.
  intros m SP v1 v8 v9 v18 v19 v20 v21 x HS Hx H.
  apply (wchainS_frame_in (LQD v1 v8 v9 v18 v19 v20 v21) m SP (-56) 0); [lia | lia | reflexivity | reflexivity | exact Hx | lia].
Qed.

(* [comment removed for export] *)
Section QROOM.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (m : word -> option byte) (regs : bvmap 5 word) (QC SB qj qn qb sz mp mx SP : Z).
Hypothesis IQ : q_inv m QC SB qj qn qb.
Hypothesis Hqn : 1 <= qn <= 1020.
Hypothesis H1 : getr regs 1 = wa 277240.
Hypothesis H2 : getr regs 2 = wa SP.
Hypothesis H9 : getr regs 9 = wa QC.
Hypothesis H10 : getr regs 10 = wa QC.
Hypothesis H13 : getr regs 13 = wa mp.
Hypothesis H14 : getr regs 14 = wa sz.
Hypothesis H22 : getr regs 22 = wa mx.
Hypothesis HSP : 2^46 + 4096 <= SP <= 2^47 /\ SP mod 16 = 0.
Hypothesis HSTK : stk_ok SEGS m (wa SP) 2048.
Hypothesis HQC : ((4176 <= QC /\ QC + 4016 <= 65536) \/ 6529104 <= QC) /\ QC + 32 <= SP - 2048.
Hypothesis HSB : 17594333495296 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048.
Hypothesis HSEP : QC + 32 <= SB \/ SB + 137438953472 + 4096 <= QC.
Hypothesis Hsz : 0 <= sz <= 2^40 /\ 0 <= mp < 2^64 /\ 0 <= mx < 2^62 /\ qb + sz <= mx.
Hypothesis Hwq : wr m (QC + 24) 8.

#[using="mx IQ Hqn H1 H2 H9 H10 H13 H14 H22 HSP HSTK HQC HSB HSEP Hsz Hwq"] Theorem qroom_contract :
  exists R m', msteps SEGS (mkst regs (wa 0x43b04) m rom) (mkst R (wa 0x43a30) m' rom) /\
    (forall k, In k KQ -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
    q_inv m' QC SB qj (qn + 1) (qb + sz) /\
    rd m' (SB + 103079215104 + 8192 * qj + 24 + 8 * qn) 8 mp /\
    (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ (QC + 24 <= x < QC + 32) ->
       ~ (SB + 103079215104 + 8192 * qj + 8 <= x < SB + 103079215104 + 8192 * qj + 24) ->
       ~ (SB + 103079215104 + 8192 * qj + 24 + 8 * qn <= x < SB + 103079215104 + 8192 * qj + 32 + 8 * qn) -> m' (wa x) = m (wa x)) /\
    mem_grows m m'.
Proof. LiaFast.lf_pins (fun (mx IQ Hqn H1 H2 H9 H10 H13 H14 H22 HSP HSTK HQC HSB HSEP Hsz Hwq : LiaFast.U) => LiaFast.u0).
  destruct IQ as (Hqb & Rqb & [[Hq0 _]|(_ & Hqj & Rsz & Rfirst & Rlast & Rbsz & Rcnt & Wb)]); [lia|].
  set (B := SB + 103079215104 + 8192 * qj) in *.
  assert (HZ : ((4176 <= QC /\ QC + 4016 <= 65536) \/ 6529104 <= QC) /\ QC + 32 <= SP - 2048 /\ 17594333495296 <= SB /\ SB mod 4096 = 0 /\
               SB + 137438953472 + 4096 <= SP - 2048 /\ 2^46 + 4096 <= SP <= 2^47 /\ (QC + 32 <= SB \/ SB + 137438953472 + 4096 <= QC) /\
               B = SB + 103079215104 + 8192 * qj /\ 0 <= qj < 32 /\ 1 <= qn <= 1020 /\ 0 <= qb < 2^62 /\ 0 <= sz <= 2^40 /\ 0 <= mp < 2^64 /\
               0 <= mx < 2^62 /\ qb + sz <= mx) by (unfold B; lia).
  clear HQC HSB HSEP Hsz Hqj Hqb. clearbody B.
  assert (HSPa : bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) = SP) by (rgz; rewrite H2, u_wa_small by (zlh HZ); reflexivity).
  assert (P : AXF_qroomz.qroom_pre regs m QC B qn qb qb sz mp mx).
  { constructor; try assumption; try (zlh HZ).
    - rewrite H2. apply (stk_ok_shrink m (wa SP) 2048 1024); [lia | exact HSTK].
    - rewrite HSPa. zlh HZ.
    - rewrite Z.add_0_r. exact Rsz.
    - intros d k Hd Hk. rewrite Z.add_0_r. apply Wb; lia.
    - intros d k Hd Hk. replace (B + 8 * qn + 24 + d) with (B + (8 * qn + 24 + d)) by ring. apply Wb; clear - HZ Hd Hk; lia. }
  destruct (AXF_qroomz.qroom_proom regs m rom QC B qn qb qb sz mp mx P (sc_qroom regs m SP HSPa QC B qn qb qb sz mp mx ltac:(zlh HZ)))
    as (R & Hms & A1 & A9 & _ & _ & _ & _ & _ & _ & _ & _ & A22 & KK).
  clear P.
  set (v8 := bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))) in *. set (v18 := bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) in *.
  set (v19 := bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) in *. set (v20 := bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))) in *.
  set (v21 := bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) in *.
  set (m1 := wchainS m SP (LQD 277240 v8 QC v18 v19 v20 v21)).
  set (m' := wbytes (wbytes (wbytes (wbytes m1 (wa (B + 8)) (word_to_le_bytes 8 (wa (qb + sz)))) (wa (B + 16)) (word_to_le_bytes 8 (wa (qn + 1))))
                            (wa (B + 8 * qn + 24)) (word_to_le_bytes 8 (wa mp))) (wa (QC + 24)) (word_to_le_bytes 8 (wa (qb + sz)))).
  assert (EM : AXF_qroomz.qroom_mem_proom m regs QC B qn qb qb sz mp mx = m').
  { unfold AXF_qroomz.qroom_mem_proom, m', m1, LQD. cbn [wchainS]. rewrite HSPa. reflexivity. }
  rewrite EM in Hms. clear EM.
  assert (G1 : mem_grows m m1) by (apply wchainS_grows).
  assert (F1 : forall x, 0 <= x < 2^64 -> ~ (SP - 56 <= x < SP) -> m1 (wa x) = m (wa x)) by (intros x Hx Hn; apply qd_frame; [zlh HZ | exact Hx | exact Hn]).
  assert (FRM : forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ (QC + 24 <= x < QC + 32) -> ~ (B + 8 <= x < B + 24) ->
                  ~ (B + 24 + 8 * qn <= x < B + 32 + 8 * qn) -> m' (wa x) = m (wa x)).
  { intros x Hx Q1 Q2 Q3 Q4. unfold m'. repeat (rewrite wb_other by first [exact Hx | (lenq; zlh HZ) | (lenq; clear - HZ Q2 Q3 Q4; lia)]).
    apply F1; [exact Hx | clear - Q1; lia]. }
  assert (G : mem_grows m m') by (unfold m'; do 4 apply grows_wb; exact G1).
  exists R, m'. split; [exact Hms|].
  split.
  { intros k Hk. cbn [KQ In] in Hk.
    repeat (destruct Hk as [<-|Hk]; [first [ apply KK; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ]
                                           | (transitivity (wa 277240); [exact A1 | symmetry; exact H1])
                                           | (transitivity (wa QC); [exact A9 | symmetry; exact H9])
                                           | (transitivity (wa mx); [exact A22 | symmetry; exact H22]) ]|]).
    destruct Hk. }
  split.
  { unfold q_inv. replace (SB + 103079215104 + 8192 * qj) with B by (zlh HZ). split; [zlh HZ|]. split.
    { unfold m'. apply wb_rd_hit; [lia | zlh HZ | lenq; zlh HZ]. }
    right. split; [zlh HZ|]. split; [zlh HZ|].
    assert (RF : forall a w v, 0 <= a -> a + Z.of_nat w <= 2^64 -> ~ (SP - 2048 < a + Z.of_nat w /\ a < SP) -> ~ (QC + 24 < a + Z.of_nat w /\ a < QC + 32) ->
                   ~ (B + 8 < a + Z.of_nat w /\ a < B + 24) -> ~ (B + 24 + 8 * qn < a + Z.of_nat w /\ a < B + 32 + 8 * qn) -> rd m a w v -> rd m' a w v).
    { intros a w v Ha Haw Q1 Q2 Q3 Q4 Hr. apply (rd_frame m m'); [exact Ha | exact Haw | | exact Hr].
      intros x Hx. apply FRM; [lia | lia | lia | lia | lia]. }
    split; [apply RF; [zlh HZ | znq; zlh HZ | znq; zlh HZ | znq; zlh HZ | znq; zlh HZ | znq; zlh HZ | exact Rsz]|].
    split; [apply RF; [zlh HZ | znq; zlh HZ | znq; zlh HZ | znq; zlh HZ | znq; zlh HZ | znq; zlh HZ | exact Rfirst]|].
    split; [apply RF; [zlh HZ | znq; zlh HZ | znq; zlh HZ | znq; zlh HZ | znq; zlh HZ | znq; zlh HZ | exact Rlast]|].
    split.
    { unfold m'. apply wb_rd_other; [zlh HZ | lenq; zlh HZ | zlh HZ | lenq; zlh HZ | lenq; zlh HZ|].
      apply wb_rd_other; [zlh HZ | lenq; zlh HZ | zlh HZ | lenq; zlh HZ | lenq; zlh HZ|].
      apply wb_rd_other; [zlh HZ | lenq; zlh HZ | zlh HZ | lenq; zlh HZ | lenq; zlh HZ|].
      apply wb_rd_hit; [lia | zlh HZ | lenq; zlh HZ]. }
    split.
    { unfold m'. apply wb_rd_other; [zlh HZ | lenq; zlh HZ | zlh HZ | lenq; zlh HZ | lenq; zlh HZ|].
      apply wb_rd_other; [zlh HZ | lenq; zlh HZ | zlh HZ | lenq; zlh HZ | lenq; zlh HZ|].
      apply wb_rd_hit; [lia | zlh HZ | lenq; zlh HZ]. }
    intros d k Hd Hk. apply (store_ok_mono SEGS k m m' _ G). apply Wb; assumption. }
  split.
  { replace (B + 24 + 8 * qn) with (B + 8 * qn + 24) by ring.
    unfold m'. apply wb_rd_other; [zlh HZ | lenq; zlh HZ | zlh HZ | lenq; zlh HZ | lenq; zlh HZ|].
    apply wb_rd_hit; [lia | zlh HZ | lenq; zlh HZ]. }
  split; [exact FRM | exact G].
Qed.
End QROOM.
